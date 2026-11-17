import html
from html.parser import HTMLParser
import ipaddress
import json
import mimetypes
import os
from pathlib import Path
import re
import socket
from functools import lru_cache
import threading
import time
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, unquote, urljoin, urlsplit, urlunsplit
from urllib.request import HTTPRedirectHandler, ProxyHandler, Request, build_opener
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from core import extract_metadata


HOST = '127.0.0.1'
PORT = int(os.environ.get('TECHNETIUM_FRONTEND_PORT', '8000'))
PROXY_URL = os.environ.get('TECHNETIUM_PROXY', 'http://127.0.0.1:8080')
FRONTEND_DIR = Path(__file__).resolve().parent.parent / 'frontend'
REQUEST_TIMEOUT = 20
MAX_PAGE_BYTES = 5 * 1024 * 1024
MAX_RESOURCE_BYTES = 12 * 1024 * 1024
MAX_REDIRECTS = 8
MAX_DEBUG_ENTRIES = 200
PUBLIC_PORTS = {80, 443}

MIME_TYPES = {
    '.css': 'text/css',
    '.html': 'text/html',
    '.js': 'text/javascript',
    '.svg': 'image/svg+xml',
}

_css_url_pattern = re.compile(r'url\(\s*(["\']?)(.*?)\1\s*\)', re.IGNORECASE)
_css_import_pattern = re.compile(r'@import\s+(["\'])(.*?)\1', re.IGNORECASE)
_unsafe_css_pattern = re.compile(
    r'expression\s*\(|-moz-binding\s*:|(?:^|[;{])\s*behavior\s*:|javascript\s*:', re.IGNORECASE)
_debug_entries = []
_debug_lock = threading.Lock()


def _redact_debug_url(url):
    try:
        parsed = urlsplit(url)
        hostname = parsed.hostname
        port = parsed.port
    except ValueError:
        return '<invalid URL>'
    if hostname is None:
        return '<invalid URL>'
    host = '[' + hostname + ']' if ':' in hostname else hostname
    netloc = host + (':' + str(port) if port is not None else '')
    return urlunsplit((
        parsed.scheme,
        netloc,
        parsed.path,
        '[redacted]' if parsed.query else '',
        '',
    ))


def _record_debug_entry(kind, url, status, content_type, duration_ms, error=None):
    entry = {
        'time': time.strftime('%H:%M:%S'),
        'method': 'GET',
        'kind': kind,
        'url': _redact_debug_url(url),
        'status': status,
        'content_type': content_type,
        'duration_ms': round(duration_ms, 1),
    }
    if error:
        entry['error'] = error
    with _debug_lock:
        _debug_entries.append(entry)
        del _debug_entries[:-MAX_DEBUG_ENTRIES]


def _get_debug_entries(limit=100):
    with _debug_lock:
        return list(_debug_entries[-limit:])


class TechnetiumProxyHandler(ProxyHandler):
    def proxy_open(self, req, proxy, request_type):
        proxy_url = urlsplit(proxy)
        if proxy_url.scheme.lower() not in ('http', 'https') or not proxy_url.netloc:
            raise ValueError('TECHNETIUM_PROXY must be an HTTP or HTTPS proxy URL.')
        req.set_proxy(proxy_url.netloc, proxy_url.scheme.lower())
        return None


class NoRedirectHandler(HTTPRedirectHandler):
    def redirect_request(self, request, response, code, message, headers, new_url):
        return None


_proxy_opener = build_opener(
    TechnetiumProxyHandler({'http': PROXY_URL, 'https': PROXY_URL}),
    NoRedirectHandler(),
)


def validate_url(url):
    """Return a normalized public HTTP(S) URL or raise ValueError."""
    if not isinstance(url, str) or len(url) > 4096:
        raise ValueError('The URL is missing or too long.')
    parsed = urlsplit(url.strip())
    scheme = parsed.scheme.lower()
    if scheme not in ('http', 'https') or not parsed.hostname:
        raise ValueError('Only complete HTTP and HTTPS URLs are supported.')
    if parsed.username is not None or parsed.password is not None:
        raise ValueError('URLs containing credentials are not supported.')
    try:
        configured_port = parsed.port
        port = configured_port if configured_port is not None else (443 if scheme == 'https' else 80)
    except ValueError as error:
        raise ValueError('The URL contains an invalid port.') from error
    if port not in PUBLIC_PORTS:
        raise ValueError('Only the standard HTTP and HTTPS ports are supported.')

    host = parsed.hostname.rstrip('.').lower()
    if host == 'localhost' or host.endswith('.localhost') or host.endswith('.local'):
        raise ValueError('Local network destinations are not allowed.')
    if not _host_is_public(host, port):
        raise ValueError('Local and private network destinations are not allowed.')

    return urlunsplit((scheme, parsed.netloc, parsed.path or '/', parsed.query, ''))


@lru_cache(maxsize=512)
def _host_is_public(host, port):
    try:
        addresses = [ipaddress.ip_address(host)]
    except ValueError:
        try:
            addresses = [
                ipaddress.ip_address(result[4][0].split('%')[0])
                for result in socket.getaddrinfo(host, port, type=socket.SOCK_STREAM)
            ]
        except (OSError, ValueError):
            return False
    return bool(addresses) and all(address.is_global for address in addresses)


def _read_response(url, max_bytes, referer=None):
    current_url = validate_url(url)
    visited = set()
    for _ in range(MAX_REDIRECTS + 1):
        current_url = validate_url(current_url)
        if current_url in visited:
            raise ValueError('The destination returned a redirect loop.')
        visited.add(current_url)

        request_headers = {
            'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/150.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,image/svg+xml,*/*;q=0.8',
            'Accept-Encoding': 'identity',
            'Connection': 'close',
        }
        if referer:
            try:
                request_headers['Referer'] = validate_url(referer)
            except ValueError:
                pass
        request = Request(current_url, headers=request_headers, method='GET')
        try:
            response = _proxy_opener.open(request, timeout=REQUEST_TIMEOUT)
        except HTTPError as error:
            response = error
        except (URLError, OSError, TimeoutError) as error:
            raise RuntimeError(
                'The request could not be completed through the Technetium proxy.') from error

        with response:
            status = response.getcode()
            headers = response.headers
            location = headers.get('Location')
            if status in (301, 302, 303, 307, 308) and location:
                current_url = urljoin(current_url, location)
                continue
            try:
                body = response.read(max_bytes + 1)
            except (OSError, TimeoutError) as error:
                raise RuntimeError('The destination response could not be read.') from error
            if len(body) > max_bytes:
                raise ValueError('The destination response exceeds the size limit.')
            return current_url, status, headers, body
    raise ValueError('The destination redirected too many times.')


def _resource_url(url, base_url):
    absolute = urljoin(base_url, url.strip())
    try:
        absolute = validate_url(absolute)
    except ValueError:
        return ''
    referer = validate_url(base_url)
    return '/api/resource?url=' + quote(absolute, safe='') + '&referer=' + quote(referer, safe='')


def _rewrite_css(css, base_url):
    css = _unsafe_css_pattern.sub('', css)

    def replace_url(match):
        resource = _resource_url(match.group(2), base_url)
        return 'url("' + resource + '")' if resource else 'url("")'

    css = _css_url_pattern.sub(replace_url, css)
    return _css_import_pattern.sub(
        lambda match: '@import url("' + (_resource_url(match.group(2), base_url) or '') + '")',
        css)


class SanitizingHTMLParser(HTMLParser):
    _void_tags = {
        'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link',
        'meta', 'param', 'source', 'track', 'wbr',
    }
    _removed_subtrees = {'script', 'iframe', 'object', 'embed', 'frame', 'frameset', 'svg'}

    def __init__(self, base_url):
        super().__init__(convert_charrefs=True)
        self.base_url = base_url
        self.output = []
        self.links = []
        self.hidden = []
        self.title_text = []
        self.link_stack = []
        self.in_title = False

    def handle_starttag(self, tag, attrs):
        tag = tag.lower()
        if self.hidden:
            if tag == self.hidden[-1]:
                self.hidden.append(tag)
            return
        if tag in self._removed_subtrees:
            self.hidden.append(tag)
            return
        if tag == 'title':
            self.in_title = True

        values = dict(attrs)
        if tag == 'base':
            base_href = values.get('href')
            if base_href:
                try:
                    self.base_url = validate_url(urljoin(self.base_url, base_href))
                except ValueError:
                    pass
            return
        if tag == 'link':
            rel = (values.get('rel') or '').lower().split()
            if 'stylesheet' not in rel:
                return

        safe_attrs = []
        for name, value in attrs:
            name = name.lower()
            value = value or ''
            if name.startswith('on') or name in {
                    'srcdoc', 'action', 'formaction', 'integrity', 'nonce', 'background',
                    'cite', 'longdesc', 'manifest', 'ping', 'profile', 'xlink:href',
                    'data-technetium-url'}:
                continue
            if name == 'style':
                safe_attrs.append((name, _rewrite_css(value, self.base_url)))
            elif name == 'srcset':
                candidates = []
                for candidate in value.split(','):
                    parts = candidate.strip().split()
                    if parts:
                        rewritten = _resource_url(parts[0], self.base_url)
                        if rewritten:
                            candidates.append(' '.join([rewritten] + parts[1:]))
                if candidates:
                    safe_attrs.append((name, ', '.join(candidates)))
            elif name in ('src', 'poster'):
                rewritten = _resource_url(value, self.base_url)
                if rewritten:
                    safe_attrs.append((name, rewritten))
            elif name == 'href':
                if tag == 'link':
                    rewritten = _resource_url(value, self.base_url)
                    if rewritten:
                        safe_attrs.append((name, rewritten))
                elif tag in ('a', 'area'):
                    try:
                        absolute = validate_url(urljoin(self.base_url, value))
                        if tag == 'a':
                            safe_attrs.append(('href', '#'))
                            safe_attrs.append(('data-technetium-url', absolute))
                            self.links.append({'text': '', 'url': absolute})
                            self.link_stack.append(len(self.links) - 1)
                    except ValueError:
                        continue
            elif name not in ('target', 'download', 'http-equiv', 'content', 'charset'):
                safe_attrs.append((name, value))

        attrs_text = ''.join(
            ' ' + name + '="' + html.escape(value, quote=True) + '"'
            for name, value in safe_attrs)
        self.output.append('<' + tag + attrs_text + '>')

    def handle_startendtag(self, tag, attrs):
        hidden_depth = len(self.hidden)
        self.handle_starttag(tag, attrs)
        if len(self.hidden) > hidden_depth:
            self.hidden.pop()
        elif tag.lower() not in self._void_tags:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        tag = tag.lower()
        if self.hidden:
            if tag == self.hidden[-1]:
                self.hidden.pop()
            return
        if tag == 'title':
            self.in_title = False
        if tag == 'a' and self.link_stack:
            self.link_stack.pop()
        if tag not in self._void_tags:
            self.output.append('</' + tag + '>')

    def handle_data(self, data):
        if self.hidden:
            return
        if self.in_title:
            self.title_text.append(data)
        if self.link_stack:
            index = self.link_stack[-1]
            self.links[index]['text'] += data
        if self.output and self.output[-1].startswith('<style'):
            self.output.append(_rewrite_css(data, self.base_url))
        else:
            self.output.append(html.escape(data))


def sanitize_html(source, base_url):
    parser = SanitizingHTMLParser(base_url)
    parser.feed(source)
    parser.close()
    links = [
        {'text': ' '.join(link['text'].split()), 'url': link['url']}
        for link in parser.links
    ]
    return ''.join(parser.output), links, ''.join(parser.title_text).strip()


def _decode_body(body, content_type):
    charset = 'utf-8'
    match = re.search(r'charset\s*=\s*["\']?([^;"\']+)', content_type or '', re.IGNORECASE)
    if match:
        charset = match.group(1).strip()
    try:
        return body.decode(charset, errors='replace')
    except LookupError:
        return body.decode('utf-8', errors='replace')


class FrontendRequestHandler(BaseHTTPRequestHandler):
    server_version = 'TechnetiumFrontend/1.0'
    protocol_version = 'HTTP/1.1'

    def _send(self, status, body, content_type, extra_headers=None):
        self.send_response(status)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Cache-Control', 'no-store')
        if extra_headers:
            for name, value in extra_headers.items():
                self.send_header(name, value)
        self.end_headers()
        self.wfile.write(body)

    def _send_json(self, status, data):
        body = json.dumps(data, ensure_ascii=False).encode('utf-8')
        self._send(status, body, 'application/json; charset=utf-8')

    def _check_host(self):
        host = self.headers.get('Host', '').split(':')[0].strip('[]').lower()
        return host in {'localhost', '127.0.0.1'}

    def do_GET(self):
        if not self._check_host():
            self._send_json(403, {'error': 'This server only accepts localhost requests.'})
            return

        parsed = urlsplit(self.path)
        if parsed.path == '/api/browse':
            self._browse(parse_qs(parsed.query).get('url', [''])[0])
        elif parsed.path == '/api/resource':
            query = parse_qs(parsed.query)
            self._resource(
                query.get('url', [''])[0],
                query.get('referer', [''])[0],
            )
        elif parsed.path == '/api/debug/logs':
            try:
                limit = int(parse_qs(parsed.query).get('limit', ['100'])[0])
            except ValueError:
                self._send_json(400, {'error': 'The log limit must be an integer.'})
                return
            self._send_json(200, {'entries': _get_debug_entries(max(1, min(limit, 200)))})
        else:
            self._static_file(parsed.path)

    def _browse(self, url):
        started = time.perf_counter()
        final_url = url
        status = None
        content_type = None
        debug_error = None
        try:
            final_url, status, headers, body = _read_response(url, MAX_PAGE_BYTES)
            content_type = headers.get('Content-Type', 'application/octet-stream')
            if 'text/html' not in content_type.lower():
                debug_error = 'Destination did not return HTML'
                self._send_json(415, {
                    'url': final_url,
                    'status': status,
                    'content_type': content_type,
                    'error': 'This destination did not return an HTML page.',
                })
                return
            metadata = extract_metadata(body, content_type, final_url)
            page_html, links, title = sanitize_html(_decode_body(body, content_type), final_url)
            link_urls = {link['url'] for link in links}
            for link_url in metadata.links:
                try:
                    safe_url = validate_url(link_url)
                except ValueError:
                    continue
                if safe_url not in link_urls:
                    links.append({'text': '', 'url': safe_url})
                    link_urls.add(safe_url)
            canonical_url = None
            if metadata.canonical_url:
                try:
                    canonical_url = validate_url(metadata.canonical_url)
                except ValueError:
                    pass
            safe_headers = {
                name.lower(): headers.get(name)
                for name in ('Content-Type', 'Last-Modified', 'ETag')
                if headers.get(name)
            }
            self._send_json(status, {
                'url': final_url,
                'status': status,
                'content_type': content_type.split(';', 1)[0].strip(),
                'headers': safe_headers,
                'title': title or metadata.title,
                'description': metadata.description,
                'canonical_url': canonical_url,
                'html': page_html,
                'links': links,
            })
        except ValueError as error:
            debug_error = str(error)
            self._send_json(400, {'error': str(error)})
        except RuntimeError as error:
            debug_error = str(error)
            self._send_json(502, {'error': str(error)})
        finally:
            _record_debug_entry(
                'page', final_url, status, content_type,
                (time.perf_counter() - started) * 1000, debug_error)

    def _resource(self, url, referer=None):
        started = time.perf_counter()
        final_url = url
        status = None
        content_type = None
        debug_error = None
        try:
            final_url, status, headers, body = _read_response(
                url, MAX_RESOURCE_BYTES, referer)
            content_type = headers.get('Content-Type', '').split(';', 1)[0].strip().lower()
            if not (content_type.startswith('image/')
                    or content_type == 'text/css'
                    or content_type.startswith('font/')
                    or content_type in ('application/font-woff', 'application/font-woff2',
                                        'application/vnd.ms-fontobject')):
                debug_error = 'Unsupported resource type'
                self._send_json(415, {'error': 'This resource type is not supported.'})
                return
            if status < 200 or status >= 300:
                debug_error = 'Resource returned an unsuccessful status'
                self._send_json(status, {'error': 'The resource could not be loaded.'})
                return
            if content_type == 'text/css':
                body = _rewrite_css(_decode_body(body, headers.get('Content-Type')), final_url).encode('utf-8')
                content_type = 'text/css; charset=utf-8'
            self._send(status, body, content_type, {
                'Access-Control-Allow-Origin': '*',
            })
        except ValueError as error:
            debug_error = str(error)
            self._send_json(400, {'error': str(error)})
        except RuntimeError as error:
            debug_error = str(error)
            self._send_json(502, {'error': str(error)})
        finally:
            _record_debug_entry(
                'resource', final_url, status, content_type,
                (time.perf_counter() - started) * 1000, debug_error)

    def _static_file(self, request_path):
        relative = unquote(request_path).lstrip('/')
        if not relative:
            relative = 'index.html'
        target = (FRONTEND_DIR / relative).resolve()
        if not target.is_relative_to(FRONTEND_DIR.resolve()) or not target.is_file():
            self._send_json(404, {'error': 'File not found.'})
            return
        body = target.read_bytes()
        content_type = MIME_TYPES.get(target.suffix.lower())
        if not content_type:
            content_type = mimetypes.guess_type(str(target))[0] or 'application/octet-stream'
        headers = {}
        if target.name == 'index.html':
            headers['Content-Security-Policy'] = (
                "default-src 'self'; frame-src 'self'; img-src 'self' data:; "
                "style-src 'self' 'unsafe-inline'; script-src 'self'; connect-src 'self'; "
                "object-src 'none'; base-uri 'none'; frame-ancestors 'none'")
            headers['Referrer-Policy'] = 'no-referrer'
        self._send(200, body, content_type + ('; charset=utf-8' if content_type.startswith('text/') else ''), headers)

    def log_message(self, format_string, *args):
        print('%s - %s' % (self.address_string(), format_string % args))


def serve_forever():
    server = ThreadingHTTPServer((HOST, PORT), FrontendRequestHandler)
    server.daemon_threads = True
    print('Technetium frontend is serving http://%s:%d' % (HOST, PORT))
    print('Using Technetium proxy at %s' % PROXY_URL)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nStopping Technetium frontend.')
    finally:
        server.server_close()


if __name__ == '__main__':
    serve_forever()
