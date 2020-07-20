#!/usr/bin/env python3
import argparse
import base64
import binascii
import cgi
import configparser
import datetime
import fcntl
import glob
import hashlib
import hmac
import html
import http.cookies
import http.server
import io
import ipaddress
import json
import os
import pwd
import qr
import random
import socket
import socketserver
import subprocess
import sys
import traceback
import urllib


class ConfigMultiDict(dict):
    def __setitem__(self, key, value):
        if key in self and isinstance(value, list):
            self[key].extend(value)
        else:
            super().__setitem__(key, value)


class IPList:
    @classmethod
    def from_str(cls, value):
        res = []
        for s in value.split(cls.separator):
            s = s.strip()
            if s:
                try:
                    addr = cls.parser(s)
                except ValueError:
                    continue
                res.append(addr)

        return res

    @classmethod
    def to_str(cls, value):
        return cls.separator.join(str(x) for x in value)

    @classmethod
    def valid_str(cls, value):
        for s in value.split(cls.separator):
            s = s.strip()
            try:
                cls.parser(s)
            except ValueError:
                return False

        return True


class CommaSepIPNets(IPList):
    separator = ','
    parser = ipaddress.ip_network


class MultilineIPIFaces(IPList):
    separator = os.linesep
    parser = ipaddress.ip_interface


class CommaSepIPIFaces(IPList):
    separator = ','
    parser = ipaddress.ip_interface


class MultilineIPAddrs(IPList):
    separator = os.linesep
    parser = ipaddress.ip_address


class CommaSepIPAddrs(IPList):
    separator = ','
    parser = ipaddress.ip_address


class OptBase64Key256:
    def from_str(value):
        return value

    @classmethod
    def to_str(cls, value):
        if not cls.valid_str(value):
            raise Exception('Invalid base64 key.')
        return value

    def valid_str(value):
        try:
            return not value or len(base64.b64decode(value, validate=True)) == 32
        except binascii.Error:
            return False


class UIntStr:
    def from_str(value):
        return value

    @classmethod
    def to_str(cls, value):
        if not cls.valid_str(value):
            raise Exception('Invalid UInt value')
        return value

    def valid_str(value):
        try:
            return not value or int(value) > 0
        except:
            return False


class TunnelConfig:
    __attrs = {
            'netdev_name': ['netdev', 'NetDev', 'Name'],
            'netdev_description': ['netdev', 'NetDev', 'Description'],
            'netdev_listen_port': ['netdev', 'WireGuard', 'ListenPort', UIntStr],
            'network_address': ['network', 'Network', 'Address', MultilineIPIFaces],
            'network_dns': ['network', 'Network', 'DNS', MultilineIPAddrs],
            'peer_public_key': ['peer', 'WireGuardPeer', 'PublicKey', OptBase64Key256],
            'peer_allowed_ips': ['peer', 'WireGuardPeer', 'AllowedIPs', CommaSepIPNets],
            'peer_preshared_key': ['peer', 'WireGuardPeer', 'PresharedKey', OptBase64Key256],
            'peer_persistent_keepalive': ['peer', 'WireGuardPeer', 'PersistentKeepalive', UIntStr],
    }

    def __init__(self, *, netdev=None, network=None, peer=None):
        def parse(path):
            config = configparser.ConfigParser(strict=False, dict_type=ConfigMultiDict)
            config.optionxform = lambda opt: opt
            if path:
                if not config.read(path):
                    path = None
            else:
                path = None
            return config, bool(path)

        self.__paths = {
                'netdev': netdev,
                'network': network,
                'peer': peer
                }

        self.__configs = {}
        self.__parsed = {}
        for n, p in self.__paths.items():
            self.__configs[n], self.__parsed[n] = parse(p)

        self.netdev_parsed = self.__parsed['netdev']
        self.network_parsed = self.__parsed['network']
        self.peer_parsed = self.__parsed['peer']
        self.netdev_file = self.__paths['netdev']
        self.network_file = self.__paths['network']
        self.peer_file = self.__paths['peer']
        self.netdev_public_key_file = None
        self.__peer_private_key = None

    @property
    def peer_private_key(self):
        return self.__peer_private_key

    @peer_private_key.setter
    def peer_private_key(self, value):
        self.__peer_private_key = OptBase64Key256.to_str(value)

    @property
    def netdev_public_key(self):
        try:
            return self.__netdev_public_key
        except AttributeError:
            pass

        if not self.netdev_public_key_file:
            return None

        try:
            with open(self.netdev_public_key_file, 'rt') as f:
                self.__netdev_public_key = f.read().strip()
        except:
            traceback.print_exc()
            return None

        return self.__netdev_public_key

    def __getitem__(self, key):
        path = self.__attrs[key]
        value = self.__configs[path[0]].get(path[1], path[2], fallback='')
        if len(path) >= 4:
            value = path[3].from_str(value)
        return value

    def __getattr__(self, key):
        if key not in self.__attrs:
            return super().__getattr__(key)
        return self.__getitem__(key)

    def __setitem__(self, key, value):
        path = self.__attrs[key]
        if len(path) >= 4:
            value = path[3].to_str(value)

        conf = self.__configs[path[0]]

        if value and not conf.has_section(path[1]):
            conf.add_section(path[1])

        if not value and conf.has_section(path[1]):
            conf.remove_option(path[1], path[2])

        if not value:
            return None

        return conf.set(path[1], path[2], value)

    def __setattr__(self, key, value):
        if key not in self.__attrs:
            return super().__setattr__(key, value)
        return self.__setitem__(key, value)

    def save_peer(self):
        with open(self.peer_file, 'w') as fo:
            self.__configs['peer'].write(fo)

    def write_peer_wgquick_config(self, out):
        peer_addrs = []
        addr_type_selected = set()
        for peer_subnet in self.peer_allowed_ips:
            if type(peer_subnet) in addr_type_selected:
                continue
            addr = next(iter(peer_subnet))
            prefix = peer_subnet.prefixlen
            for iface in self.network_address:
                if type(iface.network) == type(peer_subnet) and \
                        iface.network.supernet_of(peer_subnet):
                    prefix = iface.network.prefixlen
                    break
            iface_type = ipaddress.IPv4Interface if addr.version == 4 \
                    else ipaddress.IPv6Interface
            peer_addrs.append(iface_type((addr, prefix)))
            addr_type_selected.add(type(peer_subnet))

        conf = configparser.ConfigParser()
        conf.optionxform = lambda opt: opt

        conf.add_section('Interface')
        if peer_addrs:
            conf.set('Interface', 'Address', CommaSepIPIFaces.to_str(peer_addrs))
        if self.peer_private_key:
            conf.set('Interface', 'PrivateKey', self.peer_private_key)
        if self.network_dns:
            conf.set('Interface', 'DNS', CommaSepIPAddrs.to_str(self.network_dns))

        conf.add_section('Peer')
        if self.netdev_public_key:
            conf.set('Peer', 'PublicKey', self.netdev_public_key)
        if self.peer_preshared_key:
            conf.set('Peer', 'PresharedKey', self.peer_preshared_key)
        conf.set('Peer', 'AllowedIPs', '::/0,0.0.0.0/0')
        conf.set('Peer', 'Endpoint', socket.gethostname() + ':' + self.netdev_listen_port)
        if self.peer_persistent_keepalive:
            conf.set('Peer', 'PersistentKeepalive', self.peer_persistent_keepalive)

        class skip_blank_lines:
            def __init__(self, out):
                self.out = out
                self.end = False

            def write(self, s):
                s = ''.join(x[0] for x in zip(s, ' ' + s) if x != ('\n', '\n'))
                if s[:1] == '\n' and self.end:
                    s = s[1:]
                if s:
                    self.end = s[-1] == '\n'
                return self.out.write(s)

        conf.write(skip_blank_lines(out), space_around_delimiters=False)


def hash_password(password):
    password = password.encode('utf-8')
    salt = socket.gethostname().encode('utf-8')
    f = lambda k, m: hmac.new(k, m, hashlib.sha256).digest()
    u = f(password, salt)
    res = int.from_bytes(u, 'big')
    for i in range(5 * 10**5):
        u = f(password, u)
        res ^= int.from_bytes(u, 'big')
    return base64.b64encode(res.to_bytes(len(u), 'big')).decode('ascii')


class AdmHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    def __init__(self, netdev_file, network_file, pubkey_file, *args, **kwargs):
        self.netdev_file = netdev_file
        self.network_file = network_file
        self.pubkey_file = pubkey_file
        self.allow_reuse_address = True
        self.timeout = 20
        socketserver.ThreadingMixIn.__init__(self)
        http.server.HTTPServer.__init__(self, *args, **kwargs)

    @property
    def admin_pwdhash(self):
        try:
            return self.__admin_pwdhash
        except AttributeError:
            pass

        try:
            with open('/var/tmp/wgadm_pwdhash.bin', 'rt') as f:
                fcntl.lockf(f, fcntl.LOCK_SH)
                h = f.read().strip() or None
            if h:
                self.__admin_pwdhash = h
            return h
        except (FileNotFoundError, PermissionError):
            return None

    @admin_pwdhash.setter
    def admin_pwdhash(self, h):
        if not h:
            self.__admin_pwdhash = None
            del self.__admin_pwdhash
            return
        with open('/var/tmp/wgadm_pwdhash.bin', 'wt') as f:
            fcntl.lockf(f, fcntl.LOCK_EX)
            f.write(h)
        self.__admin_pwdhash = h

    @staticmethod
    def set_password(pwd):
        if not pwd:
            return
        h = hash_password(pwd)
        with open('/var/tmp/wgadm_pwdhash.bin', 'wt') as f:
            fcntl.lockf(f, fcntl.LOCK_EX)
            f.write(h)

    @property
    def jwt_key(self):
        try:
            return self.__jwt_key
        except AttributeError:
            pass

        with open('/var/tmp/wgadm_jwt_key.bin', 'ab+') as f:
            fcntl.lockf(f, fcntl.LOCK_SH)
            KEY_LEN = 32
            f.seek(0)
            key = f.read(KEY_LEN)
            if len(key) != KEY_LEN or os.fstat(f.fileno()).st_size != KEY_LEN:
                fcntl.lockf(f, fcntl.LOCK_UN)
                fcntl.lockf(f, fcntl.LOCK_EX)
                f.seek(0)
                key = f.read(KEY_LEN)
                if len(key) != KEY_LEN or os.fstat(f.fileno()).st_size != KEY_LEN:
                    key = random.getrandbits(KEY_LEN * 8).to_bytes(KEY_LEN, 'big')
                    f.seek(0)
                    f.truncate(0)
                    f.write(key)

        self.__jwt_key = key
        return self.__jwt_key


class AdmHTTPHandler(http.server.BaseHTTPRequestHandler):

    def begin(self):
        self.path_parts = urllib.parse.urlparse(self.path)
        self.out_body = io.BytesIO()
        self.in_body = b''
        clen = self.headers.get('Content-Length')
        if clen is not None:
            clen = int(clen)
            if clen > (32 << 20):
                self.send_error(413, explain='Maximum allowed size of body is 32MB')
                self.close_connection = True
                return False
            self.in_body = self.rfile.read(clen)
        elif self.command not in ['GET', 'HEAD']:
            raise Exception('Content-Length expected')

        self.user_agent = self.headers.get('User-Agent') or ''
        usr_agent = self.user_agent.lower()
        self.text_based_agent = 'links' in usr_agent or 'lynx' in usr_agent

        return True


    def echo(self, s):
        if type(s) == str:
            self.out_body.write(s.encode('utf-8'))
        else:
            self.out_body.write(s)
        return self


    def end(self):
        self.out_body.seek(0)
        b = self.out_body.read()
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.send_header('Content-Length', str(len(b)))
        self.end_headers()
        self.wfile.write(b)


    def quote_b64(self, s):
        bs = s if type(s) == bytes else s.encode('utf-8')
        return urllib.parse.quote(base64.b64encode(bs))

    def b64d_unquote(self, s):
        return base64.b64decode(urllib.parse.unquote(s)).decode('utf-8')


    def sign(self, s):
        data_to_sign = s.encode('utf-8')
        return hmac.new(self.server.jwt_key, data_to_sign, hashlib.sha256).digest()


    def echo_href_button(self, url, name):
        if self.text_based_agent:
            return self.echo('<a href="%s">%s</a>' % (url, name))
        else:
            return self.echo('<a href="%s"><button type="button">%s</button></a>' % (url, name))


    def check_authenticated(self):
        def redirect_to_auth():
            self.send_response(303)
            self.send_header('Cache-Control', 'no-store')
            self.send_header('Location', '/auth')
            self.end_headers()
            return False

        self.session = None

        cookie_hdr = self.headers.get('Cookie')
        if not cookie_hdr:
            return redirect_to_auth()

        cookies = http.cookies.SimpleCookie(cookie_hdr)
        session_cookie = cookies.get('session', None)
        if not session_cookie or not session_cookie.value:
            return redirect_to_auth()
        session_cookie = session_cookie.value

        parts = session_cookie.split('.')
        if len(parts) != 2:
            return redirect_to_auth()
        session_str, session_sign = parts
        session_str = self.b64d_unquote(session_str)

        if self.quote_b64(self.sign(session_str)) != session_sign:
            return redirect_to_auth()

        try:
            session = json.loads(session_str)
        except json.JSONDecodeError:
            return redirect_to_auth()

        if session.get('user', None) != 'admin':
            return redirect_to_auth()
        if session.get('valid_till', 0) < datetime.datetime.now().timestamp():
            return redirect_to_auth()
        self.session = session

        return True


    def auth_form(self):
        h = self.server.admin_pwdhash
        if not h and not ipaddress.ip_address(self.client_address[0]).is_loopback:
            self.send_response(200)
            self.echo('<html><body>Password not set.</body></html>\n')
            return

        self.send_response(200)
        self.echo(b'''<html><body>
        <form ation="/auth" method="POST" enctype="application/x-www-form=urlencoded">
        <p>Password: <input type="password" name="password" /></p>''')
        if not h:
            self.echo('''
            <p>Confirm password: <input type="password" name="password_confirm" /></p>''')
        self.echo(b'''
        <p><input type="submit" value="Login" /></p>
        </form>
        </body></html>''')
        self.echo('\n')


    def auth(self):
        def redirect_to_auth():
            self.send_response(303)
            self.send_header('Cache-Control', 'no-store')
            self.send_header('Location', '/auth')
            self.end_headers()

        form = cgi.FieldStorage(io.BytesIO(self.in_body), environ={'REQUEST_METHOD': 'POST'})
        password = form.getfirst('password')
        if not password:
            return redirect_to_auth()
        h = hash_password(password)

        if not self.server.admin_pwdhash:
            password_confirm = form.getfirst('password_confirm')
            if not password or password != password_confirm:
                return redirect_to_auth()
            self.server.admin_pwdhash = h

        if h != self.server.admin_pwdhash:
            return redirect_to_auth()

        session_str = json.dumps({'user': 'admin', 'valid_till': int((datetime.datetime.now() + datetime.timedelta(minutes=15)).timestamp())})
        ses_cookie_str = self.quote_b64(session_str) + '.' + self.quote_b64(self.sign(session_str))
        cookies = http.cookies.BaseCookie({'session': ses_cookie_str})
        cookies['session'].update({'httponly': True})

        self.send_response(303)
        self.flush_headers()
        self.wfile.write(cookies.output().encode('ascii') + b'\r\n')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Location', '/')
        self.end_headers()


    def view_all(self):
        conf = TunnelConfig(netdev=self.server.netdev_file, network=self.server.network_file)
        conf.netdev_public_key_file = self.server.pubkey_file

        self.send_response(200)
        self.echo('<html><body>')
        self.echo('NetDev.Name = %s<br/>\n' % html.escape(conf.netdev_name))
        self.echo('WireGuard.PublicKey = %s<br/>\n' % html.escape(conf.netdev_public_key or ''))
        self.echo('WireGuard.ListenPort = %s<br/>\n' % html.escape(conf.netdev_listen_port))
        for addr in conf.network_address:
            self.echo('Network.Address = %s<br/>\n' % html.escape(str(addr)))
        for dns in conf.network_dns:
            self.echo('Network.DNS = %s<br/>\n' % html.escape(str(dns)))

        self.echo('<br/>\nPeers:<br/>\n')
        self.echo('<table cellspacing="0" cellpadding="0" border="2" bordercolor="black">\n')
        self.echo('<tr><th>Name</th><th>Config</th><th>Edit</th><th>Delete</th></tr>\n')
        peer_files = glob.glob(os.path.join(self.server.netdev_file + '.d', '*.conf'))
        for peer_file in sorted(peer_files):
            if not os.path.isfile(peer_file):
                continue
            peer_name = os.path.splitext(os.path.split(peer_file)[1])[0]
            peer_conf = TunnelConfig(peer=peer_file)
            self.echo('<tr>')
            self.echo('<td>%s</td>\n' % html.escape(peer_name))
            self.echo('<td>PublicKey = %s<br/>\nAllowedIPs = %s' % (
                html.escape(peer_conf.peer_public_key),
                html.escape(CommaSepIPNets.to_str(peer_conf.peer_allowed_ips))))
            if peer_conf.peer_persistent_keepalive:
                self.echo('<br/>\nPersistentKeepalive = %s' %
                        html.escape(peer_conf.peer_persistent_keepalive))
            self.echo('</td>\n')
            self.echo('<td><a href="/editpeer?peer=%s">Edit</a></td>\n' % urllib.parse.quote(peer_name))
            self.echo('<td><a href="/delpeer?peer=%s">Delete</a></td>\n' % urllib.parse.quote(peer_name))
            self.echo('</tr>')
        self.echo('</table><br/>\n')

        self.echo('<a href="/addpeer">Add peer (unsafe)</a><br/>\n')

        self.echo('</body></html>')


    def peer_in_netdev_dir(self, peer_name):
        if not peer_name:
            return None
        if '/' in peer_name or '\\' in peer_name:
            return None
        filename = peer_name + '.conf'
        netdev_dir = os.path.abspath(self.server.netdev_file + '.d')
        file_path = os.path.abspath(os.path.join(netdev_dir, filename))
        file_dir, basename = os.path.split(file_path)
        if file_dir != netdev_dir or basename != filename:
            return None

        return file_path


    def peer_config_from_qs(self):
        query = urllib.parse.parse_qs(self.path_parts.query)
        peer_name = query.get('peer', [])
        if len(peer_name) != 1:
            self.send_error(404)
            return None, None
        peer_name = peer_name[0]

        peer_file = self.peer_in_netdev_dir(peer_name)
        if not peer_file:
            self.send_error(404)
            return None, peer_name

        config = TunnelConfig(netdev=self.server.netdev_file,
                network=self.server.network_file,
                peer=peer_file)

        if not config.peer_parsed:
            self.send_error(404)
            return None, peer_name

        return config, peer_name


    @staticmethod
    def update_peer_config(config, **kwargs):
        errors = []

        if 'public_key' in kwargs:
            public_key = kwargs['public_key']
            if OptBase64Key256.valid_str(public_key):
                config.peer_public_key = public_key
            else:
                errors.append('Invalid public key.')

        if 'persistent_keepalive' in kwargs:
            persistent_keepalive = kwargs['persistent_keepalive']
            if UIntStr.valid_str(persistent_keepalive):
                config.peer_persistent_keepalive = persistent_keepalive
            else:
                errors.append('Invalid persistent keepalive.')

        if 'preshared_key' in kwargs:
            preshared_key = kwargs['preshared_key']
            if OptBase64Key256.valid_str(preshared_key):
                config.peer_preshared_key = preshared_key
            else:
                errors.append('Invalid preshared key.')

        if 'allowed_ips' in kwargs:
            allowed_ips = kwargs['allowed_ips']
            if CommaSepIPNets.valid_str(allowed_ips):
                allowed_ips = CommaSepIPNets.from_str(allowed_ips)

                ips_ok = True
                for subnet in allowed_ips:
                    ok = False
                    for iface in config.network_address:
                        ok = type(subnet) == type(iface.network) and iface.network.supernet_of(subnet)
                        if ok:
                            break
                    if not ok:
                        ips_ok = False
                        errors.append('Allowed ips %s is not subnet of any Network.Address.'
                                % str(subnet))

                if ips_ok:
                    config.peer_allowed_ips = allowed_ips
            else:
                errors.append('Invalid allowed ips comma separated list.')

        if 'private_key' in kwargs:
            private_key = kwargs['private_key']
            if OptBase64Key256.valid_str(private_key):
                config.peer_private_key = private_key
            else:
                errors.append('Invalid private key.')

        return errors


    def edit_peer_form(self, errors=[]):
        config, peer_name = self.peer_config_from_qs()
        if not config:
            return

        self.send_response(200)
        self.echo('<html><body>\n')
        self.echo('Name: %s<br/>\n' % html.escape(peer_name))
        self.echo('<form action="%s" method="POST" enctype="application/x-www-form-urlencoded">\n' % html.escape(self.path))
        self.echo('Public key: <input name="public_key" size="50" value="%s"/><br/>\n' % html.escape(config.peer_public_key))
        self.echo('Allowed IPs: <input name="allowed_ips" size="50" value="%s"/><br/>\n' % html.escape(CommaSepIPNets.to_str(config.peer_allowed_ips)))
        self.echo('Preshared key: <input name="preshared_key" size="50" value="%s"/><br/>\n' % html.escape(config.peer_preshared_key))
        self.echo('Persistent keepalive: <input name="persistent_keepalive" size="5" value="%s"/><br/>\n' % html.escape(config.peer_persistent_keepalive))
        self.echo('<input type="submit" value="Save" />\n')
        self.echo_href_button('/', 'Cancel')
        self.echo('</form>\n')

        if errors:
            self.echo('<p>\n')
            self.echo('<h3>Errors:</h3>\n')
            self.echo('<ul>\n')
            for er in errors:
                self.echo('<li>%s</li>\n' % html.escape(er))
            self.echo('</ul>\n')
            self.echo('</p>\n')

        self.echo('</body></html>')


    def edit_peer(self):
        config, peer_name = self.peer_config_from_qs()
        if not config:
            return

        form = cgi.FieldStorage(io.BytesIO(self.in_body), environ={'REQUEST_METHOD': 'POST'})
        public_key = form.getfirst('public_key')
        allowed_ips = form.getfirst('allowed_ips')
        preshared_key = form.getfirst('preshared_key')
        persistent_keepalive = form.getfirst('persistent_keepalive')

        errors = self.update_peer_config(config, public_key=public_key,
                allowed_ips=allowed_ips, preshared_key=preshared_key,
                persistent_keepalive=persistent_keepalive)

        if errors:
            return self.edit_peer_form(errors)

        config.save_peer()

        self.send_response(303)
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Location', self.path)
        self.end_headers()


    def delete_peer_form(self, errors = []):
        config, peer_name = self.peer_config_from_qs()
        if not config:
            return

        self.send_response(200)
        self.echo('<html><body>\n')
        self.echo('Enter peer name <b>%s</b> to confirm you want to delete it.' %
                html.escape(peer_name))
        self.echo('<form action="%s" method="POST" enctype="application/x-www-form-urlencoded">\n' %
                html.escape(self.path))
        self.echo('<input name="confirm_peer" />\n')
        self.echo('<input type="submit" value="Delete" />\n')
        self.echo('</form>\n')

        if errors:
            self.echo('<p>\n')
            self.echo('<h3>Errors:</h3>\n')
            self.echo('<ul>\n')
            for er in errors:
                self.echo('<li>%s</li>\n' % html.escape(er))
            self.echo('</ul>\n')
            self.echo('</p>\n')

        self.echo('</body></html>')

    def delete_peer(self):
        config, peer_name = self.peer_config_from_qs()
        if not config:
            return

        form = cgi.FieldStorage(io.BytesIO(self.in_body), environ={'REQUEST_METHOD': 'POST'})
        confirm_peer = form.getfirst('confirm_peer')

        if peer_name != confirm_peer:
            return self.delete_peer_form(['You entered incorrect peer name.'])

        try:
            os.remove(config.peer_file)
        except Exception as e:
            return self.delete_peer_form([str(e)])

        self.send_response(303)
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Location', '/')
        self.end_headers()


    def add_peer_form(self, errors=[]):
        used_subnets = {}
        for peer_file in glob.glob(os.path.join(self.server.netdev_file +'.d', '*.conf')):
            peer_conf = TunnelConfig(peer=peer_file)
            for allowed_ips in peer_conf.peer_allowed_ips:
                used_subnets.setdefault(type(allowed_ips), []).append(allowed_ips)

        conf = TunnelConfig(network=self.server.network_file)
        for iface in conf.network_address:
            net_t = type(iface.network)
            used_subnets.setdefault(net_t, []).append(net_t(iface.ip, iface.ip.max_prefixlen))

        suggest_allowed_ips = []
        for iface in conf.network_address:
            net_t = type(iface.network)
            used = used_subnets.get(net_t, [])
            for ip in iface.network.hosts():
                ip_net = net_t(ip, ip.max_prefixlen)
                found_used = False
                for u in used:
                    found_used = u.supernet_of(ip_net)
                    if found_used:
                        break
                if not found_used:
                    suggest_allowed_ips.append(ip_net)
                    break

        self.send_response(200)
        self.echo('<html><body>\n')
        self.echo('<form action="%s" method="POST" enctype="application/x-www-form-urlencoded">\n' % html.escape(self.path))
        self.echo('Name *: <input name="name"/><br/>\n')
        self.echo('Public key: <input name="public_key" size="50"/><br/>\n')
        self.echo('Preshared key: <input type="checkbox" name="need_preshared_key" checked="checked"/> \n')
        self.echo('<input name="preshared_key" size="50"/><br/>\n')
        self.echo('Allowed IPs: <input name="allowed_ips" size="50" value="%s"/><br/>\n' % html.escape(CommaSepIPNets.to_str(suggest_allowed_ips)))
        self.echo('Persistent keepalive: <input name="persistent_keepalive" size="5"/><br/>\n')
        self.echo('<input type="submit" value="Save" />\n')
        self.echo_href_button('/', 'Cancel')
        self.echo('</form>\n')

        if errors:
            self.echo('<p>\n')
            self.echo('<h3>Errors:</h3>\n')
            self.echo('<ul>\n')
            for er in errors:
                self.echo('<li>%s</li>\n' % html.escape(er))
            self.echo('</ul>\n')
            self.echo('</p>\n')

        self.echo('</body></html>\n')


    def add_peer(self):
        form = cgi.FieldStorage(io.BytesIO(self.in_body), environ={'REQUEST_METHOD': 'POST'})
        peer_name = form.getfirst('name')
        public_key = form.getfirst('public_key')
        need_preshared_key = form.getfirst('need_preshared_key') is not None
        preshared_key = form.getfirst('preshared_key')
        allowed_ips = form.getfirst('allowed_ips')
        persistent_keepalive = form.getfirst('persistent_keepalive')

        errors = []

        peer_file = self.peer_in_netdev_dir(peer_name)
        if not peer_file:
            errors.append('Invalid peer name.')

        config = TunnelConfig(netdev=self.server.netdev_file,
                network=self.server.network_file,
                peer=peer_file)

        if config.peer_parsed:
            errors.append('Peer with name "%s" already exists.' % peer_name)

        if need_preshared_key and not preshared_key:
            preshared_key = base64.b64encode(random.getrandbits(256).to_bytes(32, 'big')).decode('ascii')

        private_key = None
        if not public_key:
            try:
                keys = subprocess.check_output(
                    b'PRIVKEY=$(openssl genpkey -algorithm x25519 -outform pem) ; '
                    b'echo "$PRIVKEY" | openssl pkey -inform pem -pubout -outform der | tail -c 32 | base64 ; '
                    b'echo "$PRIVKEY" | openssl pkey -inform pem -outform der | tail -c 32 | base64',
                    shell=True)
                keys = keys.decode('ascii').strip().split('\n')
                if len(keys) == 2:
                    public_key, private_key = keys
                else:
                    errors.append('Error while generating key pair.')
            except subprocess.CalledProcessError:
                errors.append('Error while generating key pair.')

        errors += self.update_peer_config(config, public_key=public_key,
                preshared_key=preshared_key, allowed_ips=allowed_ips,
                persistent_keepalive=persistent_keepalive,
                private_key=private_key)

        if errors:
            return self.add_peer_form(errors)

        config.save_peer()

        config.netdev_public_key_file = self.server.pubkey_file
        wgquick_conf = io.StringIO()
        config.write_peer_wgquick_config(wgquick_conf)
        wgquick_conf = wgquick_conf.getvalue()

        code = qr.QRCode(error_correction=qr.ERROR_CORRECT_L)
        code.add_data(wgquick_conf.encode('utf-8'))
        matr = code.get_matrix()

        usr_agent = (self.headers.get('User-Agent') or '').lower()

        self.send_response(200)
        self.echo('<html><body>\n')

        if 'links' in usr_agent or 'lynx' in usr_agent:
            self.echo('<table bgcolor="white"><tr><td>\n')
            self.echo('<font color="black">\n')
            for matr_r in matr:
                for el in matr_r:
                    self.echo(('&#x2588;' if el else '&nbsp;') * 2)
                self.echo('<br/>\n')
            self.echo('</font>\n')
            self.echo('</td></tr></table>\n')
        else:
            self.echo('<table border="0" cellspacing="0" cellpadding="0" rules="none" width="800px" height="800px">\n')
            for matr_r in matr:
                self.echo('<tr>\n')
                for el in matr_r:
                    self.echo('<td bgcolor="%s"/>' % ('black' if el else 'white'))
                self.echo('</tr>\n')
            self.echo('</table>\n')

        self.echo('<form action="/dlconfig" method="POST" enctype="application/x-www-form-urlencoded">\n')
        self.echo('<textarea name="config" cols="75" rows="11">%s</textarea><br/>\n' %
                html.escape(wgquick_conf))
        self.echo('<input type="submit" value="Download" />\n')
        self.echo_href_button('/editpeer?peer=%s' % html.escape(peer_name), 'Edit')
        self.echo_href_button('/', 'Cancel')
        self.echo('</form>\n')
        self.echo('</body></html>\n')


    def dlconfig(self):
        form = cgi.FieldStorage(io.BytesIO(self.in_body), environ={'REQUEST_METHOD': 'POST'})
        config = form.getfirst('config').encode('utf-8')
        self.send_response(200)
        self.send_header('Content-Type', 'application/octet-stream')
        self.send_header('Content-Disposition', 'attachment; filename="wg.conf"')
        self.send_header('Content-Length', len(config))
        self.end_headers()
        self.wfile.write(config)


    def get_file(self, path=None, content_type='application/octet-stream'):
        path = path or self.path[1:]
        try:
            stat = os.stat(path)
            self.send_response(200)
            if content_type:
                self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(stat.st_size))
            self.end_headers()
            with open(path, 'rb') as f:
                while True:
                    data = f.read(1024**2)
                    if not data:
                        break
                    self.wfile.write(data)

        except FileNotFoundError:
            return self.send_error(404)


    def do_GET(self):
        try:
            if not self.begin():
                return
            if self.path_parts.path not in ('/auth', '/favicon.ico') and \
                    not self.check_authenticated():
                return

            if self.path_parts.path == '/auth':
                self.auth_form()
            elif self.path_parts.path == '/':
                self.view_all()
            elif self.path_parts.path == '/editpeer':
                self.edit_peer_form()
            elif self.path_parts.path == '/delpeer':
                self.delete_peer_form()
            elif self.path_parts.path == '/addpeer':
                self.add_peer_form()
            else:
                return self.send_error(404)

            self.end()
        except Exception as e:
            self.send_error(500)
            self.close_connection = True
            self.request.close()
            traceback.print_exc()
        finally:
            sys.stderr.flush()
            sys.stdout.flush()


    def do_POST(self):
        try:
            if not self.begin():
                return

            if self.path_parts.path == '/auth':
                self.auth()
                return

            if not self.check_authenticated():
                return

            if self.path_parts.path == '/editpeer':
                self.edit_peer()
            elif self.path_parts.path == '/delpeer':
                self.delete_peer()
            elif self.path_parts.path == '/addpeer':
                self.add_peer()
            elif self.path_parts.path == '/dlconfig':
                self.dlconfig()
            else:
                return self.send_error(404)
            self.end()
        except Exception as e:
            self.send_error(500)
            self.close_connection = True
            self.request.close()
            traceback.print_exc()
        finally:
            sys.stderr.flush()
            sys.stdout.flush()


def run_server(listen_port, netdev_file, network_file, pubkey_file):
    httpd = AdmHTTPServer(netdev_file, network_file, pubkey_file, ('', listen_port), AdmHTTPHandler)
    nobody = pwd.getpwnam('nobody')
    os.setegid(nobody.pw_gid)
    os.seteuid(nobody.pw_uid)
    httpd.serve_forever()

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--port', metavar='PORT', type=int, default=80, nargs='?')
    parser.add_argument('--netdev', metavar='NETDEV_FILE', required=True)
    parser.add_argument('--network', metavar='NETWORK_FILE', required=True)
    parser.add_argument('--pubkey', metavar='SERVER_PUBKEY_FILE', default=None)
    parser.add_argument('--set-password', action='store_true')
    args = parser.parse_args()
    if args.set_password:
        import getpass
        pwd = getpass.getpass('Enter new wgadm password: ')
        AdmHTTPServer.set_password(pwd)
    else:
        run_server(args.port, args.netdev, args.network, args.pubkey)
