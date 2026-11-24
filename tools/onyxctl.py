#!/usr/bin/env python3
"""onyxctl: drive a running OnyxOS guest over the DevLink socket.

The guest-side half is user/agent.c.  This tool speaks the framed protocol
it implements; every request has a timeout and a retry budget, and a
failure reports the request id and how many bytes arrived before giving
up, because a silent hang is the least useful outcome for a dev channel.

    onyxctl ping
    onyxctl exec testrun cowtest
    onyxctl put ./_echo /tmp/echo 0755
    onyxctl get /tmp/out.txt ./out.txt
    onyxctl stat /etc/passwd
    onyxctl klog --seq 0
    onyxctl watch user            # rebuild, upload and run on save

Only the standard library is used.  This is a development interface, not
a remote-administration protocol: it has no authentication and must be
reachable only through a local UNIX socket by a root guest process.
"""

import argparse
import hashlib
import os
import shlex
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

MAGIC = 0x58594E4F  # "ONYX" little endian
HDR = struct.Struct("<IBBHI")
HDRSZ = HDR.size
MAX_PAYLOAD = 4000
MAX_BODY = 64 * 1024
MORE = 0x1

T_PING, T_EXEC, T_PUT, T_GET, T_STAT, T_KLOG = 1, 2, 3, 4, 5, 6
R_MASK = 0x80
NAMES = {T_PING: "ping", T_EXEC: "exec", T_PUT: "put", T_GET: "get",
         T_STAT: "stat", T_KLOG: "klog"}

DEFAULT_SOCKET = os.environ.get("DEVSOCKET", str(Path.home() / ".onyx-dev" / "dev.sock"))
DEFAULT_TIMEOUT = float(os.environ.get("ONYXCTL_TIMEOUT", "5"))
DEFAULT_RETRIES = int(os.environ.get("ONYXCTL_RETRIES", "2"))


class Error(Exception):
    pass


class Client:
    """One connection to the guest agent."""

    def __init__(self, path=DEFAULT_SOCKET, timeout=DEFAULT_TIMEOUT,
                 retries=DEFAULT_RETRIES):
        self.path = path
        self.timeout = timeout
        self.retries = retries
        self.sock = None
        self.next_id = 1

    def connect(self, wait=0.0):
        deadline = time.monotonic() + wait
        while True:
            s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            try:
                s.settimeout(self.timeout)
                s.connect(self.path)
                self.sock = s
                return self
            except OSError as exc:
                s.close()
                if time.monotonic() >= deadline:
                    raise Error(f"{self.path}: {exc.strerror or exc}") from None
                time.sleep(0.1)

    def close(self):
        if self.sock:
            self.sock.close()
            self.sock = None

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    # -- framing ---------------------------------------------------------

    def _recv_exact(self, n):
        buf = b""
        while len(buf) < n:
            try:
                chunk = self.sock.recv(n - len(buf))
            except socket.timeout:
                raise Error(f"timeout after {len(buf)} of {n} bytes") from None
            except OSError as exc:
                raise Error(f"socket error after {len(buf)} of {n} bytes: "
                            f"{exc}") from None
            if not chunk:
                raise Error(f"connection closed after {len(buf)} of {n} bytes")
            buf += chunk
        return buf

    def _send_frames(self, typ, rid, payload):
        off = 0
        try:
            while True:
                chunk = payload[off:off + MAX_PAYLOAD]
                off += len(chunk)
                flags = MORE if off < len(payload) else 0
                self.sock.sendall(HDR.pack(MAGIC, typ, flags, len(chunk), rid))
                if chunk:
                    self.sock.sendall(chunk)
                if off >= len(payload):
                    break
        except OSError as exc:
            raise Error(f"send failed after {off} of {len(payload)} bytes: "
                        f"{exc}") from None

    def _recv_frames(self, rid, want):
        body = b""
        try:
            while True:
                hdr = self._recv_exact(HDRSZ)
                magic, typ, flags, length, got = HDR.unpack(hdr)
                if magic != MAGIC:
                    raise Error(f"bad frame magic 0x{magic:08x}")
                if got != rid:
                    raise Error(f"response id {got} does not match request "
                                f"{rid}")
                if typ != (want | R_MASK):
                    raise Error(f"response type {typ} for request {rid}")
                if flags & ~MORE:
                    raise Error(f"unknown frame flags 0x{flags:02x}")
                if length > MAX_PAYLOAD:
                    raise Error(f"frame of {length} bytes for request {rid}")
                body += self._recv_exact(length)
                if len(body) > MAX_BODY:
                    raise Error(f"response for request {rid} exceeds "
                                f"{MAX_BODY}")
                if not flags & MORE:
                    return body
        except Error as exc:
            # The plan asks for the request id and how much actually
            # arrived; both make a flaky channel diagnosable.
            raise Error(f"{exc} ({len(body)} response bytes received)") from None

    def request(self, typ, payload=b""):
        if len(payload) > MAX_BODY:
            raise Error(f"request body exceeds {MAX_BODY} bytes")
        retries = 0 if typ in (T_EXEC, T_PUT) else self.retries
        last = None
        if self.sock is None:
            self.connect(wait=self.timeout)
        for attempt in range(retries + 1):
            rid = self.next_id
            self.next_id += 1
            try:
                self._send_frames(typ, rid, payload)
                return self._recv_frames(rid, typ)
            except Error as exc:
                last = Error(f"{NAMES.get(typ, typ)} request {rid} failed "
                             f"after {attempt + 1} attempt(s): {exc}")
                if self.sock:
                    self.close()
                if attempt < retries:
                    self.connect(wait=self.timeout)
        raise last

    # -- operations ------------------------------------------------------

    def ping(self):
        body = self.request(T_PING)
        if len(body) < 4:
            raise Error("short ping response")
        return struct.unpack("<I", body[:4])[0]

    def exec(self, argv, timeout=None):
        if self.sock is None:
            self.connect(wait=self.timeout)
        old = self.sock.gettimeout()
        if timeout:
            self.sock.settimeout(timeout)
        try:
            payload = struct.pack("<H", len(argv))
            for arg in argv:
                raw = arg.encode()
                payload += struct.pack("<H", len(raw)) + raw
            body = self.request(T_EXEC, payload)
        finally:
            if self.sock is not None:
                self.sock.settimeout(old)
        if len(body) < 16:
            raise Error("short exec response")
        status, ticks, outlen, errlen = struct.unpack("<iIII", body[:16])
        if 16 + outlen + errlen != len(body):
            raise Error(f"exec response says {outlen}+{errlen} output bytes, "
                        f"got {len(body) - 16}")
        out = body[16:16 + outlen]
        err = body[16 + outlen:]
        return status, ticks, out, err

    def put(self, path, data, mode=0o644):
        raw = path.encode()
        if not 0 < len(raw) < 128:
            raise Error(f"{path}: name length out of range")
        payload = struct.pack("<H", len(raw)) + raw
        payload += struct.pack("<I", mode) + data
        body = self.request(T_PUT, payload)
        if len(body) < 4 or struct.unpack("<I", body[:4])[0] != 0:
            raise Error(f"{path}: guest refused the upload")

    def get(self, path):
        raw = path.encode()
        if not 0 < len(raw) < 128:
            raise Error(f"{path}: name length out of range")
        body = self.request(T_GET, struct.pack("<H", len(raw)) + raw)
        if len(body) < 8:
            raise Error("short get response")
        status, length = struct.unpack("<II", body[:8])
        if status != 0:
            raise Error(f"{path}: no such file")
        data = body[8:8 + length]
        if len(data) != length:
            raise Error(f"{path}: truncated ({len(data)} of {length} bytes)")
        return data

    def stat(self, path):
        raw = path.encode()
        if not 0 < len(raw) < 128:
            raise Error(f"{path}: name length out of range")
        body = self.request(T_STAT, struct.pack("<H", len(raw)) + raw)
        if len(body) < 16:
            raise Error("short stat response")
        status, typ, mode, size = struct.unpack("<iIII", body[:16])
        if status != 0:
            raise Error(f"{path}: no such file")
        return typ, mode, size

    def klog(self, seq=0, max_bytes=16384):
        body = self.request(T_KLOG,
                            struct.pack("<QII", seq, max_bytes, 0)[:12])
        if len(body) < 20:
            raise Error("short klog response")
        newseq, lost, length = struct.unpack("<QQI", body[:20])
        if 20 + length != len(body):
            raise Error(f"klog response says {length} bytes, got "
                        f"{len(body) - 20}")
        return newseq, lost, body[20:]


TYPES = {1: "directory", 2: "file", 3: "device"}

TYPE_DIR, TYPE_FILE, TYPE_DEVICE = 1, 2, 3


def split_command(words):
    """A single quoted argument is split the way a caller would expect.

    The agent never parses a shell, so `onyxctl exec "a b" c' is ambiguous;
    treat exactly one argument as a whole command line and split it here.
    """
    if len(words) == 1 and " " in words[0]:
        return shlex.split(words[0])
    return words


def cmd_ping(client, args):
    start = time.monotonic()
    version = client.ping()
    rtt = (time.monotonic() - start) * 1000
    print(f"pong protocol={version} rtt={rtt:.1f}ms")
    return 0


def cmd_exec(client, args):
    argv = split_command(args.argv)
    if len(argv) > 32:
        print(f"exec: {len(argv)} arguments, the agent accepts at most 32",
              file=sys.stderr)
        return 2
    status, ticks, out, err = client.exec(argv, timeout=args.exec_timeout)
    sys.stdout.buffer.write(out)
    sys.stdout.buffer.flush()
    sys.stderr.buffer.write(err)
    sys.stderr.buffer.flush()
    print(f"[exec status={status} guest_ticks={ticks} "
          f"({ticks * 100}ms)]", file=sys.stderr)
    return status if status >= 0 else 1


def cmd_put(client, args):
    if args.host == "-":
        data = sys.stdin.buffer.read()
    else:
        data = Path(args.host).read_bytes()
    client.put(args.guest, data, args.mode)
    print(f"put {args.host} -> {args.guest} ({len(data)} bytes, "
          f"mode 0o{args.mode:04o})")
    return 0


def cmd_get(client, args):
    data = client.get(args.guest)
    if args.host == "-":
        sys.stdout.buffer.write(data)
        sys.stdout.buffer.flush()
        print(f"get {args.guest} -> stdout ({len(data)} bytes, sha256 "
              f"{hashlib.sha256(data).hexdigest()[:16]})", file=sys.stderr)
        return 0
    Path(args.host).write_bytes(data)
    print(f"get {args.guest} -> {args.host} ({len(data)} bytes, "
          f"sha256 {hashlib.sha256(data).hexdigest()[:16]})")
    return 0


def cmd_stat(client, args):
    typ, mode, size = client.stat(args.path)
    print(f"{args.path}: type={TYPES.get(typ, typ)} mode=0o{mode:04o} "
          f"size={size}")
    return 0


def cmd_klog(client, args):
    seq = args.seq
    if args.cursor_file:
        try:
            seq = int(Path(args.cursor_file).read_text().strip() or 0)
        except (OSError, ValueError):
            seq = args.seq
    while True:
        newseq, lost, data = client.klog(seq, args.max)
        if lost:
            print(f"[klog: {lost} bytes lost before seq {seq}]",
                  file=sys.stderr, flush=True)
        if data:
            sys.stdout.buffer.write(data)
            sys.stdout.buffer.flush()
        seq = newseq
        if args.cursor_file:
            Path(args.cursor_file).write_text(f"{seq}\n")
        if not args.follow:
            break
        if args.show_seq:
            print(f"[klog cursor {seq}]", file=sys.stderr, flush=True)
        time.sleep(args.interval)
    if args.show_seq and not args.follow:
        print(f"[klog cursor {seq}]", file=sys.stderr)
    return 0


# -- watch ---------------------------------------------------------------

def sources(target):
    path = Path(target)
    if path.is_file():
        return [path]
    return sorted(path.glob("*.c"))


def mtimes(target):
    return {p: p.stat().st_mtime_ns for p in sources(target)}


def cmd_watch(client, args):
    target = Path(args.directory)
    if not target.exists():
        print(f"watch: {target} does not exist", file=sys.stderr)
        return 2
    state = mtimes(target)
    print(f"watch: {target} ({len(state)} files); press Ctrl-C to stop",
          flush=True)
    while True:
        time.sleep(0.2)
        current = mtimes(target)
        changed = [p for p, t in current.items() if state.get(p) != t]
        state = current
        for path in changed:
            build = ["make", f"user/_{path.stem}"]
            start = time.monotonic()
            result = subprocess.run(build, capture_output=True, text=True)
            if result.returncode != 0:
                # Keep both halves of the failure: what the guest still has,
                # and why the host build refused the new one.
                print(f"watch: build failed for {path}; keeping the old "
                      f"program in the guest", flush=True)
                sys.stderr.write(result.stdout + result.stderr)
                continue
            guest = f"/tmp/{path.stem}.{os.getpid()}"
            try:
                client.put(guest, Path(f"user/_{path.stem}").read_bytes(),
                           0o755)
                status, ticks, out, err = client.exec([guest] + args.args)
            except Error as exc:
                print(f"watch: {path}: {exc}", file=sys.stderr)
                continue
            took = (time.monotonic() - start) * 1000
            sys.stdout.buffer.write(out)
            sys.stdout.buffer.flush()
            sys.stderr.buffer.write(err)
            sys.stderr.buffer.flush()
            print(f"[watch] {path} ran as {guest} status={status} "
                  f"ticks={ticks} wall={took:.0f}ms", flush=True)
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--socket", default=DEFAULT_SOCKET,
                        help=f"UNIX socket the guest is attached to "
                             f"(default {DEFAULT_SOCKET})")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--retries", type=int, default=DEFAULT_RETRIES)
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("ping", help="check that the agent answers")

    p = sub.add_parser("exec", help="run a program, return its output")
    p.add_argument("--timeout", type=float, dest="exec_timeout", default=30.0)
    p.add_argument("argv", nargs=argparse.REMAINDER)

    p = sub.add_parser("put", help="upload a host file ('-' reads stdin)")
    p.add_argument("host")
    p.add_argument("guest")
    p.add_argument("mode", nargs="?", default="0644")

    p = sub.add_parser("get", help="download a guest file ('-' writes stdout)")
    p.add_argument("guest")
    p.add_argument("host")

    p = sub.add_parser("stat", help="show size, type and mode")
    p.add_argument("path")

    p = sub.add_parser("klog", help="read the kernel log from a seq cursor")
    p.add_argument("--seq", type=int, default=0,
                   help="absolute byte offset to start at (default 0)")
    p.add_argument("--max", type=int, default=16384,
                   help="bytes to ask for, at most 16384")
    p.add_argument("--show-seq", action="store_true",
                   help="print the new cursor on stderr")
    p.add_argument("--follow", "-f", action="store_true",
                   help="keep polling, printing only new bytes")
    p.add_argument("--interval", type=float, default=0.5)
    p.add_argument("--cursor-file", default=None,
                   help="read the start cursor from this file and update it")

    p = sub.add_parser("watch", help="rebuild on save, upload, run")
    p.add_argument("directory", nargs="?", default="user")
    p.add_argument("args", nargs=argparse.REMAINDER,
                   help="arguments passed to the rebuilt program")

    args = parser.parse_args(argv)
    if getattr(args, "argv", None) == []:
        parser.error("exec needs a command")
    if args.command == "put":
        try:
            args.mode = int(args.mode, 8)
        except ValueError:
            parser.error(f"mode must be octal, got {args.mode!r}")
    if getattr(args, "args", None) and args.args and args.args[0] == "--":
        args.args = args.args[1:]

    handlers = {"ping": cmd_ping, "exec": cmd_exec, "put": cmd_put,
                "get": cmd_get, "stat": cmd_stat, "klog": cmd_klog,
                "watch": cmd_watch}
    client = None
    try:
        if args.command == "klog":
            args.max = max(1, min(args.max, 16384))
            if args.interval <= 0:
                parser.error("--interval must be positive")
        client = Client(args.socket, args.timeout, args.retries)
        client.connect(wait=args.timeout)
        return handlers[args.command](client, args)
    except Error as exc:
        print(f"onyxctl: {exc}", file=sys.stderr)
        return 1
    finally:
        if client:
            client.close()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
