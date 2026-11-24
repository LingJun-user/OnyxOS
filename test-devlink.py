#!/usr/bin/env python3
"""End-to-end tests for DevLink (batch 17).

Starts `make dev' with a private UNIX socket, talks to the guest agent with
the same client library tools/onyxctl.py uses, and checks the four paths
the batch exists for: liveness, exec, file transfer and hot reload.  The
serial console is captured to test-results/ and the qemu process group is
killed at the end, so a failure leaves a log and nothing running.

    python3 test-devlink.py            # build first: make kernel/kernel fs.img
    python3 test-devlink.py --keep     # leave qemu running for inspection

The serial-console tests (test-xv6.py, test-shell.py) stay authoritative
for terminal semantics; this file only exercises the second path.
"""

import argparse
import hashlib
import importlib.util
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "test-results"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


onyxctl = load("onyxctl", ROOT / "tools" / "onyxctl.py")


class Guest:
    """One `make dev' qemu, running in its own process group."""

    def __init__(self, socket_path, log_path):
        self.socket_path = socket_path
        self.log_path = log_path
        self.log = open(log_path, "wb")
        self.proc = subprocess.Popen(
            ["make", "dev", f"DEVSOCKET={socket_path}", "CPUS=1"],
            stdin=subprocess.DEVNULL, stdout=self.log,
            stderr=subprocess.STDOUT, start_new_session=True)

    def stop(self):
        if self.proc.poll() is None:
            try:
                os.killpg(self.proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait()
        self.log.close()
        try:
            os.unlink(self.socket_path)
        except FileNotFoundError:
            pass

    def tail(self, lines=25):
        try:
            text = self.log_path.read_text(errors="replace").splitlines()
        except OSError:
            return "(no serial log)"
        return "\n".join(text[-lines:])


def client_wait(socket_path, timeout):
    client = onyxctl.Client(socket_path, timeout=5, retries=0)
    deadline = time.monotonic() + timeout
    while True:
        try:
            client.connect(wait=1)
            return client
        except onyxctl.Error:
            if time.monotonic() >= deadline:
                raise
            client.close()
            time.sleep(0.2)


def build_echo():
    result = subprocess.run(["make", "user/_echo"], cwd=ROOT,
                            capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"make user/_echo failed:\n{result.stderr}")


def main():
    parser = argparse.ArgumentParser(description="DevLink end-to-end tests")
    parser.add_argument("--socket", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave qemu running after the tests")
    parser.add_argument("--timeout", type=float, default=45.0,
                        help="how long to wait for the agent to answer")
    args = parser.parse_args()

    if not (ROOT / "kernel" / "kernel").exists() or not (ROOT / "fs.img").exists():
        raise SystemExit("build kernel/kernel and fs.img first")
    if not (ROOT / "user" / "_echo").exists():
        raise SystemExit("build user programs first (make fs.img)")

    RESULTS.mkdir(exist_ok=True)
    stamp = str(time.time_ns())
    directory = Path(tempfile.mkdtemp(prefix="devlink-"))
    socket_path = args.socket or str(directory / "dev.sock")
    log_path = RESULTS / f"{stamp}-devlink-serial.log"

    guest = Guest(socket_path, log_path)
    client = None
    checks = [0]
    stopped = [False]

    def ok(name, detail=""):
        checks[0] += 1
        print(f"PASS devlink/{name} {detail}".rstrip())

    try:
        try:
            client = client_wait(socket_path, args.timeout)
        except onyxctl.Error as exc:
            raise RuntimeError(f"agent never answered: {exc}\n{guest.tail()}")

        version = client.ping()
        if version != 1:
            raise RuntimeError(f"unexpected protocol version {version}")
        ok("ping", f"protocol={version}")

        status, ticks, out, err = client.exec(["testrun", "cowtest"],
                                              timeout=60)
        if status != 0 or b"cowtest: OK" not in out:
            raise RuntimeError(
                f"exec testrun cowtest: status={status}\n"
                f"stdout:\n{out.decode(errors='replace')}\n"
                f"stderr:\n{err.decode(errors='replace')}")
        ok("exec", f"status={status} ticks={ticks}")

        data = bytes((i * 37 + 11) % 251 for i in range(9000))
        digest = hashlib.sha256(data).hexdigest()
        client.put("/tmp/devlink.bin", data, 0o600)
        back = client.get("/tmp/devlink.bin")
        if hashlib.sha256(back).hexdigest() != digest:
            raise RuntimeError(
                f"put/get mismatch: {len(back)} bytes back, wanted {len(data)}")
        typ, mode, size = client.stat("/tmp/devlink.bin")
        if (typ, mode, size) != (onyxctl.TYPE_FILE, 0o600, len(data)):
            raise RuntimeError(
                f"stat: type={typ} mode=0o{mode:04o} size={size}")
        ok("transfer", f"{len(data)} bytes sha256={digest[:16]}")

        typ, mode, _ = client.stat("/dev/agent")
        if typ != onyxctl.TYPE_DEVICE or mode != 0o600:
            raise RuntimeError(
                f"/dev/agent: type={typ} mode=0o{mode:04o}, want 0600")
        ok("permissions", "mode=0o600 root-only node")

        # Hot reload: the same build -> upload -> exec path `make dev-reload'
        # uses.  Time is reported rather than asserted tightly, because a
        # loaded CI machine is allowed to be slower than the 2 s target.
        start = time.monotonic()
        (ROOT / "user" / "echo.c").touch()  # force a real rebuild
        build_echo()
        guest_path = f"/tmp/echo.{os.getpid()}"
        client.put(guest_path, (ROOT / "user" / "_echo").read_bytes(), 0o755)
        status, ticks, out, err = client.exec([guest_path, "hot", "reload"])
        elapsed = time.monotonic() - start
        if status != 0 or out != b"hot reload\n":
            raise RuntimeError(
                f"hot reload: status={status} stdout={out!r} stderr={err!r}")
        if elapsed > 10:
            raise RuntimeError(f"hot reload took {elapsed:.1f}s, budget 10s")
        ok("reload", f"build+put+exec {elapsed * 1000:.0f}ms")

        # A command that fails must come back with its exit status and
        # stderr instead of hanging the channel.
        status, ticks, out, err = client.exec(["no-such-program"], timeout=30)
        if status != 127 or b"exec no-such-program failed" not in err:
            raise RuntimeError(
                f"missing program: status={status} stderr={err!r}")
        ok("exec-failure", "status=127 preserved")

    finally:
        if client:
            client.close()
        if args.keep:
            print(f"qemu left running; socket {socket_path}; log {log_path}")
        else:
            guest.stop()
            stopped[0] = guest.proc.poll() is not None
        shutil.rmtree(directory, ignore_errors=True)

    if not args.keep and not stopped[0]:
        raise RuntimeError("qemu process group did not exit")
    print(f"devlink: {checks[0]} checks passed, serial log {log_path}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
