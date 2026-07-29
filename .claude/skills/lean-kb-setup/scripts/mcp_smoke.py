#!/usr/bin/env python3
"""Minimal MCP stdio client for smoke-testing a server. Standard library only.

Speaks just enough of the protocol to prove a server starts, handshakes, and
answers: initialize -> notifications/initialized -> tools/list -> tools/call.

    mcp_smoke.py [--timeout S] [--expect-tools a,b] [--call NAME --args JSON]
                 [--quiet] -- COMMAND [ARGS...]

Exit 0 when every requested check passes, 1 otherwise.
"""

import argparse
import json
import os
import queue
import subprocess
import sys
import threading

PROTOCOL_VERSION = "2025-06-18"


class Server:
    """A subprocess speaking newline-delimited JSON-RPC over stdio."""

    def __init__(self, argv, timeout):
        self.timeout = timeout
        self._next_id = 0
        self._replies = queue.Queue()

        env = dict(os.environ)
        # Keep the server's own logging off the wire we are parsing.
        env.setdefault("LEAN_LOG_LEVEL", "ERROR")

        self.proc = subprocess.Popen(
            argv,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            env=env,
        )
        self._stderr = []
        threading.Thread(target=self._pump_stdout, daemon=True).start()
        threading.Thread(target=self._pump_stderr, daemon=True).start()

    def _pump_stdout(self):
        for line in self.proc.stdout:
            line = line.strip()
            if not line:
                continue
            try:
                self._replies.put(json.loads(line))
            except json.JSONDecodeError:
                # Servers occasionally print non-protocol noise; ignore it.
                pass
        self._replies.put(None)  # EOF sentinel

    def _pump_stderr(self):
        for line in self.proc.stderr:
            self._stderr.append(line.rstrip())

    def _send(self, msg):
        self.proc.stdin.write(json.dumps(msg) + "\n")
        self.proc.stdin.flush()

    def notify(self, method, params=None):
        self._send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def request(self, method, params=None):
        self._next_id += 1
        want = self._next_id
        self._send({"jsonrpc": "2.0", "id": want, "method": method, "params": params or {}})

        # Skip server-initiated traffic until our own reply shows up.
        while True:
            try:
                msg = self._replies.get(timeout=self.timeout)
            except queue.Empty:
                raise TimeoutError(f"{method}: no reply within {self.timeout}s")
            if msg is None:
                raise RuntimeError(f"{method}: server exited\n" + "\n".join(self._stderr[-20:]))
            if msg.get("id") == want:
                if "error" in msg:
                    raise RuntimeError(f"{method}: {msg['error']}")
                return msg.get("result", {})

    def handshake(self):
        result = self.request(
            "initialize",
            {
                "protocolVersion": PROTOCOL_VERSION,
                "capabilities": {},
                "clientInfo": {"name": "lean-kb-setup-smoke", "version": "1"},
            },
        )
        self.notify("notifications/initialized")
        return result

    def close(self):
        try:
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=10)
        except Exception:
            self.proc.kill()


def render(result):
    """Flatten a tools/call result into plain text."""
    parts = []
    for block in result.get("content", []):
        if block.get("type") == "text":
            parts.append(block.get("text", ""))
        else:
            parts.append(json.dumps(block))
    return "\n".join(parts) if parts else json.dumps(result)


def main():
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--timeout", type=float, default=180)
    ap.add_argument("--expect-tools", default="")
    ap.add_argument("--call")
    ap.add_argument("--args", default="{}")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("command", nargs=argparse.REMAINDER)
    opts = ap.parse_args()

    argv = opts.command[1:] if opts.command and opts.command[0] == "--" else opts.command
    if not argv:
        ap.error("no server command given (put it after --)")

    def say(*a):
        if not opts.quiet:
            print(*a)

    try:
        server = Server(argv, opts.timeout)
    except OSError as exc:
        print(f"error: cannot launch {argv[0]}: {exc}", file=sys.stderr)
        return 1

    try:
        info = server.handshake().get("serverInfo", {})
        say(f"connected: {info.get('name', '?')} {info.get('version', '')}".rstrip())

        tools = [t["name"] for t in server.request("tools/list").get("tools", [])]
        say(f"tools ({len(tools)}): {', '.join(sorted(tools))}")

        missing = [t for t in opts.expect_tools.split(",") if t and t not in tools]
        if missing:
            print(f"missing expected tools: {', '.join(missing)}", file=sys.stderr)
            return 1

        if opts.call:
            result = server.request(
                "tools/call", {"name": opts.call, "arguments": json.loads(opts.args)}
            )
            text = render(result)
            say(f"{opts.call} ->")
            say(text[:2000])
            if result.get("isError"):
                print(f"{opts.call} returned an error", file=sys.stderr)
                return 1
            if not text.strip():
                print(f"{opts.call} returned nothing", file=sys.stderr)
                return 1
        return 0
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    finally:
        server.close()


if __name__ == "__main__":
    sys.exit(main())
