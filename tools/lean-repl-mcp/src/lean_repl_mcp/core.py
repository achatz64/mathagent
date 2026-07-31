from __future__ import annotations

import asyncio
import hashlib
import json
import os
import shutil
import signal
import time
import uuid
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


class LeanReplMcpError(Exception):
    """Base class for expected wrapper failures."""

    kind = "wrapper_error"


class ConfigurationError(LeanReplMcpError):
    kind = "configuration_error"


class ReplProcessError(LeanReplMcpError):
    kind = "repl_process_error"


class ReplTimeoutError(ReplProcessError):
    kind = "timeout"


class ReplProtocolError(ReplProcessError):
    kind = "protocol_error"


class InvalidRequestError(LeanReplMcpError):
    kind = "invalid_request"


class StaleEnvironmentError(LeanReplMcpError):
    kind = "stale_environment"


@dataclass(frozen=True)
class Settings:
    project: Path
    lake: Path
    repl: Path
    timeout_seconds: float = 60.0
    max_frame_bytes: int = 5 * 1024 * 1024
    max_environments: int = 256
    stderr_tail_bytes: int = 64 * 1024
    warm_on_startup: bool = False
    warm_imports: tuple[str, ...] = ()

    @property
    def warm_enabled(self) -> bool:
        return self.warm_on_startup or bool(self.warm_imports)


@dataclass
class EnvironmentRecord:
    env_id: int
    generation: int
    fingerprint: str
    file_path: Path | None = None
    source_hash: str | None = None


def _lakefile_exists(path: Path) -> bool:
    return (path / "lakefile.toml").is_file() or (path / "lakefile.lean").is_file()


def find_project(explicit: str | os.PathLike[str] | None = None) -> Path:
    candidate = explicit or os.environ.get("LEAN_PROJECT_PATH")
    if candidate:
        project = Path(candidate).expanduser().resolve()
        if not project.is_dir():
            raise ConfigurationError(f"Lean project directory does not exist: {project}")
        if not (project / "lean-toolchain").is_file() or not _lakefile_exists(project):
            raise ConfigurationError(
                f"Not a Lean Lake project (need lean-toolchain and lakefile): {project}"
            )
        return project

    current = Path.cwd().resolve()
    for directory in (current, *current.parents):
        if (directory / "lean-toolchain").is_file() and _lakefile_exists(directory):
            return directory
    raise ConfigurationError(
        "Could not discover a Lean project; pass --project or set LEAN_PROJECT_PATH"
    )


def find_lake(explicit: str | os.PathLike[str] | None = None) -> Path:
    candidate = explicit or os.environ.get("LEAN_LAKE_PATH") or shutil.which("lake")
    if not candidate:
        raise ConfigurationError("Could not find Lake; pass --lake or put lake on PATH")
    # Elan installs Lake as a multi-call symlink. Resolving that symlink to the
    # `elan` binary would change argv[0] and turn `lake env ...` into
    # `elan env ...`, so make the path absolute without dereferencing it.
    path = Path(candidate).expanduser().absolute()
    if not path.is_file():
        raise ConfigurationError(f"Lake executable does not exist: {path}")
    if os.name != "nt" and not os.access(path, os.X_OK):
        raise ConfigurationError(f"Lake is not executable: {path}")
    return path


def find_repl(
    project: Path, explicit: str | os.PathLike[str] | None = None
) -> Path:
    candidate = explicit or os.environ.get("LEAN_REPL_PATH")
    if candidate:
        path = Path(candidate).expanduser().resolve()
        if not path.is_file():
            raise ConfigurationError(f"Lean REPL executable does not exist: {path}")
        if os.name != "nt" and not os.access(path, os.X_OK):
            raise ConfigurationError(f"Lean REPL is not executable: {path}")
        return path

    relative_candidates = (
        Path(".lake/packages/repl/.lake/build/bin/repl"),
        Path(".lake/packages/REPL/.lake/build/bin/repl"),
    )
    if os.name == "nt":
        relative_candidates = tuple(Path(f"{path}.exe") for path in relative_candidates)
    for relative in relative_candidates:
        path = (project / relative).resolve()
        if path.is_file() and (os.name == "nt" or os.access(path, os.X_OK)):
            return path
    raise ConfigurationError(
        "Could not find a built Lean REPL. Add the repl dependency matching the "
        "project toolchain and run `lake build repl`, or pass --repl."
    )


def build_settings(
    *,
    project: str | os.PathLike[str] | None = None,
    lake: str | os.PathLike[str] | None = None,
    repl: str | os.PathLike[str] | None = None,
    timeout_seconds: float = 60.0,
    max_frame_bytes: int = 5 * 1024 * 1024,
    max_environments: int = 256,
    stderr_tail_bytes: int = 64 * 1024,
    warm_on_startup: bool = False,
    warm_imports: Iterable[str] = (),
) -> Settings:
    project_path = find_project(project)
    return Settings(
        project=project_path,
        lake=find_lake(lake),
        repl=find_repl(project_path, repl),
        timeout_seconds=timeout_seconds,
        max_frame_bytes=max_frame_bytes,
        max_environments=max_environments,
        stderr_tail_bytes=stderr_tail_bytes,
        warm_on_startup=warm_on_startup,
        warm_imports=normalize_imports(warm_imports),
    )


def normalize_imports(imports: Iterable[str]) -> tuple[str, ...]:
    normalized: set[str] = set()
    for value in imports:
        module = value.strip()
        if not module:
            raise InvalidRequestError("Import module names must not be empty")
        if any(char.isspace() or ord(char) < 32 for char in module):
            raise InvalidRequestError(f"Invalid Lean module name: {value!r}")
        parts = module.split(".")
        if any(not part for part in parts):
            raise InvalidRequestError(f"Invalid Lean module name: {value!r}")
        for part in parts:
            first, rest = part[0], part[1:]
            if not (first.isalpha() or first == "_"):
                raise InvalidRequestError(f"Invalid Lean module name: {value!r}")
            if any(not (char.isalnum() or char in "_'") for char in rest):
                raise InvalidRequestError(f"Invalid Lean module name: {value!r}")
        normalized.add(module)
    return tuple(sorted(normalized))


def source_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(128 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def project_fingerprint(project: Path) -> str:
    """Fingerprint inputs that can change locally imported Lean environments."""
    digest = hashlib.sha256()
    metadata_files = (
        project / "lean-toolchain",
        project / "lakefile.toml",
        project / "lakefile.lean",
        project / "lake-manifest.json",
    )
    for path in metadata_files:
        if not path.is_file():
            continue
        digest.update(path.name.encode())
        digest.update(source_hash(path).encode())

    build_root = project / ".lake/build/lib/lean"
    if build_root.is_dir():
        paths = sorted(
            (
                path
                for path in build_root.rglob("*")
                if path.is_file() and ".olean" in path.name
            ),
            key=lambda path: path.as_posix(),
        )
        for path in paths:
            stat = path.stat()
            digest.update(path.relative_to(build_root).as_posix().encode())
            digest.update(str(stat.st_size).encode())
            digest.update(str(stat.st_mtime_ns).encode())
    return digest.hexdigest()


class ReplProcess:
    """One serialized blank-line-framed JSON REPL process."""

    def __init__(self, settings: Settings):
        self.settings = settings
        self._process: asyncio.subprocess.Process | None = None
        self._lock = asyncio.Lock()
        self._stderr_task: asyncio.Task[None] | None = None
        self._stderr_chunks: deque[bytes] = deque()
        self._stderr_size = 0
        self.last_error: str | None = None
        self.started_at: float | None = None

    @property
    def pid(self) -> int | None:
        process = self._process
        if process is None or process.returncode is not None:
            return None
        return process.pid

    @property
    def state(self) -> str:
        process = self._process
        if process is None:
            return "stopped"
        if process.returncode is None:
            return "ready"
        return "exited"

    @property
    def stderr_tail(self) -> str:
        return b"".join(self._stderr_chunks).decode(errors="replace")

    async def _start_locked(self) -> None:
        if self.pid is not None:
            return
        if self._process is not None:
            await self._stop_locked()
        kwargs: dict[str, Any] = {
            "cwd": str(self.settings.project),
            "stdin": asyncio.subprocess.PIPE,
            "stdout": asyncio.subprocess.PIPE,
            "stderr": asyncio.subprocess.PIPE,
            "limit": self.settings.max_frame_bytes + 1024,
        }
        if os.name != "nt":
            kwargs["start_new_session"] = True
        else:
            kwargs["creationflags"] = getattr(
                __import__("subprocess"), "CREATE_NEW_PROCESS_GROUP", 0
            )
        self._stderr_chunks.clear()
        self._stderr_size = 0
        self._process = await asyncio.create_subprocess_exec(
            str(self.settings.lake),
            "env",
            str(self.settings.repl),
            **kwargs,
        )
        self.started_at = time.time()
        assert self._process.stderr is not None
        self._stderr_task = asyncio.create_task(self._drain_stderr(self._process.stderr))

    async def _drain_stderr(self, stream: asyncio.StreamReader) -> None:
        try:
            while chunk := await stream.read(4096):
                self._stderr_chunks.append(chunk)
                self._stderr_size += len(chunk)
                while (
                    self._stderr_chunks
                    and self._stderr_size > self.settings.stderr_tail_bytes
                ):
                    removed = self._stderr_chunks.popleft()
                    self._stderr_size -= len(removed)
        except (asyncio.CancelledError, RuntimeError):
            return

    async def request(self, payload: dict[str, Any]) -> dict[str, Any]:
        async with self._lock:
            try:
                await self._start_locked()
                return await asyncio.wait_for(
                    self._exchange_locked(payload),
                    timeout=self.settings.timeout_seconds,
                )
            except asyncio.TimeoutError as exc:
                message = (
                    f"Lean REPL request exceeded {self.settings.timeout_seconds:g}s"
                )
                await self._abort_locked(message)
                raise ReplTimeoutError(message) from exc
            except ReplProcessError:
                raise
            except Exception as exc:
                message = f"Lean REPL request failed: {exc}"
                await self._abort_locked(message)
                raise ReplProcessError(message) from exc

    async def _exchange_locked(self, payload: dict[str, Any]) -> dict[str, Any]:
        process = self._process
        if process is None or process.stdin is None or process.stdout is None:
            message = "Lean REPL is not running"
            await self._abort_locked(message)
            raise ReplProcessError(message)
        if process.returncode is not None:
            message = self._process_failure("Lean REPL exited before the request")
            await self._abort_locked(message)
            raise ReplProcessError(message)

        encoded = json.dumps(payload, ensure_ascii=False).encode() + b"\n\n"
        process.stdin.write(encoded)
        await process.stdin.drain()

        frame = bytearray()
        while True:
            try:
                line = await process.stdout.readline()
            except (ValueError, asyncio.LimitOverrunError) as exc:
                message = (
                    "Lean REPL response contained a line larger than the "
                    f"{self.settings.max_frame_bytes}-byte frame limit"
                )
                await self._abort_locked(message)
                raise ReplProtocolError(message) from exc
            if not line:
                message = self._process_failure("Lean REPL closed stdout")
                await self._abort_locked(message)
                raise ReplProcessError(message)
            if not line.strip():
                break
            frame.extend(line)
            if len(frame) > self.settings.max_frame_bytes:
                message = (
                    "Lean REPL response exceeded "
                    f"{self.settings.max_frame_bytes} bytes"
                )
                await self._abort_locked(message)
                raise ReplProtocolError(message)
        if not frame:
            message = "Lean REPL returned an empty response frame"
            await self._abort_locked(message)
            raise ReplProtocolError(message)
        try:
            response = json.loads(frame)
        except json.JSONDecodeError as exc:
            message = f"Lean REPL returned malformed JSON: {exc}"
            await self._abort_locked(message)
            raise ReplProtocolError(message) from exc
        if not isinstance(response, dict):
            message = "Lean REPL response was not a JSON object"
            await self._abort_locked(message)
            raise ReplProtocolError(message)
        return response

    def _process_failure(self, prefix: str) -> str:
        process = self._process
        details = [prefix]
        if process is not None and process.returncode is not None:
            details.append(f"exit code {process.returncode}")
        tail = self.stderr_tail.strip()
        if tail:
            details.append(f"stderr: {tail[-4000:]}")
        return "; ".join(details)

    async def _abort_locked(self, reason: str) -> None:
        self.last_error = reason
        await self._stop_locked()

    async def reset(self, reason: str | None = None) -> None:
        async with self._lock:
            if reason:
                self.last_error = reason
            await self._stop_locked()

    async def _stop_locked(self) -> None:
        process = self._process
        self._process = None
        if process is not None and process.returncode is None:
            try:
                if os.name != "nt":
                    os.killpg(process.pid, signal.SIGTERM)
                else:
                    process.terminate()
            except ProcessLookupError:
                pass
            try:
                await asyncio.wait_for(process.wait(), timeout=2.0)
            except asyncio.TimeoutError:
                try:
                    if os.name != "nt":
                        os.killpg(process.pid, signal.SIGKILL)
                    else:
                        process.kill()
                except ProcessLookupError:
                    pass
                await process.wait()
        if self._stderr_task is not None:
            self._stderr_task.cancel()
            try:
                await self._stderr_task
            except asyncio.CancelledError:
                pass
            self._stderr_task = None

    async def close(self) -> None:
        await self.reset()


class LeanReplManager:
    """State, invalidation, and normalized operations above one REPL process."""

    def __init__(self, settings: Settings):
        self.settings = settings
        self.instance_id = uuid.uuid4().hex
        self.process = ReplProcess(settings)
        self.generation = 0
        self._fingerprint = project_fingerprint(settings.project)
        self._operation_lock = asyncio.Lock()
        self._active_context = "none"
        self._active_imports: tuple[str, ...] = ()
        self._active_file: str | None = None
        self._base_environment: int | None = None
        self._environments: dict[str, EnvironmentRecord] = {}
        self._created_environments = 0
        self.warm_state = "pending" if settings.warm_enabled else "not_configured"
        self.warm_error: str | None = None

    async def _invalidate_locked(
        self, reason: str, *, preserve_imports: bool = False
    ) -> None:
        active_imports = self._active_imports if preserve_imports else ()
        await self.process.reset(reason)
        self.generation += 1
        self._active_context = "imports" if preserve_imports else "none"
        self._active_imports = active_imports
        self._active_file = None
        self._base_environment = None
        self._environments.clear()
        self._created_environments = 0
        if self.settings.warm_enabled:
            self.warm_state = "not_warmed"

    async def _check_fingerprint_locked(self) -> None:
        current = project_fingerprint(self.settings.project)
        if current != self._fingerprint:
            await self._invalidate_locked(
                "Lean project build inputs changed",
                preserve_imports=self._active_context == "imports",
            )
            self._fingerprint = current

    async def _ensure_capacity_locked(self) -> None:
        if self._created_environments >= self.settings.max_environments:
            await self._invalidate_locked(
                "Lean REPL environment limit reached",
                preserve_imports=self._active_context == "imports",
            )

    async def _request_locked(self, payload: dict[str, Any]) -> dict[str, Any]:
        try:
            return await self.process.request(payload)
        except ReplProcessError:
            self.generation += 1
            self._base_environment = None
            self._environments.clear()
            self._created_environments = 0
            if self._active_context == "file":
                self._active_context = "none"
                self._active_file = None
            if self.settings.warm_enabled:
                self.warm_state = "not_warmed"
            raise

    @staticmethod
    def _has_errors(response: dict[str, Any]) -> bool:
        if response.get("error"):
            return True
        return any(
            str(message.get("severity", "")).lower() == "error"
            for message in response.get("messages", [])
            if isinstance(message, dict)
        )

    @staticmethod
    def _error_summary(response: dict[str, Any]) -> str:
        if response.get("error"):
            return str(response["error"])
        errors = [
            str(message.get("data", "Lean error"))
            for message in response.get("messages", [])
            if isinstance(message, dict)
            and str(message.get("severity", "")).lower() == "error"
        ]
        return "\n".join(errors) or "Lean rejected the request"

    async def _active_base_environment_locked(
        self, additions: tuple[str, ...]
    ) -> int:
        if self._active_context == "file":
            await self._invalidate_locked("Lean import context replaced a loaded file")

        had_import_context = self._active_context == "imports"
        previous = self._active_imports if self._active_context == "imports" else ()
        target = normalize_imports((*previous, *additions))
        if self._active_context == "imports" and target != previous:
            await self._invalidate_locked("Lean active import set expanded")

        if self._active_context != "imports":
            self._active_context = "imports"
            self._active_imports = target
        elif target != self._active_imports:
            self._active_imports = target

        if self._base_environment is not None:
            return self._base_environment

        header = "\n".join(f"import {module}" for module in self._active_imports)
        probe = "#check True"
        bootstrap = f"{header}\n{probe}" if header else probe
        response = await self._request_locked({"cmd": bootstrap})
        probe_succeeded = any(
            str(message.get("severity", "")).lower() == "info"
            and str(message.get("data", "")).startswith("True :")
            for message in response.get("messages", [])
            if isinstance(message, dict)
        )
        if (
            self._has_errors(response)
            or not isinstance(response.get("env"), int)
            or not probe_succeeded
        ):
            failed_imports = additions or self._active_imports
            names = ", ".join(f"`{module}`" for module in failed_imports)
            message = "Failed to load requested Lean imports"
            if names:
                message += ": " + names
            if self._has_errors(response):
                detail = self._error_summary(response)
                # A missing import can leave the REPL in an empty environment,
                # making the validation probe itself appear unknown.  That
                # symptom is less useful than the requested module names.
                if detail.strip() != "Unknown identifier `True`":
                    message += "\nLean reported: " + detail
            elif not probe_succeeded:
                message += "\nLean did not complete the import validation probe"
            else:
                message += "\nLean did not return an environment"
            await self._invalidate_locked(message)
            if had_import_context:
                self._active_context = "imports"
                self._active_imports = previous
            raise InvalidRequestError(message)
        env_id = int(response["env"])
        self._base_environment = env_id
        self._created_environments += 1
        if self.settings.warm_enabled and all(
            module in self._active_imports for module in self.settings.warm_imports
        ):
            self.warm_state = "ready"
        return env_id

    def _context_fields(self) -> dict[str, Any]:
        return {
            "active_context": self._active_context,
            "active_imports": (
                list(self._active_imports)
                if self._active_context == "imports"
                else None
            ),
            "active_file": self._active_file,
        }

    def _new_token_locked(
        self,
        env_id: int,
        *,
        file_path: Path | None = None,
        file_hash: str | None = None,
    ) -> str:
        token = uuid.uuid4().hex
        self._environments[token] = EnvironmentRecord(
            env_id=env_id,
            generation=self.generation,
            fingerprint=self._fingerprint,
            file_path=file_path,
            source_hash=file_hash,
        )
        return token

    def _resolve_token_locked(self, token: str) -> EnvironmentRecord:
        record = self._environments.get(token)
        if record is None:
            raise StaleEnvironmentError("Unknown or expired Lean environment token")
        if (
            record.generation != self.generation
            or record.fingerprint != self._fingerprint
        ):
            self._environments.pop(token, None)
            raise StaleEnvironmentError("Lean environment token belongs to an older generation")
        if record.file_path is not None:
            if not record.file_path.is_file():
                self._environments.pop(token, None)
                raise StaleEnvironmentError("The source file for this environment no longer exists")
            if source_hash(record.file_path) != record.source_hash:
                self._environments.pop(token, None)
                raise StaleEnvironmentError("The source file changed; load it again")
        return record

    @staticmethod
    def _bounded_lists(response: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        bounded = dict(response)
        truncated = False
        for key in ("messages", "sorries", "tactics"):
            values = bounded.get(key)
            if isinstance(values, list) and len(values) > 100:
                bounded[key] = values[:100]
                truncated = True
        messages = bounded.get("messages")
        if isinstance(messages, list):
            copied: list[Any] = []
            for value in messages:
                if not isinstance(value, dict):
                    copied.append(value)
                    continue
                message = dict(value)
                data = message.get("data")
                if isinstance(data, str) and len(data) > 16384:
                    message["data"] = data[:16384] + "\n… [truncated]"
                    truncated = True
                copied.append(message)
            bounded["messages"] = copied
        return bounded, truncated

    def _normalize_result(
        self,
        response: dict[str, Any],
        *,
        elapsed_ms: int,
        token: str | None,
    ) -> dict[str, Any]:
        has_errors = self._has_errors(response)
        response, truncated = self._bounded_lists(response)
        sorries = response.get("sorries", [])
        goals = response.get("goals", [])
        complete = not has_errors and not bool(sorries) and not bool(goals)
        result: dict[str, Any] = {
            "success": not has_errors,
            "complete": complete,
            "generation": self.generation,
            "elapsed_ms": elapsed_ms,
            "messages": response.get("messages", []),
            "sorries": sorries,
            "tactics": response.get("tactics", []),
            "truncated": truncated,
            **self._context_fields(),
        }
        if response.get("error"):
            result["error"] = response["error"]
        if goals:
            result["goals"] = goals
        if response.get("proofStatus"):
            result["proof_status"] = response["proofStatus"]
        if token is not None:
            result["environment"] = token
        return result

    async def check(
        self,
        code: str,
        *,
        imports: Iterable[str] | None = None,
        environment: str | None = None,
    ) -> dict[str, Any]:
        if environment is not None and imports is not None:
            raise InvalidRequestError("Pass either imports or environment, not both")
        additions = normalize_imports(imports or ())
        started = time.perf_counter()
        async with self._operation_lock:
            await self._check_fingerprint_locked()
            await self._ensure_capacity_locked()
            if environment is not None:
                env_id = self._resolve_token_locked(environment).env_id
            else:
                env_id = await self._active_base_environment_locked(additions)
            response = await self._request_locked({"cmd": code, "env": env_id})
            self._created_environments += 1
            token = None
            if not self._has_errors(response) and isinstance(response.get("env"), int):
                token = self._new_token_locked(int(response["env"]))
            elapsed_ms = round((time.perf_counter() - started) * 1000)
            return self._normalize_result(response, elapsed_ms=elapsed_ms, token=token)

    def _resolve_project_file(self, value: str) -> Path:
        requested = Path(value)
        path = requested if requested.is_absolute() else self.settings.project / requested
        path = path.expanduser().resolve()
        try:
            path.relative_to(self.settings.project)
        except ValueError as exc:
            raise InvalidRequestError("Lean file must be inside the configured project") from exc
        if not path.is_file():
            raise InvalidRequestError(f"Lean file does not exist: {value}")
        if path.suffix != ".lean":
            raise InvalidRequestError("lean_load_file only accepts .lean files")
        return path

    async def load_file(self, path_value: str) -> dict[str, Any]:
        path = self._resolve_project_file(path_value)
        file_hash_before = source_hash(path)
        started = time.perf_counter()
        async with self._operation_lock:
            await self._check_fingerprint_locked()
            if self._active_context != "none" or self.process.pid is not None:
                await self._invalidate_locked("Lean source file context changed")
            self._active_context = "file"
            self._active_file = str(path.relative_to(self.settings.project))
            response = await self._request_locked({"path": str(path)})
            self._created_environments += 1
            file_hash = source_hash(path)
            if file_hash != file_hash_before:
                raise InvalidRequestError("The Lean source changed while it was loading; retry")
            token = None
            if not self._has_errors(response) and isinstance(response.get("env"), int):
                token = self._new_token_locked(
                    int(response["env"]), file_path=path, file_hash=file_hash
                )
            elapsed_ms = round((time.perf_counter() - started) * 1000)
            result = self._normalize_result(
                response, elapsed_ms=elapsed_ms, token=token
            )
            result["path"] = str(path.relative_to(self.settings.project))
            result["source_hash"] = file_hash
            return result

    async def reset(self, reason: str = "Manual reset") -> dict[str, Any]:
        async with self._operation_lock:
            await self._invalidate_locked(reason)
            self._fingerprint = project_fingerprint(self.settings.project)
            return {
                "success": True,
                "generation": self.generation,
                "message": "Lean REPL stopped; the next execution will start it lazily",
            }

    async def warm(self) -> None:
        if not self.settings.warm_enabled:
            return
        self.warm_state = "warming"
        try:
            async with self._operation_lock:
                await self._check_fingerprint_locked()
                await self._ensure_capacity_locked()
                await self._active_base_environment_locked(self.settings.warm_imports)
            self.warm_state = "ready"
        except Exception as exc:
            self.warm_state = "failed"
            self.warm_error = str(exc)

    def status(self) -> dict[str, Any]:
        toolchain_path = self.settings.project / "lean-toolchain"
        toolchain = (
            toolchain_path.read_text(encoding="utf-8").strip()
            if toolchain_path.is_file()
            else None
        )
        started_at = self.process.started_at if self.process.pid is not None else None
        return {
            "success": True,
            "instance_id": self.instance_id,
            "server_pid": os.getpid(),
            "repl_pid": self.process.pid,
            "repl_state": self.process.state,
            "repl_started_at": started_at,
            "repl_uptime_seconds": (
                round(time.time() - started_at, 3) if started_at is not None else None
            ),
            "generation": self.generation,
            "project": str(self.settings.project),
            "toolchain": toolchain,
            "lake": str(self.settings.lake),
            "repl": str(self.settings.repl),
            "warm_state": self.warm_state,
            "warm_imports": list(self.settings.warm_imports),
            "warm_error": self.warm_error,
            **self._context_fields(),
            "cached_import_sets": (
                [list(self._active_imports)]
                if self._active_context == "imports"
                and self._base_environment is not None
                else []
            ),
            "environment_tokens": len(self._environments),
            "created_environments": self._created_environments,
            "max_environments": self.settings.max_environments,
            "timeout_seconds": self.settings.timeout_seconds,
            "max_frame_bytes": self.settings.max_frame_bytes,
            "last_error": self.process.last_error,
            "stderr_tail": self.process.stderr_tail[-4000:],
        }

    def active_imports(self) -> dict[str, Any]:
        return {
            "success": True,
            "generation": self.generation,
            **self._context_fields(),
        }

    async def close(self) -> None:
        async with self._operation_lock:
            await self.process.close()
