#!/usr/bin/env python3
"""Idempotently upload the validated QPBT tree as private Prove2Me entries."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import threading
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
PAYLOADS_PATH = ROOT / "prove2me" / "generated" / "payloads.json"
COLLISION_PATH = ROOT / "prove2me" / "generated" / "collision_check.json"
VALIDATION_RECEIPT = ROOT / "prove2me" / "generated" / "validation_receipt.json"
STATE_PATH = ROOT / "prove2me" / "records" / "upload_state.json"
PLATFORM = ROOT / "prove2me" / "platform"
LIDT_UPLOADED = Path("/home/drx/p2m/status/lidt-uploaded")
API_KEY_PATH = Path("/home/drx/.config/prove2me/api_key")
BASE = "https://prove2.me/api/v1"
TERMINAL_JOB = {"PUBLISHED", "FAILED", "ERROR"}
TERMINAL_SUBMISSION = {
    "ACCEPTED", "SKETCH_ACCEPTED", "FAILED", "CE", "WA", "SORRY", "ERROR",
}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def platform_digest() -> str:
    digest = hashlib.sha256()
    for path in sorted(PLATFORM.rglob("*.lean")):
        digest.update(str(path.relative_to(PLATFORM)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def require_validated_inputs() -> None:
    if not LIDT_UPLOADED.is_file():
        raise RuntimeError(f"LIDT upload gate is absent: {LIDT_UPLOADED}")
    if not VALIDATION_RECEIPT.is_file():
        raise RuntimeError("missing validation receipt; run validate_upload.py first")
    receipt = json.loads(VALIDATION_RECEIPT.read_text(encoding="utf-8"))
    expected = {
        "planSha256": sha256(PLAN_PATH),
        "payloadsSha256": sha256(PAYLOADS_PATH),
        "platformSha256": platform_digest(),
        "typeAuditFailures": 0,
    }
    mismatches = {
        key: (receipt.get(key), value) for key, value in expected.items()
        if receipt.get(key) != value
    }
    if mismatches:
        raise RuntimeError(f"validation receipt does not match exact upload text: {mismatches}")
    collision = json.loads(COLLISION_PATH.read_text(encoding="utf-8"))
    if (
        not collision.get("complete")
        or collision.get("planSha256") != sha256(PLAN_PATH)
        or collision.get("definitionCollisions")
        or collision.get("theoremCollisions")
        or collision.get("extensionCollisions")
        or len(collision.get("checkedExtensions", [])) != collision.get("sourceExtensions")
    ):
        raise RuntimeError("collision preflight is missing, stale, or nonempty")


class State:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.lock = threading.Lock()
        if path.is_file():
            self.data = json.loads(path.read_text(encoding="utf-8"))
        else:
            self.data = {
                "schemaVersion": 1,
                "createdAt": now(),
                "inputs": None,
                "platformVersions": [],
                "definitions": {},
                "theorems": {},
                "solutions": {},
                "preflight": None,
                "finalVerification": None,
                "requests": {"inFlight": {}, "completedCount": 0, "lastCompleted": None},
            }
            self.save()
        self.data.setdefault(
            "requests", {"inFlight": {}, "completedCount": 0, "lastCompleted": None}
        )
        self.data.setdefault("inputs", None)

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temporary = self.path.with_suffix(".json.tmp")
        temporary.write_text(
            json.dumps(self.data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        temporary.replace(self.path)

    def entry(self, section: str, key: str) -> dict[str, Any]:
        with self.lock:
            return dict(self.data[section].get(key, {}))

    def update(self, section: str, key: str, **values: Any) -> None:
        with self.lock:
            entry = self.data[section].setdefault(key, {})
            entry.update(values)
            entry["updatedAt"] = now()
            self.save()

    def add_version(self, version: str | None) -> None:
        if not version:
            return
        with self.lock:
            if version not in self.data["platformVersions"]:
                self.data["platformVersions"].append(version)
                self.save()

    def bind_inputs(self, inputs: dict[str, str]) -> None:
        with self.lock:
            prior = self.data.get("inputs")
            has_progress = any(self.data.get(section) for section in (
                "definitions", "theorems", "solutions",
            ))
            if prior is None and not has_progress:
                self.data["inputs"] = inputs
                self.save()
                return
            if prior != inputs:
                raise RuntimeError(
                    "upload state belongs to different validated inputs: "
                    f"stored={prior}, current={inputs}"
                )

    def request_start(self, method: str, path: str) -> str:
        request_id = str(uuid.uuid4())
        with self.lock:
            requests = self.data["requests"]
            requests["inFlight"][request_id] = {
                "method": method, "path": path, "startedAt": now(),
            }
            self.save()
        return request_id

    def request_finish(self, request_id: str, outcome: str) -> None:
        with self.lock:
            requests = self.data["requests"]
            item = requests["inFlight"].pop(request_id, {"requestId": request_id})
            item.update({"requestId": request_id, "outcome": outcome, "finishedAt": now()})
            requests["completedCount"] += 1
            requests["lastCompleted"] = item
            self.save()


class Api:
    def __init__(self, state: State) -> None:
        self.api_key = API_KEY_PATH.read_text(encoding="utf-8").strip()
        self.state = state

    def refresh(self) -> str:
        for attempt in range(8):
            request_id = self.state.request_start("POST", "/agent/refresh")
            request = urllib.request.Request(
                BASE + "/agent/refresh",
                data=json.dumps({"api_key": self.api_key}).encode(),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
                    payload = json.load(response)
                    status = response.status
                self.state.request_finish(request_id, f"HTTP {status}")
                self.state.add_version(payload.get("version"))
                return payload["access_token"]
            except urllib.error.HTTPError as error:
                self.state.request_finish(request_id, f"HTTP {error.code}")
                if error.code != 429 and not 500 <= error.code < 600:
                    raise
            except (TimeoutError, ConnectionError, urllib.error.URLError):
                self.state.request_finish(request_id, "transport-error")
                pass
            time.sleep(min(60, 2 ** attempt))
        raise RuntimeError("access-token refresh retries exhausted")

    def request(
        self,
        method: str,
        path: str,
        *,
        body: dict[str, Any] | None = None,
        multipart: dict[str, str | bytes] | None = None,
    ) -> dict[str, Any]:
        for attempt in range(8):
            token = self.refresh()
            headers = {"Authorization": f"Bearer {token}"}
            data: bytes | None = None
            if body is not None:
                data = json.dumps(body).encode()
                headers["Content-Type"] = "application/json"
            elif multipart is not None:
                boundary = f"----p2m-qpbt-{random.getrandbits(64):016x}"
                chunks: list[bytes] = []
                for key, value in multipart.items():
                    chunks.append(f"--{boundary}\r\n".encode())
                    if key == "file":
                        chunks.append(
                            b'Content-Disposition: form-data; name="file"; '
                            b'filename="solution.lean"\r\n'
                        )
                        chunks.append(b"Content-Type: text/plain\r\n\r\n")
                    else:
                        chunks.append(
                            f'Content-Disposition: form-data; name="{key}"\r\n\r\n'.encode()
                        )
                    chunks.append(value if isinstance(value, bytes) else value.encode())
                    chunks.append(b"\r\n")
                chunks.append(f"--{boundary}--\r\n".encode())
                data = b"".join(chunks)
                headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
            request = urllib.request.Request(BASE + path, data=data, headers=headers, method=method)
            request_id = self.state.request_start(method, path)
            try:
                with urllib.request.urlopen(request, timeout=180) as response:
                    payload = json.load(response)
                    status = response.status
                self.state.request_finish(request_id, f"HTTP {status}")
                return payload
            except urllib.error.HTTPError as error:
                content = error.read().decode("utf-8", errors="replace")
                self.state.request_finish(request_id, f"HTTP {error.code}")
                if method != "POST" and (error.code == 429 or 500 <= error.code < 600):
                    time.sleep(min(60, 2 ** attempt))
                    continue
                raise RuntimeError(f"API {method} {path} returned {error.code}: {content}") from error
            except (TimeoutError, ConnectionError, urllib.error.URLError):
                self.state.request_finish(request_id, "transport-error")
                if method == "POST" or attempt == 7:
                    raise
                time.sleep(min(60, 2 ** attempt))
        raise RuntimeError(f"API retries exhausted: {method} {path}")


def exact_search(api: Api, kind: str, name: str) -> list[dict[str, Any]]:
    if kind == "definition":
        endpoint, key, rows = "/definitions", "definition_name", "definitions"
    else:
        endpoint, key, rows = "/theorems", "theorem_name", "theorems"
    query = urllib.parse.urlencode({key: name, "view": "full", "limit": 10})
    payload = api.request("GET", endpoint + "?" + query)
    return [row for row in payload.get(rows, []) if row.get(key) == name]


def assert_safe_payloads(payloads: dict[str, Any]) -> None:
    if payloads.get("tag") != "QPBT" or payloads.get("private") is not True:
        raise RuntimeError("payload manifest is not private and tagged QPBT")
    for section in ("definitions", "theorems"):
        for item in payloads[section]:
            if item.get("private") is not True or item.get("tags") != ["QPBT"]:
                raise RuntimeError(f"unsafe {section} payload: {item.get('definition_name') or item.get('theorem_name')}")


def preflight(
    api: Api, state: State, definition_names: list[str], theorem_names: list[str], jobs: int
) -> None:
    digest = sha256(PAYLOADS_PATH)
    prior = state.data.get("preflight")
    if prior and prior.get("complete") and prior.get("payloadsSha256") == digest:
        return
    requests = [("definition", name) for name in definition_names]
    requests.extend(("theorem", name) for name in theorem_names)
    collisions: list[tuple[str, str]] = []
    with ThreadPoolExecutor(max_workers=min(jobs, 4)) as executor:
        futures = {
            executor.submit(exact_search, api, kind, name): (kind, name)
            for kind, name in requests
        }
        for future in as_completed(futures):
            kind, name = futures[future]
            matches = future.result()
            if not matches:
                continue
            section = "definitions" if kind == "definition" else "theorems"
            id_key = "definition_id" if kind == "definition" else "theorem_id"
            entry = state.entry(section, name)
            owned = entry.get(id_key)
            if owned and all(row.get(id_key) == owned for row in matches):
                continue
            if len(matches) == 1 and entry.get("status") == "INTENT":
                row = matches[0]
                if row.get("visibility") != "private":
                    collisions.append((kind, name))
                    continue
                values: dict[str, Any] = {
                    "status": "PUBLISHED", "recovered": True, id_key: row.get(id_key),
                }
                if kind == "theorem":
                    values["theoremStatus"] = row.get("status")
                state.update(section, name, **values)
                continue
            collisions.append((kind, name))
    if collisions:
        raise RuntimeError(f"platform name collisions before upload: {collisions[:20]}")
    with state.lock:
        state.data["preflight"] = {
            "complete": True,
            "checkedAt": now(),
            "payloadsSha256": digest,
            "definitions": len(definition_names),
            "theorems": len(theorem_names),
        }
        state.save()


def recover_published(api: Api, state: State, section: str, name: str, kind: str) -> bool:
    matches = exact_search(api, kind, name)
    if len(matches) > 1:
        raise RuntimeError(f"multiple exact platform matches for {name}")
    if not matches:
        return False
    row = matches[0]
    if row.get("visibility") != "private":
        raise RuntimeError(f"existing entry is not private: {name}")
    values: dict[str, Any] = {"status": "PUBLISHED", "recovered": True}
    if kind == "definition":
        values["definition_id"] = row.get("definition_id")
    else:
        values["theorem_id"] = row.get("theorem_id")
        values["theoremStatus"] = row.get("status")
    state.update(section, name, **values)
    return True


def recover_job(api: Api, state: State, section: str, name: str, kind: str) -> bool:
    intent = state.entry(section, name).get("intentAt", "")
    offset = 0
    found: list[dict[str, Any]] = []
    while True:
        query = urllib.parse.urlencode({"limit": 200, "offset": offset})
        payload = api.request("GET", "/publish-jobs?" + query)
        batch = payload.get("publish_jobs", [])
        for job in batch:
            job_name = job.get("definition_name") if kind == "definition" else job.get("theorem_name")
            if job_name == name and job.get("created_at", "") >= intent:
                found.append(job)
        offset += len(batch)
        if not batch or offset >= payload.get("total", offset):
            break
    if not found:
        return False
    job = max(found, key=lambda item: item.get("created_at", ""))
    job_id = job.get("job_id") or job.get("id")
    if not job_id:
        return False
    state.update(section, name, job_id=job_id, status=job.get("status", "PENDING"), recovered=True)
    return True


def submit_definition(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["definition_name"]
    entry = state.entry("definitions", name)
    if entry.get("status") == "PUBLISHED":
        return
    if entry.get("job_id") and entry.get("status") in {"PENDING", "COMPILING"}:
        return
    if entry.get("status") == "INTENT":
        if recover_published(api, state, "definitions", name, "definition"):
            return
        if not recover_job(api, state, "definitions", name, "definition"):
            raise RuntimeError(f"unresolved definition intent: {name}")
        return
    if entry.get("status") == "FAILED":
        raise RuntimeError(f"definition previously failed: {name}")
    if entry.get("status") == "ERROR":
        state.update("definitions", name, status="RETRY")
    if not entry and recover_published(api, state, "definitions", name, "definition"):
        return
    state.update("definitions", name, status="INTENT", intentAt=now())
    body = {key: payload[key] for key in (
        "definition_name", "definition_title", "definition",
        "natural_language_statement", "source", "tags", "private",
    )}
    response = api.request("POST", "/submit-definition", body=body)
    job_id = response.get("job_id")
    if not job_id:
        raise RuntimeError(f"definition response has no job_id: {name}")
    state.update("definitions", name, status="PENDING", job_id=job_id, submittedAt=now())


def submit_theorem(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["theorem_name"]
    entry = state.entry("theorems", name)
    if entry.get("status") == "PUBLISHED":
        return
    if entry.get("job_id") and entry.get("status") in {"PENDING", "COMPILING"}:
        return
    if entry.get("status") == "INTENT":
        if recover_published(api, state, "theorems", name, "theorem"):
            return
        if not recover_job(api, state, "theorems", name, "theorem"):
            raise RuntimeError(f"unresolved theorem intent: {name}")
        return
    if entry.get("status") == "FAILED":
        raise RuntimeError(f"theorem previously failed: {name}")
    if not entry and recover_published(api, state, "theorems", name, "theorem"):
        return
    state.update("theorems", name, status="INTENT", intentAt=now())
    body = {key: payload[key] for key in (
        "theorem_name", "theorem_title", "formal_statement", "natural_language_statement",
        "preamble", "source", "tags", "private",
    )}
    response = api.request("POST", "/submit-problem", body=body)
    errors = response.get("errors", [])
    jobs = response.get("jobs", [])
    if errors or len(jobs) != 1 or not jobs[0].get("job_id"):
        raise RuntimeError(f"theorem pre-queue rejection for {name}: errors={errors}, jobs={jobs}")
    state.update("theorems", name, status="PENDING", job_id=jobs[0]["job_id"], submittedAt=now())


def poll_publish(api: Api, state: State, section: str, name: str) -> None:
    while True:
        entry = state.entry(section, name)
        if entry.get("status") == "PUBLISHED":
            return
        job_id = entry.get("job_id")
        if not job_id:
            raise RuntimeError(f"missing publish job id: {section}/{name}")
        result = api.request("GET", f"/publish-jobs/{job_id}")
        status = result.get("status")
        values: dict[str, Any] = {"status": status, "lastPollAt": now()}
        for key in ("definition_id", "theorem_id", "visibility", "error_message"):
            if result.get(key) is not None:
                values[key] = result[key]
        state.update(section, name, **values)
        if status == "PUBLISHED":
            if result.get("visibility") != "private":
                raise RuntimeError(f"published entry is not private: {name}")
            return
        if status == "FAILED":
            raise RuntimeError(f"publish failed for {name}: {result.get('error_message')}")
        if status == "ERROR":
            return
        time.sleep(3)


def run_publish_phase(
    api: Api,
    state: State,
    section: str,
    order: list[str],
    dependencies: dict[str, set[str]],
    payloads: dict[str, dict[str, Any]],
    submit: Callable[[Api, State, dict[str, Any]], None],
    jobs: int,
) -> None:
    pending = set(order)
    while pending:
        complete = {name for name in order if state.entry(section, name).get("status") == "PUBLISHED"}
        pending -= complete
        if not pending:
            return
        ready = [name for name in order if name in pending and dependencies[name] <= complete][:jobs]
        if not ready:
            blocked = {name: sorted(dependencies[name] - complete) for name in sorted(pending)}
            raise RuntimeError(f"blocked {section} DAG: {dict(list(blocked.items())[:8])}")
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            futures = {executor.submit(submit, api, state, payloads[name]): name for name in ready}
            for future in as_completed(futures):
                future.result()
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            futures = {executor.submit(poll_publish, api, state, section, name): name for name in ready}
            for future in as_completed(futures):
                future.result()


def recover_submission(api: Api, state: State, name: str) -> bool:
    intent = state.entry("solutions", name).get("intentAt", "")
    page = 1
    found: list[dict[str, Any]] = []
    while True:
        payload = api.request("GET", f"/submissions?page={page}")
        batch = payload.get("submissions", [])
        for item in batch:
            theorem = item.get("theorem") or {}
            item_name = item.get("theorem_name") or theorem.get("theorem_name")
            if item_name == name and item.get("created_at", "") >= intent:
                found.append(item)
        if not batch or page * 100 >= payload.get("total", page * 100):
            break
        page += 1
    if not found:
        return False
    item = max(found, key=lambda row: row.get("created_at", ""))
    submission_id = item.get("submission_id") or item.get("id")
    if not submission_id:
        return False
    state.update("solutions", name, submission_id=submission_id,
                 status=item.get("status", "PENDING"), recovered=True)
    return True


def submit_solution(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["theorem_name"]
    entry = state.entry("solutions", name)
    if entry.get("status") == "ACCEPTED":
        return
    if entry.get("submission_id") and entry.get("status") == "PENDING":
        return
    if entry.get("status") == "INTENT":
        if not recover_submission(api, state, name):
            raise RuntimeError(f"unresolved solution intent: {name}")
        return
    if entry.get("status") in TERMINAL_SUBMISSION - {"ACCEPTED", "ERROR"}:
        raise RuntimeError(f"solution previously ended {entry.get('status')}: {name}")
    theorem = state.entry("theorems", name)
    theorem_id = theorem.get("theorem_id")
    if not theorem_id:
        matches = exact_search(api, "theorem", name)
        if len(matches) != 1:
            raise RuntimeError(f"cannot resolve theorem id: {name}")
        theorem_id = matches[0]["theorem_id"]
        state.update("theorems", name, theorem_id=theorem_id, status="PUBLISHED")
    state.update("solutions", name, status="INTENT", intentAt=now())
    response = api.request("POST", "/verify", multipart={
        "theorem_id": theorem_id,
        "proof_type": "prove",
        "file": (ROOT / payload["solution_path"]).read_bytes(),
        "explanation": payload["explanation"],
    })
    submission_id = response.get("submission_id")
    if not submission_id:
        raise RuntimeError(f"verify response has no submission_id: {name}")
    state.update("solutions", name, status="PENDING", submission_id=submission_id,
                 theorem_id=theorem_id, submittedAt=now())


def poll_solution(api: Api, state: State, name: str) -> None:
    while True:
        entry = state.entry("solutions", name)
        if entry.get("status") == "ACCEPTED":
            return
        submission_id = entry.get("submission_id")
        if not submission_id:
            raise RuntimeError(f"missing submission id: {name}")
        query = urllib.parse.urlencode({"submission_id": submission_id})
        result = api.request("GET", "/verify?" + query)
        status = result.get("status")
        state.update("solutions", name, status=status, lastPollAt=now())
        if status == "ACCEPTED":
            return
        if status == "ERROR":
            return
        if status in TERMINAL_SUBMISSION:
            raise RuntimeError(
                f"solution ended {status} for {name}: {result.get('error') or result.get('message')}"
            )
        time.sleep(3)


def run_solution_phase(
    api: Api,
    state: State,
    order: list[str],
    dependencies: dict[str, set[str]],
    payloads: dict[str, dict[str, Any]],
    jobs: int,
) -> None:
    pending = set(order)
    while pending:
        complete = {name for name in order if state.entry("solutions", name).get("status") == "ACCEPTED"}
        pending -= complete
        if not pending:
            return
        ready = [name for name in order if name in pending and dependencies[name] <= complete][:jobs]
        if not ready:
            blocked = {name: sorted(dependencies[name] - complete) for name in sorted(pending)}
            raise RuntimeError(f"blocked solution DAG: {dict(list(blocked.items())[:8])}")
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            futures = {executor.submit(submit_solution, api, state, payloads[name]): name for name in ready}
            for future in as_completed(futures):
                future.result()
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            futures = {executor.submit(poll_solution, api, state, name): name for name in ready}
            for future in as_completed(futures):
                future.result()


def paged_tag(api: Api, endpoint: str, rows_key: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    offset = 0
    while True:
        query = urllib.parse.urlencode({
            "tags": "QPBT", "view": "full", "limit": 200, "offset": offset,
        })
        payload = api.request("GET", endpoint + "?" + query)
        batch = payload.get(rows_key, [])
        rows.extend(batch)
        offset += len(batch)
        if not batch or offset >= payload.get("total", offset):
            return rows


def final_verify(
    api: Api,
    state: State,
    expected_definitions: set[str],
    expected_theorems: set[str],
    targets: set[str],
) -> None:
    definitions = paged_tag(api, "/definitions", "definitions")
    theorems = paged_tag(api, "/theorems", "theorems")
    definition_names = {row.get("definition_name") for row in definitions}
    theorem_names = {row.get("theorem_name") for row in theorems}
    problems: list[str] = []
    if definition_names != expected_definitions:
        problems.append(
            f"definition set mismatch: missing={sorted(expected_definitions-definition_names)[:8]}, "
            f"extra={sorted(definition_names-expected_definitions)[:8]}"
        )
    if theorem_names != expected_theorems:
        problems.append(
            f"theorem set mismatch: missing={sorted(expected_theorems-theorem_names)[:8]}, "
            f"extra={sorted(theorem_names-expected_theorems)[:8]}"
        )
    nonprivate = [
        row.get("definition_name") for row in definitions if row.get("visibility") != "private"
    ] + [row.get("theorem_name") for row in theorems if row.get("visibility") != "private"]
    nonproved = [row.get("theorem_name") for row in theorems if row.get("status") != "Proved"]
    if nonprivate:
        problems.append(f"nonprivate entries: {nonprivate[:8]}")
    if nonproved:
        problems.append(f"non-Proved entries: {nonproved[:8]}")
    theorem_by_name = {row.get("theorem_name"): row for row in theorems}
    target_ids = {
        target: theorem_by_name.get(target, {}).get("theorem_id") for target in sorted(targets)
    }
    if any(not value for value in target_ids.values()):
        problems.append(f"missing target ids: {target_ids}")
    result = {
        "checkedAt": now(),
        "definitions": len(definitions),
        "theorems": len(theorems),
        "proved": sum(row.get("status") == "Proved" for row in theorems),
        "open": sum(row.get("status") == "Open" for row in theorems),
        "allPrivate": not nonprivate,
        "targetTheoremIds": target_ids,
        "problems": problems,
    }
    with state.lock:
        state.data["finalVerification"] = result
        state.save()
    if problems:
        raise RuntimeError("final verification failed: " + "; ".join(problems))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--phase", choices=("definitions", "theorems", "solutions", "verify", "all"),
        default="all",
    )
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 16:
        raise RuntimeError("jobs must be between 1 and 16")
    require_validated_inputs()
    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    manifest = json.loads(PAYLOADS_PATH.read_text(encoding="utf-8"))
    assert_safe_payloads(manifest)
    state = State(STATE_PATH)
    state.bind_inputs({
        "planSha256": sha256(PLAN_PATH),
        "payloadsSha256": sha256(PAYLOADS_PATH),
        "platformSha256": platform_digest(),
    })
    api = Api(state)

    definition_payload_by_id = {item["bundle_id"]: item for item in manifest["definitions"]}
    definition_order = [plan["definitions"][bid]["definitionName"] for bid in plan["definitionOrder"]]
    definition_payloads = {
        plan["definitions"][bid]["definitionName"]: definition_payload_by_id[bid]
        for bid in plan["definitionOrder"]
    }
    definition_dependencies = {
        plan["definitions"][bid]["definitionName"]: {
            plan["definitions"][dependency]["definitionName"]
            for dependency in plan["definitions"][bid]["definitionDependencies"]
        }
        for bid in plan["definitionOrder"]
    }
    theorem_payload_by_id = {item["command_id"]: item for item in manifest["theorems"]}
    solution_payload_by_id = {item["command_id"]: item for item in manifest["solutions"]}
    theorem_order = [plan["nodes"][cid]["platformName"] for cid in plan["nodeOrder"]]
    theorem_payloads = {
        plan["nodes"][cid]["platformName"]: theorem_payload_by_id[cid]
        for cid in plan["nodeOrder"]
    }
    solution_payloads = {
        plan["nodes"][cid]["platformName"]: solution_payload_by_id[cid]
        for cid in plan["nodeOrder"]
    }
    theorem_dependencies = {
        plan["nodes"][cid]["platformName"]: {
            plan["nodes"][dependency]["platformName"]
            for dependency in plan["nodes"][cid]["theoremDependencies"]
        }
        for cid in plan["nodeOrder"]
    }
    preflight(api, state, definition_order, theorem_order, args.jobs)
    phases = (
        ("definitions", "theorems", "solutions", "verify")
        if args.phase == "all" else (args.phase,)
    )
    for phase in phases:
        print(f"phase {phase}", flush=True)
        if phase == "definitions":
            run_publish_phase(
                api, state, "definitions", definition_order, definition_dependencies,
                definition_payloads, submit_definition, args.jobs,
            )
        elif phase == "theorems":
            if any(state.entry("definitions", name).get("status") != "PUBLISHED"
                   for name in definition_order):
                raise RuntimeError("all QPBT definitions must be PUBLISHED before theorem stubs")
            run_publish_phase(
                api, state, "theorems", theorem_order, theorem_dependencies,
                theorem_payloads, submit_theorem, args.jobs,
            )
        elif phase == "solutions":
            if any(state.entry("theorems", name).get("status") != "PUBLISHED"
                   for name in theorem_order):
                raise RuntimeError("all QPBT theorem stubs must be PUBLISHED before solutions")
            run_solution_phase(
                api, state, theorem_order, theorem_dependencies, solution_payloads, args.jobs,
            )
        elif phase == "verify":
            final_verify(
                api, state, set(definition_order), set(theorem_order), set(plan["targets"]),
            )
    print(json.dumps(state.data["finalVerification"] or {
        "definitionsPublished": sum(
            item.get("status") == "PUBLISHED" for item in state.data["definitions"].values()
        ),
        "theoremsPublished": sum(
            item.get("status") == "PUBLISHED" for item in state.data["theorems"].values()
        ),
        "solutionsAccepted": sum(
            item.get("status") == "ACCEPTED" for item in state.data["solutions"].values()
        ),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
