#!/usr/bin/env python3
"""Publish the QPBT tree and verify its public theorem pages."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
UPLOAD_STATE = ROOT / "prove2me" / "records" / "upload_state.json"
PAYLOADS = ROOT / "prove2me" / "generated" / "payloads.json"
FINAL_DEFINITIONS = Path("/home/drx/p2m/status/final/qpbt-bundles-final.json")
STATE_PATH = ROOT / "prove2me" / "records" / "qpbt_publish_state.json"
LOG_PATH = ROOT / "prove2me" / "records" / "qpbt_publish.log"
GATE = Path("/home/drx/p2m/status/lidt-public")
API_KEY_PATH = Path("/home/drx/.config/prove2me/api_key")
API_BASE = "https://prove2.me/api/v1"
PAGE_BASE = "https://prove2.me/theorems"
TARGET_NAMES = (
    "MIPStarRE.QPBT.Palomar.exists_spcc_value_one",
    "MIPStarRE.QPBT.Palomar.exists_ld_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness_qubit",
)
REASON = "Full statement and description before publication"
RETRYABLE = {429, 500, 502, 503, 504}
TERMS_RE = re.compile(r"\b(?:terms?|licen[cs](?:e|ing|ed)|accept(?:ance|ed)?)\b", re.I)
SENSITIVE_KEYS = {"access_token", "api_key", "authorization", "token", "password"}


class TermsError(RuntimeError):
    pass


class PublishError(RuntimeError):
    def __init__(self, code: int, method: str, stage: str):
        self.code = code
        self.method = method
        self.stage = stage
        super().__init__(f"{stage}: {method} HTTP {code}")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def save_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def log_line(text: str) -> None:
    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as handle:
        handle.write(f"{now()} {text}\n")


def response_summary(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {"type": type(payload).__name__}
    result: dict[str, Any] = {
        "keys": sorted(key for key in payload if key.lower() not in SENSITIVE_KEYS),
    }
    for key in ("visibility", "status"):
        value = payload.get(key)
        if isinstance(value, (str, int, float, bool)):
            result[key] = value
    return result


def check_terms(payload: Any, code: int) -> None:
    if code < 400:
        return
    if TERMS_RE.search(json.dumps(payload, ensure_ascii=False)):
        raise TermsError("Prove2Me returned a terms or licensing error")


class Client:
    def __init__(self, state: dict[str, Any]) -> None:
        self.state = state
        self.token: str | None = None
        self.token_expires = 0.0

    def record_call(self, method: str, path: str, code: int, payload: Any, auth: bool) -> None:
        self.state["calls"].append({
            "at": now(),
            "method": method,
            "path": path,
            "authenticated": auth,
            "status": code,
            "response": response_summary(payload),
        })
        save_json(STATE_PATH, self.state)

    def refresh(self) -> None:
        key = API_KEY_PATH.read_text(encoding="utf-8").strip()
        request = urllib.request.Request(
            API_BASE + "/agent/refresh",
            data=json.dumps({"api_key": key}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        for attempt in range(8):
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    payload = json.load(response)
                    code = response.status
                self.record_call("POST", "/agent/refresh", code, payload, False)
                token = payload.get("access_token") if isinstance(payload, dict) else None
                if not token:
                    raise RuntimeError("access-token refresh returned no token")
                self.token = token
                self.token_expires = time.time() + 3300
                return
            except urllib.error.HTTPError as error:
                raw = error.read().decode("utf-8", errors="replace")
                try:
                    payload = json.loads(raw)
                except json.JSONDecodeError:
                    payload = {}
                self.record_call("POST", "/agent/refresh", error.code, payload, False)
                check_terms(payload, error.code)
                if error.code not in RETRYABLE:
                    raise PublishError(error.code, "POST", "token refresh") from error
            except (TimeoutError, urllib.error.URLError):
                self.record_call("POST", "/agent/refresh", 0, {}, False)
                if attempt == 7:
                    raise
            time.sleep(min(60, 2**attempt))
        raise RuntimeError("token refresh retries exhausted")

    def request(
        self,
        method: str,
        path: str,
        *,
        body: dict[str, Any] | None = None,
        allow: set[int] | None = None,
        stage: str,
    ) -> tuple[int, Any]:
        for attempt in range(8):
            if self.token is None or time.time() >= self.token_expires:
                self.refresh()
            headers = {"Authorization": f"Bearer {self.token}"}
            data = None
            if body is not None:
                data = json.dumps(body, ensure_ascii=False).encode("utf-8")
                headers["Content-Type"] = "application/json"
            request = urllib.request.Request(API_BASE + path, data=data, headers=headers, method=method)
            try:
                with urllib.request.urlopen(request, timeout=180) as response:
                    raw = response.read()
                    payload = json.loads(raw.decode("utf-8")) if raw else {}
                    code = response.status
                self.record_call(method, path, code, payload, True)
                return code, payload
            except urllib.error.HTTPError as error:
                raw = error.read().decode("utf-8", errors="replace")
                try:
                    payload = json.loads(raw)
                except json.JSONDecodeError:
                    payload = {}
                self.record_call(method, path, error.code, payload, True)
                check_terms(payload, error.code)
                if error.code == 401 and attempt == 0:
                    self.token = None
                    continue
                if error.code in RETRYABLE and attempt < 7:
                    time.sleep(min(60, 2**attempt))
                    continue
                if allow and error.code in allow:
                    return error.code, payload
                raise PublishError(error.code, method, stage) from error
            except (TimeoutError, urllib.error.URLError):
                self.record_call(method, path, 0, {}, True)
                if attempt == 7:
                    raise
                time.sleep(min(60, 2**attempt))
        raise RuntimeError(f"request retries exhausted during {stage}")


def first_sentence(text: str) -> str:
    paragraph = next((line.strip() for line in text.splitlines() if line.strip()), "")
    match = re.search(r"[.!?](?:\s|$)", paragraph)
    sentence = paragraph[: match.end() - 1] if match else paragraph
    sentence = re.sub(r"[*`#]", "", sentence)
    return re.sub(r"\s+", " ", sentence).strip()


def load_entries() -> list[dict[str, Any]]:
    upload = read_json(UPLOAD_STATE)
    payloads = read_json(PAYLOADS)
    final_definitions = read_json(FINAL_DEFINITIONS)
    for payload in payloads["theorems"] + payloads["definitions"]:
        tags = {str(tag).lower() for tag in payload.get("tags", [])}
        if "qpbt" not in tags:
            raise RuntimeError("QPBT payload census contains an entry without the QPBT tag")
    theorem_text = {item["theorem_name"]: item["natural_language_statement"] for item in payloads["theorems"]}
    definition_text = {
        name: item["natural_language_statement"] for name, item in final_definitions.items()
    }
    entries: list[dict[str, Any]] = []
    for name, record in sorted(upload["theorems"].items()):
        theorem_id = record.get("theorem_id")
        if not theorem_id or name not in theorem_text:
            raise RuntimeError("theorem upload state or payload is incomplete")
        text = theorem_text[name]
        entries.append({
            "kind": "theorem",
            "name": name,
            "id": theorem_id,
            "text": text,
            "firstSentence": first_sentence(text),
        })
    for name, record in sorted(upload["definitions"].items()):
        if not name.startswith("QPBT_QPBT_"):
            raise RuntimeError("definition upload state contains a non-QPBT entry")
        definition_id = record.get("definition_id") or record.get("theorem_id")
        if not definition_id or name not in definition_text:
            raise RuntimeError("definition upload state or final manifest is incomplete")
        text = definition_text[name]
        entries.append({
            "kind": "definition",
            "name": name,
            "id": definition_id,
            "text": text,
            "firstSentence": first_sentence(text),
        })
    if len(entries) != 863 or len({item["id"] for item in entries}) != len(entries):
        raise RuntimeError("QPBT entry census or id uniqueness check failed")
    names = {item["name"] for item in entries}
    if any(name not in names for name in TARGET_NAMES):
        raise RuntimeError("one or more QPBT publication targets are missing")
    return entries


def key_for(item: dict[str, Any]) -> str:
    return f"{item['kind']}:{item['name']}"


def initial_state(entries: list[dict[str, Any]]) -> dict[str, Any]:
    state = read_json(STATE_PATH) if STATE_PATH.is_file() else {
        "schemaVersion": 1,
        "project": "QPBT",
        "createdAt": now(),
        "entries": {},
        "calls": [],
        "termsOrLicensingErrors": [],
    }
    state.setdefault("entries", {})
    state.setdefault("calls", [])
    state.setdefault("termsOrLicensingErrors", [])
    for item in entries:
        state["entries"].setdefault(key_for(item), {
            "kind": item["kind"],
            "name": item["name"],
            "id": item["id"],
            "firstSentenceSha256": digest(item["firstSentence"]),
        })
    state["entryCount"] = len(entries)
    state["theoremCount"] = sum(item["kind"] == "theorem" for item in entries)
    state["definitionCount"] = sum(item["kind"] == "definition" for item in entries)
    state["targets"] = list(TARGET_NAMES)
    return state


def update_entry(state: dict[str, Any], item: dict[str, Any], field: str, value: dict[str, Any]) -> None:
    state["entries"].setdefault(key_for(item), {}).update({field: value, "updatedAt": now()})
    save_json(STATE_PATH, state)


def ordered_for_publication(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_name = {item["name"]: item for item in entries}
    result = [by_name[name] for name in TARGET_NAMES]
    result.extend(item for item in entries if item["kind"] == "theorem" and item["name"] not in TARGET_NAMES)
    result.extend(item for item in entries if item["kind"] == "definition")
    return result


def public_phase(entries: list[dict[str, Any]], state: dict[str, Any], client: Client) -> None:
    if not GATE.is_file():
        raise RuntimeError("LIDT publication gate is absent")
    posted = 0
    already_public = 0
    unsupported_definitions = 0
    for index, item in enumerate(ordered_for_publication(entries), start=1):
        previous = state["entries"].get(key_for(item), {})
        previous_publication = previous.get("publication", {})
        previous_status = previous_publication.get("status")
        if previous_status == "PUBLIC":
            if "httpStatus" in previous_publication:
                posted += 1
            else:
                already_public += 1
            continue
        if previous_status == "UNSUPPORTED":
            unsupported_definitions += 1
            continue
        code, payload = client.request(
            "GET", f"/theorems/{item['id']}", stage="authenticated visibility check"
        )
        visibility = payload.get("visibility") if isinstance(payload, dict) else None
        update_entry(state, item, "authenticatedBefore", {
            "status": code,
            "visibility": visibility,
        })
        if visibility == "public":
            already_public += 1
            update_entry(state, item, "publication", {
                "status": "PUBLIC",
                "reason": "already public before this resumable run",
            })
            continue
        if visibility != "private":
            raise RuntimeError(f"unexpected visibility during publication at item {index}")
        allow = {400, 404, 405} if item["kind"] == "definition" else None
        code, payload = client.request(
            "POST",
            f"/theorems/{item['id']}/make-public",
            allow=allow,
            stage="make-public",
        )
        if code in {400, 404, 405} and item["kind"] == "definition":
            unsupported_definitions += 1
            update_entry(state, item, "publication", {
                "status": "UNSUPPORTED",
                "httpStatus": code,
                "reason": "No documented definition make-public endpoint accepted this definition id",
            })
            log_line(f"definition make-public unsupported name={item['name']}")
        else:
            posted += 1
            update_entry(state, item, "publication", {
                "status": "PUBLIC",
                "httpStatus": code,
                "response": response_summary(payload),
            })
            log_line(f"make-public requested kind={item['kind']} name={item['name']}")
        if index % 25 == 0 or index == len(entries):
            print(f"public progress={index}/{len(entries)} posted={posted} already_public={already_public} unsupported_definitions={unsupported_definitions}", flush=True)
    state["publicationSummary"] = {
        "finishedAt": now(),
        "postedCalls": posted,
        "alreadyPublic": already_public,
        "unsupportedDefinitions": unsupported_definitions,
    }
    save_json(STATE_PATH, state)


def final_visibility_phase(entries: list[dict[str, Any]], state: dict[str, Any], client: Client) -> None:
    counts = {"public": 0, "private": 0, "other": 0}
    private: list[str] = []
    for index, item in enumerate(entries, start=1):
        previous = state["entries"].get(key_for(item), {})
        previous_final = previous.get("authenticatedFinal")
        if isinstance(previous_final, dict) and "visibility" in previous_final:
            visibility = previous_final.get("visibility")
        else:
            code = 0
            payload: Any = {}
            for attempt in range(3):
                code, payload = client.request(
                    "GET",
                    f"/theorems/{item['id']}",
                    allow={404},
                    stage="authenticated final visibility audit",
                )
                if code != 404 or attempt == 2:
                    break
                time.sleep(5 * (attempt + 1))
            visibility = payload.get("visibility") if isinstance(payload, dict) else None
            if code == 404:
                update_entry(state, item, "authenticatedFinal", {
                    "visibility": None,
                    "httpStatus": code,
                    "reason": "Authenticated visibility endpoint returned 404 after retries",
                })
                visibility = None
            else:
                update_entry(state, item, "authenticatedFinal", {"visibility": visibility})
        if visibility == "public":
            counts["public"] += 1
        elif visibility == "private":
            counts["private"] += 1
            private.append(item["name"])
        else:
            counts["other"] += 1
        if index % 50 == 0 or index == len(entries):
            print(f"visibility progress={index}/{len(entries)} public={counts['public']} private={counts['private']} other={counts['other']}", flush=True)
    state["authenticatedFinalSummary"] = {
        "finishedAt": now(),
        "counts": counts,
        "privateNames": private,
    }
    save_json(STATE_PATH, state)


def page_contains_sentence(body: str, sentence: str) -> bool:
    raw = html.unescape(body)
    if sentence in raw or sentence.replace("&", "&amp;") in body:
        return True
    serialized = raw
    while "\\\\" in serialized:
        serialized = serialized.replace("\\\\", "\\")
    serialized = re.sub(
        r"\\u([0-9a-fA-F]{4})",
        lambda match: chr(int(match.group(1), 16)),
        serialized,
    )
    return sentence in serialized


class PageVerifier:
    def __init__(self) -> None:
        self.last_start = 0.0

    def fetch(self, url: str) -> tuple[int, str]:
        delay = 0.5 - (time.monotonic() - self.last_start)
        if delay > 0:
            time.sleep(delay)
        self.last_start = time.monotonic()
        request = urllib.request.Request(
            url,
            headers={"User-Agent": "prove2me-qpbt-signed-out-check/1.0"},
            method="GET",
        )
        for attempt in range(3):
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    return response.status, response.read().decode("utf-8", errors="replace")
            except urllib.error.HTTPError as error:
                error.read()
                return error.code, ""
            except (TimeoutError, urllib.error.URLError):
                if attempt == 2:
                    raise
                time.sleep(2 ** attempt)
        raise RuntimeError("page fetch retries exhausted")


def page_phase(entries: list[dict[str, Any]], state: dict[str, Any]) -> None:
    verifier = PageVerifier()
    counts = {"verified": 0, "failed": 0, "status200WrongSentence": 0, "non200": 0}
    for index, item in enumerate(entries, start=1):
        previous = state["entries"].get(key_for(item), {})
        if (
            previous.get("signedOutPage", {}).get("status") == "VERIFIED"
            and previous.get("signedOutPage", {}).get("firstSentenceSha256")
            == digest(item["firstSentence"])
        ):
            counts["verified"] += 1
            continue
        status, body = verifier.fetch(f"{PAGE_BASE}/{item['id']}")
        matches = status == 200 and page_contains_sentence(body, item["firstSentence"])
        if matches:
            counts["verified"] += 1
            result = {
                "status": "VERIFIED",
                "httpStatus": status,
                "firstSentenceSha256": digest(item["firstSentence"]),
            }
        else:
            counts["failed"] += 1
            if status == 200:
                counts["status200WrongSentence"] += 1
            else:
                counts["non200"] += 1
            result = {
                "status": "FAILED",
                "httpStatus": status,
                "firstSentenceMatched": False,
            }
        update_entry(state, item, "signedOutPage", result)
        if index % 25 == 0 or index == len(entries):
            print(f"page progress={index}/{len(entries)} verified={counts['verified']} failed={counts['failed']} non200={counts['non200']}", flush=True)
    state["signedOutPageSummary"] = {"finishedAt": now(), **counts}
    save_json(STATE_PATH, state)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("public", "verify-pages", "all"), default="all")
    args = parser.parse_args()
    entries = load_entries()
    state = initial_state(entries)
    save_json(STATE_PATH, state)
    client = Client(state)
    if args.phase in {"public", "all"}:
        public_phase(entries, state, client)
        final_visibility_phase(entries, state, client)
    if args.phase in {"verify-pages", "all"}:
        page_phase(entries, state)
    print(json.dumps({
        "entries": len(entries),
        "publication": state.get("publicationSummary"),
        "authenticatedFinal": state.get("authenticatedFinalSummary"),
        "signedOutPages": state.get("signedOutPageSummary"),
        "termsOrLicensingErrors": len(state.get("termsOrLicensingErrors", [])),
    }, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except TermsError as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(2)
    except Exception as error:
        print(f"publish failed: {type(error).__name__}", file=sys.stderr)
        raise SystemExit(1)
