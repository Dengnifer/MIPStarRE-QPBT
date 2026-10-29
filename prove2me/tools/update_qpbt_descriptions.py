#!/usr/bin/env python3
"""Synchronize the final QPBT definition descriptions through the theorem API."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
FINAL_PATH = Path("/home/drx/p2m/status/final/qpbt-bundles-final.json")
STATE_PATH = ROOT / "prove2me" / "records" / "description_update_state.json"
UPLOAD_STATE_PATH = ROOT / "prove2me" / "records" / "upload_state.json"

sys.path.insert(0, str(ROOT / "prove2me" / "tools"))
from upload_private import Api, State, now  # noqa: E402


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def classify_error(error: Exception) -> str:
    match = re.search(r"returned (\d+)", str(error))
    if match:
        return f"http-{match.group(1)}"
    return "request-error"


def load_state() -> dict[str, Any]:
    if STATE_PATH.is_file():
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    return {"schemaVersion": 1, "createdAt": now(), "entries": {}}


def save_state(data: dict[str, Any]) -> None:
    temporary = STATE_PATH.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(STATE_PATH)


def patch_and_verify(api: Api, theorem_id: str, desired: str) -> tuple[str, bool, str | None]:
    path = f"/theorems/{theorem_id}"
    try:
        current = api.request("GET", path)
        if current.get("natural_language_statement") != desired:
            api.request(
                "PATCH",
                path,
                body={
                    "natural_language_statement": desired,
                    "reason": "Full statement and description before publication",
                },
            )
            patched = True
        else:
            patched = False
        checked = api.request("GET", path)
        if checked.get("natural_language_statement") != desired:
            return "mismatch", patched, "readback-mismatch"
        return "verified", patched, None
    except Exception as error:  # keep the resumable run moving across entries
        return "error", False, classify_error(error)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()

    final = json.loads(FINAL_PATH.read_text(encoding="utf-8"))
    names = list(final)
    if args.limit:
        names = names[: args.limit]
    state = load_state()
    state.setdefault("entries", {})
    state["manifest"] = str(FINAL_PATH)
    state["manifestCount"] = len(final)
    state["lastStartedAt"] = now()
    save_state(state)

    api = Api(State(UPLOAD_STATE_PATH))
    patched = 0
    verified = 0
    errors = 0
    for index, name in enumerate(names, start=1):
        item = final[name]
        theorem_id = item.get("definition_id") or item.get("theorem_id")
        desired = item["natural_language_statement"]
        result, did_patch, error = patch_and_verify(api, theorem_id, desired)
        record = {
            "definition_id": theorem_id,
            "desired_sha256": digest(desired),
            "status": result,
            "patched": did_patch,
            "checkedAt": now(),
        }
        if error:
            record["error"] = error
        state["entries"][name] = record
        state["lastCompletedAt"] = record["checkedAt"]
        save_state(state)
        patched += int(did_patch)
        verified += int(result == "verified")
        errors += int(result != "verified")
        if index % 10 == 0 or index == len(names):
            print(f"progress={index}/{len(names)} patched={patched} verified={verified} errors={errors}", flush=True)

    state["lastFinishedAt"] = now()
    state["lastRun"] = {
        "requested": len(names),
        "patched": patched,
        "verified": verified,
        "errors": errors,
    }
    save_state(state)
    return int(errors != 0)


if __name__ == "__main__":
    raise SystemExit(main())
