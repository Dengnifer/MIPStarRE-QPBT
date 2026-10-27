#!/usr/bin/env python3
"""Check every planned QPBT platform name in the default environment."""

from __future__ import annotations

import hashlib
import json
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
OUTPUT = ROOT / "prove2me" / "generated" / "collision_check.json"
API_KEY_PATH = Path("/home/drx/.config/prove2me/api_key")
BASE = "https://prove2.me/api/v1"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Api:
    def __init__(self) -> None:
        self.api_key = API_KEY_PATH.read_text(encoding="utf-8").strip()
        self.versions: set[str] = set()
        self.lock = threading.Lock()

    def token(self) -> str:
        for attempt in range(8):
            request = urllib.request.Request(
                BASE + "/agent/refresh",
                data=json.dumps({"api_key": self.api_key}).encode(),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
                    payload = json.load(response)
                if payload.get("version"):
                    with self.lock:
                        self.versions.add(payload["version"])
                return payload["access_token"]
            except urllib.error.HTTPError as error:
                if error.code != 429 and not 500 <= error.code < 600:
                    raise
            except (TimeoutError, ConnectionError, urllib.error.URLError):
                pass
            time.sleep(min(30, 2 ** attempt))
        raise RuntimeError("API token refresh retries exhausted")

    def get(self, path: str) -> dict[str, Any]:
        for attempt in range(8):
            token = self.token()
            request = urllib.request.Request(
                BASE + path,
                headers={"Authorization": f"Bearer {token}"},
                method="GET",
            )
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    return json.load(response)
            except urllib.error.HTTPError as error:
                if error.code == 429 or 500 <= error.code < 600:
                    time.sleep(min(30, 2 ** attempt))
                    continue
                raise
        raise RuntimeError(f"API retries exhausted for {path}")


def exact_search(api: Api, kind: str, name: str) -> list[dict[str, Any]]:
    if kind == "definition":
        endpoint, rows_key, name_key = "/definitions", "definitions", "definition_name"
    else:
        endpoint, rows_key, name_key = "/theorems", "theorems", "theorem_name"
    query = urllib.parse.urlencode({name_key: name, "view": "compact", "limit": 10})
    payload = api.get(endpoint + "?" + query)
    return [row for row in payload.get(rows_key, []) if row.get(name_key) == name]


def source_extension_name(anchor: str | None) -> str | None:
    if not anchor:
        return None
    for prefix in ("MIPStarRE.LDT.", "MIPStarRE.Quantum."):
        if anchor.startswith(prefix):
            return "LIDT." + anchor
        marker = "." + prefix
        if anchor.startswith("_private.") and marker in anchor:
            return "LIDT." + prefix + anchor.split(marker, 1)[1]
    return None


def search_extension(api: Api, name: str) -> list[str]:
    return [
        kind for kind in ("definition", "theorem")
        if exact_search(api, kind, name)
    ]


def main() -> int:
    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    plan_hash = sha256(PLAN_PATH)
    planned_definitions = {
        item["definitionName"] for item in plan["definitions"].values()
    }
    planned_theorems = {item["platformName"] for item in plan["nodes"].values()}
    extension_names = {
        name
        for command in plan["commands"].values()
        if (name := source_extension_name(command.get("anchor"))) is not None
    }
    api = Api()
    prior: dict[str, Any] = {}
    if OUTPUT.is_file():
        candidate = json.loads(OUTPUT.read_text(encoding="utf-8"))
        if candidate.get("planSha256") == plan_hash:
            prior = candidate
    api.versions.update(prior.get("platformVersions", []))
    checked_definitions = set(prior.get("checkedDefinitions", []))
    checked_theorems = set(prior.get("checkedTheorems", []))
    definition_collisions = list(prior.get("definitionCollisions", []))
    theorem_collisions = list(prior.get("theoremCollisions", []))
    checked_extensions = set(prior.get("checkedExtensions", []))
    extension_collision_kinds = {
        name: list(kinds)
        for name, kinds in prior.get("extensionCollisionKinds", {}).items()
    }
    requests = [
        ("definition", name) for name in planned_definitions - checked_definitions
    ]
    requests.extend(
        ("theorem", name) for name in planned_theorems - checked_theorems
    )
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {
            executor.submit(exact_search, api, kind, name): (kind, name)
            for kind, name in requests
        }
        for future in as_completed(futures):
            kind, name = futures[future]
            if future.result():
                if kind == "definition":
                    definition_collisions.append(name)
                else:
                    theorem_collisions.append(name)
            if kind == "definition":
                checked_definitions.add(name)
            else:
                checked_theorems.add(name)
            checkpoint = {
                "planSha256": plan_hash,
                "uploadNamespace": plan["uploadNamespace"],
                "checkedDefinitions": sorted(checked_definitions),
                "checkedTheorems": sorted(checked_theorems),
                "definitionCollisions": sorted(set(definition_collisions)),
                "theoremCollisions": sorted(set(theorem_collisions)),
                "checkedExtensions": sorted(checked_extensions),
                "extensionCollisions": sorted(extension_collision_kinds),
                "extensionCollisionKinds": extension_collision_kinds,
                "complete": False,
            }
            temporary = OUTPUT.with_suffix(".json.tmp")
            temporary.write_text(json.dumps(checkpoint, indent=2, sort_keys=True) + "\n",
                                 encoding="utf-8")
            temporary.replace(OUTPUT)
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {
            executor.submit(search_extension, api, name): name
            for name in extension_names - checked_extensions
        }
        for future in as_completed(futures):
            name = futures[future]
            kinds = future.result()
            if kinds:
                extension_collision_kinds[name] = kinds
            checked_extensions.add(name)
            checkpoint = {
                "planSha256": plan_hash,
                "uploadNamespace": plan["uploadNamespace"],
                "checkedDefinitions": sorted(checked_definitions),
                "checkedTheorems": sorted(checked_theorems),
                "definitionCollisions": sorted(set(definition_collisions)),
                "theoremCollisions": sorted(set(theorem_collisions)),
                "checkedExtensions": sorted(checked_extensions),
                "extensionCollisions": sorted(extension_collision_kinds),
                "extensionCollisionKinds": extension_collision_kinds,
                "complete": False,
            }
            temporary = OUTPUT.with_suffix(".json.tmp")
            temporary.write_text(json.dumps(checkpoint, indent=2, sort_keys=True) + "\n",
                                 encoding="utf-8")
            temporary.replace(OUTPUT)
    definition_collisions.sort()
    theorem_collisions.sort()
    result = {
        "checkedAt": datetime.now(timezone.utc).isoformat(),
        "planSha256": plan_hash,
        "uploadNamespace": plan["uploadNamespace"],
        "platformVersions": sorted(api.versions),
        "plannedDefinitions": len(planned_definitions),
        "plannedTheorems": len(planned_theorems),
        "exactDefinitionSearches": len(planned_definitions),
        "exactTheoremSearches": len(planned_theorems),
        "sourceExtensions": len(extension_names),
        "exactExtensionDefinitionSearches": len(extension_names),
        "exactExtensionTheoremSearches": len(extension_names),
        "checkedDefinitions": sorted(checked_definitions),
        "checkedTheorems": sorted(checked_theorems),
        "checkedExtensions": sorted(checked_extensions),
        "definitionCollisions": definition_collisions,
        "theoremCollisions": theorem_collisions,
        "extensionCollisions": sorted(extension_collision_kinds),
        "extensionCollisionKinds": extension_collision_kinds,
        "complete": True,
    }
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "definitions": len(planned_definitions),
        "theorems": len(planned_theorems),
        "definitionCollisions": len(definition_collisions),
        "theoremCollisions": len(theorem_collisions),
        "extensions": len(extension_names),
        "extensionCollisions": len(extension_collision_kinds),
        "platformVersions": sorted(api.versions),
    }, sort_keys=True))
    return 2 if definition_collisions or theorem_collisions or extension_collision_kinds else 0


if __name__ == "__main__":
    raise SystemExit(main())
