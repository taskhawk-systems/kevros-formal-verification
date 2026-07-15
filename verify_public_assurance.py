#!/usr/bin/env python3
"""Verify the public Lean assurance capsule without writing evidence files."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "KevrosCorrect.lean"
MANIFEST = ROOT / "kevros-verification-manifest.json"
ALLOWLIST = ROOT / "PUBLIC_REPO_ALLOWLIST.txt"
EXPECTED_LEAN_VERSION = "4.15.0"
EXPECTED_THEOREMS = 20
ALLOWED_FOUNDATIONS = {"propext", "Quot.sound"}


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )


def strip_lean_comments(text: str) -> str:
    """Remove nested block comments and line comments from Lean source."""

    output: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                break
            output.append("\n")
            i = newline + 1
            continue
        output.append(text[i])
        i += 1
    if depth:
        fail("unclosed Lean block comment")
    return "".join(output)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_allowlist() -> None:
    allowed = {
        line.strip()
        for line in ALLOWLIST.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }
    result = run("git", "ls-files")
    if result.returncode == 0:
        tracked = {line for line in result.stdout.splitlines() if line}
    else:
        ignored_parts = {".git", ".lake", "__pycache__"}
        ignored_files = {"lake-manifest.json"}
        tracked = {
            path.relative_to(ROOT).as_posix()
            for path in ROOT.rglob("*")
            if path.is_file()
            and not ignored_parts.intersection(path.relative_to(ROOT).parts)
            and path.name not in ignored_files
        }
    unexpected = sorted(tracked - allowed)
    missing = sorted(allowed - tracked)
    if unexpected:
        fail(f"tracked files are not allowlisted: {unexpected}")
    if missing:
        fail(f"allowlisted files are not tracked: {missing}")


def verify_source() -> tuple[int, str]:
    source_text = SOURCE.read_text(encoding="utf-8")
    code = strip_lean_comments(source_text)
    theorem_count = len(re.findall(r"(?m)^\s*(?:theorem|lemma)\s+", code))
    if theorem_count != EXPECTED_THEOREMS:
        fail(f"expected {EXPECTED_THEOREMS} theorem declarations, found {theorem_count}")

    forbidden = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "axiom": r"(?m)^\s*axiom\s+",
        "unsafe": r"(?m)^\s*unsafe\s+",
    }
    for name, pattern in forbidden.items():
        if re.search(pattern, code):
            fail(f"forbidden Lean declaration or term found: {name}")
    return theorem_count, sha256(SOURCE)


def verify_build() -> str:
    version = run("lean", "--version")
    if version.returncode != 0:
        fail(f"Lean is unavailable:\n{version.stdout}")
    match = re.search(r"version\s+([0-9]+\.[0-9]+\.[0-9]+)", version.stdout)
    if not match or match.group(1) != EXPECTED_LEAN_VERSION:
        fail(f"expected Lean {EXPECTED_LEAN_VERSION}, got: {version.stdout.strip()}")

    build = run("lake", "build")
    if build.returncode != 0:
        fail(f"lake build failed:\n{build.stdout}")

    audit = run("lake", "env", "lean", "AxiomAudit.lean")
    if audit.returncode != 0:
        fail(f"axiom audit failed:\n{audit.stdout}")
    foundations = set(re.findall(r"\b(?:propext|Quot\.sound)\b", audit.stdout))
    reported_lists = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit.stdout)
    for reported in reported_lists:
        names = {item.strip() for item in reported.split(",") if item.strip()}
        if not names <= ALLOWED_FOUNDATIONS:
            fail(f"unexpected theorem foundation: {sorted(names - ALLOWED_FOUNDATIONS)}")
    if foundations - ALLOWED_FOUNDATIONS:
        fail(f"unexpected theorem foundation: {sorted(foundations - ALLOWED_FOUNDATIONS)}")
    return version.stdout.strip()


def verify_manifest(source_digest: str) -> None:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("artifact") != "Kevros public Lean assurance capsule":
        fail("manifest artifact identifier is invalid")
    proof = data.get("public_proof", {})
    if proof.get("source_sha256") != source_digest:
        fail("manifest source digest does not match KevrosCorrect.lean")
    if proof.get("theorem_declarations") != EXPECTED_THEOREMS:
        fail("manifest theorem count is invalid")


def main() -> int:
    verify_allowlist()
    theorem_count, source_digest = verify_source()
    lean_version = verify_build()
    verify_manifest(source_digest)
    print(
        json.dumps(
            {
                "status": "PASS",
                "scope": "public abstract Lean proof",
                "lean": lean_version,
                "theorem_declarations": theorem_count,
                "sorry": 0,
                "admit": 0,
                "project_defined_axiom": 0,
                "unsafe": 0,
                "source_sha256": source_digest,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
