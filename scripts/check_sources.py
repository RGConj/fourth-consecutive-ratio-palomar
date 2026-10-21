#!/usr/bin/env python3
"""Check the release-source allowlist. Kernel axiom auditing is a separate gate."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHALLENGES = {"Challenge.lean": 2, "ChallengeConditional.lean": 1}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern)\b")
RAW_STRING = re.compile(r'r(#+)?"')


def code_only(text: str) -> str:
    """Blank nested comments and strings, preserving source line positions."""
    out = list(text)
    i = 0
    depth = 0
    in_string = False
    raw_hashes: int | None = None
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            ending = '"' + "#" * (raw_hashes or 0)
            if text.startswith(ending, i):
                out[i:i + len(ending)] = " " * len(ending)
                i += len(ending)
                in_string = False
                raw_hashes = None
            elif raw_hashes is None and text[i] == "\\":
                for j in range(i, min(i + 2, len(text))):
                    if text[j] != "\n":
                        out[j] = " "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        elif text[i] == "r" and (m := RAW_STRING.match(text, i)) is not None:
            raw_hashes = len(m.group(1) or "")
            out[i:i + len(m.group())] = " " * len(m.group())
            i += len(m.group())
            in_string = True
        else:
            i += 1
    if depth or in_string:
        raise ValueError("unterminated block comment or string")
    return "".join(out)


def main() -> int:
    files = sorted(ROOT.glob("*.lean"))
    files += sorted((ROOT / "RequestProject").rglob("*.lean"))
    files += sorted((ROOT / "scripts").rglob("*.lean"))
    failures: list[str] = []
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if path.is_symlink() or any(parent.is_symlink() for parent in path.parents if parent != ROOT):
            failures.append(f"{relative}: source symlink is not permitted")
        text = path.read_text(encoding="utf-8-sig")
        try:
            code = code_only(text)
        except ValueError as error:
            failures.append(f"{relative}: {error}")
            continue
        if re.match(r"\s*module\b", code) is None:
            failures.append(f"{relative}: missing module header")
        if len(text.splitlines()) > 10_000:
            failures.append(f"{relative}: exceeds 10,000 lines")
        matches = list(FORBIDDEN.finditer(code))
        if relative in CHALLENGES:
            holes = [m for m in matches if m.group() == "sorry"]
            if len(holes) != CHALLENGES[relative]:
                failures.append(
                    f"{relative}: expected {CHALLENGES[relative]} deliberate Challenge sorry terms"
                )
            matches = [m for m in matches if m.group() != "sorry"]
            if len(text.splitlines()) > 1_000 or len(text.encode("utf-8")) > 100 * 1024:
                failures.append(f"{relative}: exceeds Challenge size limit")
        for match in matches:
            line = code.count("\n", 0, match.start()) + 1
            failures.append(f"{relative}:{line}: forbidden token {match.group()}")
    print(f"Checked {len(files)} Lean files in the documented source allowlist.")
    for failure in failures:
        print(failure)
    print("FAIL" if failures else "PASS")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
