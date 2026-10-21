#!/usr/bin/env python3
"""Conservative source-drift gate for the independently stated main theorem.

Compare the 15 shared definitions, and freeze the small public entry-point
interfaces after erasing their proof bodies. Comments and layout whitespace do
not matter. Unexpected declarations or a changed source layout fail closed.

This is NOT a Lean parser or a semantic proof checker. In particular, matching
source interfaces cannot certify elaboration, imported declarations, proof
dependencies, or the meaning of notation. Comparator is the semantic authority;
the Lean build, axiom audit, and independent kernels remain required gates.
The quotient proof itself is checked by those gates, not by a Python search for
the name of a positivity lemma.
"""

from __future__ import annotations

import re
from pathlib import Path

from check_sources import code_only

ROOT = Path(__file__).resolve().parent.parent
DEFINITIONS = (
    "RN", "L2", "L2v", "Amb", "IsAdmissible", "IsDomain", "testGraph", "H",
    "qf", "l2", "rayleigh", "eigenvalue", "besselJ", "besselZero", "CN",
)

# A token comparison preserves identifier boundaries (unlike deleting every
# whitespace character). This only needs the syntax used by these fixed small
# interfaces; it does not purport to implement Lean's extensible lexer.
TOKEN = re.compile(r"\w+(?:'\w*)*|[^\w\s]")


def canonical(code: str) -> tuple[str, ...]:
    return tuple(TOKEN.findall(code))


def declaration(code: str, kind: str, name: str) -> tuple[int, int]:
    """Locate one declaration in the repository's existing column-zero layout.

    Reject ambiguity or unsupported layout instead of guessing at Lean syntax.
    The returned range ends at the next nonblank column-zero command.
    """
    lines = code.splitlines(keepends=True)
    offsets: list[int] = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)
    matches = [
        i for i, line in enumerate(lines)
        if line.split()[:2] == [kind, name] and line[0] not in " \t"
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one column-zero {kind} {name}")
    first = matches[0]
    last = next(
        (i for i in range(first + 1, len(lines))
         if lines[i].strip() and lines[i][0] not in " \t"),
        len(lines),
    )
    return offsets[first], offsets[last] if last < len(lines) else len(code)


def definition(code: str, name: str) -> tuple[int, int]:
    return declaration(code, "abbrev" if name in DEFINITIONS[:4] else "def", name)


def interface(code: str, names: tuple[str, ...], *, erase_definitions: bool = False) -> str:
    """Keep declaration headers and surrounding commands; erase only proofs."""
    replacements: list[tuple[int, int, str]] = []
    for name in names:
        start, end = declaration(code, "theorem", name)
        assignment = code.find(":=", start, end)
        if assignment < 0:
            raise ValueError(f"{name}: missing theorem assignment")
        if not code[assignment + 2:end].strip():
            raise ValueError(f"{name}: missing proof body")
        replacements.append((assignment, end, ":= PROOF\n\n"))
    if erase_definitions:
        for name in DEFINITIONS:
            start, end = definition(code, name)
            replacements.append((start, end, f"DEFINITION {name}\n\n"))
    for start, end, replacement in sorted(replacements, reverse=True):
        code = code[:start] + replacement + code[end:]
    return code


CHALLENGE_INTERFACE = """
module
public import Mathlib
@[expose] public section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
noncomputable section
namespace FourthRatio
DEFINITION RN
DEFINITION L2
DEFINITION L2v
DEFINITION Amb
variable {N : ℕ}
DEFINITION IsAdmissible
DEFINITION IsDomain
DEFINITION testGraph
DEFINITION H
DEFINITION qf
DEFINITION l2
DEFINITION rayleigh
DEFINITION eigenvalue
DEFINITION besselJ
DEFINITION besselZero
DEFINITION CN
theorem fourth_consecutive_ratio (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 := PROOF
theorem fourth_consecutive_ratio_div (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := PROOF
end FourthRatio
end
"""

ENTRY_PREAMBLE = """
module
public import RequestProject.RatioStatement
@[expose] public section
noncomputable section
namespace FourthRatio
"""

SOLUTION_INTERFACE = ENTRY_PREAMBLE + """
theorem fourth_consecutive_ratio (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 := PROOF
end FourthRatio
end
"""

QUOTIENT_INTERFACE = ENTRY_PREAMBLE.replace("RequestProject.RatioStatement", "RequestProject.Unconditional") + """
theorem fourth_consecutive_ratio_div_of_ppw (N : ℕ) (hppw : PPWInequality N)
    (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := PROOF
theorem fourth_consecutive_ratio_div (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := PROOF
end FourthRatio
end
"""


def check_statement(sources: dict[str, str]) -> list[str]:
    """Return actionable failures; accepts in-memory sources for negative checks."""
    failures: list[str] = []
    try:
        clean = {name: code_only(text) for name, text in sources.items()}
        challenge = clean["Challenge.lean"]
        definitions = clean["RequestProject/Defs.lean"]
        for name in DEFINITIONS:
            left_start, left_end = definition(challenge, name)
            right_start, right_end = definition(definitions, name)
            if canonical(challenge[left_start:left_end]) != canonical(definitions[right_start:right_end]):
                failures.append(f"{name}: Challenge.lean and RequestProject/Defs.lean differ")
        checks = (
            ("Challenge.lean", ("fourth_consecutive_ratio", "fourth_consecutive_ratio_div"),
             CHALLENGE_INTERFACE, True),
            ("Solution.lean", ("fourth_consecutive_ratio",), SOLUTION_INTERFACE, False),
            ("RequestProject/RatioStatement.lean",
             ("fourth_consecutive_ratio_div_of_ppw", "fourth_consecutive_ratio_div"),
             QUOTIENT_INTERFACE, False),
        )
        for path, names, expected, erase_defs in checks:
            actual = interface(clean[path], names, erase_definitions=erase_defs)
            if canonical(actual) != canonical(expected):
                failures.append(f"{path}: public source interface changed; review the source and Comparator configuration")
    except (KeyError, ValueError) as error:
        failures.append(str(error))
    return failures


def main() -> int:
    paths = ("Challenge.lean", "RequestProject/Defs.lean", "Solution.lean", "RequestProject/RatioStatement.lean")
    try:
        sources = {path: (ROOT / path).read_text(encoding="utf-8-sig") for path in paths}
        failures = check_statement(sources)
    except (OSError, UnicodeError) as error:
        failures = [str(error)]
    for failure in failures:
        print(failure)
    if failures:
        print("FAIL: statement source-drift gate")
    else:
        print("PASS: 15 shared definitions and fixed public source interfaces")
    print("Comparator remains the semantic authority; Lean, axiom, and kernel checks are required.")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
