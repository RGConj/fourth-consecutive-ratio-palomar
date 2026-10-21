#!/usr/bin/env python3
"""Validate release metadata, dependency pins and Comparator configuration."""
from __future__ import annotations

import argparse
import json
import re
import tomllib
import urllib.request
from pathlib import Path

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    "99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json"
)
SHA = re.compile(r"[0-9a-f]{40}\Z")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PALOMAR_SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--schema", type=Path, help="use a downloaded copy of the pinned v0.4 schema")
    args = parser.parse_args()
    if args.schema:
        schema = json.loads(args.schema.read_text(encoding="utf-8"))
    else:
        with urllib.request.urlopen(SCHEMA_URL, timeout=60) as response:
            schema = json.load(response)
    metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    jsonschema.Draft202012Validator(schema).validate(metadata)
    require(metadata["version"] == "v0.4", "metadata must use v0.4")
    require(metadata["status"]["sorry_count"] == 0, "production proofs must be complete")
    require(metadata["status"]["sorry_in_definitions"] == 0, "definitions must be complete")
    require(set(metadata["status"]["axioms"]) == ALLOWED_AXIOMS, "unexpected metadata axioms")
    # The upstream schema allows free-form source types; Palomar's submission
    # standard specifies a smaller vocabulary (CONTRIBUTING.md, section 3.2).
    for source in metadata["sources"]:
        require("type" not in source or source["type"] in PALOMAR_SOURCE_TYPES,
                "source type is outside Palomar's documented vocabulary")

    config = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    require(manifest["name"] == config["name"], "lakefile/manifest package name mismatch")
    packages = {package["name"]: package for package in manifest["packages"]}
    for package in packages.values():
        require(package["type"] == "git", "non-Git dependency")
        require(SHA.fullmatch(package["rev"]) is not None, "dependency revision is not a full SHA")
        require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", package["url"]) is not None,
                "dependency URL must be public HTTPS GitHub without credentials")
    for dependency in config.get("require", []):
        require(SHA.fullmatch(dependency["rev"]) is not None, "lakefile dependency must use a full SHA")
        require(dependency["rev"] == packages[dependency["name"]]["rev"], "lakefile/manifest revision mismatch")
    mathlib_toolchain = ROOT / ".lake/packages/mathlib/lean-toolchain"
    require(mathlib_toolchain.is_file(), "fetch the pinned dependencies before running this check")
    require((ROOT / "lean-toolchain").read_text().strip() == mathlib_toolchain.read_text().strip(),
            "project and pinned Mathlib toolchains differ")

    for name in ("comparator.json", "comparator-conditional.json"):
        comparator = json.loads((ROOT / name).read_text(encoding="utf-8"))
        allowed = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms", "definition_names", "enable_nanoda"}
        require(not (set(comparator) - allowed), f"{name}: unsupported submitter fields")
        require(set(comparator["permitted_axioms"]) == ALLOWED_AXIOMS, f"{name}: nonstandard axioms")
        for field in ("challenge_module", "solution_module"):
            require((ROOT / (comparator[field].replace(".", "/") + ".lean")).is_file(), f"{name}: missing module")
    require((ROOT / "LICENSE").is_file(), "root LICENSE is missing")
    print("PASS: v0.4 metadata, exact dependency pins, toolchain, and Comparator configuration")


if __name__ == "__main__":
    main()
