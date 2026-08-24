"""Unit coverage for scripts/kb/extract_lean_citations.py.

Tests the pure helpers: citation-pattern construction (longest-key-first so
prefix collisions resolve correctly) and reference-key loading with the
references.json -> references.bib fallback chain.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

from extract_lean_citations import build_pattern, load_reference_keys  # noqa: E402


def test_build_pattern_matches_known_keys() -> None:
    pattern = build_pattern(["key_a", "key_b"])
    assert pattern.search("[key_a]").group(1) == "key_a"
    assert pattern.search("[key_b]").group(1) == "key_b"
    assert pattern.search("[unknown]") is None


def test_build_pattern_longest_key_wins_on_prefix() -> None:
    # "abc" is a prefix of "abcdef"; the longest key must match first so a
    # citation to the longer key is not captured as the shorter one.
    pattern = build_pattern(["abc", "abcdef"])
    assert pattern.search("[abcdef]").group(1) == "abcdef"
    assert pattern.search("[abc]").group(1) == "abc"


def test_build_pattern_escapes_regex_specials() -> None:
    pattern = build_pattern(["a.b", "c(d)"])
    assert pattern.search("[a.b]").group(1) == "a.b"
    assert pattern.search("[c(d)]").group(1) == "c(d)"


def test_load_reference_keys_from_json(tmp_path: Path) -> None:
    refs = tmp_path / "references.json"
    refs.write_text(
        json.dumps({"entries": {"beta": {}, "alpha": {}}}),
        encoding="utf-8",
    )
    bib = tmp_path / "references.bib"
    bib.write_text("@article{unused, title={x}}", encoding="utf-8")
    keys = load_reference_keys(refs, bib)
    assert keys == ["alpha", "beta"]


def test_load_reference_keys_falls_back_to_bib(tmp_path: Path) -> None:
    bib = tmp_path / "references.bib"
    bib.write_text(
        "@article{zeta, title={a}}\n@book{gamma, title={b}}",
        encoding="utf-8",
    )
    keys = load_reference_keys(tmp_path / "missing.json", bib)
    assert keys == ["gamma", "zeta"]


def test_load_reference_keys_empty_bib(tmp_path: Path) -> None:
    bib = tmp_path / "references.bib"
    bib.write_text("", encoding="utf-8")
    keys = load_reference_keys(tmp_path / "missing.json", bib)
    assert keys == []


def test_extract_citations_scans_lean_files(tmp_path: Path) -> None:
    from extract_lean_citations import extract_citations

    lean_dir = tmp_path / "lean"
    (lean_dir / "sub").mkdir(parents=True)
    (lean_dir / "a.lean").write_text(
        "import Mathlib\n-- [key_a] and [key_b]\n",
        encoding="utf-8",
    )
    (lean_dir / "sub" / "b.lean").write_text(
        "theorem t : True := by trivial\n-- [key_a]\n",
        encoding="utf-8",
    )
    result = extract_citations(lean_dir, ["key_a", "key_b", "key_c"])
    files = result["files"]
    keys = result["keys"]
    # Keys are relative to lean_root.parents[0] (i.e. the tmp root).
    a_rel = next(k for k in files if k.endswith("a.lean"))
    b_rel = next(k for k in files if k.endswith("sub/b.lean"))
    assert set(files[a_rel]) == {"key_a", "key_b"}
    assert set(files[b_rel]) == {"key_a"}
    assert "key_a" in keys
    assert "key_c" not in keys  # unused keys are pruned
    assert result["counts"]["total_citation_edges"] == 3
