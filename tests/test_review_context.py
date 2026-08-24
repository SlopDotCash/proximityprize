"""Unit coverage for scripts/kb/review_context.py.

Tests CSV item parsing, repo-path normalization, citation-key inference from
Lean files, repo/external ref building, order-preserving dedup, and explicit
key validation against the bibliography.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

import review_context  # noqa: E402


def test_parse_csv_items_flattens_and_strips() -> None:
    assert review_context.parse_csv_items(["a, b", "c"]) == ["a", "b", "c"]
    assert review_context.parse_csv_items(["a,,b"]) == ["a", "b"]
    assert review_context.parse_csv_items([]) == []


def test_infer_keys_from_files() -> None:
    payload = {
        "files": {
            "ArkLib/Data/Nat.lean": ["keyA", "keyB"],
            "ArkLib/Data/Bool.lean": ["keyB"],
        }
    }
    keys = review_context.infer_keys_from_files(
        ["ArkLib/Data/Nat.lean", "ArkLib/Data/Bool.lean"], payload
    )
    assert keys == {"keyA", "keyB"}


def test_infer_keys_from_files_missing_file() -> None:
    payload = {"files": {"ArkLib/Data/Nat.lean": ["keyA"]}}
    keys = review_context.infer_keys_from_files(["ArkLib/Other.lean"], payload)
    assert keys == set()


def test_build_repo_refs_only_existing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(review_context, "REPO_ROOT", tmp_path)
    paper = tmp_path / "docs" / "kb" / "papers"
    meta = tmp_path / "docs" / "kb" / "sources"
    paper.mkdir(parents=True)
    meta.mkdir(parents=True)
    (paper / "keyA.md").write_text("x", encoding="utf-8")
    (meta / "keyA").mkdir()
    (meta / "keyA" / "metadata.yml").write_text("y", encoding="utf-8")

    refs = review_context.build_repo_refs(["keyA", "keyB"])
    assert "docs/kb/papers/keyA.md" in refs
    assert "docs/kb/sources/keyA/metadata.yml" in refs
    assert all("keyB" not in r for r in refs)


def test_build_external_refs() -> None:
    payload = {
        "entries": {
            "keyA": {"url": "https://a"},
            "keyB": {"url": "  "},
            "keyC": {},
        }
    }
    refs = review_context.build_external_refs(["keyA", "keyB", "keyC"], payload)
    assert refs == ["https://a"]


def test_unique_in_order() -> None:
    assert review_context.unique_in_order(["b", "a", "b", "c", "a"]) == ["b", "a", "c"]
    assert review_context.unique_in_order([]) == []


def test_validate_explicit_keys_rejects_unknown(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(review_context, "REPO_ROOT", tmp_path)
    payload = {"entries": {"known": {}}}
    with pytest.raises(SystemExit, match="unknown"):
        review_context.validate_explicit_keys(["known", "unknown"], payload)


def test_validate_explicit_keys_accepts_all_known() -> None:
    payload = {"entries": {"a": {}, "b": {}}}
    # No raise.
    review_context.validate_explicit_keys(["a", "b"], payload)
