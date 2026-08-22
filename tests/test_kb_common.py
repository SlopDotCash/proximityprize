"""Unit coverage for scripts/kb/common.py and scripts/kb/sync_from_bib.py.

Tests the BibTeX parser (brace-aware, comment/string handling), BibEntry.to_json
normalization (author splitting, venue fallback), and build_payload (sorted
entries, count, source path).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

from common import BibEntry, load_bib_entries  # noqa: E402
from sync_from_bib import build_payload  # noqa: E402


def test_load_bib_entries_basic(tmp_path: Path) -> None:
    bib = tmp_path / "refs.bib"
    bib.write_text(
        '@article{keyA, title={Alpha}, author={Doe, Jane and Smith, Bob}, year={2020}}\n'
        "@book{keyB, title={Beta}, author={Lee, Kim}, year={2019}}\n",
        encoding="utf-8",
    )
    entries = load_bib_entries(bib)
    assert [e.key for e in entries] == ["keyA", "keyB"]
    assert entries[0].entry_type == "article"
    assert entries[0].fields["title"] == "Alpha"


def test_load_bib_entries_brace_nesting(tmp_path: Path) -> None:
    bib = tmp_path / "refs.bib"
    bib.write_text(
        '@article{k, title={Nested {Braces} work}, author={A, B}}\n',
        encoding="utf-8",
    )
    entries = load_bib_entries(bib)
    assert entries[0].fields["title"] == "Nested {Braces} work"


def test_load_bib_entries_ignores_comments(tmp_path: Path) -> None:
    bib = tmp_path / "refs.bib"
    bib.write_text(
        "% this is a comment\n"
        "@article{k, title={Real}, author={A, B}}\n",
        encoding="utf-8",
    )
    entries = load_bib_entries(bib)
    assert len(entries) == 1
    assert entries[0].key == "k"


def test_to_json_splits_authors() -> None:
    entry = BibEntry(
        key="k",
        entry_type="article",
        fields={"author": "Doe, Jane and Smith, Bob", "title": "T"},
    )
    data = entry.to_json()
    assert data["authors"] == ["Doe, Jane", "Smith, Bob"]
    assert data["authors_text"] == "Doe, Jane and Smith, Bob"
    assert data["title"] == "T"
    assert data["year"] == ""


def test_to_json_venue_fallback() -> None:
    journal = BibEntry(
        key="j", entry_type="article", fields={"journal": "JMIR"}
    )
    assert journal.to_json()["venue"] == "JMIR"

    book = BibEntry(
        key="b", entry_type="inproceedings", fields={"booktitle": "ICML"}
    )
    assert book.to_json()["venue"] == "ICML"


def test_build_payload_sorts_and_counts(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr("sync_from_bib.REPO_ROOT", tmp_path)
    bib = tmp_path / "refs.bib"
    bib.write_text(
        '@article{beta, title={B}}\n@article{alpha, title={A}}\n',
        encoding="utf-8",
    )
    payload = build_payload(bib.resolve())
    assert payload["count"] == 2
    assert list(payload["entries"].keys()) == ["alpha", "beta"]
    assert payload["source_bib"] == "refs.bib"
