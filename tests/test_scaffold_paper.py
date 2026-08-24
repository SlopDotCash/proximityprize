"""Unit coverage for scripts/kb/scaffold_paper.py.

Tests YAML quoting, entry loading with the references.json -> bib fallback,
and the paper/metadata template builders (frontmatter fields, canonical URL
line presence/absence, source paths).
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

from scaffold_paper import (  # noqa: E402
    build_metadata_template,
    build_paper_template,
    load_entries,
    yaml_quote,
)


def test_yaml_quote_uses_json_strings() -> None:
    assert yaml_quote("simple") == '"simple"'
    assert yaml_quote('has "quotes"') == '"has \\"quotes\\""'
    assert yaml_quote("") == '""'


def test_load_entries_from_json(tmp_path: Path) -> None:
    refs = tmp_path / "references.json"
    refs.write_text(
        json.dumps({"entries": {"a": {"title": "A"}, "b": {"title": "B"}}}),
        encoding="utf-8",
    )
    entries = load_entries(refs, tmp_path / "missing.bib")
    assert set(entries.keys()) == {"a", "b"}
    assert entries["a"]["title"] == "A"


def test_load_entries_falls_back_to_bib(tmp_path: Path) -> None:
    bib = tmp_path / "refs.bib"
    bib.write_text("@article{k, title={T}, author={X, Y}}", encoding="utf-8")
    entries = load_entries(tmp_path / "missing.json", bib)
    assert set(entries.keys()) == {"k"}
    assert entries["k"]["title"] == "T"


def test_build_paper_template_basic() -> None:
    text = build_paper_template("keyA", {"title": "A Title", "year": "2020"})
    assert "bibkey: keyA" in text
    assert "title: \"A Title\"" in text
    assert "year: \"2020\"" in text
    assert "kind: paper" in text
    assert "status: stub" in text
    assert "# keyA" in text


def test_build_paper_template_url_line_optional() -> None:
    with_url = build_paper_template("k1", {"title": "T", "url": "https://x"})
    assert "canonical_url: https://x" in with_url

    no_url = build_paper_template("k2", {"title": "T"})
    assert "canonical_url:" not in no_url


def test_build_metadata_template() -> None:
    text = build_metadata_template("keyA", {"title": "A", "url": "https://x"})
    assert "bibkey: keyA" in text
    assert "source_kind: bibliography-only" in text
    assert "canonical_url: https://x" in text
    assert "committed_artifacts: []" in text

    no_url = build_metadata_template("keyB", {"title": "B"})
    assert "canonical_url:" not in no_url
