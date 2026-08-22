"""Unit coverage for scripts/kb/regenerate.py scaffold_missing.

Tests that missing paper pages / source metadata are scaffolded for cited
keys, existing files are never touched, and uncited/missing entries are
skipped.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

import regenerate  # noqa: E402


def _fake_templates(key: str, entry: dict) -> str:
    return f"# {key}\n"


def test_scaffold_missing_writes_both_files(tmp_path: Path, monkeypatch) -> None:
    papers = tmp_path / "papers"
    sources = tmp_path / "sources"
    monkeypatch.setattr(regenerate, "PAPERS_DIR", papers)
    monkeypatch.setattr(regenerate, "SOURCES_DIR", sources)
    monkeypatch.setattr(regenerate, "build_paper_template", _fake_templates)
    monkeypatch.setattr(regenerate, "build_metadata_template", _fake_templates)

    written = regenerate.scaffold_missing(
        ["keyA", "keyB"], {"keyA": {"title": "A"}, "keyB": {"title": "B"}}
    )
    assert len(written) == 4
    assert (papers / "keyA.md").exists()
    assert (sources / "keyA" / "metadata.yml").exists()
    assert (papers / "keyB.md").exists()
    assert (sources / "keyB" / "metadata.yml").exists()


def test_scaffold_missing_never_touches_existing(tmp_path: Path, monkeypatch) -> None:
    papers = tmp_path / "papers"
    sources = tmp_path / "sources"
    (papers).mkdir(parents=True)
    (sources / "keyA").mkdir(parents=True)
    existing_paper = papers / "keyA.md"
    existing_meta = sources / "keyA" / "metadata.yml"
    existing_paper.write_text("keep", encoding="utf-8")
    existing_meta.write_text("keep", encoding="utf-8")

    monkeypatch.setattr(regenerate, "PAPERS_DIR", papers)
    monkeypatch.setattr(regenerate, "SOURCES_DIR", sources)
    monkeypatch.setattr(regenerate, "build_paper_template", _fake_templates)
    monkeypatch.setattr(regenerate, "build_metadata_template", _fake_templates)

    written = regenerate.scaffold_missing(["keyA"], {"keyA": {"title": "A"}})
    assert written == []
    assert existing_paper.read_text(encoding="utf-8") == "keep"
    assert existing_meta.read_text(encoding="utf-8") == "keep"


def test_scaffold_missing_skips_uncited_and_missing_entries(
    tmp_path: Path, monkeypatch
) -> None:
    papers = tmp_path / "papers"
    sources = tmp_path / "sources"
    monkeypatch.setattr(regenerate, "PAPERS_DIR", papers)
    monkeypatch.setattr(regenerate, "SOURCES_DIR", sources)
    monkeypatch.setattr(regenerate, "build_paper_template", _fake_templates)
    monkeypatch.setattr(regenerate, "build_metadata_template", _fake_templates)

    # keyB cited but absent from entries; keyC not cited.
    written = regenerate.scaffold_missing(["keyA", "keyB"], {"keyA": {"title": "A"}})
    assert len(written) == 2  # only keyA scaffolded
    assert (papers / "keyA.md").exists()
    assert not (papers / "keyB.md").exists()
