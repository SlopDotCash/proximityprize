"""Unit coverage for scripts/kb/check_generated.py.

Tests the staleness comparators: compare_text (generated text files) and
compare_payload (generated JSON files), including the stale error message
that names the regenerating script.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

import check_generated  # noqa: E402


def test_compare_text_matches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(check_generated, "REPO_ROOT", tmp_path)
    target = tmp_path / "out.txt"
    target.write_text("same", encoding="utf-8")
    assert check_generated.compare_text("gen.py", "same", target) == []


def test_compare_text_stale_reports_regenerator(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(check_generated, "REPO_ROOT", tmp_path)
    target = tmp_path / "out.txt"
    target.write_text("old", encoding="utf-8")
    errors = check_generated.compare_text("gen.py", "new", target)
    assert len(errors) == 1
    assert "out.txt is out of date" in errors[0]
    assert "gen.py" in errors[0]


def test_compare_payload_matches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(check_generated, "REPO_ROOT", tmp_path)
    target = tmp_path / "out.json"
    target.write_text(json.dumps({"a": 1, "b": [1, 2]}), encoding="utf-8")
    assert (
        check_generated.compare_payload(
            "gen.py", {"a": 1, "b": [1, 2]}, target
        )
        == []
    )


def test_compare_payload_stale_reports_regenerator(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(check_generated, "REPO_ROOT", tmp_path)
    target = tmp_path / "out.json"
    target.write_text(json.dumps({"a": 1}), encoding="utf-8")
    errors = check_generated.compare_payload(
        "gen.py", {"a": 2}, target
    )
    assert len(errors) == 1
    assert "out.json is out of date" in errors[0]
    assert "gen.py" in errors[0]


def test_compare_payload_order_insensitive(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(check_generated, "REPO_ROOT", tmp_path)
    target = tmp_path / "out.json"
    target.write_text(json.dumps({"x": 1, "y": 2}), encoding="utf-8")
    # Key order differs in the committed file; JSON equality is dict equality.
    assert (
        check_generated.compare_payload(
            "gen.py", {"y": 2, "x": 1}, target
        )
        == []
    )


def test_load_json_parses(tmp_path: Path) -> None:
    target = tmp_path / "data.json"
    target.write_text('{"k": [1, 2]}', encoding="utf-8")
    assert check_generated.load_json(target) == {"k": [1, 2]}
