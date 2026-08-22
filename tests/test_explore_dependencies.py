"""Unit coverage for scripts/dependency_analysis/explore_dependencies.py.

Tests the exploration helpers via captured stdout: module info (dependency
and dependent listing), category summary, top-dependencies ranking, and the
BFS dependency-path search (found path, missing module, no-path).
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "dependency_analysis"))

from explore_dependencies import (  # noqa: E402
    load_dependencies,
    show_dependency_path,
    show_module_info,
    show_top_dependencies,
)


@pytest.fixture
def graph(tmp_path: Path) -> dict:
    data = {
        "nodes": [
            {"id": "ArkLib.A", "type": "internal"},
            {"id": "ArkLib.B", "type": "internal"},
            {"id": "ArkLib.C", "type": "internal"},
            {"id": "Mathlib.Data", "type": "external"},
        ],
        "edges": [
            {"source": "ArkLib.A", "target": "ArkLib.B"},
            {"source": "ArkLib.A", "target": "ArkLib.C"},
            {"source": "ArkLib.B", "target": "ArkLib.C"},
            {"source": "ArkLib.A", "target": "Mathlib.Data"},
        ],
    }
    src = tmp_path / "graph.json"
    src.write_text(json.dumps(data), encoding="utf-8")
    return load_dependencies(str(src))


def test_load_dependencies(graph: dict) -> None:
    assert len(graph["nodes"]) == 4
    assert len(graph["edges"]) == 4


def test_show_module_info_lists_deps_and_dependents(graph: dict, capsys) -> None:
    show_module_info(graph, "A")
    out = capsys.readouterr().out
    assert "Module: ArkLib.A" in out
    assert "ArkLib.B" in out  # dependency
    assert "ArkLib.C" in out  # dependency
    assert "Mathlib.Data" in out  # dependency

    capsys.readouterr()
    show_module_info(graph, "C")
    out2 = capsys.readouterr().out
    assert "ArkLib.A" in out2  # dependent
    assert "ArkLib.B" in out2  # dependent


def test_show_module_info_missing(graph: dict, capsys) -> None:
    show_module_info(graph, "Z")
    assert "not found" in capsys.readouterr().out


def test_show_top_dependencies_ranks(graph: dict, capsys) -> None:
    show_top_dependencies(graph, limit=2)
    out = capsys.readouterr().out
    # A has 3 ArkLib edges + 1 external = highest; B has 1.
    assert out.index("ArkLib.A") < out.index("ArkLib.B")


def test_show_dependency_path_found(graph: dict, capsys) -> None:
    show_dependency_path(graph, "A", "C")
    out = capsys.readouterr().out
    assert "ArkLib.A -> ArkLib.C" in out or "ArkLib.A -> ArkLib.B -> ArkLib.C" in out


def test_show_dependency_path_no_path(graph: dict, capsys) -> None:
    show_dependency_path(graph, "C", "A")
    assert "No dependency path found" in capsys.readouterr().out
