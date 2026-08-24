"""Unit coverage for scripts/dependency_analysis/generate_top_level_graph.py.

Tests category grouping (ArkLib.<category>.<module>), inter-category edge
construction (skipping same-category and non-ArkLib edges), and DOT output
structure.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "dependency_analysis"))

from generate_top_level_graph import generate_top_level_graph  # noqa: E402


def _write_graph(tmp_path: Path) -> Path:
    data = {
        "nodes": [
            {"id": "ArkLib.Data.Nat", "type": "internal"},
            {"id": "ArkLib.Algebra.Group", "type": "internal"},
            {"id": "Mathlib.Data.Nat", "type": "external"},
        ],
        "edges": [
            {"source": "ArkLib.Data.Nat", "target": "ArkLib.Algebra.Group"},
            {"source": "ArkLib.Data.Nat", "target": "Mathlib.Data.Nat"},
            {"source": "Mathlib.Data.Nat", "target": "ArkLib.Algebra.Group"},
        ],
    }
    src = tmp_path / "graph.json"
    src.write_text(json.dumps(data), encoding="utf-8")
    return src


def test_generate_top_level_graph_categories_and_edges(tmp_path: Path) -> None:
    src = _write_graph(tmp_path)
    out = tmp_path / "top.dot"
    generate_top_level_graph(str(src), str(out))
    text = out.read_text(encoding="utf-8")
    assert text.startswith("digraph ArkLibTopLevel")
    # Category nodes with module counts.
    assert '"Data" [label="Data\\n(1 modules)"' in text
    assert '"Algebra" [label="Algebra\\n(1 modules)"' in text
    # Cross-category edge Data -> Algebra present.
    assert '"Data" -> "Algebra";' in text
    # External-only edges and same-category edges absent.
    assert '"Mathlib"' not in text


def test_generate_top_level_graph_empty(tmp_path: Path) -> None:
    src = tmp_path / "graph.json"
    src.write_text(json.dumps({"nodes": [], "edges": []}), encoding="utf-8")
    out = tmp_path / "top.dot"
    generate_top_level_graph(str(src), str(out))
    text = out.read_text(encoding="utf-8")
    assert text.startswith("digraph ArkLibTopLevel")
    assert '"Data"' not in text
