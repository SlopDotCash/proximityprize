"""Unit coverage for scripts/dependency_analysis/generate_dependency_graph.py.

Tests import parsing, module-name normalization, graph construction
(internal ArkLib imports only), cycle detection, and the DOT/JSON output
formats.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "dependency_analysis"))

from generate_dependency_graph import (  # noqa: E402
    build_dependency_graph,
    find_cycles,
    generate_dot_graph,
    generate_json_graph,
    normalize_module_name,
    parse_imports,
)


def test_parse_imports(tmp_path: Path) -> None:
    src = tmp_path / "Mod.lean"
    src.write_text(
        "import Mathlib.Data.Nat\n"
        "import ArkLib.Basic\n"
        "-- import ArkLib.Commented\n"
        "theorem t : True := by trivial\n",
        encoding="utf-8",
    )
    imports = parse_imports(str(src))
    assert imports == ["Mathlib.Data.Nat", "ArkLib.Basic"]


def test_parse_imports_missing_file(tmp_path: Path) -> None:
    assert parse_imports(str(tmp_path / "missing.lean")) == []


def test_normalize_module_name(tmp_path: Path) -> None:
    root = tmp_path
    src = root / "Data" / "Nat.lean"
    assert normalize_module_name(str(src), str(root)) == "Data.Nat"


def test_build_dependency_graph_internal_only(tmp_path: Path) -> None:
    a = tmp_path / "A.lean"
    b = tmp_path / "B.lean"
    a.write_text("import ArkLib.B\nimport Mathlib.Data.Nat\n", encoding="utf-8")
    b.write_text("", encoding="utf-8")
    graph = build_dependency_graph(
        [str(a), str(b)], str(tmp_path)
    )
    # A imports ArkLib.B → graph["ArkLib.B"] = ["A"]
    assert graph == {"ArkLib.B": ["A"]}


def test_find_cycles_detects_simple_cycle() -> None:
    graph = {"ArkLib.A": ["ArkLib.B"], "ArkLib.B": ["ArkLib.A"]}
    cycles = find_cycles(graph)
    assert len(cycles) == 1
    assert set(cycles[0]) == {"ArkLib.A", "ArkLib.B"}


def test_find_cycles_no_cycle() -> None:
    graph = {"ArkLib.A": ["ArkLib.B"], "ArkLib.B": []}
    assert find_cycles(graph) == []


def test_generate_dot_graph(tmp_path: Path) -> None:
    out = tmp_path / "graph.dot"
    generate_dot_graph({"ArkLib.B": ["A"]}, str(out))
    text = out.read_text(encoding="utf-8")
    assert text.startswith("digraph ArkLibDependencies")
    assert '"ArkLib.B"' in text
    assert '"ArkLib.B" -> "A"' in text


def test_generate_json_graph(tmp_path: Path) -> None:
    out = tmp_path / "graph.json"
    generate_json_graph({"ArkLib.B": ["A"]}, str(out))
    data = json.loads(out.read_text(encoding="utf-8"))
    assert any(n["id"] == "ArkLib.B" and n["type"] == "internal" for n in data["nodes"])
    assert any(n["id"] == "A" and n["type"] == "external" for n in data["nodes"])
    assert {"source": "ArkLib.B", "target": "A"} in data["edges"]
