"""Unit coverage for scripts/kb/find_dedup_candidates.py.

Tests the pure helpers: doc-word extraction, Jaccard similarity, group
collection, interestingness ranking, and the short-name report rendering
(trivial-name filtering, cross-file requirement, ordering).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

from find_dedup_candidates import (  # noqa: E402
    TRIVIAL_NAMES,
    _doc_words,
    _interestingness,
    _jaccard,
    collect_groups,
    render_short_name_report,
)


def test_doc_words_extracts_lowercased_min_length() -> None:
    words = _doc_words("The quick fox and the lazy DOG run")
    assert "quick" in words
    assert "lazy" in words  # lowercased
    assert "dog" not in words  # len < 4
    assert "the" not in words  # len < 4
    assert "and" not in words


def test_doc_words_empty() -> None:
    assert _doc_words("") == set()
    assert _doc_words("a b c") == set()  # all too short


def test_jaccard_basics() -> None:
    assert _jaccard({"a", "b"}, {"a", "b"}) == 1.0
    assert _jaccard({"a"}, {"a", "b"}) == 0.5
    assert _jaccard({"a"}, {"b"}) == 0.0
    assert _jaccard(set(), {"a"}) == 0.0


def test_collect_groups_buckets_by_short_name() -> None:
    data = {
        "files": {
            "A.lean": {
                "declarations": [
                    {"short_name": "foo", "namespace": "X", "name": "X.foo"},
                    {"short_name": "bar", "namespace": "X", "name": "X.bar"},
                ]
            },
            "B.lean": {
                "declarations": [
                    {"short_name": "foo", "namespace": "Y", "name": "Y.foo"},
                ]
            },
        }
    }
    groups = collect_groups(data)
    assert set(groups.keys()) == {"foo", "bar"}
    assert len(groups["foo"]) == 2
    assert groups["foo"][0]["file"] == "A.lean"


def test_collect_groups_skips_anon() -> None:
    data = {
        "files": {
            "A.lean": {
                "declarations": [
                    {"short_name": "_anon_1", "namespace": "X", "name": "X._anon_1"},
                    {"short_name": "", "namespace": "X", "name": "X.unnamed"},
                ]
            }
        }
    }
    groups = collect_groups(data)
    assert groups == {}


def test_interestingness_weights_files() -> None:
    group_1file = [
        {"file": "A", "namespace": "X"},
        {"file": "A", "namespace": "X"},
    ]
    group_2file = [
        {"file": "A", "namespace": "X"},
        {"file": "B", "namespace": "Y"},
    ]
    assert _interestingness(group_2file) > _interestingness(group_1file)


def test_render_short_name_report_filters_trivial_and_same_file() -> None:
    data = {
        "files": {
            "A.lean": {
                "declarations": [
                    {"short_name": "foo", "namespace": "X", "name": "X.foo",
                     "kind": "def", "line": 10, "doc": "A useful function"},
                    {"short_name": "mk", "namespace": "X", "name": "X.mk",
                     "kind": "def", "line": 20, "doc": "trivial name"},
                ]
            },
            "B.lean": {
                "declarations": [
                    {"short_name": "foo", "namespace": "Y", "name": "Y.foo",
                     "kind": "def", "line": 5, "doc": "Another useful thing"},
                ]
            },
        }
    }
    groups = collect_groups(data)
    lines = render_short_name_report(groups, min_group=2)
    text = "\n".join(lines)
    # foo group (cross-file) present; mk filtered as trivial; same-file-only
    # groups absent.
    assert "foo" in text
    assert "mk" not in text
    assert "A.lean:10" in text
