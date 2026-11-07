#!/usr/bin/env python3
"""Regenerate ArkLib knowledge-base derived files."""

from __future__ import annotations

import argparse

from common import (
    DEFAULT_BIB_PATH,
    DEFAULT_CITATIONS_JSON,
    DEFAULT_DECLARATIONS_JSON,
    DEFAULT_DEDUP_REPORT,
    DEFAULT_LEAN_ROOTS,
    DEFAULT_REFERENCES_JSON,
    REPO_ROOT,
    write_json,
)
from extract_declarations import extract_declarations
from extract_lean_citations import extract_citations
from find_dedup_candidates import build_report
# Missing-paper/metadata scaffolding is delegated to the shared helper so that the
# input and overwrite guards live in one place (`scaffold_paper.write_if_allowed`);
# its default is non-overwriting, matching the previous inline loop here.
from scaffold_paper import scaffold_missing
from sync_from_bib import build_payload


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--no-paper-stubs",
        action="store_true",
        help="Only refresh generated indexes; do not scaffold missing cited paper pages.",
    )
    return parser.parse_args()


def main() -> int:
    """Entry point."""

    args = parse_args()

    references = build_payload(DEFAULT_BIB_PATH)
    write_json(DEFAULT_REFERENCES_JSON, references)

    keys = sorted(references["entries"])
    citations = extract_citations(DEFAULT_LEAN_ROOTS, keys)
    citations["reference_source"] = DEFAULT_REFERENCES_JSON.relative_to(REPO_ROOT).as_posix()
    write_json(DEFAULT_CITATIONS_JSON, citations)

    declarations = extract_declarations(DEFAULT_LEAN_ROOTS)
    write_json(DEFAULT_DECLARATIONS_JSON, declarations)

    DEFAULT_DEDUP_REPORT.parent.mkdir(parents=True, exist_ok=True)
    DEFAULT_DEDUP_REPORT.write_text(build_report(declarations) + "\n", encoding="utf-8")

    print(f"Regenerated {DEFAULT_REFERENCES_JSON.relative_to(REPO_ROOT)}")
    print(f"Regenerated {DEFAULT_CITATIONS_JSON.relative_to(REPO_ROOT)}")
    print(f"Regenerated {DEFAULT_DECLARATIONS_JSON.relative_to(REPO_ROOT)}")
    print(f"Regenerated {DEFAULT_DEDUP_REPORT.relative_to(REPO_ROOT)}")

    if not args.no_paper_stubs:
        cited_keys = sorted(citations["keys"])
        written = scaffold_missing(cited_keys, references["entries"])
        if written:
            for path in written:
                print(f"Scaffolded {path.relative_to(REPO_ROOT)}")
        else:
            print("No missing cited paper pages or source metadata to scaffold.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
