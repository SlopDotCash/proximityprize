"""The published HDd window-fraction table must match the certificate registry.

``docs/kb/deltastar-hdd-cap-design-2026-09-06.md`` prints a four-row table of
Johnson radii, interpolation faces, and window percentages. Those faces are
produced by ``scripts/probes/hdd_certificates.py`` (``n = 2**18``). A row may
call a face tight only when that record is in ``RECORDS``, where the registry
checks infeasibility at ``A - 1``. ``RECORDS_LOOSE`` is feasible and not tight.
Each printed window percentage is the greatest whole percent that does not
exceed ``(face - Johnson) / (capacity - Johnson)`` for the radii in that row.
"""

from __future__ import annotations

import ast
import math
import re
import unittest
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NOTE = ROOT / "docs/kb/deltastar-hdd-cap-design-2026-09-06.md"
REGISTRY = ROOT / "scripts/probes/hdd_certificates.py"
N = 1 << 18

ROW_RE = re.compile(
    r"^\| 1/(?P<rate>\d+) \| (?P<johnson>[0-9.]+) \| "
    r"\*\*(?P<face>[0-9.]+)\*\* \((?P<detail>[^)]*)\) \| "
    r"(?P<capacity>[0-9.]+) \| (?P<percent>\d+) %",
    re.M,
)
POSITIVE_TIGHT_RE = re.compile(r"(?<!not )\btight\b")


def load_registry():
    values = {}
    for stmt in ast.parse(REGISTRY.read_text(encoding="utf-8")).body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name) and target.id in {
                    "NEXP", "RECORDS", "RECORDS_LOOSE",
                }:
                    values[target.id] = ast.literal_eval(stmt.value)
    if values["NEXP"] != 18:
        raise AssertionError(values["NEXP"])
    strict = {}
    loose = {}
    for record in values["RECORDS"]:
        strict.setdefault((record[0], record[1], record[2]), []).append(record)
    for record in values["RECORDS_LOOSE"]:
        loose.setdefault((record[0], record[1], record[2]), []).append(record)
    return strict, loose


def radius(agreement: int) -> Decimal:
    return Decimal(f"{1 - agreement / N:.5f}")


def window_rows():
    text = NOTE.read_text(encoding="utf-8")
    header = "| rate | Johnson | face (best) | capacity | window fraction (lower bound) |"
    start = text.index(header)
    block = text[start:].split("\n\n", 1)[0]
    rows = [match.groupdict() for match in ROW_RE.finditer(block)]
    if len(rows) != 4:
        raise AssertionError(f"expected 4 window rows, found {len(rows)}")
    return text, rows


class PublishedWindowFractionTable(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.strict, cls.loose = load_registry()
        cls.text, cls.rows = window_rows()

    def test_rows_match_the_certificate_registry(self):
        seen = []
        for row in self.rows:
            rate = int(row["rate"])
            detail = row["detail"]
            cited = re.search(r"d=(\d+), m=(\d+)", detail)
            self.assertIsNotNone(cited, detail)
            key = (rate, int(cited.group(1)), int(cited.group(2)))
            strict = self.strict.get(key, [])
            loose = self.loose.get(key, [])
            records = strict + loose
            self.assertTrue(records, key)
            face = Decimal(row["face"])
            matched = [record for record in records if radius(record[5]) == face]
            self.assertEqual(len(matched), 1, (key, face, [record[5] for record in records]))
            record = matched[0]
            claims_tight = POSITIVE_TIGHT_RE.search(detail) is not None
            if record in loose:
                self.assertFalse(claims_tight, detail)
                self.assertIn("not tight", detail)
            if claims_tight:
                self.assertIn(record, strict)
                self.assertNotIn(record, loose)
            johnson = Decimal(f"{1 - math.sqrt(1 / rate):.5f}")
            self.assertEqual(Decimal(row["johnson"]), johnson)
            self.assertEqual(Decimal(row["capacity"]), Decimal(1) - Decimal(1) / Decimal(rate))
            fraction = (face - johnson) / (Decimal(row["capacity"]) - johnson)
            floored = (fraction * 100).to_integral_value(rounding=ROUND_FLOOR)
            self.assertEqual(int(row["percent"]), int(floored), (rate, fraction))
            seen.append(rate)
        self.assertEqual(seen, [2, 4, 8, 16])

    def test_note_does_not_say_the_shares_grow_as_the_rate_falls(self):
        normalized = re.sub(r"\s+", " ", self.text)
        self.assertNotIn("grow as the rate falls", normalized)
        self.assertIn("rate-1/4 share is smaller than the rate-1/2 share", normalized)

    def test_loose_rate_sixteenth_certificate_is_not_tight(self):
        import sys

        sys.path.insert(0, str(ROOT / "scripts/probes"))
        from hdspec_search import trunc_wedge, verify_exact_int

        record = self.loose[(16, 32, 256)][0]
        rate, degree, multiplicity, smax, jcap, agreement = record
        omega = trunc_wedge(degree, smax, jcap)
        code_length = N // rate
        feasible, _, _ = verify_exact_int(
            degree, N, code_length, multiplicity, omega, agreement)
        below, _, _ = verify_exact_int(
            degree, N, code_length, multiplicity, omega, agreement - 1)
        self.assertTrue(feasible)
        self.assertTrue(below)


if __name__ == "__main__":
    unittest.main()
