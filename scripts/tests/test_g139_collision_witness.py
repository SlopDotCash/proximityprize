# Copyright (c) 2026 luke303081209-cloud.
# Released under MIT and Apache-2.0; see LICENSE-MIT and LICENSE.
"""Collision certificates must contradict injectivity, not just repeat an input."""

import json
from decimal import Decimal
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "scripts" / "probes"
VERIFIER = PROBES / "verify_g139_phi_collision_witness.py"
sys.path.insert(0, str(PROBES))

import verify_g139_n2e30_arithmetic_contract as contract
import verify_g139_phi_collision_witness as verifier


class G139CollisionWitness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.retained = json.loads(
            (PROBES / "_out_g139_phi_collision_witnesses.json").read_text()
        )
        cls.expected = json.loads(
            (PROBES / "_out_g139_phi_collision_witness_verification.json").read_text()
        )

    def cli(self, *args, optimized=False):
        return subprocess.run(
            [sys.executable, *(["-O"] if optimized else []), str(VERIFIER), *args],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )

    def test_retained_collision_evidence_is_preserved(self):
        self.assertEqual(len(self.retained), 6)
        result = self.cli("--witness-json", str(PROBES / "_out_g139_phi_collision_witnesses.json"))
        self.assertEqual(result.returncode, 0, result.stderr)
        for actual, expected in zip(json.loads(result.stdout), self.expected, strict=True):
            self.assertEqual({key: actual[key] for key in expected}, expected)
            self.assertNotEqual(actual["r"], actual["s"])
            self.assertTrue(actual["verified"])

    def test_exhaustive_small_field_matches_noninjectivity_definition(self):
        n, p, g = 16, 97, 8
        self.assertEqual(pow(g, n, p), 1)
        self.assertEqual(pow(g, n // 2, p), p - 1)
        image = {r: pow((pow(g, r, p) - 1) % p, n, p) for r in range(1, n // 2 + 1)}
        for r in image:
            for s in image:
                with self.subTest(r=r, s=s):
                    result = verifier.verify_witness(
                        label="exhaustive", n=n, p=p, generator=g,
                        r=r, s=s, u=None, u_exponent=None,
                    )
                    self.assertEqual(result.verified, r != s and image[r] == image[s])

    def test_production_self_pairs_are_not_collision_certificates(self):
        for r in (1, contract.N // 2):
            for u, exponent in ((1, None), (None, 0), (None, None)):
                with self.subTest(r=r, u=u, exponent=exponent):
                    result = verifier.verify_witness(
                        label="production-self-pair", n=contract.N, p=contract.P,
                        generator=contract.G, r=r, s=r, u=u, u_exponent=exponent,
                    )
                    self.assertTrue(result.exact_order_power2)
                    self.assertTrue(result.phi_collision_holds)
                    self.assertTrue(result.normalized_g139_lawful)
                    self.assertFalse(result.verified)

    def test_custom_cli_rejects_production_self_pair(self):
        for optimized in (False, True):
            for multiplier in (("--u", "1"), ("--u-exp", "0")):
                with self.subTest(optimized=optimized, multiplier=multiplier):
                    result = self.cli(
                        "--n", str(contract.N), "--p", str(contract.P),
                        "--g", str(contract.G), "--r", "1", "--s", "1",
                        *multiplier, optimized=optimized,
                    )
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")

    def test_json_cli_rejects_self_pair_and_mixed_batch(self):
        self_pair = dict(
            label="production-self-pair", n=contract.N, p=contract.P,
            generator=contract.G, r=1, s=1, u=1,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "witness.json"
            for records in (self_pair, [self.retained[0], self_pair]):
                path.write_text(json.dumps(records))
                for optimized in (False, True):
                    with self.subTest(batch=isinstance(records, list), optimized=optimized):
                        result = self.cli("--witness-json", str(path), optimized=optimized)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(result.stdout, "")

    def test_tampered_real_collision_is_rejected_with_optimization(self):
        record = dict(self.retained[0], u=self.retained[0]["u"] + 1)
        self.assertFalse(verifier.verify_from_record(record).verified)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "witness.json"
            path.write_text(json.dumps(record))
            for optimized in (False, True):
                with self.subTest(optimized=optimized):
                    result = self.cli("--witness-json", str(path), optimized=optimized)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")

    def test_fractional_certificate_fields_are_not_truncated(self):
        fields = ("n", "p", "generator", "r", "s", "u", "u_exponent")
        for field in fields:
            record = dict(self.retained[0])
            record[field] = Decimal(record[field]) + Decimal("0.5")
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    verifier.verify_from_record(record)

    def test_boolean_certificate_fields_are_not_integers(self):
        for field in ("n", "p", "generator", "r", "s", "u", "u_exponent"):
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    verifier.verify_from_record(dict(self.retained[0], **{field: True}))

    def test_nonfinite_certificate_fields_are_rejected(self):
        for value in (float("nan"), float("inf"), Decimal("NaN"), Decimal("Infinity")):
            with self.subTest(value=str(value)):
                with self.assertRaises(ValueError):
                    verifier.verify_from_record(dict(self.retained[0], r=value))

    def test_json_cli_rejects_fractional_and_rounded_collision_inputs(self):
        record = self.retained[0]
        original = f'"r": {record["r"]}'
        # The second fraction rounds to the retained integer under json's
        # default float decoder, so checking is_integer() alone is insufficient.
        cases = (
            (original, f'"r": {record["r"]}.5'),
            (original, f'"r": {record["r"]}.00000000000000000001'),
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "witness.json"
            for before, after in cases:
                contents = json.dumps(record)
                self.assertIn(before, contents)
                malformed = contents.replace(before, after)
                for records in (malformed, f'[{json.dumps(record)}, {malformed}]'):
                    path.write_text(records, encoding="utf-8")
                    for optimized in (False, True):
                        with self.subTest(value=after, batch=records.startswith("["),
                                          optimized=optimized):
                            result = self.cli("--witness-json", str(path), optimized=optimized)
                            self.assertNotEqual(result.returncode, 0)
                            self.assertEqual(result.stdout, "")

    def test_exact_numeric_encodings_preserve_collision_witness(self):
        fields = ("n", "p", "generator", "r", "s", "u", "u_exponent")
        for converter in (int, str, float, Decimal):
            record = dict(self.retained[0])
            for field in fields:
                record[field] = converter(record[field])
            with self.subTest(encoding=converter.__name__):
                result = verifier.verify_from_record(record)
                self.assertTrue(result.verified)
                self.assertEqual(result.r, self.retained[0]["r"])


if __name__ == "__main__":
    unittest.main()
