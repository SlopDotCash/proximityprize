"""Regression coverage for the Pocklington contract and its JSON CLI inputs."""
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import verify_g139_n2e30_arithmetic_contract as contract


class ArithmeticContractPrimality(unittest.TestCase):
    def test_seven_base_composite_is_rejected(self):
        composite = 10670053 * 32010157
        self.assertEqual(composite, 341550071728321)
        self.assertFalse(contract.is_prime_u64(composite))

    def test_small_values_match_trial_division(self):
        for n in range(1000):
            expected = n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))
            self.assertEqual(contract.is_prime_u64(n), expected, n)

    def test_out_of_range_is_not_certified(self):
        with self.assertRaises(ValueError):
            contract.is_prime_u64(1 << 64)

    def test_complete_arithmetic_contract(self):
        self.assertEqual(contract.verify_arithmetic(), (True, True, True))


class ArithmeticContractJsonCLI(unittest.TestCase):
    """Use synthetic JSON documents, not retained release artifacts."""

    @staticmethod
    def result_record():
        return {
            "n": contract.N,
            "p": contract.P,
            "q": contract.Q,
            "generator": contract.G,
            "domain_size": contract.DOMAIN_SIZE,
            "merged_count": contract.DOMAIN_SIZE,
            "collision_count": 0,
            "injective": True,
            "phi_image_sha256": contract.PHI_IMAGE_SHA256,
            "sorted_record_stream_sha256": contract.SORTED_RECORD_STREAM_SHA256,
        }

    @classmethod
    def independent_record(cls):
        result = cls.result_record()
        summary = {key: result[key] for key in (
            "merged_count", "collision_count", "injective", "phi_image_sha256",
            "sorted_record_stream_sha256",
        )}
        summary["first_collision"] = None
        return {
            "status": "verified",
            "mismatches": {},
            **{key: result[key] for key in ("n", "p", "q", "generator", "domain_size")},
            "chunk_records_sum": contract.DOMAIN_SIZE,
            "recomputed": summary,
            "expected": dict(summary),
        }

    @staticmethod
    def numeric_locations(flag, record):
        for key in ("n", "p", "q", "generator", "domain_size"):
            yield record, key
        if flag == "--result-json":
            for key in ("merged_count", "collision_count"):
                yield record, key
        else:
            yield record, "chunk_records_sum"
            for section in ("recomputed", "expected"):
                for key in ("merged_count", "collision_count"):
                    yield record[section], key

    @staticmethod
    def run_cli(flag, record):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "synthetic-certificate.json"
            contents = record if isinstance(record, str) else json.dumps(record)
            path.write_text(contents, encoding="utf-8")
            return subprocess.run(
                [sys.executable, "-X", "utf8", "-B", contract.__file__, flag, str(path)],
                capture_output=True, text=True, encoding="utf-8", timeout=10,
            )

    def assert_accepted(self, flag, record):
        completed = self.run_cli(flag, record)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        result = json.loads(completed.stdout)
        checked = ("result_json_checked" if flag == "--result-json"
                   else "independent_verify_json_checked")
        self.assertIs(result[checked], True)
        self.assertIs(result["p_prime_pocklington"], True)
        self.assertIs(result["exact_order_n"], True)

    def test_integer_and_decimal_string_records(self):
        for flag, factory in (("--result-json", self.result_record),
                              ("--verify-json", self.independent_record)):
            for converter in (int, str):
                with self.subTest(flag=flag, converter=converter.__name__):
                    record = factory()
                    for section, key in self.numeric_locations(flag, record):
                        section[key] = converter(section[key])
                    self.assert_accepted(flag, record)

    def test_exact_integral_floats_remain_supported(self):
        for flag, factory in (("--result-json", self.result_record),
                              ("--verify-json", self.independent_record)):
            with self.subTest(flag=flag):
                record = factory()
                for section, key in self.numeric_locations(flag, record):
                    # Large prime/generator values are not exactly representable as floats.
                    if key not in ("p", "q", "generator"):
                        section[key] = float(section[key])
                self.assert_accepted(flag, record)

    def test_fractional_fields_are_rejected_without_verified_output(self):
        cases = (
            ("--result-json", "n", contract.N + 0.5),
            ("--result-json", "domain_size", contract.DOMAIN_SIZE + 0.5),
            ("--result-json", "merged_count", contract.DOMAIN_SIZE + 0.5),
            ("--result-json", "collision_count", 0.5),
            ("--result-json", "collision_count", -0.5),
            ("--verify-json", "n", contract.N + 0.5),
            ("--verify-json", "domain_size", contract.DOMAIN_SIZE + 0.5),
            ("--verify-json", "chunk_records_sum", contract.DOMAIN_SIZE + 0.5),
            ("--verify-json", "merged_count", contract.DOMAIN_SIZE + 0.5),
            ("--verify-json", "collision_count", 0.5),
            ("--verify-json", "collision_count", -0.5),
        )
        for flag, key, value in cases:
            with self.subTest(flag=flag, key=key, value=value):
                record = (self.result_record() if flag == "--result-json"
                          else self.independent_record())
                if flag == "--verify-json" and key in ("merged_count", "collision_count"):
                    record["recomputed"][key] = record["expected"][key] = value
                else:
                    record[key] = value
                completed = self.run_cli(flag, record)
                self.assertNotEqual(completed.returncode, 0)
                self.assertEqual(completed.stdout, "")

    def test_boolean_collision_counts_are_rejected(self):
        cases = (
            ("--result-json", (None,)),
            ("--verify-json", ("recomputed",)),
            ("--verify-json", ("expected",)),
            ("--verify-json", ("recomputed", "expected")),
        )
        for flag, sections in cases:
            with self.subTest(flag=flag, sections=sections):
                record = (self.result_record() if flag == "--result-json"
                          else self.independent_record())
                for section in sections:
                    (record if section is None else record[section])["collision_count"] = False
                completed = self.run_cli(flag, record)
                self.assertNotEqual(completed.returncode, 0)
                self.assertEqual(completed.stdout, "")


    def test_raw_fractional_numbers_cannot_round_to_valid_integers(self):
        cases = (
            ("n", "1073741824.00000000000001"),
            ("collision_count", "1e-400"),
            ("collision_count", "-1e-400"),
        )
        for flag, factory in (("--result-json", self.result_record),
                              ("--verify-json", self.independent_record)):
            for key, raw_number in cases:
                with self.subTest(flag=flag, key=key, raw_number=raw_number):
                    record = factory()
                    section = record if key in record else record["recomputed"]
                    original = f'"{key}": {section[key]}'
                    contents = json.dumps(record)
                    self.assertIn(original, contents)
                    # Replace both summary copies without first parsing this decimal as float.
                    contents = contents.replace(original, f'"{key}": {raw_number}')
                    completed = self.run_cli(flag, contents)
                    self.assertNotEqual(completed.returncode, 0)
                    self.assertEqual(completed.stdout, "")


if __name__ == "__main__":
    unittest.main()
