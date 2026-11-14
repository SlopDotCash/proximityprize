"""Regression tests for the b = n - 1 zero-membership law probe."""

import subprocess
import sys
import textwrap
import unittest
from pathlib import Path

PROBES = Path(__file__).resolve().parents[1] / "probes"
sys.path.insert(0, str(PROBES))

import probe_t3_ceiling_column_non2power as merged  # noqa: E402
import probe_t3_ceiling_column_zero_law as probe  # noqa: E402


class ZeroLaw(unittest.TestCase):
    def test_law_is_the_mod_four_law_on_two_powers(self):
        for n in (4, 8, 16, 32, 64):
            with self.subTest(n=n):
                self.assertEqual(
                    probe.zero_law(n), tuple(a for a in range(n) if a % 4 in (0, 1)))

    def test_law_off_the_two_power_ladder(self):
        self.assertEqual(probe.zero_law(9), (0, 1, 3, 4, 6, 7))
        self.assertEqual(probe.zero_law(5), (0, 1))
        self.assertEqual(probe.zero_law(6), (0, 1, 3, 4))
        self.assertEqual(probe.zero_law(10), (0, 1, 5, 6))

    def test_collision_test_matches_merged_engine(self):
        for n, p in ((9, 19), (12, 37), (16, 97), (20, 41)):
            with self.subTest(n=n, p=p):
                shapes = merged.Shapes(n, p)
                _, profile = shapes.column(n - 1)
                engine = tuple(a for a in range(n) if profile[a][2])
                self.assertEqual(probe.zero_set(n, p, shapes.generator), engine)

    def test_small_prime_exception_is_detected_not_hidden(self):
        found = probe.zero_set(16, 17, merged.order_element(17, 16))
        law = probe.zero_law(16)
        self.assertLess(set(law), set(found))

    def test_law_is_exact_above_the_norm_bound(self):
        for n in (3, 5, 8, 9, 12):
            with self.subTest(n=n):
                floor = 6 ** probe.totient(n)
                p, k, exponent, witness = probe.proth_prime_above(n, floor)
                self.assertEqual(p, k * 2 ** exponent + 1)
                self.assertGreater(p, floor)
                self.assertEqual((p - 1) % n, 0)
                self.assertEqual(pow(witness, (p - 1) // 2, p), p - 1)
                self.assertEqual(
                    probe.zero_set(n, p, merged.order_element(p, n)), probe.zero_law(n))

    def test_wrong_order_generator_is_rejected(self):
        with self.assertRaises(AssertionError):
            probe.zero_set(16, 97, merged.order_element(97, 8))

    def test_gates_stay_active_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(PROBES)!r})
            import probe_t3_ceiling_column_zero_law as probe
            probe.require(False, "gate fired")
            """
        )
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True, text=True, check=False)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("gate fired", result.stderr)


if __name__ == "__main__":
    unittest.main()
