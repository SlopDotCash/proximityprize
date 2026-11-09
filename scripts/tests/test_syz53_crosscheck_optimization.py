"""The SYZ53 parity cross-check must remain active under Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


class SYZ53CrosscheckOptimization(unittest.TestCase):
    def run_optimized_crosscheck(
        self, bad, inf, wholefield, expected_error, u0=(0, 0, 1, 1), u1=(0, 1, 0, 1)
    ):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(PROBES)!r})
            import probe_syz53_p_scaling as probe

            u0 = {list(u0)!r}
            u1 = {list(u1)!r}
            alpha = [1, 2, 3, 4]
            p = 5
            tensor = probe.build_interp_tensor(alpha, 1, 2, p)
            probe._crosscheck(
                u0, u1, alpha, 1, 2, p, tensor, {bad!r}, {inf!r}, {wholefield!r}
            )
            """
        )
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                if expected_error is None:
                    self.assertEqual(result.returncode, 0, result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(expected_error, result.stderr)

    def test_consistent_result_passes(self):
        self.run_optimized_crosscheck(
            {0, 1, 4}, True, False, None
        )

    def test_non_wholefield_bad_scalar_set_is_checked(self):
        self.run_optimized_crosscheck(
            {0, 1}, True, False, "BADZ MISMATCH p=5"
        )

    def test_wholefield_claim_requires_the_full_finite_field(self):
        self.run_optimized_crosscheck(
            {1, 4}, True, True, "WHOLEFIELD PREMISE FAIL p=5"
        )

    def test_genuine_wholefield_result_passes(self):
        self.run_optimized_crosscheck(
            {2}, True, True, None, u1=(0, 0, 2, 2)
        )

    def test_infinity_candidate_is_checked(self):
        self.run_optimized_crosscheck(
            {2}, False, True, "INF MISMATCH p=5", u1=(0, 0, 2, 2)
        )


if __name__ == "__main__":
    unittest.main()
