"""The beta = 4 ladder certificate re-checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_ztz_beta4_ladder.py"


def run_probe_with(flag, old, new):
    """Run the probe's main() with one source line changed."""
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        assert source.count({old!r}) == 1
        source = source.replace({old!r}, {new!r})
        namespace = {{"__name__": "probe"}}
        exec(compile(source, "probe", "exec"), namespace)
        namespace["main"]()
        print("ALL CHECKS PASSED")
        """
    )
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class ZtzBetaFourLadderOptimization(unittest.TestCase):
    def test_square_witness_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(flag, "        return g\n", "        return 4\n")
                self.assertNotEqual(result.returncode, 0, result.stdout[-500:])
                self.assertIn("g^((p-1)/2) = 1", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_prime_shape_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(
                    flag,
                    "    return lo, hi, chosen\n",
                    "    return lo, hi, [(p + 2, c, e, g) for (p, c, e, g) in chosen]\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout[-500:])
                self.assertIn("p - 1 != 2^e * c", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
