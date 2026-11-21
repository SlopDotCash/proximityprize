"""The G95 probe must fail when reported dictionary or exactness claims fail."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_g95_cyclic_dictionary.py"
SMALL_PRIMES = {8: 41, 16: 113, 32: 353, 64: 449}


class G95FailClosedChecks(unittest.TestCase):
    def run_probe(self, optimization, corruption):
        mutation = {
            "periods": '''
module.periods = lambda n, p, G: {b: float(b // (p // n)) for b in range(1, p)}
''',
            "integrality": '''
original = module.N_r
module.N_r = lambda G, p, r: original(G, p, r) + (1 if r == 2 else 0)
''',
        }.get(corruption, "")
        code = f"""
import importlib.util
spec = importlib.util.spec_from_file_location("g95_probe", {str(PROBE)!r})
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.good_prime = lambda n, beta=4.0: {SMALL_PRIMES!r}[n]
{mutation}
module.main()
"""
        return subprocess.run(
            [sys.executable, optimization, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_cells_and_bad_claims(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, corruption=None):
                result = self.run_probe(optimization, None)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertNotIn(": FAIL", result.stdout)
                self.assertIn("two-valued collapse = CONFIRMED", result.stdout)
            for corruption, message in (
                ("periods", "found 9 period values, expected 5"),
                ("integrality", "power-sum numerator for r=2 is not divisible by n"),
            ):
                with self.subTest(optimization=optimization, corruption=corruption):
                    result = self.run_probe(optimization, corruption)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(message, result.stderr)


if __name__ == "__main__":
    unittest.main()
