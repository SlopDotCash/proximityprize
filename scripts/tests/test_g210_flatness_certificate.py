"""G210's mathematical certificate checks must survive Python optimization."""
import subprocess
import sys
from pathlib import Path
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes/g210_tail_floor_flatness_certificate.py"
LOAD = f"""
import builtins
import runpy
from unittest.mock import patch
probe = runpy.run_path({str(PROBE)!r})
scope = probe['analyze'].__globals__
"""


class FlatnessCertificate(unittest.TestCase):
    def run_probe(self, source, flag):
        return subprocess.run(
            [sys.executable, *([flag] if flag else []), "-c", LOAD + source],
            text=True, capture_output=True, check=False,
        )

    def test_published_cells_pass_in_all_modes(self):
        source = """
expected = {
    (17, 8): (25, False), (113, 8): (13, True),
    (97, 16): (53, False), (2593, 16): (29, True),
    (257, 32): (181, False), (3617, 32): (61, True),
    (50177, 32): (73, False), (51137, 32): (73, False),
}
for (p, n), answer in expected.items():
    row = probe['analyze'](p, n)
    if (row['sumsq'], row['distinct']) != answer:
        raise RuntimeError((p, n, row))
probe['main']()
"""
        outputs = []
        for flag in (None, "-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(source, flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("ALL PASS", result.stdout)
                outputs.append(result.stdout)
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(outputs[0], outputs[2])

    def test_corrupt_certificates_fail_in_all_modes(self):
        cases = {
            "partition mismatch": """
original = probe['primitive_partition']
def corrupted(p, n, g):
    histogram, atoms, collisions = original(p, n, g)
    return [n - 1], atoms, collisions
with patch.dict(scope, primitive_partition=corrupted):
    probe['main']()
""",
            "flatness equivalence": """
original = probe['primitive_partition']
def corrupted(p, n, g):
    histogram, atoms, collisions = original(p, n, g)
    return histogram, atoms, {}
with patch.dict(scope, primitive_partition=corrupted):
    probe['main']()
""",
            "subgroup membership": """
def corrupted_pow(base, exponent, modulus):
    if exponent == modulus - 2:
        return 0
    return builtins.pow(base, exponent, modulus)
with patch.dict(scope, pow=corrupted_pow):
    probe['main']()
""",
            "weighted relation": """
def corrupted_pow(base, exponent, modulus):
    value = builtins.pow(base, exponent, modulus)
    return value * 2 % modulus if exponent == modulus - 2 else value
with patch.dict(scope, pow=corrupted_pow):
    probe['main']()
""",
            "orbit divisibility": """
# A generator of the wrong order produces non-integral orbit multiplicities.
probe['direct_partition'](7, 2, 2)
print('ALL PASS')
""",
            "order divisibility": """
probe['primitive_n_root'](17, 3)
print('ALL PASS')
""",
        }
        for case, source in cases.items():
            for flag in (None, "-O", "-OO"):
                with self.subTest(case=case, flag=flag):
                    result = self.run_probe(source, flag)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertNotIn("ALL PASS", result.stdout)
                    self.assertIn(case, result.stderr)


if __name__ == "__main__":
    unittest.main()
