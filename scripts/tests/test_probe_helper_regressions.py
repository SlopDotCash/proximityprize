"""Regression coverage for generic arithmetic helpers and census certificate entry points.

* `probe_ant46_kappa_dyadic_recurrence.poly_div_exact` used to drop quotient degrees when one
  step cancelled several leading coefficients (`(X^2 - 1) / 1` gave `X - 1`).
* its `bareiss_determinant` raised `StopIteration` on a singular matrix with no pivot
  replacement (`[[0, 0], [0, 1]]`) instead of returning `0`.
* its `discriminant` omitted the division by the leading coefficient (only valid for monic input).
* `g296_palindrome_census_collapse.subgroup` carried an inert `for ...: pass` loop.
* non-two-power ceiling probes must reject optimization that disables their certificate assertions.

The g296 probe runs its checks at import time, so its helper is extracted with `ast` and executed
in isolation instead of importing the module.
"""
import ast
import os
from itertools import permutations
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

PROBES = Path(__file__).resolve().parents[1] / "probes"
sys.path.insert(0, str(PROBES))
import probe_ant46_kappa_dyadic_recurrence as ant46  # noqa: E402


def leibniz_determinant(matrix):
    size = len(matrix)
    total = 0
    for perm in permutations(range(size)):
        inversions = sum(1 for i in range(size) for j in range(i + 1, size) if perm[i] > perm[j])
        term = -1 if inversions % 2 else 1
        for row, column in enumerate(perm):
            term *= matrix[row][column]
        total += term
    return total


def rational_discriminant_quadratic(a, b, c):
    return b * b - 4 * a * c


class PolyDivExact(unittest.TestCase):
    def test_division_by_constant_keeps_all_degrees(self):
        self.assertEqual(ant46.poly_div_exact([1, 0, -1], [1]), [1, 0, -1])

    def test_division_by_linear_factor(self):
        self.assertEqual(ant46.poly_div_exact([1, 0, -1], [1, -1]), [1, 1])

    def test_multi_coefficient_cancellation(self):
        # (X^3 + 1) / (X + 1) = X^2 - X + 1; (X^4 - 1) / (X^2 + 1) = X^2 - 1
        self.assertEqual(ant46.poly_div_exact([1, 0, 0, 1], [1, 1]), [1, -1, 1])
        self.assertEqual(ant46.poly_div_exact([1, 0, 0, 0, -1], [1, 0, 1]), [1, 0, -1])

    def test_random_products_round_trip(self):
        rng = random.Random(46)
        for _ in range(200):
            left = [rng.choice([1, -1, 2, -3])] + [rng.randint(-3, 3) for _ in range(rng.randint(0, 4))]
            right = [rng.choice([1, -1, 2])] + [rng.randint(-3, 3) for _ in range(rng.randint(0, 4))]
            product = ant46.poly_mul(left, right)
            self.assertEqual(ant46.poly_div_exact(product, right), ant46.trim(left))

    def test_inexact_division_is_rejected(self):
        with self.assertRaises(AssertionError):
            ant46.poly_div_exact([1, 0, 1], [1, -1])


class BareissDeterminant(unittest.TestCase):
    def test_singular_without_pivot_replacement_is_zero(self):
        self.assertEqual(ant46.bareiss_determinant([[0, 0], [0, 1]]), 0)
        self.assertEqual(ant46.bareiss_determinant([[1, 2, 3], [0, 0, 5], [0, 0, 7]]), 0)

    def test_matches_leibniz_expansion(self):
        rng = random.Random(1946)
        for _ in range(300):
            size = rng.randint(1, 4)
            matrix = [[rng.choice([0, 0, 1, -1, 2, -2, 3]) for _ in range(size)]
                      for _ in range(size)]
            self.assertEqual(ant46.bareiss_determinant(matrix), leibniz_determinant(matrix))


class Discriminant(unittest.TestCase):
    def test_non_monic_quadratics(self):
        for a, b, c in [(2, 3, 1), (3, 0, -5), (-2, 1, 4), (1, -1, -1)]:
            self.assertEqual(ant46.discriminant([a, b, c]), rational_discriminant_quadratic(a, b, c))

    def test_monic_cubic(self):
        # X^3 + pX + q has discriminant -4p^3 - 27q^2
        for p, q in [(1, 1), (-3, 2), (0, 5)]:
            self.assertEqual(ant46.discriminant([1, 0, p, q]), -4 * p ** 3 - 27 * q ** 2)


def g296_subgroup():
    source = (PROBES / "g296_palindrome_census_collapse.py").read_text()
    tree = ast.parse(source)
    node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "subgroup")
    namespace = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), "g296_subgroup", "exec"), namespace)
    return node, namespace["subgroup"]


class G296Subgroup(unittest.TestCase):
    def test_no_inert_loop(self):
        node, _ = g296_subgroup()
        inert = [loop.lineno for loop in ast.walk(node)
                 if isinstance(loop, (ast.For, ast.While))
                 and all(isinstance(stmt, ast.Pass) for stmt in loop.body)]
        self.assertEqual(inert, [])

    def test_subgroup_is_the_order_n_subgroup(self):
        _, subgroup = g296_subgroup()
        for p, n in [(17, 8), (97, 16), (193, 16), (13, 6)]:
            expected = sorted(x for x in range(1, p) if pow(x, n, p) == 1)
            self.assertEqual(subgroup(p, n), expected)


T3_NON2POWER_PROBES = (
    "probe_t3_ceiling_column_non2power.py",
    "probe_t3_ceiling_column_non2power_crosscheck.py",
    "probe_t3_ceiling_column_non2power_staged_anchor.py",
)
T3_CERTIFICATE_ENTERED = "certificate entry point reached"

# Replace only the expensive arithmetic body. Keep the real module setup and
# entry point so a removed or misplaced optimization guard fails this test.
T3_ENTRY_POINT_HARNESS = r'''
import ast
from pathlib import Path
import sys

path = Path(sys.argv[1])
tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
main = next(node for node in tree.body
            if isinstance(node, ast.FunctionDef) and node.name == "main")
main.body = ast.parse('print("certificate entry point reached"); return 0').body
ast.fix_missing_locations(tree)
exec(compile(tree, str(path), "exec"), {"__name__": "__main__", "__file__": str(path)})
'''


class NonTwoPowerOptimization(unittest.TestCase):
    def run_entry_point(self, name, *, flags=(), optimize=None):
        env = os.environ.copy()
        env.pop("PYTHONOPTIMIZE", None)
        if optimize is not None:
            env["PYTHONOPTIMIZE"] = optimize
        return subprocess.run(
            [sys.executable, *flags, "-B", "-c", T3_ENTRY_POINT_HARNESS, str(PROBES / name)],
            env=env, capture_output=True, text=True, timeout=10,
        )

    def test_normal_mode_reaches_each_entry_point(self):
        for name in T3_NON2POWER_PROBES:
            with self.subTest(probe=name):
                result = self.run_entry_point(name)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(T3_CERTIFICATE_ENTERED, result.stdout)

    def test_optimized_modes_stop_before_certificate_work(self):
        for name in T3_NON2POWER_PROBES:
            for flags, optimize in ((("-O",), None), (("-OO",), None), ((), "1")):
                with self.subTest(probe=name, flags=flags, environment=optimize):
                    result = self.run_entry_point(name, flags=flags, optimize=optimize)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("Run without Python optimization", result.stderr)
                    self.assertNotIn(T3_CERTIFICATE_ENTERED, result.stdout)

    def test_corrupted_ceiling_anchor_is_rejected(self):
        for name in T3_NON2POWER_PROBES[:2]:
            source = (PROBES / name).read_text(encoding="utf-8")
            anchor = ("N8_CEILING_DEFAULT = 40" if name == T3_NON2POWER_PROBES[0]
                      else "N8_CEILING_DEFAULT, N8_CEILING_EXCEPTIONS = 40,")
            self.assertEqual(source.count(anchor), 1)
            source = source.replace(anchor, anchor.replace("40", "41"))
            with tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / name
                path.write_text(source, encoding="utf-8")
                for flags in ((), ("-O",), ("-OO",)):
                    with self.subTest(probe=name, flags=flags):
                        env = os.environ.copy()
                        env.pop("PYTHONOPTIMIZE", None)
                        result = subprocess.run(
                            [sys.executable, *flags, "-B", str(path)], env=env,
                            capture_output=True, text=True, timeout=10,
                        )
                        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertNotIn("PASS", result.stdout)

    def test_mismatched_digest_anchor_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            probes = root / "scripts" / "probes"
            probes.mkdir(parents=True)
            (probes / T3_NON2POWER_PROBES[0]).write_text(
                'STAGED_TWO_POWER_DIGESTS = {(8, "65537"): "bad"}\n', encoding="utf-8")
            (probes / "probe_t3_ceiling_column_high_rungs.py").write_text(
                'PINNED_VECTOR_DIGESTS = {(8, "65537"): "good"}\n', encoding="utf-8")
            for flags in ((), ("-O",), ("-OO",)):
                with self.subTest(flags=flags):
                    env = os.environ.copy()
                    env.pop("PYTHONOPTIMIZE", None)
                    result = subprocess.run(
                        [sys.executable, *flags, "-B", str(PROBES / T3_NON2POWER_PROBES[2]), str(root)],
                        env=env, capture_output=True, text=True, timeout=10,
                    )
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertNotIn("PASS:", result.stdout)


if __name__ == "__main__":
    unittest.main()
