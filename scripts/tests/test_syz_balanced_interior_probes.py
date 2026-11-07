"""Regression tests for the SYZ48 / SYZ50 / SYZ52 balanced-interior probes.

Audit findings L128, L129, L130 (repository review 2026-10-28):
* SYZ48 must count a constant-syzygy configuration as an F_p-point realization only when the
  combination polynomial splits into distinct F_p roots;
* SYZ50 must separate the necessary profile relaxation from strict-band core ownership;
* SYZ52 must lift the selected profile (triple region of the selected size, checked core and
  overlap sizes) and classify MCA badness per scalar, never by a whole-stack filter.
"""
from itertools import combinations, product
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz48_balanced_interior as syz48  # noqa: E402
import probe_syz50_witness_realizability as syz50  # noqa: E402

try:
    import numpy  # noqa: F401
    import probe_syz52_witness_lift as syz52  # noqa: E402
except ImportError:  # pragma: no cover - numpy is optional for the other probes
    syz52 = None


class SYZ48Splitting(unittest.TestCase):
    def test_fp_root_count_matches_exhaustive(self):
        rng = random.Random(5)
        for mod in (7, 11, 13, 29):
            for _ in range(60):
                deg = rng.randrange(1, 7)
                p = [rng.randrange(mod) for _ in range(deg)] + [rng.randrange(1, mod)]
                expected = sum(1 for x in range(mod) if syz48.poly_eval(p, x, mod) == 0)
                self.assertEqual(syz48.fp_root_count(p, mod), expected)
                if syz48.splits_squarefree(p, mod):
                    self.assertEqual(expected, deg)

    def test_audit_nonsplit_example_is_not_a_realization(self):
        # first accepted seeded trial of experiment_4 at F_10007: degree 5, one F_p root
        poly = [4530, 779, 7449, 7161, 983, 8860]
        self.assertEqual(syz48.fp_root_count(poly, 10007), 1)
        self.assertEqual(syz48.poly_eval(poly, 7883, 10007), 0)
        self.assertFalse(syz48.splits_squarefree(poly, 10007))
        r = syz48.experiment_4(10007, trials=40)
        first = r['examples'][0]
        self.assertEqual(first['P'], poly)
        self.assertEqual(first['iota'], 2)
        self.assertFalse(first['splits'])
        self.assertLess(r['split_fp_point_realizations'], r['algebraic_iota_ge_2_configurations'])


class SYZ50Ownership(unittest.TestCase):
    def test_relaxation_is_not_strict_band_realizability(self):
        self.assertTrue(syz50.realizable(4, 5, 5, 3, 9))
        self.assertTrue(syz50.balanced_interior(4, 5, 5))
        self.assertIsNone(syz50.strict_band_ownership(4, 5, 5, 3, 9))

    def test_genuine_profiles_survive(self):
        self.assertEqual(syz50.strict_band_ownership(4, 4, 4, 2, 7), (0, 0, 0))
        self.assertEqual(syz50.strict_band_ownership(4, 4, 4, 3, 8), (0, 0, 0))
        self.assertFalse(any(syz50.realizable(4, 4, 4, t, 6) for t in range(6)))

    def test_ownership_matches_exhaustive_private_counts(self):
        for k in range(4, 10):
            n = 2 * k
            lo, hi = syz50.band_bounds(n)
            self.assertTrue(3 * lo > 2 * n and 3 * (lo - 1) <= 2 * n)
            self.assertTrue(4 * hi < 3 * n and 4 * (hi + 1) >= 3 * n)
            for a, b, c in product(range(1, k), repeat=3):
                for t in range(k):
                    if not syz50.realizable(a, b, c, t, k):
                        continue
                    free = n - (a + b + c + t)
                    exists = any(
                        all(lo <= base + q <= hi for base, q in
                            zip((a + b + t, a + c + t, b + c + t), qs))
                        for qs in product(range(free + 1), repeat=3) if sum(qs) <= free)
                    self.assertEqual(syz50.strict_band_realizable(a, b, c, t, k), exists,
                                     (a, b, c, t, k))


@unittest.skipIf(syz52 is None, 'numpy unavailable')
class SYZ52Lift(unittest.TestCase):
    def test_scale_profile_has_selected_geometry(self):
        n, k, a, t = 16, 8, 4, 3
        own = syz50.strict_band_ownership(a, a, a, t, k)
        self.assertEqual(own, (0, 0, 0))
        mu, recs = syz52.find_profile_witnesses(17, n, a, t, privates=own, max_wit=6)
        self.assertTrue(recs)
        for AC, BC, AB, T, R, P in recs:
            self.assertEqual(len(T), t)
            cores = syz52.cores_of(AC, BC, AB, T, P)
            self.assertEqual(syz52.check_profile(cores, n, k, a, t, own), 11)
        # the legacy full-leftover enumerator builds |T| = 4, cores of size 12 and overlap 8 = k
        _, legacy = syz52.find_witnesses(17, n, a, max_wit=1)
        AC, BC, AB, T, R = legacy[0]
        self.assertEqual(len(T), n - 3 * a)
        with self.assertRaises(AssertionError):
            syz52.check_profile(syz52.cores_of(AC, BC, AB, T), n, k, a, t)

    def test_per_scalar_mca_finds_nonjoint_witness_behind_joint_set(self):
        # F_17, domain 0..15, k=8, s=11: u0,u1 vanish on {0..10} (a joint threshold set), yet
        # gamma=1 has the nonjoint witness {0..6,11..15} of prod_{a<7}(X-a).
        p, k, s = 17, 8, 11
        alpha = list(range(16))
        u0 = [0] * 11 + [1, 0, 0, 0, 0]
        u1 = [0] * 11 + [4, 12, 9, 1, 4]
        tensor = syz52.build_interp_tensor(alpha, k, s, p)
        self.assertTrue(syz52.whole_stack_joint_set_exists(u0, u1, tensor))
        bad, close = syz52.mca_bad_scalars(u0, u1, tensor)
        self.assertIn(1, close)
        self.assertIn(1, bad)

    def test_per_scalar_mca_matches_brute_force(self):
        p, k, s = 7, 2, 4
        alpha = list(range(1, 7))
        n = len(alpha)
        tensor = syz52.build_interp_tensor(alpha, k, s, p)
        code = [tuple((c0 + c1 * x) % p for x in alpha) for c0 in range(p) for c1 in range(p)]
        sets = [S for r in range(s, n + 1) for S in combinations(range(n), r)]

        def agrees(w, c, S):
            return all(w[i] == c[i] for i in S)

        rng = random.Random(3)
        for _ in range(25):
            u0 = [rng.randrange(p) for _ in range(n)]
            u1 = [rng.randrange(p) for _ in range(n)]
            if rng.random() < 0.4:  # plant shared structure so joint sets occur
                c = rng.choice(code)
                for i in rng.sample(range(n), s):
                    u0[i] = c[i]
                    u1[i] = code[rng.randrange(len(code))][i] if rng.random() < 0.3 else 0
            expected_bad, expected_close = [], []
            for z in range(p):
                w = [(x + z * y) % p for x, y in zip(u0, u1)]
                witnesses = [S for S in sets if any(agrees(w, c, S) for c in code)]
                if witnesses:
                    expected_close.append(z)
                if any(not (any(agrees(u0, c, S) for c in code) and
                            any(agrees(u1, c, S) for c in code)) for S in witnesses):
                    expected_bad.append(z)
            bad, close = syz52.mca_bad_scalars(u0, u1, tensor)
            self.assertEqual(close, expected_close)
            self.assertEqual(bad, expected_bad)

    def test_interpolation_base_guard(self):
        with self.assertRaises(ValueError):
            syz52.build_interp_tensor(list(range(16)), 8, 10, 17)


if __name__ == '__main__':
    unittest.main()
