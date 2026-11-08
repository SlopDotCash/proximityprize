"""Regression tests for exact-arithmetic contracts of the SW1 / ZTZ probes (audit L134, L135)."""
import cmath
import importlib
from pathlib import Path
import random
import sys
import types
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import sw1_ctr_structured_families as ctr
import sw1_sparse_root_locus as sparse
import sw1_transv_multiplicity_profile as transv
import probe_ztz_beta3_ladder as beta3
import probe_ztz_beta4_ladder as beta4
import probe_ztz_beta5_ladder as beta5
import probe_ztz_beta4_prize_scale as beta4p
import probe_ztz_beta35_prize_scale as beta35p


def import_arc_probe():
    """sw1_arc_max_ap_profile imports sympy at module load; the helper under test does not use
    it, so a temporary stub is installed only when sympy is absent."""
    if importlib.util.find_spec('sympy') is not None:
        return importlib.import_module('sw1_arc_max_ap_profile')
    sys.modules['sympy'] = types.SimpleNamespace(isprime=None, primitive_root=None)
    try:
        return importlib.import_module('sw1_arc_max_ap_profile')
    finally:
        del sys.modules['sympy']


class CtrInt64Accumulation(unittest.TestCase):
    def test_interp_large_k_does_not_overflow(self):
        # n=128, k=80, p=536870657 passes the constructor guards; the unblocked int64 sum of
        # 80 products of residues overflowed and changed all 48 off-basis coordinates.
        E = ctr.Engine(128, 80, 536870657, 128)
        self.assertEqual(E.P, 1)
        Tc, Lc = next(E.chunks())
        U = np.full((1, 128), E.p - 1, dtype=np.int64)
        H = E.interp(U, Tc, Lc)[0, 0]
        self.assertTrue(np.all(H == E.p - 1))

    def test_interp_matches_python_integers(self):
        rng = random.Random(7)
        E = ctr.Engine(64, 40, 536870849, 64)
        Tc, Lc = next(E.chunks())
        u = [rng.randrange(E.p) for _ in range(64)]
        H = E.interp(np.array([u], dtype=np.int64), Tc, Lc)[0, 0]
        for l in range(64):
            want = sum(int(Lc[0, t, l]) * u[int(Tc[0, t])] for t in range(40)) % E.p
            self.assertEqual(int(H[l]), want)

    def test_dot_block_bound(self):
        for p in (17, 65537, 536870657):
            b = ctr.mod_dot_block(p)
            self.assertLessEqual((p - 1) + b * (p - 1) ** 2, ctr.INT64_MAX)
            self.assertGreater((p - 1) + (b + 1) * (p - 1) ** 2, ctr.INT64_MAX)
        self.assertGreaterEqual(ctr.mod_dot_block((1 << 29) - 3), 32)


class TwelveBaseMillerRabinRange(unittest.TestCase):
    PSEUDOPRIME = 318665857834031151167461  # = 399165290221 * 798330580441

    def test_twelve_base_helpers_refuse_the_first_pseudoprime(self):
        self.assertEqual(399165290221 * 798330580441, self.PSEUDOPRIME)
        for helper in (beta3.is_prime, beta4.is_prime, beta5.is_prime,
                       beta4p.is_prime_exact_small, beta35p.is_prime_exact_small):
            with self.assertRaises(ValueError):
                helper(self.PSEUDOPRIME)
            self.assertTrue(helper((1 << 61) - 1))              # Mersenne prime, in range
            self.assertFalse(helper(((1 << 61) - 1) * 1009))     # composite, in range

    def test_helpers_agree_with_trial_division_on_small_inputs(self):
        def trial(m):
            return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
        for m in range(0, 3000):
            for helper in (beta3.is_prime, beta4.is_prime, beta5.is_prime,
                           beta4p.is_prime_exact_small, beta35p.is_prime_exact_small):
                self.assertEqual(helper(m), trial(m), (helper.__module__, m))


class ArcRandomModel(unittest.TestCase):
    def test_uniform_subsets_have_distinct_entries(self):
        arc = import_arc_probe()
        rng = np.random.default_rng(1)
        rows = arc.uniform_subsets(rng, 4000, 8, 20)   # with replacement, most rows repeat
        self.assertEqual(rows.shape, (4000, 8))
        self.assertTrue(np.all((rows >= 0) & (rows < 20)))
        S = np.sort(rows, axis=1)
        self.assertFalse(np.any(S[:, 1:] == S[:, :-1]))


class TransvMultiplicityProfile(unittest.TestCase):
    def test_first_driver_cell_runs_with_a_none_returning_logger(self):
        # the logging callback used to shadow math.log inside profile_cell
        res = transv.profile_cell(8, 2, 17, lambda s: None)
        self.assertEqual(res['fails'], [])
        self.assertGreater(res['n_checked'], 0)

    def test_exact_norm_matches_product_of_conjugates(self):
        rng = random.Random(3)
        for n in (8, 16):
            d = n // 2
            for _ in range(20):
                c = [rng.randint(-3, 3) for _ in range(d)]
                approx = 1.0
                for u in range(1, n, 2):
                    z = cmath.exp(2j * cmath.pi * u / n)
                    approx *= abs(sum(cj * z ** j for j, cj in enumerate(c)))
                self.assertEqual(transv.exact_norm(c), round(approx))
        self.assertEqual(transv.exact_norm([1, 1, 0, 0]), 2)    # N(1 + zeta_8) = Phi_8(-1)

    def test_floor_log_pow_is_exact_at_boundaries(self):
        self.assertEqual(transv.floor_log_pow(17 ** 3, 17), 3)
        self.assertEqual(transv.floor_log_pow(17 ** 3 - 1, 17), 2)
        self.assertEqual(transv.floor_log_pow(1, 17), 0)
        with self.assertRaises(ValueError):
            transv.profile_cell(64, 2, 193, lambda s: None)


class SparseRootLocusI2(unittest.TestCase):
    def test_direct_recount_runs_on_small_cell(self):
        res = sparse.run_cell(8, 17, 2, verbose=False)
        self.assertTrue(res['ok'])


if __name__ == '__main__':
    unittest.main()
