"""Regression for the dyadic-domain escape probe's subgroup/coset construction.

The probe once took strides of a numerically sorted list of mu_256 and called them
the mu_32 / mu_64 subgroups; those strides are arbitrary subsets (audit 2026-10-28,
finding L115).  The probe must build subgroups and cosets from exponent-ordered
powers with representatives from distinct quotient classes.
"""
import contextlib
import io
from pathlib import Path
import runpy
import unittest

PROBE = (Path(__file__).resolve().parents[1] / 'probes'
         / 'probe_rate_quarter_p1_dyadic_domain_escape.py')


def run_probe():
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        globs = runpy.run_path(str(PROBE), run_name='__main__')
    return globs, buf.getvalue()


class DyadicDomainEscapeCosets(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.g, cls.out = run_probe()

    def test_sorted_strides_are_not_subgroups(self):
        # Documents the original defect: the stride of the sorted list is not mu_32.
        q, dom = self.g['q'], self.g['DOM']
        stride = dom[::8]
        self.assertEqual(sum(pow(x, 32, q) == 1 for x in stride), 5)
        self.assertEqual(stride[1], 141)
        self.assertEqual(pow(141, 32, q), 4096)

    def test_subgroups_are_genuine(self):
        q = self.g['q']
        for name, size in (('mu32', 32), ('mu64', 64)):
            sub = self.g[name]
            self.assertEqual(len(set(sub)), size)
            self.assertTrue(all(pow(x, size, q) == 1 for x in sub))
            self.assertLessEqual(set(sub), set(self.g['DOM']))

    def test_cosets_are_disjoint_cosets(self):
        q = self.g['q']
        for name, size, count in (('cos32', 32, 6), ('cos64', 64, 3)):
            fam = self.g[name]
            self.assertEqual(len(fam), count)
            union = set()
            for c in fam:
                self.assertEqual(len(set(c)), size)
                # x and y lie in one mu_size-coset iff x^size == y^size
                self.assertEqual(len({pow(x, size, q) for x in c}), 1)
                self.assertFalse(set(c) & union)
                union |= set(c)
            self.assertNotIn(1, {pow(c[0], size, q) for c in fam})

    def test_arcs_follow_exponent_order(self):
        w, q, cyc = self.g['w256'], self.g['q'], self.g['DOM_CYC']
        self.assertEqual(cyc, [pow(w, i, q) for i in range(256)])

    def test_output_reports_checks_and_corrected_battery(self):
        self.assertIn('subgroup/coset checks passed', self.out)
        self.assertNotIn('Exact Bezout dimension = 0 across all', self.out)
        self.assertRegex(self.out, r'two-level shared\s*: Sigma = 167, dim = 8')
        self.assertRegex(self.out, r'mu64-coset trunc\s*: Sigma = 167, dim = 0')


if __name__ == '__main__':
    unittest.main()
