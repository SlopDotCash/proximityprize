"""Compare W11's interpolation-based bad set against exhaustive polynomial search."""
from itertools import product
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_w11_c3_kill as probe


class BadScalarCertificates(unittest.TestCase):
    def test_engine_count_disagreement_is_rejected_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(Path(__file__).resolve().parents[1] / 'probes')!r})
            import probe_w11_c3_kill as probe
            probe._require_certified_count(7, 3)
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
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("engine 7 != certified 3", result.stderr)

    def test_bad_interpolation_certificate_is_rejected_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(Path(__file__).resolve().parents[1] / 'probes')!r})
            import numpy as np
            from types import SimpleNamespace
            import probe_w11_c3_kill as probe

            st = SimpleNamespace(
                q=5, P=1, Tidx=np.array([[0]]),
                C=np.zeros((1, 1, 1), dtype=np.int64), xs=np.array([0])
            )
            pack = {{
                'B': np.array([[1]]), 'Binv': np.array([1]),
                'valid': np.array([True]), 'u1': np.array([1])
            }}
            probe.interp_poly = lambda xs, ys, q: [1]
            probe.certified_bad_count(st, [1], pack, 1)
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
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("CERTIFICATE FAILED gamma=4: agreement 0 < 1", result.stderr)

    def test_complete_small_field_bad_sets(self):
        st = probe.Setting(8, 2, 17)
        direction = st.mono(2)
        pack = st.pack(direction)
        code = [[(a + b * int(x)) % 17 for x in st.xs]
                for a, b in product(range(17), repeat=2)]
        for exponent in (3, 4, 5):
            offset = st.mono(exponent)
            expected = []
            for gamma in range(17):
                word = [(int(a) + gamma * int(b)) % 17
                        for a, b in zip(offset, direction)]
                if any(sum(x == y for x, y in zip(word, c)) >= 3 for c in code):
                    expected.append(gamma)
            count, actual = probe.certified_bad_count(st, offset, pack, 3)
            self.assertEqual(actual, expected)
            self.assertEqual(count, len(expected))


if __name__ == '__main__':
    unittest.main()
