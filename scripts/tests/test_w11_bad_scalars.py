"""Compare W11's interpolation-based bad set against exhaustive polynomial search."""
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_w11_c3_kill as probe


class BadScalarCertificates(unittest.TestCase):
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
