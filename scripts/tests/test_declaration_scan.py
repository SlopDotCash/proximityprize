"""Declaration scanning must retain audit coverage across large masked comments."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forbidden_tokens import DECL_RE, comment_mask


class DeclarationScan(unittest.TestCase):
    def test_masked_comment_does_not_consume_preceding_lines(self):
        source = '/-\n' + 'commentary\n' * 5000 + '-/\nprivate opaque missing : True\n'
        mask = comment_mask(source)
        live = ''.join(' ' if hidden and ch != '\n' else ch
                       for ch, hidden in zip(source, mask))
        match, = DECL_RE.finditer(live)
        self.assertEqual(match.groups(), ('opaque', 'missing'))
        self.assertEqual(match.start(), live.index('private opaque'))

    def test_multiline_attributes_and_modifiers_remain_visible(self):
        source = '@[simp]\n\nprivate theorem fact : True := by trivial\n'
        match, = DECL_RE.finditer(source)
        self.assertEqual(match.groups(), ('theorem', 'fact'))


if __name__ == '__main__':
    unittest.main()
