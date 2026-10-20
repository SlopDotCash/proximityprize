"""String literals must not open phantom comments in the laundering precheck."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forbidden_tokens import comment_mask


def live_text(source):
    mask = comment_mask(source)
    return ''.join(' ' if hidden and ch != '\n' else ch
                   for ch, hidden in zip(source, mask))


class StringLiteralScan(unittest.TestCase):
    def test_string_holding_block_comment_opener_does_not_mask_following_code(self):
        # A literal such as "/-" used to open a phantom block comment that
        # blanked the rest of the file, hiding every later axiom from the gate.
        source = 'def banner : String := "/-"\n\naxiom hidden : False\n'
        self.assertIn('axiom hidden', live_text(source))

    def test_string_holding_line_comment_marker_does_not_mask_same_line_code(self):
        source = 'def s := "--"; axiom hidden : False\n'
        self.assertIn('axiom hidden', live_text(source))

    def test_escaped_quote_does_not_end_the_literal(self):
        source = 'def s := "quote \\" then /-"\naxiom hidden : False\n'
        self.assertIn('axiom hidden', live_text(source))

    def test_char_literal_quote_does_not_open_a_string(self):
        source = 'def q : Char := \'"\'\naxiom hidden : False\n'
        self.assertIn('axiom hidden', live_text(source))

    def test_real_comments_still_hide_their_contents(self):
        source = '/- axiom hidden : False -/\naxiom kept : False\n'
        live = live_text(source)
        self.assertNotIn('axiom hidden', live)
        self.assertIn('axiom kept', live)

    def test_tokens_inside_a_string_are_not_live_code(self):
        source = 'def note : String := "native_decide"\n'
        self.assertNotIn('native_decide', live_text(source))


if __name__ == '__main__':
    unittest.main()
