"""Sorry/admit census must not treat string text as comments or as holes."""
import json
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import sorry_census


def kinds(source: str) -> list[tuple[str, str, str]]:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        folder = root / "ArkLib"
        folder.mkdir()
        (folder / "Probe.lean").write_text(source, encoding="utf-8")
        rows = sorry_census.census(root)
    return [(row["token"], row["kind"], row["decl"]) for row in rows]


class SorryCensusStrings(unittest.TestCase):
    def test_live_sorry_and_admit_are_holes(self):
        self.assertEqual(
            kinds("theorem t : True := sorry\nlemma u : False := admit\n"),
            [("sorry", "hole", "theorem t"), ("admit", "hole", "lemma u")])

    def test_comments_and_docstrings_are_not_holes(self):
        source = (
            "/-- uses sorry in prose -/\n"
            "theorem t : True := trivial\n"
            "-- admit is only a word here\n"
            "/- nested /- sorry -/ still admit -/\n"
        )
        self.assertEqual(
            [(token, kind) for token, kind, _decl in kinds(source)],
            [("sorry", "doc"), ("admit", "doc"), ("sorry", "doc"), ("admit", "doc")])

    def test_line_comment_does_not_hide_the_next_line(self):
        self.assertEqual(
            kinds("theorem t : True := by\n  -- sorry\n  sorry\n"),
            [("sorry", "doc", "theorem t"), ("sorry", "hole", "theorem t")])

    def test_dashes_inside_string_do_not_hide_sorry(self):
        source = 'theorem t : String := "a -- b" ++ sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_block_opener_inside_string_does_not_hide_sorry(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "open /-"\n'
            "  sorry\n"
            '  let _ := "-/"\n'
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_sorry_inside_string_literal_is_not_a_hole(self):
        self.assertEqual(
            kinds('def msg := "do not sorry or admit this"\n'),
            [("sorry", "doc", "def msg"), ("admit", "doc", "def msg")])

    def test_escaped_quote_keeps_later_sorry_live(self):
        source = 'theorem t : String := "a \\" -- " ++ sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_char_literal_quote_does_not_swallow_sorry(self):
        source = "theorem t : True := by let _ := '\"'; exact sorry\n"
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_multiline_string_does_not_start_a_comment(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "hello\n'
            '/- not a comment"\n'
            "  sorry\n"
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_string_gap_does_not_let_a_later_block_opener_hide_sorry(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "a\\\n'
            '/- "\n'
            "  sorry\n"
            '  let _ := "-/"\n'
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_sorry_inside_a_continued_string_is_not_a_hole(self):
        source = 'def msg := "keep\\\n  sorry here"\n'
        self.assertEqual(kinds(source), [("sorry", "doc", "def msg")])

    def test_raw_string_internal_quote_does_not_hide_sorry(self):
        source = 'theorem t : True := by let _ := r#"foo " -- bar"#; exact sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_raw_string_text_is_not_a_hole(self):
        self.assertEqual(
            kinds('def msg := r##"sorry and admit"##\n'),
            [("sorry", "doc", "def msg"), ("admit", "doc", "def msg")])

    def test_identifier_ending_in_r_is_not_a_raw_string(self):
        plain = 'theorem t : String := foor"a -- b" ++ sorry\n'
        self.assertEqual(kinds(plain), [("sorry", "hole", "theorem t")])
        # `foo_1r` is an identifier, so the `"` closes before `--` and the sorry
        # is a comment. A raw string would keep going until `"#` and leave sorry live.
        numbered = 'theorem t : True := by let _ := foo_1r#"a " -- "# ++ sorry\n'
        self.assertEqual(kinds(numbered), [("sorry", "doc", "theorem t")])

    def test_raw_string_after_a_numeric_token(self):
        for literal in ('1_0r#"a " -- b"#', '0x1r#"a " -- b"#'):
            with self.subTest(literal=literal):
                source = f"theorem t : True := by let _ := {literal}; exact sorry\n"
                self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_interpolated_sorry_is_a_hole_and_literal_sorry_is_not(self):
        source = (
            'theorem t : String := s!"{sorry}"\n'
            'theorem u : String := s!"sorry"\n'
            'theorem v : String := s!"\\{sorry}"\n'
        )
        self.assertEqual(
            kinds(source),
            [
                ("sorry", "hole", "theorem t"),
                ("sorry", "doc", "theorem u"),
                ("sorry", "doc", "theorem v"),
            ])

    def test_interpolation_tracks_comments_and_nested_braces(self):
        source = (
            'theorem t : String := s!"{-- sorry\nexact sorry}"\n'
            'theorem u : String := m!"{({admit})}"\n'
            'theorem v : String := println! "{sorry}"\n'
        )
        self.assertEqual(
            kinds(source),
            [
                ("sorry", "doc", "theorem t"),
                ("sorry", "hole", "theorem t"),
                ("admit", "hole", "theorem u"),
                ("sorry", "hole", "theorem v"),
            ])

    def test_comment_inside_interpolation_can_contain_a_brace(self):
        source = 'theorem t : String := s!"{/- } -/ sorry}"\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])


FIXTURE = (
    "theorem prizeAuditProbe : 1 = 1 := by\n"
    "  let _ : Nat := dbg_trace \"{(sorry : Nat)}\"; 0\n"
    "  rfl\n"
    "#print axioms prizeAuditProbe\n"
)

# Bang-less interpolatedStr(term) consumers in Lean v4.30.0-rc2
# (src/Lean/Parser/Term.lean, Parser/Do.lean, Exception.lean, Util/Trace.lean,
# Meta/Tactic/Grind/Types.lean, Init/MacroTrace.lean).
NON_BANG_CONSUMERS = [
    'dbg_trace "{sorry}"; 0',
    'throwError "{sorry}"',
    'throwErrorAt stx "{sorry}"',
    'throwNamedError lean.foo "{sorry}"',
    'throwNamedErrorAt stx lean.foo "{sorry}"',
    'logNamedError lean.foo "{sorry}"',
    'logNamedErrorAt stx lean.foo "{sorry}"',
    'logNamedWarning lean.foo "{sorry}"',
    'logNamedWarningAt stx lean.foo "{sorry}"',
    'trace[Meta.debug] "{sorry}"',
    'trace_goal[grind] "{sorry}"',
    'Macro.trace[Meta.debug] "{sorry}"',
]


class SorryCensusBanglessInterpolation(unittest.TestCase):
    def test_reviewer_fixture_is_a_hole(self):
        self.assertEqual(kinds(FIXTURE), [("sorry", "hole", "theorem prizeAuditProbe")])

    def test_every_bangless_consumer_keeps_splice_live(self):
        for call in NON_BANG_CONSUMERS:
            with self.subTest(call=call):
                self.assertEqual(
                    kinds(f"def t := do\n  {call}\n"), [("sorry", "hole", "def t")])

    def test_admit_in_bangless_splice_is_a_hole(self):
        self.assertEqual(
            kinds('def t := throwError "x {admit} y"\n'), [("admit", "hole", "def t")])

    def test_literal_text_outside_braces_stays_doc(self):
        self.assertEqual(
            kinds('def t := throwError "sorry {x} admit"\n'),
            [("sorry", "doc", "def t"), ("admit", "doc", "def t")])

    def test_raw_string_braces_stay_doc(self):
        self.assertEqual(kinds('def t := r"{sorry}"\n'), [("sorry", "doc", "def t")])

    def test_cli_fail_on_holes_rejects_fixture(self):
        self.assertEqual(cli_holes(FIXTURE), (1, True))


def probe(splice: str) -> str:
    return (
        "theorem prizeAuditProbe : 1 = 1 := by\n"
        f"  let _ : Nat := dbg_trace \"{splice}\"; 0\n"
        "  rfl\n"
        "#print axioms prizeAuditProbe\n"
    )


def cli_holes(source: str) -> tuple[int, bool]:
    """(holes, gate failed) from the real CLI on a temp root holding `source`."""
    script = Path(__file__).resolve().parents[1] / "sorry_census.py"
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "ArkLib").mkdir()
        folder = root / "Research" / "ProximityPrize" / "Frontier"
        folder.mkdir(parents=True)
        (folder / "Probe.lean").write_text(source, encoding="utf-8")
        out = root / "census.json"
        proc = subprocess.run(
            [sys.executable, str(script), "--root", str(root), "--fail-on-holes",
             "--baseline", str(root / "missing-baseline.json"), "--out", str(out)],
            capture_output=True, text=True)
        return json.loads(out.read_text())["summary"]["holes"], proc.returncode != 0


# Reviewer fixtures (both compile with sorryAx on Lean v4.30.0-rc2).
REVIEW_COMMENT_BRACE = probe("{/- } -/ (sorry : Nat)}")
REVIEW_NESTED_STRING = probe('{let _ := "x"; (sorry : Nat)}')

# Extra adversarial splice contents: each hides a `}` or `"` from naive scans.
ADVERSARIAL_SPLICES = {
    "nested_interpolated_string": '{let _ := s!"{"}"}"; (sorry : Nat)}',
    "nested_bangless_string_with_brace": '{let _ := "}"; (sorry : Nat)}',
    "char_literal_close_brace": "{let _ := '}'; (sorry : Nat)}",
    "char_literal_quote": "{let _ := '\"'; (sorry : Nat)}",
    "line_comment_with_brace": "{-- } \"\n  (sorry : Nat)}",
    "raw_string_with_brace_and_quote": '{let _ := r#"}"\"#; (sorry : Nat)}',
    "nested_block_comment": "{/- /- } -/ } -/ (sorry : Nat)}",
    "nested_braces": "{({ val := (sorry : Nat), property := trivial } : Subtype fun (_ : Nat) => True).1}",
}


class SorryCensusSpliceParsing(unittest.TestCase):
    def test_reviewer_fixtures_are_holes(self):
        for source in (REVIEW_COMMENT_BRACE, REVIEW_NESTED_STRING):
            with self.subTest(source=source):
                self.assertEqual(kinds(source), [("sorry", "hole", "theorem prizeAuditProbe")])
                self.assertEqual(cli_holes(source), (1, True))

    def test_adversarial_splices_are_holes(self):
        for name, splice in ADVERSARIAL_SPLICES.items():
            with self.subTest(name=name):
                source = probe(splice)
                self.assertEqual(kinds(source), [("sorry", "hole", "theorem prizeAuditProbe")])
                self.assertEqual(cli_holes(source), (1, True))

    def test_comment_and_literal_text_inside_splice_stay_doc(self):
        # Comments inside a splice are masked under both readings. (A word in a
        # nested string literal inside a bang-less splice is a hole under the
        # plain reading, a deliberate fail-safe false positive.)
        source = probe("{/- sorry -/ let _ := 0; -- admit\n  0}")
        self.assertEqual(
            [(t, k) for t, k, _ in kinds(source)], [("sorry", "doc"), ("admit", "doc")])
        self.assertEqual(cli_holes(source), (0, False))

    def test_unbalanced_brace_in_plain_string_cannot_hide_later_sorry(self):
        source = 'def s := "{" ++ "x"\ntheorem t : True := sorry\n'
        self.assertIn(("sorry", "hole", "theorem t"), kinds(source))
        source = 'def s := "a } b \\" c"\ntheorem t : True := sorry\n'
        self.assertIn(("sorry", "hole", "theorem t"), kinds(source))

    def test_bang_control_matches_bangless(self):
        source = 'def t := s!"{/- } -/ (sorry : Nat)}"\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "def t")])


# Reviewer fixture: compiles on Lean v4.30.0-rc2 with `hidden` depending on
# [sorryAx]. The `"` is part of the escaped identifier, not a string opener.
REVIEW_ESCAPED_QUOTE = (
    'def «"» : Nat := 1\n'
    "theorem hidden : False := sorry\n"
    "#print axioms hidden\n"
)

# Each also compiles with [sorryAx]; a naive scan opens a string, comment, or
# splice brace inside the escaped identifier.
ESCAPED_IDENTIFIER_SOURCES = {
    "line_comment_marker": "def «a -- b» : Nat := 1\ntheorem t : False := sorry\n",
    "block_comment_opener": "def «/-» : Nat := 2\ntheorem t : False := sorry\n",
    "multiline_with_quote": 'def «multi\nline"» : Nat := 4\ntheorem t : False := sorry\n',
    "dotted_component": 'def Foo.«x"y».bar : Nat := 5\ntheorem t : False := sorry\n',
    "brace_in_splice": (
        "theorem t : True := by\n"
        '  let _ : Nat := dbg_trace "{let «}» := 0; (sorry : Nat)}"; 0\n'
        "  trivial\n"
    ),
}


class SorryCensusEscapedIdentifiers(unittest.TestCase):
    def test_reviewer_fixture_is_a_hole(self):
        self.assertEqual(kinds(REVIEW_ESCAPED_QUOTE), [("sorry", "hole", "theorem hidden")])
        self.assertEqual(cli_holes(REVIEW_ESCAPED_QUOTE), (1, True))

    def test_markers_inside_escaped_identifiers_do_not_hide_sorry(self):
        for name, source in ESCAPED_IDENTIFIER_SOURCES.items():
            with self.subTest(name=name):
                self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])
                self.assertEqual(cli_holes(source), (1, True))

    def test_guillemet_in_literal_or_comment_does_not_open_an_identifier(self):
        source = (
            "def c := '«'\n"
            'def s := "«"\n'
            "/- « -/\n"
            "theorem t : False := sorry -- »\n"
            'def u := "sorry »"\n'
        )
        self.assertEqual(
            kinds(source), [("sorry", "hole", "theorem t"), ("sorry", "doc", "def u")])

    def test_unterminated_escape_scans_on(self):
        # Lean rejects this file, but the scanner must not mask the rest.
        source = "def «x : Nat := 1\ntheorem t : False := sorry\n"
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])


class SorryCensusRawSorryAx(unittest.TestCase):
    """`sorry`/`admit` elaborate to the kernel axiom `sorryAx`; naming it
    directly is a hole the plain `sorry|admit` word match would miss."""

    def test_sorryAx_matches_the_hole_token(self):
        match = sorry_census.TOKEN_RE.search("example : False := sorryAx False false")
        self.assertIsNotNone(match)
        assert match is not None
        self.assertEqual(match.group(1), "sorryAx")

    def test_sorryAx_in_live_code_is_a_hole(self):
        self.assertEqual(
            kinds("theorem t : False := sorryAx False false\n"),
            [("sorryAx", "hole", "theorem t")])

    def test_sorryAx_in_comment_or_string_is_doc(self):
        source = (
            "-- prose mentioning sorryAx is not a hole\n"
            "/-- nor is sorryAx in a docstring -/\n"
            'def msg := "sorryAx"\n'
        )
        self.assertEqual(
            [(t, k) for t, k, _ in kinds(source)],
            [("sorryAx", "doc"), ("sorryAx", "doc"), ("sorryAx", "doc")])

    def test_cli_fail_on_holes_rejects_raw_sorryAx(self):
        self.assertEqual(cli_holes("theorem t : False := sorryAx False false\n"), (1, True))


if __name__ == "__main__":
    unittest.main()
