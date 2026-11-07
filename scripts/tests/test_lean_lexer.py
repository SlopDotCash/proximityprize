"""The proof gates share one Lean lexer (repository audit 2026-10-28, T01).

`scripts/forbidden_tokens.py` (CI gate 1), `scripts/sorry_census.py` (CI gate 2)
and `scripts/check-research-boundary.py` decide what is live code with
`scripts/lean_lexer.py`. Every `HIDDEN` template below is valid Lean: Lean
v4.30.0-rc2 compiles both of its variants and `#print axioms` lists the hidden
axiom or `sorryAx` (set LEAN_TEST_EXECUTABLE to a Lean binary to re-check).
Each one hid its forbidden declaration from an earlier scanner, which read a
literal as a comment opener or a comment as unterminated. Each `DATA` fixture
mentions forbidden words only inside comments or literal text and must pass
both gates. A lexical scan is still not an elaborated declaration or axiom
audit.
"""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import forbidden_tokens  # noqa: E402
import lean_lexer  # noqa: E402
import sorry_census  # noqa: E402

_spec = importlib.util.spec_from_file_location("boundary", SCRIPTS / "check-research-boundary.py")
boundary = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(boundary)

LEAN = os.environ.get("LEAN_TEST_EXECUTABLE")
AXIOM = "axiom hiddenAxiom : False"
SORRY = "theorem hiddenSorry : False := sorry"

SCIENTIFIC_SYNTAX = (
    "syntax \"fooSci\" scientific str : command\n"
    "macro_rules | `(fooSci $_n $s) => `(#eval $s)\n"
)
CHAR_SYNTAX = (
    "syntax \"fooChar\" num char : command\n"
    "macro_rules | `(fooChar $_n $c) => `(#eval $c)\n"
)

# `{decl}` is replaced by AXIOM (forbidden-token precheck) or SORRY (census).
HIDDEN = {
    # The audit's fixture: the string `"/-"` is not a comment opener.
    "comment_opener_in_string": 'def marker : String := "/-"\n{decl}\n',
    "line_comment_in_string": 'def s : String := "--" {decl}\n',
    "escaped_quote": 'def s : String := "\\"/-"\n{decl}\ndef t : String := "-/"\n',
    "raw_string": 'def s : String := r#"/-"#\n{decl}\ndef t : String := r#"-/"#\n',
    # A number ends its token: `1e5r#"…"#` is a scientific literal and a raw
    # string, `1'"'` a number and a character literal (checked with `syntax`).
    "raw_string_after_scientific": SCIENTIFIC_SYNTAX + 'fooSci 1e5r#"""#\n{decl}\n'
                                   'def t : String := "x"\n',
    "char_after_number": CHAR_SYNTAX + "fooChar 1'\"'\n{decl}\ndef t : String := \"x\"\n",
    # A doc comment's body starts after `/--`, so `/--/` does not close it.
    "doc_comment_slash": '/--/ " -/\n{decl}\ndef x : String := "y"\n',
    # Strings inside real comments are comment text.
    "quote_in_block_comment": '/- " -/\n{decl}\ndef t : String := "x"\n',
    "quote_in_line_comment": '-- "\n{decl}\ndef t : String := "x"\n',
    "quote_in_nested_comment": '/- a /- b -/ " -/\n{decl}\ndef t : String := "x"\n',
    "slash_nesting_in_comment": '/- a /-/ b -/ " -/\n{decl}\ndef t : String := "x"\n',
}

# The forbidden words occur only in comments or literal text.
DATA = {
    "eval_string": '#eval IO.println "axiom foo : False"\n',
    "plain_string": 'def s : String := "theorem t : False := sorry"\n',
    "raw_string": 'def s : String := r#"sorry axiom native_decide run_cmd"#\n',
    "escaped_string": 'def s : String := "\\"axiom x : False\\" -- sorry"\n',
    "token_words": 'def s : String := "implemented_by unsafeCast bv_decide addDecl"\n',
    "comments": "-- axiom foo : False, sorry, native_decide\n/- run_cmd addDecl -/\n"
                "theorem ok : 1 = 1 := rfl\n",
    "doc_comment": "/-- mentions `sorry`, `axiom bad : False` and `decide +native` -/\n"
                   "theorem ok : 2 = 2 := rfl\n",
    "primes_and_chars": "def c : Char := 'a'\ndef x' : Nat := 1\n"
                        "def s : String := \"x' -- sorry\"\n",
}


def write_root(source: str) -> tempfile.TemporaryDirectory:
    tmp = tempfile.TemporaryDirectory()
    root = Path(tmp.name)
    (root / "ArkLib").mkdir()
    (root / "ArkLib" / "Probe.lean").write_text(source, encoding="utf-8")
    (root / "residual_axioms.txt").write_text("", encoding="utf-8")
    return tmp


def precheck(source: str) -> subprocess.CompletedProcess:
    """Run the forbidden-token precheck on `source` with an empty residual manifest."""
    with write_root(source) as directory:
        root = Path(directory)
        return subprocess.run(
            [sys.executable, str(SCRIPTS / "forbidden_tokens.py"), "--root", str(root),
             "--allowlist", str(root / "residual_axioms.txt"), str(root / "ArkLib")],
            capture_output=True, text=True, encoding="utf-8",
            env={**os.environ, "PYTHONIOENCODING": "utf-8"})


def census_gate(source: str) -> tuple[int, int]:
    """(live holes, exit code) of `sorry_census.py --fail-on-holes` on `source`."""
    with write_root(source) as directory:
        root = Path(directory)
        out = root / "census.json"
        proc = subprocess.run(
            [sys.executable, str(SCRIPTS / "sorry_census.py"), "--root", str(root),
             "--fail-on-holes", "--baseline", str(root / "missing.json"), "--out", str(out)],
            capture_output=True, text=True)
        return json.loads(out.read_text())["summary"]["holes"], proc.returncode


class HiddenDeclarations(unittest.TestCase):
    def test_precheck_sees_each_hidden_axiom(self):
        for name, template in HIDDEN.items():
            with self.subTest(name=name):
                result = precheck(template.format(decl=AXIOM))
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden custom axiom declaration hiddenAxiom", result.stderr)

    def test_census_sees_each_hidden_sorry(self):
        for name, template in HIDDEN.items():
            with self.subTest(name=name):
                self.assertEqual(census_gate(template.format(decl=SORRY)), (1, 1))

    def test_audit_fixture_fails_both_gates(self):
        # tooling-counterexamples.json, case `comment_in_string`.
        source = ('def marker : String := "/-"\naxiom fabricated : False\n'
                  'theorem omitted : False := by sorry\n')
        result = precheck(source)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("forbidden custom axiom declaration fabricated", result.stderr)
        self.assertEqual(census_gate(source), (1, 1))


# Readings of plain/interpolated literals. `dbg_trace` parses its string with
# `interpolatedStr(term)`, so the hole holds the character literal `'"'`.
MIXED_AXIOM = (
    "def a : IO Unit := do\n"
    "  dbg_trace \"{'\"'}\"; pure ()\n"
    "  dbg_trace \"{'\"'}\"; pure ()\n"
    "axiom doubleFlipHidden : False\n"
    "def b : String := \"x\"\n"
)
# Live only when the first literal is interpolated and the second is plain:
# both uniform readings hide it.
MIXED_SORRY = (
    "def t : IO Unit := do\n"
    "  dbg_trace \"{'\"'}\"; pure ()\n"
    "  IO.println (\"{\" ++ toString (sorry : Nat) ++ \"}\")\n"
)
NATIVE_IN_HOLE = (
    'def s : String := s!"{(fun (_ : 2 ^ 10 = 1024) => (0 : Nat)) (by decide +native)}"\n'
)


class StringReadings(unittest.TestCase):
    def test_axiom_hidden_by_two_misread_literals_is_rejected(self):
        result = precheck(MIXED_AXIOM)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("doubleFlipHidden", result.stderr)

    def test_sorry_live_only_in_a_mixed_reading_is_a_hole(self):
        self.assertEqual(census_gate(MIXED_SORRY), (1, 1))

    def test_native_evaluation_inside_a_hole_is_rejected(self):
        result = precheck(NATIVE_IN_HOLE)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("forbidden native evaluation", result.stderr)

    def test_unambiguous_literals_have_one_reading(self):
        readings, exhausted = lean_lexer.explore('def s (n : Nat) := s!"n = {n}" ++ "}"\n')
        self.assertEqual((len(readings), exhausted), (1, False))

    def test_too_many_readings_fail_closed(self):
        source = "".join(f'def a{i} : String := "{{" ++ "}}"\n' for i in range(7))
        source += "-- sorry\n"
        readings, exhausted = lean_lexer.explore(source)
        self.assertTrue(exhausted)
        self.assertEqual(len(readings), lean_lexer.DEFAULT_BUDGET)
        result = precheck(source)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("readings of its ambiguous", result.stderr)
        self.assertEqual(census_gate(source), (1, 1))


class DataOnly(unittest.TestCase):
    def test_words_in_strings_and_comments_pass_both_gates(self):
        for name, source in DATA.items():
            with self.subTest(name=name):
                result = precheck(source)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(census_gate(source), (0, 0))


class Tokens(unittest.TestCase):
    """Literal boundaries depend on Lean's tokens, not on single characters."""

    def kinds(self, source: str) -> str:
        reading = lean_lexer.lex(source)
        return "".join("cCL"[k] for k in reading.kind)

    def test_identifier_number_and_literal_tokens(self):
        cases = {
            # identifier `x'`, then a string
            "x'\"a\"": "ccLLL",
            # number `1`, then the character literal `'"'`
            "1'\"'": "cLLL",
            # identifier `foor`, then a string; `r` alone opens a raw string
            "foor\"a\" r\"b\"": "ccccLLLcLLLL",
            # a number before `r` ends its token
            "0x1r\"u\"": "cccLLLL",
            # a quoted identifier may contain `--` and `"`
            "«a -- \"» --c": "cccccccccCCC",
            # `''` is not a character literal
            "f '' s": "cccccc",
        }
        for source, expected in cases.items():
            with self.subTest(source=source):
                self.assertEqual(self.kinds(source), expected)

    def test_doc_comment_body_starts_after_its_opener(self):
        self.assertEqual(self.kinds('/--/ " -/x'), "C" * 9 + "c")
        # Inside a comment body `/-/` nests; right after the opener it does not.
        self.assertEqual(self.kinds("/- /-/ a -/ -/x"), "C" * 14 + "c")
        self.assertEqual(self.kinds("/-/ a -/ -/x"), "C" * 8 + "cccc")

    def test_gates_share_the_lexer(self):
        self.assertIs(forbidden_tokens.lean_lexer, lean_lexer)
        self.assertIs(sorry_census.lean_lexer, lean_lexer)
        self.assertIs(boundary.lean_lexer, lean_lexer)


class ResearchBoundary(unittest.TestCase):
    def test_import_text_in_a_string_is_not_an_import(self):
        self.assertEqual(boundary.research_imports(
            'def s : String := "\nimport Research.Hidden\n"\n'), [])

    def test_quote_in_a_comment_does_not_hide_an_import(self):
        self.assertEqual(boundary.research_imports(
            '/- " -/\nimport Research.Visible\n-- "\nimport Research.Other\n'),
            [(2, "Research.Visible"), (4, "Research.Other")])

    def test_doc_comment_slash_does_not_hide_an_import(self):
        self.assertEqual(boundary.research_imports('/--/ " -/\nimport Research.X\n'),
                         [(2, "Research.X")])


@unittest.skipUnless(LEAN, "set LEAN_TEST_EXECUTABLE to the pinned Lean binary")
class KernelChecked(unittest.TestCase):
    """The fixtures are real Lean: the hidden declarations elaborate."""

    def compile(self, source: str) -> str:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Probe.lean"
            path.write_text(source, encoding="utf-8")
            proc = subprocess.run([LEAN, str(path)], capture_output=True, text=True,
                                  timeout=120)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            return proc.stdout

    def test_hidden_templates_compile_with_their_declaration(self):
        for name, template in HIDDEN.items():
            with self.subTest(name=name, variant="axiom"):
                out = self.compile(template.format(decl=AXIOM)
                                   + "theorem usesIt : False := hiddenAxiom\n"
                                     "#print axioms usesIt\n")
                self.assertIn("depends on axioms: [hiddenAxiom]", out)
            with self.subTest(name=name, variant="sorry"):
                out = self.compile(template.format(decl=SORRY) + "#print axioms hiddenSorry\n")
                self.assertIn("sorryAx", out)

    def test_reading_fixtures_compile(self):
        out = self.compile(MIXED_AXIOM + "theorem usesIt : False := doubleFlipHidden\n"
                                         "#print axioms usesIt\n")
        self.assertIn("[doubleFlipHidden]", out)
        self.assertIn("sorryAx", self.compile(MIXED_SORRY + "#print axioms t\n"))
        self.assertIn("_native", self.compile(NATIVE_IN_HOLE + "#print axioms s\n"))

    def test_data_fixtures_compile(self):
        for name, source in DATA.items():
            with self.subTest(name=name):
                self.compile(source)


if __name__ == "__main__":
    unittest.main()
