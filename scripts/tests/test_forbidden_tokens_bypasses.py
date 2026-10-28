"""forbidden_tokens.py must not be bypassed by modifier, comment or paren variants.

Each source below is accepted by Lean 4 and introduces an unproven axiom or a
vacuous `: True` placebo, so the precheck must reject it.
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"


def run_precheck(source: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return subprocess.run([sys.executable, str(SCRIPT), str(path)],
                              capture_output=True, text=True)


DECOY = 'namespace Decoy\ndef True : Prop := False\nend Decoy\n'


class ForbiddenTokenBypasses(unittest.TestCase):
    def assert_rejected(self, source: str, needle: str):
        result = run_precheck(source)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(needle, result.stderr)

    def test_noncomputable_axiom_is_rejected(self):
        self.assert_rejected("private noncomputable axiom fooA : 1 = 2\n",
                             "forbidden custom axiom declaration fooA")

    def test_unsafe_axiom_is_rejected(self):
        self.assert_rejected("unsafe axiom fooB : 1 = 2\n",
                             "forbidden custom axiom declaration fooB")

    def test_bare_noncomputable_axiom_is_rejected(self):
        self.assert_rejected("noncomputable axiom fooN : 1 = 2\n",
                             "forbidden custom axiom declaration fooN")

    def test_partial_axiom_is_rejected(self):
        # Lean v4.30.0-rc2 (repo toolchain) accepts `partial axiom`.
        self.assert_rejected("partial axiom fooP : 1 = 2\n",
                             "forbidden custom axiom declaration fooP")

    def test_nonrec_axiom_is_rejected(self):
        # Lean v4.30.0-rc2 accepts `nonrec axiom` and `#print axioms` lists it.
        self.assert_rejected("nonrec axiom fooR : 1 = 2\n",
                             "forbidden custom axiom declaration fooR")

    def test_protected_axiom_in_namespace_is_rejected(self):
        self.assert_rejected("namespace X\nprotected axiom fooQ : 1 = 2\nend X\n",
                             "forbidden custom axiom declaration fooQ")

    def test_docstring_attribute_and_modifiers_before_axiom_is_rejected(self):
        self.assert_rejected(
            "/-- d -/ @[simp] private noncomputable axiom fooS : 1 = 2\n",
            "forbidden custom axiom declaration fooS")

    def test_comment_separator_after_axiom_is_rejected(self):
        self.assert_rejected("axiom/-c-/fooC : 1 = 2\n",
                             "forbidden custom axiom declaration fooC")

    def test_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem x_residual : (True) := trivial\n",
                             "forbidden vacuous placebo")

    def test_nested_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem y : ((True)) := trivial\n",
                             "forbidden vacuous placebo")

    def test_true_only_conjunction_placebo_is_rejected(self):
        self.assert_rejected("theorem z : True ∧ True := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")

    def test_bracketed_true_only_conjunction_placebo_is_rejected(self):
        self.assert_rejected("theorem w : (True ∧ (True)) := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")

    def test_true_only_implication_and_disjunction_placebos_are_rejected(self):
        self.assert_rejected("theorem v : True → True := id\n", "forbidden vacuous placebo")
        self.assert_rejected("theorem u : True ∨ True := Or.inl trivial\n",
                             "forbidden vacuous placebo")

    def test_true_only_obligation_def_is_rejected(self):
        self.assert_rejected("def foo_residual : Prop := True\n"
                             "abbrev bar_residual : (True ∧ True) := ⟨trivial, trivial⟩\n",
                             "obligation-like name bar_residual")

    def test_axiom_named_in_comment_is_not_flagged(self):
        result = run_precheck("-- noncomputable axiom fooD : 1 = 2\n"
                              "/- unsafe axiom fooE : 1 = 2 -/\n"
                              "theorem real : (1 : Nat) + 1 = 2 := rfl\n"
                              "theorem pair : (True ∧ (1 = 1)) := ⟨trivial, rfl⟩\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


    # --- axioms split across lines / comments (all compile with Lean v4.30.0-rc2
    # and `#print axioms bad` lists the axiom) ---------------------------------
    def test_axiom_name_on_next_line_is_rejected(self):
        self.assert_rejected("axiom\n  unproved : False\ntheorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_axiom_multiline_comment_separator_is_rejected(self):
        self.assert_rejected("axiom/- separator\n-/unproved : False\n"
                             "theorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_axiom_line_comment_then_name_is_rejected(self):
        self.assert_rejected("axiom -- trailing\n\n   unprovedL : False\n",
                             "forbidden custom axiom declaration unprovedL")

    def test_modifiers_and_axiom_split_over_lines_is_rejected(self):
        self.assert_rejected("private\nnoncomputable\naxiom\n/- a -/ /- b -/\n  unprovedM : False\n",
                             "forbidden custom axiom declaration unprovedM")

    def test_guillemet_axiom_name_is_rejected(self):
        self.assert_rejected("axiom «weird name» : False\n",
                             "forbidden custom axiom declaration «weird name»")

    def test_axiom_text_inside_quoted_identifier_is_not_flagged(self):
        # Compiles with Lean v4.30.0-rc2; `#print axioms actual_equality` is empty.
        result = run_precheck("def «an axiom counterfeit» : Nat := 0\n"
                              "theorem actual_equality : «an axiom counterfeit» = 0 := rfl\n"
                              "#print axioms actual_equality\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_quoted_axiom_containing_axiom_text_is_rejected(self):
        result = run_precheck("axiom «an axiom counterfeit» : False\n")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("forbidden custom axiom declaration «an axiom counterfeit»", result.stderr)
        self.assertEqual(result.stderr.count("forbidden custom axiom declaration"), 1,
                         result.stderr)

    def test_guillemets_in_literals_do_not_hide_axioms(self):
        # A `«` in a string or char literal is not an identifier start, so the
        # text up to a later `»` must still be scanned.
        for src in (
            'def s := "«"\naxiom unprovedG : False\ndef t := "»"\n',
            'def s := "«" axiom unprovedG : False def t := "»"\n',
            "def c := '«' axiom unprovedG : False def d := '»'\n",
            'def s := s!"{"«"}" axiom unprovedG : False def t := "»"\n',
        ):
            with self.subTest(src=src):
                self.assert_rejected(src, "forbidden custom axiom declaration unprovedG")

    def test_split_axiom_reports_keyword_line(self):
        result = run_precheck("theorem ok : 1 = 1 := rfl\naxiom\n  unprovedN : False\n")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(":2: forbidden custom axiom declaration unprovedN", result.stderr)

    # --- module-file modifiers: Lean v4.30.0-rc2 accepts exactly `public`,
    # `private`, `protected`, `noncomputable`, `unsafe`, `partial`, `nonrec`,
    # `meta` (and combinations) before `axiom`; `scoped`/`local` do not parse.
    def test_public_axiom_in_module_is_rejected(self):
        self.assert_rejected("module\nimport Init\npublic axiom unproved : False\n"
                             "public theorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_every_accepted_module_modifier_is_rejected(self):
        for mods in ("public", "private", "protected", "noncomputable", "unsafe", "partial",
                     "nonrec", "meta", "public meta", "private meta", "public noncomputable",
                     "public partial", "public nonrec", "public unsafe"):
            with self.subTest(mods=mods):
                self.assert_rejected(
                    f"module\nimport Init\nnamespace X\n{mods} axiom fooMod : False\nend X\n",
                    "forbidden custom axiom declaration fooMod")

    def test_public_true_placebo_is_rejected(self):
        self.assert_rejected("module\nimport Init\npublic theorem p_residual : True := trivial\n",
                             "forbidden vacuous placebo")

    def test_public_obligation_def_is_rejected(self):
        self.assert_rejected("public abbrev q_residual : True ∧ True := ⟨trivial, trivial⟩\n",
                             "obligation-like name q_residual")

    def test_print_axioms_and_identifiers_containing_axiom_are_not_flagged(self):
        result = run_precheck("def axiomCount : Nat := 1\ndef Foo.axiom_ok : Nat := 2\n"
                              "theorem real : (1 : Nat) = 1 := rfl\n#print axioms real\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    # --- `True` rebound locally: these are real propositions (each compiles
    # with Lean v4.30.0-rc2 and `#print axioms` reports no axioms), so they must
    # NOT be flagged as placebos. ---------------------------------------------
    def assert_clean(self, source: str):
        result = run_precheck(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_true_bound_by_binder_is_not_a_placebo(self):
        for src in (
            "theorem identity_prop (True : Prop) : True → True := fun h => h\n",
            "theorem t {True : Prop} : True → True := fun h => h\n",
            "theorem t ⦃True : Prop⦄ : True → True := fun h => h\n",
            "theorem t {{True : Prop}} : True → True := fun h => h\n",
            "theorem t (P True : Prop) : True → True := fun h => h\n",
            "theorem t (True : Prop) (h : True) : True := h\n",
            "theorem t (True : Prop := False) : True → True := fun h => h\n",
            "theorem t (True: Prop): True → True := fun h => h\n",
            "theorem t («True» : Prop) : True → True := fun h => h\n",
            "theorem t\n  (True : Prop) :\n  True → True := fun h => h\n",
            "theorem t (_x : Nat) (True : Prop) : True ∧ True → True := fun h => h.1\n",
            "lemma t (True : Prop) : (True ∧ (True)) → True := fun h => h.1\n",
        ):
            with self.subTest(src=src):
                self.assert_clean(src)

    def test_true_bound_by_variable_is_not_a_placebo(self):
        for src in (
            "variable (True : Prop) in\ntheorem t : True → True := fun h => h\n",
            "section\nvariable (True : Prop)\ntheorem t : True → True := fun h => h\nend\n",
            "section\nvariable {n : Nat}\n  {True : Prop}\ntheorem t : True → True := fun h => h\nend\n",
        ):
            with self.subTest(src=src):
                self.assert_clean(src)

    def test_true_redeclared_in_namespace_is_not_a_placebo(self):
        # Inside `namespace F`, `True` resolves to `F.True` (`#check @F.t` shows
        # `F.True → F.True`).
        self.assert_clean("namespace F\ndef True : Prop := False\n"
                          "theorem t : True → True := fun h => h\nend F\n")

    def test_shadowed_true_obligation_def_is_not_flagged(self):
        self.assert_clean("abbrev foo_residual (True : Prop) : True → True := fun h => h\n")

    def test_builtin_true_still_rejected_next_to_unrelated_binders(self):
        # Binders that merely *use* `True` or have similar names do not rebind it.
        self.assert_rejected("theorem t (h : True) : True := h\n", "forbidden vacuous placebo")
        self.assert_rejected("theorem t (Trueish : Prop) : True ∧ True := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")
        self.assert_rejected("theorem t (x : Nat) {α : Type} : (True) := trivial\n",
                             "forbidden vacuous placebo")
        self.assert_rejected("theorem t (f : True → True) : True → True := f\n",
                             "forbidden vacuous placebo")

    def test_binder_in_other_declaration_does_not_mask_placebo(self):
        self.assert_rejected("theorem a (True : Prop) : True → True := fun h => h\n"
                             "theorem b_residual : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma b_residual")


    # --- Lean lexing and Unicode identifiers (review of 2026-10-14). Every
    # source below was compiled with Lean v4.30.0-rc2 and the stated
    # `#print axioms` result checked. -----------------------------------------
    def test_quoted_identifier_with_apostrophe_is_not_flagged(self):
        # `#print axioms actual_equality`: no axioms.
        self.assert_clean("def «an axiom counterfeit'» : Nat := 0\n"
                          "theorem actual_equality : «an axiom counterfeit'» = 0 := rfl\n")

    def test_quoted_identifiers_with_comment_and_quote_text_are_names(self):
        # `«a -- b»` is one identifier, so the axiom after it is live.
        self.assert_rejected("def «a -- b» : Nat := 0\naxiom afterq : False\n",
                             "forbidden custom axiom declaration afterq")
        self.assert_clean('def «x " y» : Nat := 0\ntheorem t : «x " y» = 0 := rfl\n')

    def test_quoted_axiom_with_apostrophe_is_rejected(self):
        # `#print axioms t` lists `x'`.
        self.assert_rejected("axiom «x'» : False\ntheorem t : False := «x'»\n",
                             "forbidden custom axiom declaration «x'»")

    def test_axiom_inside_unicode_identifier_is_not_flagged(self):
        # `αaxiom` is one identifier; `#print axioms actual_equality`: no axioms.
        self.assert_clean("def αaxiom (_ : Type) : Nat := 0\n"
                          "theorem actual_equality : αaxiom Nat = 0 := rfl\n")
        self.assert_clean("def ωaxiomé : Nat := 0\ndef axiomα : Nat := 1\n")

    def test_true_declared_under_unicode_namespace_is_not_a_placebo(self):
        # `#check @α.t` prints `α.t : α.True → α.True`; no axioms.
        self.assert_clean("def α.True : Prop := False\nnamespace α\n"
                          "theorem t : True → True := fun h => h\nend α\n")
        self.assert_clean("def «my ns».True : Prop := False\nnamespace «my ns»\n"
                          "theorem t : True → True := fun h => h\nend «my ns»\n")

    def test_unicode_axiom_names_are_rejected(self):
        # Each compiles and `#print axioms` lists the axiom.
        for name in ("αbad", "ébad", "𝔽bad", "x.αy", "ℕbad"):
            with self.subTest(name=name):
                self.assert_rejected(f"axiom {name} : False\ntheorem t : False := {name}\n",
                                     f"forbidden custom axiom declaration {name}")

    def test_axiom_directly_followed_by_guillemet_is_rejected(self):
        # `axiom«qbad» : False` compiles; `#print axioms t` lists `qbad`.
        self.assert_rejected("axiom«qbad» : False\ntheorem t : False := qbad\n",
                             "forbidden custom axiom declaration «qbad»")

    def test_unicode_and_quoted_placebos_are_rejected(self):
        # Both compile with no axioms but prove only `True`.
        self.assert_rejected("theorem αt : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma αt")
        self.assert_rejected("theorem «quoted placebo» : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma «quoted placebo»")

    def test_unicode_binder_does_not_rebind_true(self):
        # `(αTrue : Prop)` binds `αTrue`, not `True`.
        self.assert_rejected("theorem t (αTrue : Prop) : True := trivial\n",
                             "forbidden vacuous placebo")

    def test_comment_openers_inside_literals_do_not_hide_axioms(self):
        # Each compiles and `#print axioms` lists the axiom.
        for src in (
            'def s1 : String := "/-"\naxiom strbad : False\ndef s2 : String := "-/"\n',
            'def s1 : String := "--" axiom strbad : False\n',
            'def s1 : String := r#"/-"#\naxiom strbad : False\ndef s2 : String := r#"-/"#\n',
            'def s1 : String := "\\"/-"\naxiom strbad : False\ndef s2 : String := "-/"\n',
            "def c1 : Char := '\"'\naxiom strbad : False\ndef s3 : String := \"\\\"-/\"\n",
        ):
            with self.subTest(src=src):
                self.assert_rejected(src, "forbidden custom axiom declaration strbad")

    def test_comment_inside_interpolation_hole_is_lexed_as_code(self):
        # `s!"{"/-"}"` is one interpolated string; the axiom after it is live.
        self.assert_rejected('def s : String := s!"{"/-"}"\naxiom interpbad : False\n',
                             "forbidden custom axiom declaration interpbad")

    def test_plain_or_interpolated_ambiguity_fails_closed(self):
        # Lean reads this as three plain strings; an interpolated reading of
        # the first would open a comment. The scan refuses to guess.
        self.assert_rejected('def s : String := "{" ++ "/-" ++ "}"\n',
                             "string literal reads differently")
        # Balanced holes / braces without comment openers stay clean.
        self.assert_clean('def s (n : Nat) : String := s!"n = {n}" ++ "{" ++ "}"\n')

    # --- dimx9173 review 5512265055. Every verdict below was checked with
    # `lake env lean` on the same source (Lean 4.30.0-rc2).

    def test_axiom_text_inside_string_literals_is_not_flagged(self):
        # `#eval IO.println "axiom foo"` compiles and prints `axiom foo`.
        self.assert_clean('#eval IO.println "axiom foo"\n')
        self.assert_clean('def s1 : String := r#"axiom bar : False"#\n'
                          'def s2 (n : Nat) : String := s!"axiom {n}"\n'
                          'def s3 : String := "\\ntheorem fooResidual : True := trivial\\naxiom baz : False\\n"\n')
        self.assert_clean('def s4 : String := "\ntheorem fooResidual : True := trivial\naxiom baz : False\n"\n')

    def test_axiom_after_string_literals_is_still_rejected(self):
        self.assert_rejected('def s : String := "x"\naxiom realbad : False\n',
                             "forbidden custom axiom declaration realbad")
        self.assert_rejected('def f (x : Nat) : String := "{" ++ toString x ++ "}"\naxiom hid : False\n',
                             "forbidden custom axiom declaration hid")

    def test_literal_whose_reading_decides_an_axiom_fails_closed(self):
        # Plain: two strings and a live axiom. Interpolated: one string. The
        # scan refuses to guess which one Lean picks.
        self.assert_rejected('def s := f "{" axiom amb : False "}"\n',
                             "string literal reads differently")

    def test_true_declared_in_closed_namespace_does_not_hide_placebo(self):
        # After `end Decoy`, `True` is the builtin (`#print axioms` is clean).
        self.assert_rejected(DECOY + "theorem mcaPrizeResidual : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma mcaPrizeResidual : True`")
        self.assert_rejected(DECOY + "def foo_residual : True := trivial\n",
                             "obligation-like name foo_residual")

    def test_open_or_export_of_true_does_not_hide_placebo(self):
        # Lean rejects each of these with "Ambiguous term True".
        for tail in ("open Decoy\n", "open Decoy in\n", "export Decoy (True)\n",
                     "open Decoy (True)\n"):
            with self.subTest(tail=tail):
                self.assert_rejected(DECOY + tail + "theorem t : True → True := fun h => h\n",
                                     "forbidden vacuous placebo")

    def test_true_scope_follows_nested_namespaces(self):
        # Inside `A`, `A.B.True` is not visible: `A.t : True → True` (builtin).
        self.assert_rejected("namespace A\nnamespace B\ndef True : Prop := False\nend B\n"
                             "theorem t : True → True := fun h => h\nend A\n",
                             "forbidden vacuous placebo")
        # Inside `A.B` it is: `A.B.t : A.B.True → A.B.True`.
        self.assert_clean("namespace A\nnamespace B\ndef True : Prop := False\nend B\nend A\n"
                          "namespace A.B\ntheorem t : True → True := fun h => h\nend A.B\n")
        # `def _root_.D.True` inside `X` declares `D.True`.
        self.assert_clean("namespace X\ndef _root_.D.True : Prop := False\nend X\n"
                          "namespace D\ntheorem t : True → True := fun h => h\nend D\n")

    def test_true_scope_follows_sections_and_mutual(self):
        # A section inside `D` still sees `D.True`.
        self.assert_clean("namespace D\ndef True : Prop := False\nnoncomputable section\n"
                          "theorem t : True → True := fun h => h\nend\nend D\n")
        # `mutual … end` does not close `D`; the placebo before it is builtin.
        self.assert_rejected("mutual\ntheorem a : True := trivial\nend\n"
                             "namespace D\ndef True : Prop := False\nend D\n",
                             "forbidden vacuous placebo `theorem/lemma a : True`")
        # A `variable (True : Prop)` ends with its section.
        self.assert_rejected("section S\nvariable (True : Prop)\nend S\n"
                             "theorem t : True := trivial\n", "forbidden vacuous placebo")
        # An `open` inside a closed section stops applying at `end`.
        self.assert_rejected(DECOY + "section\nopen Decoy\nend\ntheorem t : True := trivial\n",
                             "forbidden vacuous placebo")

    def test_protected_hidden_or_renamed_true_does_not_shadow(self):
        self.assert_rejected("namespace D\nprotected def True : Prop := False\n"
                             "theorem t : True := trivial\nend D\n", "forbidden vacuous placebo")
        self.assert_rejected(DECOY + "open Decoy hiding True\ntheorem t : True := trivial\n",
                             "forbidden vacuous placebo")
        self.assert_rejected(DECOY + "open Decoy renaming True → T\ntheorem t : True := trivial\n",
                             "forbidden vacuous placebo")
        # `private def True` in `D` still shadows inside `D`: `D.True → D.True`.
        self.assert_clean("namespace D\nprivate def True : Prop := False\n"
                          "theorem t : True → True := fun h => h\nend D\n")

    def test_variable_in_covers_only_next_command(self):
        self.assert_rejected("variable (True : Prop) in\ntheorem t : True → True := fun h => h\n"
                             "theorem u : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma u : True`")

    def test_declaration_after_another_command_on_the_same_line(self):
        # Lean's command parser ignores line breaks, so each of these declares
        # a vacuous `True` after another command on the same line.
        self.assert_rejected("def keep : Nat := 1 theorem hidden_residual : True := by trivial\n",
                             "Probe.lean:1: forbidden vacuous placebo "
                             "`theorem/lemma hidden_residual : True`")
        self.assert_rejected("def keep : Nat := 1 def helper_residual : True := trivial\n",
                             "Probe.lean:1: obligation-like name helper_residual")
        self.assert_rejected("namespace Sneaky theorem ns_residual : True := by trivial\n"
                             "end Sneaky\n", "forbidden vacuous placebo `theorem/lemma ns_residual")
        self.assert_rejected("def keep : Nat := 1 opaque hidden_opaque : True\n",
                             "bodyless opaque declaration hidden_opaque")

    def test_mid_line_non_declarations_stay_clean(self):
        # An in-proof `have … : True` and an identifier named `constant` are
        # not declaration heads.
        self.assert_clean("theorem t : 1 = 1 := by have h : True := trivial; rfl\n"
                          "def f : Nat → Nat := fun constant => constant\n")

    def test_unbalanced_scopes_fail_closed(self):
        self.assert_rejected("namespace D\ndef True : Prop := False\nend E\n"
                             "theorem t : True := trivial\n", "forbidden vacuous placebo")


if __name__ == "__main__":
    unittest.main()
