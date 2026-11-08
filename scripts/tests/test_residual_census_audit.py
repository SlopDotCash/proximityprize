"""Regression coverage for the 2026-10-28 residual-census audit (T04/L11).

The census is a syntactic inventory, not a verified completion ledger.  These
tests pin the mechanisms the audit found could label a conditional or
instance-specific result `discharged`:

* the four core-Lean fixtures of the audit's residual-counterexamples.json,
  each of which proves `BadResidual := False` from an assumption (a section
  hypothesis added by `include`, a `[i : Assumed]` instance of a `Prop` class,
  an explicit `(p : False)` binder, and the arrow `False → BadResidual`);
* the L11 LogUp rows, whose only unconditioned providers were `↔` lemmas;
* specialised providers (fixed sizes, an indicator error, a fixed claimed sum,
  an empty trailing protocol) that prove instances, not the residual family;
* mixed parameter scope: a refuted family keeps its proved instances listed.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "residual_census.py"


def _load_census():
    spec = importlib.util.spec_from_file_location("residual_census", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rc = _load_census()

BAD = "def BadResidual : Prop := False\n"
FOO = "def FooResidual (k : Nat) : Prop := True\n"


class CensusCase(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def rows(self, source):
        folder = self.root / "ArkLib"
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "Fixture.lean").write_text(source, encoding="utf-8")
        decls, residuals, _ = rc.collect(self.root)
        rc.find_providers(decls, residuals)
        return {r["name"]: r for r in residuals}

    def row(self, source, name="BadResidual"):
        return self.rows(source)[name]

    def provider(self, source, provider, name="BadResidual"):
        matches = [p for p in self.row(source, name)["providers"] if p["name"] == provider]
        self.assertEqual(len(matches), 1, matches)
        return matches[0]


class AuditFixtures(CensusCase):
    """Each fixture proves the false `BadResidual` from an assumption."""

    def test_section_hypothesis_added_by_include_in(self):
        src = BAD + (
            "section\nvariable (h : BadResidual)\ninclude h in\n"
            "theorem badResidual_holds : BadResidual := h\nend\n"
        )
        row = self.row(src)
        self.assertEqual(row["status"], "open")
        (p,) = row["providers"]
        self.assertEqual(p["verdict"], "conditional")
        self.assertEqual(p["section_hypotheses"], ["h"])
        self.assertEqual(p["conditional_on_residuals"], ["BadResidual"])

    def test_section_wide_include(self):
        src = BAD + (
            "section\nvariable (h : BadResidual)\ninclude h\n"
            "theorem badResidual_holds : BadResidual := h\nend\n"
        )
        self.assertEqual(self.row(src)["status"], "open")

    def test_section_hypothesis_not_included_is_not_assumed(self):
        # Lean adds a section variable to a theorem only when the header names
        # it or `include` does; an unmentioned hypothesis is not a parameter.
        src = FOO + (
            "section\nvariable (k : Nat) (hk : 0 < k)\n"
            "theorem fooResidual_holds : FooResidual k := trivial\nend\n"
        )
        self.assertEqual(self.row(src, "FooResidual")["status"], "discharged")

    def test_proof_typeclass_instance(self):
        src = BAD + (
            "class Assumed : Prop where\n  proof : False\n"
            "theorem badResidual_holds [i : Assumed] : BadResidual := i.proof\n"
        )
        row = self.row(src)
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["providers"][0]["extra_instance_assumptions"], ["Assumed"])

    def test_proof_binder_is_classified_by_type_not_name(self):
        for binder in ("p", "h", "proof", "_p", "_"):
            src = BAD + f"theorem badResidual_holds ({binder} : False) : BadResidual := by assumption\n"
            with self.subTest(binder=binder):
                self.assertEqual(self.row(src)["status"], "open")

    def test_hypothesis_in_result_arrow(self):
        src = BAD + "theorem badResidual_holds : False → BadResidual := fun p => p\n"
        row = self.row(src)
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["providers"][0]["result_premises"], ["False"])

    def test_hypothesis_in_result_binder(self):
        for result in (
            "∀ (p : False), BadResidual",
            "∀ p : False, BadResidual",
            "(p : False) → BadResidual",
        ):
            src = BAD + f"theorem badResidual_holds : {result} := fun p => p\n"
            with self.subTest(result=result):
                self.assertEqual(self.row(src)["status"], "open")

    def test_bounded_quantifier_is_a_premise(self):
        src = FOO + "theorem fooResidual_holds (s : Set Nat) : ∀ k ∈ s, FooResidual k := fun _ _ => trivial\n"
        self.assertEqual(self.row(src, "FooResidual")["status"], "open")


class ConclusionShape(CensusCase):
    def test_name_alone_does_not_make_a_provider(self):
        for result in ("¬¬FooResidual 0", "∃ k, FooResidual k", "FooResidual 0 ∨ True"):
            src = FOO + f"theorem fooResidual_holds : {result} := sorry\n"
            with self.subTest(result=result):
                self.assertNotEqual(self.row(src, "FooResidual")["status"], "discharged")

    def test_residual_inside_a_premise_conjunction_is_not_proved(self):
        src = FOO + "theorem t (k : Nat) : FooResidual k ∧ True → True := fun _ => trivial\n"
        self.assertEqual(self.row(src, "FooResidual")["status"], "open")

    def test_right_conjunct_is_proved(self):
        src = FOO + "theorem t (k : Nat) : True ∧ FooResidual k := ⟨trivial, trivial⟩\n"
        self.assertEqual(self.row(src, "FooResidual")["status"], "discharged")

    def test_binder_body_keeps_its_arrow(self):
        # `R x ∧ ∀ B, R B → c ≤ B`: the `→` belongs to the `∀`, so the first
        # conjunct is a (specialised) conclusion, not a premise.
        src = (
            "def SupplyResidual (k B : Nat) : Prop := True\n"
            "def best (k : Nat) : Nat := k\n"
            "theorem best_is_least (k : Nat) :\n"
            "    SupplyResidual k (best k) ∧ ∀ B, SupplyResidual k B → best k ≤ B := sorry\n"
        )
        row = self.row(src, "SupplyResidual")
        self.assertEqual(row["status"], "instance_only")
        self.assertEqual(row["providers"][0]["specialised_arguments"], ["B := (best k)"])


class LogupEquivalenceRows(CensusCase):
    """L11: four LogUp rows were `discharged` only through `↔` lemmas."""

    def test_split_iff_is_not_a_provider(self):
        src = (
            "def SubPhaseSoundnessResidual (e : Nat) : Prop := True ∧ True\n"
            "def OuterSoundnessResidual : Prop := True\n"
            "def SumcheckSoundnessResidual (e : Nat) : Prop := True\n"
            "theorem subPhaseSoundnessResidual_iff_split (e : Nat) :\n"
            "    SubPhaseSoundnessResidual e ↔\n"
            "      OuterSoundnessResidual ∧ SumcheckSoundnessResidual e := Iff.rfl\n"
        )
        row = self.row(src, "SubPhaseSoundnessResidual")
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["providers"][0]["verdict"], "not_provider")
        self.assertTrue(row["providers"][0]["equivalence"])

    def test_existential_iff_is_not_a_provider(self):
        src = (
            "def SubPhaseCompletenessResidual : Prop := True ∧ True\n"
            "def AppendCompletenessResidual (h₁ h₂ : True) : Prop := True\n"
            "def LogupCompletenessBrickResidual : Prop := True\n"
            "theorem logupCompletenessBrickResidual_iff_subPhase_append :\n"
            "    LogupCompletenessBrickResidual ↔\n"
            "      ∃ hSub : SubPhaseCompletenessResidual,\n"
            "        AppendCompletenessResidual hSub.1 hSub.2 := sorry\n"
        )
        self.assertEqual(self.row(src, "LogupCompletenessBrickResidual")["status"], "open")

    def test_restricted_discharger_is_conditional(self):
        # Shape of `subPhaseSoundnessResidual_holds`: real, but restricted.
        src = (
            "def SubPhaseSoundnessResidual (n q : Nat) : Prop := True\n"
            "theorem subPhaseSoundnessResidual_holds (n q : Nat) (hn : 0 < n)\n"
            "    (hpole : 2 ^ n < q) : SubPhaseSoundnessResidual n q := trivial\n"
        )
        row = self.row(src, "SubPhaseSoundnessResidual")
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["providers"][0]["extra_explicit_binders"], ["hn", "hpole"])


class InstanceScope(CensusCase):
    """L11: specialised providers prove instances, not the residual family."""

    def test_fixed_size_arguments(self):
        src = (
            "def FirstMomentResidual (n : Nat) (δ : Nat) (B_T b : Int) : Prop := True\n"
            "theorem firstMoment_inTree_card (n δ : Nat) :\n"
            "    FirstMomentResidual n δ ((2 ^ n : Nat) : Int) (n : Int) := trivial\n"
        )
        row = self.row(src, "FirstMomentResidual")
        self.assertEqual(row["status"], "instance_only")
        self.assertEqual(
            row["providers"][0]["specialised_arguments"],
            ["B_T := ((2 ^ n : Nat) : Int)", "b := (n : Int)"],
        )

    def test_indicator_error(self):
        src = (
            "def RbrSoundnessResidual (M : Nat) (ε : Fin 3 → Nat) : Prop := True\n"
            "theorem rbr_indicator (M : Nat) :\n"
            "    RbrSoundnessResidual M (fun i => if i = 0 then 1 else 0) := trivial\n"
        )
        self.assertEqual(self.row(src, "RbrSoundnessResidual")["status"], "instance_only")

    def test_fixed_claimed_sum(self):
        src = (
            "def BatchingConsistencyResidual (A t : Nat → Nat) (s0 : Nat) : Prop := True\n"
            "theorem batchingConsistencyResidual_sum (A t : Nat → Nat) :\n"
            "    BatchingConsistencyResidual A t (A 0 * t 0 + A 1 * t 1) := trivial\n"
        )
        self.assertEqual(self.row(src, "BatchingConsistencyResidual")["status"], "instance_only")

    def test_repeated_bound_name(self):
        src = (
            "def TransferResidual (srInit fsInit : Nat) : Prop := True\n"
            "theorem transfer_canonical (srInit : Nat) : TransferResidual srInit srInit := trivial\n"
        )
        row = self.row(src, "TransferResidual")
        self.assertEqual(row["status"], "instance_only")
        self.assertEqual(
            row["providers"][0]["specialised_arguments"], ["fsInit := srInit (same as srInit)"]
        )

    def test_literal_parameter_type(self):
        # Empty trailing protocol: the provider's section variable fixes the
        # length parameter that the residual leaves free.
        src = (
            "section\nvariable {n : Nat} (v : Fin (n + 1))\n"
            "def RunRightResidual : Prop := v = v\nend\n"
            "section\nvariable (v : Fin (0 + 1))\n"
            "theorem runRightResidual_holds_empty : RunRightResidual v := rfl\nend\n"
        )
        row = self.row(src, "RunRightResidual")
        self.assertEqual(row["status"], "instance_only")
        self.assertEqual(
            row["providers"][0]["specialised_parameter_types"], ["v : Fin (0 + 1)"]
        )

    def test_numeral_named_argument(self):
        src = (
            "def ZeroResidual {k : Nat} : Prop := 0 < k → False\n"
            "theorem zeroResidual_zero : ZeroResidual (k := 0) := by intro h; omega\n"
        )
        self.assertEqual(self.row(src, "ZeroResidual")["status"], "instance_only")

    def test_uniform_section_provider_discharges(self):
        src = (
            "section\nvariable (a b : Nat)\n"
            "def PairResidual : Prop := a = a ∧ b = b\n"
            "theorem pairResidual_holds : PairResidual a b := ⟨rfl, rfl⟩\nend\n"
        )
        self.assertEqual(self.row(src, "PairResidual")["status"], "discharged")


class InstanceAssumptions(CensusCase):
    def test_extra_fact_instance_is_conditional(self):
        src = (
            "def PrimeResidual (p : Nat) : Prop := True\n"
            "theorem primeResidual_holds (p : Nat) [Fact (Nat.Prime p)] : PrimeResidual p := trivial\n"
        )
        row = self.row(src, "PrimeResidual")
        self.assertEqual(row["status"], "open")
        self.assertEqual(
            row["providers"][0]["extra_instance_assumptions"], ["Fact (Nat.Prime p)"]
        )

    def test_shared_section_instance_is_not_extra(self):
        src = (
            "variable (p : Nat) [Fact (Nat.Prime p)]\n"
            "def PrimeResidual : Prop := p = p\n"
            "theorem primeResidual_holds : PrimeResidual p := rfl\n"
        )
        self.assertEqual(self.row(src, "PrimeResidual")["status"], "discharged")

    def test_omitted_section_instance_is_not_included(self):
        src = (
            "def PrimeResidual (p : Nat) : Prop := True\n"
            "section\nvariable (p : Nat) [Fact (Nat.Prime p)]\n"
            "omit [Fact (Nat.Prime p)] in\n"
            "theorem primeResidual_holds : PrimeResidual p := trivial\nend\n"
        )
        self.assertEqual(self.row(src, "PrimeResidual")["status"], "discharged")

    def test_decidable_equality_does_not_restrict(self):
        src = (
            "def TypeResidual (α : Type) : Prop := True\n"
            "theorem typeResidual_holds (α : Type) [DecidableEq α] : TypeResidual α := trivial\n"
        )
        self.assertEqual(self.row(src, "TypeResidual")["status"], "discharged")

    def test_finite_type_instance_restricts(self):
        src = (
            "def TypeResidual (α : Type) : Prop := True\n"
            "theorem typeResidual_holds (α : Type) [Fintype α] : TypeResidual α := trivial\n"
        )
        self.assertEqual(self.row(src, "TypeResidual")["status"], "open")

    def test_renamed_type_variable_still_matches(self):
        src = (
            "def TypeResidual (ι : Type) [Fintype ι] : Prop := True\n"
            "theorem typeResidual_holds (κ : Type) [Fintype κ] : TypeResidual κ := trivial\n"
        )
        self.assertEqual(self.row(src, "TypeResidual")["status"], "discharged")


class Refutations(CensusCase):
    def test_mixed_scope_keeps_proved_instances(self):
        src = (
            "def ZeroResidual (k : Nat) : Prop := 0 < k → False\n"
            "theorem zeroResidual_zero : ZeroResidual 0 := by intro h; omega\n"
            "theorem not_zeroResidual : ¬ ZeroResidual 1 := fun h => h (by omega)\n"
        )
        row = self.row(src, "ZeroResidual")
        self.assertEqual(row["status"], "refuted")
        self.assertEqual(row["providers"][0]["verdict"], "instance")
        self.assertEqual(row["refutations"][0]["refuted_arguments"], ["k := 1"])
        lines = rc.markdown_for_status([row], "refuted")
        self.assertIn("proved instances", lines[2])
        self.assertIn("not_zeroResidual", lines[2])

    def test_refutation_with_hypothesis_does_not_count(self):
        src = FOO + "theorem not_foo (h : False) : ¬ FooResidual 1 := h.elim\n"
        row = self.row(src, "FooResidual")
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["refutations"][0]["verdict"], "conditional")

    def test_negated_conjunction_is_not_a_refutation(self):
        src = FOO + "theorem not_foo_and : ¬ (FooResidual 1 ∧ False) := fun h => h.2\n"
        self.assertEqual(self.row(src, "FooResidual")["status"], "open")


class Reporting(CensusCase):
    def run_cli(self, source, wiki_text=None):
        (self.root / "ArkLib").mkdir(parents=True, exist_ok=True)
        (self.root / "ArkLib" / "Fixture.lean").write_text(source, encoding="utf-8")
        wiki = self.root / "wiki.md"
        if wiki_text is not None:
            wiki.write_text(wiki_text, encoding="utf-8")
        out = self.root / "census.json"
        subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), "--out", str(out),
             "--wiki-out", str(wiki)],
            check=True,
            capture_output=True,
            text=True,
        )
        return json.loads(out.read_text(encoding="utf-8")), wiki.read_text(encoding="utf-8")

    def test_outputs_declare_scope_and_method(self):
        payload, wiki = self.run_cli(FOO + "theorem t (k : Nat) : FooResidual k := trivial\n")
        self.assertEqual(payload["metadata"]["scope"],
                         "ArkLib/**/*.lean and ProximityPrize/**/*.lean only")
        self.assertEqual(payload["metadata"]["kind"], "syntactic inventory")
        self.assertEqual(payload["summary"]["discharged"], 1)
        self.assertIn("instance_only", payload["summary"])
        self.assertIn("Only `ArkLib/**/*.lean` and `ProximityPrize/**/*.lean`", wiki)
        self.assertIn("never elaborates", wiki)
        self.assertIn("**Instance-only:** 0", wiki)
        self.assertNotIn("concrete provider", wiki)

    def test_preserved_addenda_are_marked_historical(self):
        old = (
            "# old ledger\n\n"
            "> **Campaign addendum — snapshot (2000-01-01).** The census contained 7 residuals.\n"
            "\n## Summary\n"
        )
        _payload, wiki = self.run_cli(FOO, old)
        note = wiki.index("none of them is the current generated")
        block = wiki.index("> **Campaign addendum — snapshot (2000-01-01).**")
        summary = wiki.index("## Summary")
        self.assertLess(note, block)
        self.assertLess(block, summary)


if __name__ == "__main__":
    unittest.main()
