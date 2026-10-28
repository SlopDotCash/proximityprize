"""Provider classification: proposition-shaped explicit binders are hypotheses.

`extra_explicit_binders` decides whether a candidate provider of a residual is
*concrete* or *conditional*, and a conditional reduction is not a proof.  The
motivating defect: `fiatShamir_hvzkTransfer_of_coupling`
(ArkLib/OracleReduction/FiatShamir/HVZKTransferReduction.lean:103) takes
`(coupling : ∀ stmt wit, (stmt, wit) ∈ rel → evalDist … = evalDist …)` — its
docstring says the coupling "is supplied as an explicit hypothesis" — yet the
census recorded the provider with no extra binders, i.e. as an unconditional
discharge of `fiatShamir_hvzkTransferResidual`.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from residual_census import extra_explicit_binders, looks_like_proof_assumption


def is_hypothesis(typ: str) -> bool:
    """`looks_like_proof_assumption` for a single, non-`h`-named binder."""
    return looks_like_proof_assumption(["coupling"], typ)


class PropositionShapedTypes(unittest.TestCase):
    def test_equality_is_propositional(self):
        self.assertTrue(is_hypothesis("evalDist a = evalDist b"))

    def test_membership_is_propositional(self):
        self.assertTrue(is_hypothesis("(stmt, wit) ∈ rel"))

    def test_spaced_comparisons_are_propositional(self):
        self.assertTrue(is_hypothesis("m ≥ 3"))
        self.assertTrue(is_hypothesis("0 < δ"))
        self.assertTrue(is_hypothesis("η ≤ δ"))

    def test_named_argument_is_not_equality(self):
        self.assertFalse(is_hypothesis("GroupRepresentation (p := p) prev target"))

    def test_monadic_bind_is_not_equality(self):
        self.assertFalse(
            is_hypothesis(
                "Backtrack.BacktrackSequence tr state => Backtrack.BacktrackInterpreter tr state"
            )
        )

    def test_mathlib_nonnegative_reals_are_data(self):
        self.assertFalse(is_hypothesis("ProbDist ℝ≥0"))
        self.assertFalse(is_hypothesis("PMF ℝ≥0∞"))

    def test_type_family_is_not_a_proposition(self):
        self.assertFalse(is_hypothesis("ιₛᵢ → Type"))

    def test_subtype_element_is_data(self):
        self.assertFalse(is_hypothesis("{ab : ℕ × ℕ // ab ∈ monoIdx k D}"))


class ExtraExplicitBinders(unittest.TestCase):
    def test_coupling_provider_is_conditional(self):
        # Signature of Reduction.fiatShamir_hvzkTransfer_of_coupling.
        binders = (
            "(init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) "
            "(fsInit : ProbComp τ) "
            "(fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) "
            "(StateT τ ProbComp)) (rel : Set (StmtIn × WitIn)) "
            "(R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) "
            "(coupling : ∀ stmt wit, (stmt, wit) ∈ rel → "
            "evalDist (msgProjFS <$> honestTranscriptDist init impl R s) = "
            "evalDist (honestTranscriptDist fsInit fsImpl R.fiatShamir stmt wit))"
        )
        result = "fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R"
        self.assertEqual(extra_explicit_binders(binders, result), ["coupling"])

    def test_type_family_binders_stay_unflagged(self):
        # OStmtIn/OStmtOut of fiat_shamir_collapse_breakthrough are type
        # families, so that provider remains concrete.
        binders = "(OStmtIn : ιₛᵢ → Type) (OStmtOut : ιₛᵒ → Type)"
        self.assertEqual(extra_explicit_binders(binders, "SomeResidual"), [])

    def test_descriptive_inequality_binder_is_flagged(self):
        # (m_ge_3 : m ≥ 3) in ArkLib/ProofSystem/BatchedFri/QueryRoundProbability.lean.
        binders = "(m_ge_3 : m ≥ 3) (G : Type)"
        self.assertEqual(
            extra_explicit_binders(binders, "FriQuerySoundnessResidual G"),
            ["m_ge_3"],
        )

    def test_hypothesis_mentioned_in_result_is_not_extra(self):
        binders = "(h : p)"
        self.assertEqual(extra_explicit_binders(binders, "q h"), [])

    def test_h_prefixed_hypothesis_still_flagged(self):
        binders = "(hInit : NeverFail init)"
        self.assertEqual(extra_explicit_binders(binders, "SomeResidual"), ["hInit"])

    def test_instance_binders_are_ignored(self):
        binders = "[DecidableEq α] (hx : x ∈ s)"
        self.assertEqual(
            extra_explicit_binders(binders, "SomeResidual α s"), ["hx"]
        )


if __name__ == "__main__":
    unittest.main()
