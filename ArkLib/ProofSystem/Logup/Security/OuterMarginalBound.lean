/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.MarginalBound
import ArkLib.ProofSystem.Logup.Security.OuterSoundnessSharp

/-!
# LogUp outer run-marginal: the measure core, discharged in plug-in form (issue #13)

The remaining gap of the (sharp-language) outer-soundness obligation `hOuter` was the
"run-marginal": bounding the outer game's bad-accept probability by the uniform-challenge marginal
of the claim language.  This file discharges its **entire measure-theoretic content**:

`outer_bad_accept_le_outerSoundnessError_sharp` — for *any* decomposition of the outer soundness
game as `mx >>= k` around the outer challenge draw, where

* `hunif` — the drawn challenge's output distribution is dominated by the uniform one (true for
  the uniform challenge oracle: the draw *is* `$ᵖ F`, and remains uniformly dominated after the
  preceding prover/state stages by `probEvent_bind_le_of_forall_support`-style peeling);
* `hsupp` — acceptance into the (sharp) claim language pins the drawn challenge into
  `midSoundnessLanguageSharp oStmt` (the support-level consequence of the proven verifier closed
  form `simulateQ_outerVerify_eq` and the membership collapse
  `mem_midSoundnessProtocolLanguageSharp_iff`: every surviving run output carries
  `xChallenge = the drawn x`, so the event forces `x ∈ L`);

the game's bad-accept probability is bounded by `outerSoundnessError F n M params` outright,
for a bad lookup over a field with `2ⁿ < |F|`.

What remains of `hOuter` after this file is **purely syntactic**: unfolding
`Reduction.run (outerOracleReduction …)` for an arbitrary malicious prover into the
`mx >>= k` shape around the round-1 challenge query and reading off the two side conditions
(`hunif` from the challenge oracle's uniformity, `hsupp` from the verifier closed form).
No measure theory, Schwartz–Zippel, degree counting, or error arithmetic is left.
-/

open scoped ENNReal NNReal
open Polynomial Finset

universe v

namespace Logup

section OuterMarginalBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
  {params : ProtocolParams M}

/-- **The outer run-marginal, discharged at the sharp language (measure core of `hOuter`).**

For any two-stage decomposition `mx >>= k` of the outer soundness game around the challenge draw
— with the drawn value uniformly dominated and the event supported inside the sharp claim
language through the drawn value — the bad-accept probability is at most the paper-shaped
`outerSoundnessError`. -/
theorem outer_bad_accept_le_outerSoundnessError_sharp
    {β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hcard : 2 ^ n < Fintype.card F)
    (mx : m F) (k : F → m β) (q : β → Prop)
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ x : F, x ∉ midSoundnessLanguageSharp oStmt → Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k] ≤ (outerSoundnessError F n M params : ℝ≥0∞) := by
  classical
  refine le_trans
    (probEvent_bind_le_prob_uniform mx k q (midSoundnessLanguageSharp oStmt) hunif hsupp) ?_
  exact outerSoundness_sharp_le_outerSoundnessError (params := params) stmt oStmt hBad hcard

/-- **The outer run-marginal, comap form (measure core of `hOuter`, carried-challenge shape).**

The variant of `outer_bad_accept_le_outerSoundnessError_sharp` matching the shape produced by
decomposing the outer run around the round-1 challenge query: the first stage outputs a state
*carrying* the drawn challenge (extracted by `f`), rather than the bare challenge. -/
theorem outer_bad_accept_le_outerSoundnessError_sharp_comap
    {α β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hcard : 2 ^ n < Fintype.card F)
    (mx : m α) (f : α → F) (k : α → m β) (q : β → Prop)
    (hunif : ∀ x : F, Pr[ fun a => f a = x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ a : α, f a ∉ midSoundnessLanguageSharp oStmt → Pr[ q | k a] = 0) :
    Pr[ q | mx >>= k] ≤ (outerSoundnessError F n M params : ℝ≥0∞) := by
  classical
  refine le_trans
    (probEvent_bind_le_prob_uniform_comap mx f k q (midSoundnessLanguageSharp oStmt)
      hunif hsupp) ?_
  exact outerSoundness_sharp_le_outerSoundnessError (params := params) stmt oStmt hBad hcard

end OuterMarginalBound

end Logup

/-! ### Axiom audit (issue #13 outer run-marginal measure core) -/

#print axioms Logup.outer_bad_accept_le_outerSoundnessError_sharp
#print axioms Logup.outer_bad_accept_le_outerSoundnessError_sharp_comap
