/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.LogupGrandSumIdentity

/-!
# LogUp SZ soundness — the `hTotalDeg` residual, discharged (issue #13)

`Logup.Issue13Scratch.logup_SZ_soundness` (`LogupGrandSumIdentity.lean`) is the Schwartz–Zippel
core of the outer LogUp soundness route. Its module notes record that, with the per-variable
degree analysis (`logupQPolynomial_degreeOf`) fully in-tree, *"the only genuine residual in
`logup_SZ_soundness` is the `totalDegree` aggregation `hTotalDeg`"* —
`Q.totalDegree ≤ n·(M+3)`.

This file discharges that residual:

* `MvPolynomial.totalDegree_le_sum_degreeOf` — the generic aggregation
  `totalDegree p ≤ ∑ᵢ degreeOf i p` over finitely many variables (not in current Mathlib;
  upstreamable);
* `Logup.logupQPolynomial_totalDegree_le` — `Q.totalDegree ≤ n·(M+3)` from the proven
  per-variable bound;
* `Logup.logup_SZ_soundness_unconditional` — `logup_SZ_soundness` with `hTotalDeg` supplied,
  leaving `hQ_ne` (the grand-sum nonvanishing, i.e. the actual soundness content) as the sole
  remaining input.

All axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators NNReal ENNReal
open ProbabilityTheory

namespace MvPolynomial

/-- **Total degree is at most the sum of the per-variable degrees** (finitely many variables):
each monomial exponent vector `s` satisfies `s i ≤ degreeOf i p` coordinatewise, so its total
degree `∑ᵢ s i` is at most `∑ᵢ degreeOf i p`. -/
theorem totalDegree_le_sum_degreeOf {σ R : Type*} [CommSemiring R] [Fintype σ]
    (p : MvPolynomial σ R) :
    p.totalDegree ≤ ∑ i, p.degreeOf i := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [Finsupp.sum_fintype]
  · exact Finset.sum_le_sum fun i _ => MvPolynomial.monomial_le_degreeOf i hs
  · intro a; rfl

end MvPolynomial

namespace Logup

variable {F : Type} [Field F] {n M : ℕ} (params : ProtocolParams M)

/-- The `hTotalDeg` residual of `logup_SZ_soundness`, discharged:
`Q.totalDegree ≤ n·(M+3)` by aggregating the proven per-variable bound
`logupQPolynomial_degreeOf` over the `n` variables. -/
theorem logupQPolynomial_totalDegree_le
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    (logupQPolynomial F n M params stmt oStmt).totalDegree ≤ n * (M + 3) := by
  classical
  calc (logupQPolynomial F n M params stmt oStmt).totalDegree
      ≤ ∑ i : Fin n, (logupQPolynomial F n M params stmt oStmt).degreeOf i :=
        MvPolynomial.totalDegree_le_sum_degreeOf _
    _ ≤ ∑ _i : Fin n, (M + 3) :=
        Finset.sum_le_sum fun i _ => logupQPolynomial_degreeOf F n M params stmt oStmt i
    _ = n * (M + 3) := by
        simp [Finset.sum_const, Finset.card_univ]

/-- `logup_SZ_soundness` with its sole genuine residual (`hTotalDeg`) discharged in-tree.
The remaining input `hQ_ne` is the grand-sum nonvanishing — the actual soundness content
(an invalid LogUp input makes `Q ≠ 0`), supplied by the outer-soundness route. -/
theorem logup_SZ_soundness_unconditional
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (hQ_ne : logupQPolynomial F n M params stmt oStmt ≠ 0)
    (S : Fin n → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
    (m : ℕ) (hm_pos : 0 < m) (hm : ∀ i, m ≤ (S i).toFinset.card) :
    Pr_{ let x ←$ᵖ (∀ i, ↥(S i)) }[
        MvPolynomial.eval (fun i => (↑(x i) : F)) (logupQPolynomial F n M params stmt oStmt) = 0 ]
      ≤ ((n * (M + 3) : ℕ) : ℝ≥0∞) / m := by
  letI : DecidableEq F := Classical.decEq F
  exact Issue13Scratch.logup_SZ_soundness params stmt oStmt hQ_ne
    (logupQPolynomial_totalDegree_le params stmt oStmt) S m hm_pos hm

end Logup

-- Axiom audit.
#print axioms MvPolynomial.totalDegree_le_sum_degreeOf
#print axioms Logup.logupQPolynomial_totalDegree_le
#print axioms Logup.logup_SZ_soundness_unconditional
