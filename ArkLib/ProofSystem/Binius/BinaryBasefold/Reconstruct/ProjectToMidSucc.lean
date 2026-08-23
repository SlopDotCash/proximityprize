/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Round-transition recursion for the projected sumcheck polynomial

`projectToMidSumcheckPoly_succ` relates `projectToMidSumcheckPoly` at round `i.succ` to
`projectToNextSumcheckPoly` applied to `projectToMidSumcheckPoly` at round `i.castSucc`,
folding in the verifier challenge `r_i'`.

## CONVENTION (counterexample-backed): the recombination is `Fin.cons r_i' challenges`

`projectToMidSumcheckPoly`/`projectToNextSumcheckPoly` are built on `fixFirstVariablesOfMQP`,
which fixes the **last** variables (survivors on the low indices). Folding in one *more* challenge
fixes the *new last survivor* — variable `ℓ - i - 1`. In the combined `Fin i.succ` challenge vector
that index is position `0`, so the correct recombination is `Fin.cons r_i' challenges`, **not**
`Fin.snoc challenges r_i'` (which would put `r_i'` at the highest variable `ℓ - 1`).

This matches the structured-sumcheck core's `getRoundProverFinalOutput`
(`Fin.cons`, defect-#20 repair) and `RingSwitching.fixFirstVariablesOfMQP_projectToMid_step`
(whose section note in `RingSwitching/Prelude.lean` contains the `Fin.snoc`-is-false
counterexample: `L = ZMod 7`, `ℓ = 3`, `v = 1`).

The `Fin (ℓ - i.succ)` survivor index set of the directly-projected RHS and the
`Fin (ℓ - i.castSucc - 1)` index set of the folded LHS are reconciled by the canonical `finCongr`.

## Obstacle for the `Fin.snoc` call site

The `ReductionLogic.lean:412` / `Steps/Fold.lean:1432` call sites consume a `Fin.snoc`-form
`projectToMidSumcheckPoly_succ`, because `Relations.lean`'s `getFoldProverFinalOutput` and
`foldVerifierStmtOut` accumulate the sumcheck challenges via `Fin.snoc stmtIn.challenges r_i'`.
That `Fin.snoc` form is the FALSE one (see above): the snoc convention is correct for the
front-folding `getMidCodewords`/`iterated_fold` (hence `getMidCodewords_succ` proves a snoc-form
recursion) but WRONG for the end-folding `projectToMidSumcheckPoly`. Closing the call sites requires
changing `getFoldProverFinalOutput`/`foldVerifierStmtOut` in `Relations.lean` from `Fin.snoc` to
`Fin.cons` (an edit to an existing file), after which the cons-form lemma below resolves them.
-/

open MvPolynomial Finset RingSwitching

namespace Sumcheck.Structured

variable {L : Type} [CommRing L]

/-- **Round-transition recursion for the projected sumcheck polynomial (cons form).**

Folding the verifier challenge `r_i'` into the round-`i.castSucc` projected polynomial via
`projectToNextSumcheckPoly` equals directly projecting at round `i.succ` with the challenge vector
extended *at the front* by `Fin.cons r_i' challenges`, up to the canonical survivor reindex
`finCongr : Fin (ℓ - i.succ) ≃ Fin (ℓ - i.castSucc - 1)`.

See the file header for why `Fin.cons` (and not `Fin.snoc`) is the correct recombination. -/
theorem projectToMidSumcheckPoly_succ (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r_i' : L) :
    (projectToNextSumcheckPoly ℓ i
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i').val
      = rename (finCongr (show ℓ - (i.succ : ℕ) = ℓ - i.castSucc - 1 by
          have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
          (projectToMidSumcheckPoly ℓ t m i.succ (Fin.cons r_i' challenges)).val := by
  change fixFirstVariablesOfMQP (ℓ - i.castSucc)
        ⟨1, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges).val (fun _ => r_i')
    = rename (finCongr _) (projectToMidSumcheckPoly ℓ t m i.succ (Fin.cons r_i' challenges)).val
  rw [RingSwitching.fixFirstVariablesOfMQP_projectToMid_step ℓ t m i challenges r_i']

/-- **Round-transition recursion for the projected sumcheck polynomial (unrenamed form).**

This packages `RingSwitching.fixFirstVariablesOfMQP_projectToMid_succ` at the
`projectToNextSumcheckPoly` API level, avoiding repeated unfolding at downstream call sites. -/
theorem projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
    (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToNextSumcheckPoly ℓ i
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' =
      projectToMidSumcheckPoly ℓ t m i.succ (Fin.cons r_i' challenges) := by
  apply Subtype.ext
  dsimp only [projectToNextSumcheckPoly]
  exact RingSwitching.fixFirstVariablesOfMQP_projectToMid_succ (L := L) (ℓ := ℓ)
    (t := t) (m := m) (i := i) (challenges := challenges) (r' := r_i')

end Sumcheck.Structured

#print axioms Sumcheck.Structured.projectToMidSumcheckPoly_succ
#print axioms Sumcheck.Structured.projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
