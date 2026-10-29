/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-!
# Round-transition recursion for the projected sumcheck polynomial

The canonical sumcheck fixes a prefix of variables. Both recursion wrappers therefore append
the next verifier challenge with `Fin.snoc`, and delegate to `fixPrefix_initial_succ`.
The coordinate-renamed variant retains its historical cast surface for downstream clients.
-/

open MvPolynomial Finset RingSwitching

namespace Sumcheck.Structured

variable {L : Type} [CommRing L]

/-- Projecting the next prefix challenge agrees with directly projecting the longer prefix,
up to the historical explicit survivor reindex. -/
theorem projectToMidSumcheckPoly_succ (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r_i' : L) :
    (projectToNextSumcheckPoly ℓ i
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i').val
      = rename (finCongr (show ℓ - (i.succ : ℕ) = ℓ - i.castSucc - 1 by
          have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
          (projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i')).val := by
  have h := congrArg Subtype.val (fixPrefix_initial_succ ℓ t m i challenges r_i').symm
  change (projectToNextSumcheckPoly ℓ i
    (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i').val =
      (projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i')).val at h
  refine h.trans ?_
  have hid : finCongr (show ℓ - (i.succ : ℕ) = ℓ - i.castSucc - 1 by
      have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega) =
      Equiv.refl (Fin (ℓ - i.succ)) := by
    ext j
    rfl
  rw [hid, Equiv.coe_refl, MvPolynomial.rename_id_apply]

/-- **Round-transition recursion for the projected sumcheck polynomial (unrenamed form).**

This packages `RingSwitching.fixFirstVariablesOfMQP_projectToMid_succ` at the
`projectToNextSumcheckPoly` API level, avoiding repeated unfolding at downstream call sites. -/
theorem projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
    (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToNextSumcheckPoly ℓ i
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' =
      projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i') := by
  change projectToNextSumcheckPoly ℓ i
    (MvPolynomial.fixPrefix ℓ i.castSucc (computeInitialSumcheckPoly ℓ t m) challenges) r_i' =
      MvPolynomial.fixPrefix ℓ i.succ (computeInitialSumcheckPoly ℓ t m)
        (Fin.snoc challenges r_i')
  exact (fixPrefix_initial_succ ℓ t m i challenges r_i').symm

end Sumcheck.Structured

#print axioms Sumcheck.Structured.projectToMidSumcheckPoly_succ
#print axioms Sumcheck.Structured.projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
