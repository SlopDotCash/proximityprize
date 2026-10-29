/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Prelude
import ProximityPrize.Compatibility.BiniusChallengeOrder

/-!
# Canonical meaning of the destination-bounded compatibility fold

The broader legacy recursion also describes rate-tail domains. Its public destination-bounded
wrapper agrees with canonical `iteratedFold`. This compares the folded functions; their raw
matrix representations use different row conventions.
-/

open AdditiveNTT

namespace Binius.BinaryBasefold.Compatibility

set_option backward.isDefEq.respectTransparency false

/-- Convert the challenge convention while preserving all other final-statement data. -/
def reverseFinalChallenges {L : Type} {ℓ : ℕ}
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    FinalSumcheckStatementOut (L := L) (ℓ := ℓ) :=
  {stmt with challenges := fun j => stmt.challenges j.rev}

@[simp]
theorem reverseFinalChallenges_finalConstant {L : Type} {ℓ : ℕ}
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    (reverseFinalChallenges stmt).finalConstant = stmt.finalConstant := rfl

/-- Reversing twice restores the original statement, including its target and context. -/
theorem reverseFinalChallenges_involutive {L : Type} {ℓ : ℕ} :
    Function.Involutive (reverseFinalChallenges (L := L) (ℓ := ℓ)) := by
  rintro ⟨⟨target, challenges, ctx⟩, finalConstant⟩
  simp only [reverseFinalChallenges, Fin.rev_rev]


variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q]
  [Fact (Nat.Prime (ringChar 𝔽q))] [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)]
variable {ℓ 𝓡 : ℕ} [NeZero 𝓡] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- At a canonical destination, the historical wrapper computes the canonical iterated fold. -/
theorem iterated_fold_eq_canonical (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (hd : destIdx.val = i.val + steps) (hle : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate i → L) (c : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps hd hle f c =
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps hd hle f c := by
  rcases destIdx with ⟨d, hdlt⟩
  dsimp only at hd
  subst d
  funext y
  unfold iterated_fold iterated_fold_steps iteratedFold
  simp only [Fin.val_mk, Fin.val_last, cast_eq]
  simp only [fold_legacy, fold, quotientFiber, qMap_total_fiber, one_ne_zero, ↓reduceDIte]
  rfl

end Binius.BinaryBasefold.Compatibility

#print axioms Binius.BinaryBasefold.Compatibility.reverseFinalChallenges_involutive
#print axioms Binius.BinaryBasefold.Compatibility.iterated_fold_eq_canonical
