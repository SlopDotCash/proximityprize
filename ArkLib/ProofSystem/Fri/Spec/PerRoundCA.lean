/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Fri.Spec.Soundness
import ArkLib.ProofSystem.Whir.KeystoneSmallField

namespace Fri.Spec

open Polynomial OracleSpec OracleComp ProtocolSpec Finset NNReal ProximityGap Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {ω : SmoothCosetFftDomain n F}

/-- **The FRI per-round proximity-gap input in the vacuous regime (#303 item (a)).**
For the `i`-th fold round (parameters `N`, `dom`, `degBound` exactly as in `roundError`),
the curve correlated-agreement error of the round's Reed–Solomon code is bounded by
`κ · roundError i` — unconditionally whenever `|F| ≤ κ · 2^(n−N)`. Since `roundError` is
definitionally the BCIKS20 `errorBound` at the round parameters, this is
`keystone_curves_bound_of_card_le` instantiated per round. -/
theorem perRound_epsCA_le_roundError_of_card_le (δ : ℝ≥0) (i : Fin k) (κ : ℕ)
    (N : ℕ) (hN : N = ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1)
    (degBound : ℕ) (hdeg : degBound = 2 ^ ((∑ j', (s j').1) - N) * d.1)
    [NeZero degBound]
    (hδ : δ < 1 - ReedSolomon.sqrtRate degBound
      ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)))
    (hq : (Fintype.card F : ℝ≥0) ≤ (κ : ℝ≥0) * (Fintype.card (Fin (2 ^ (n - N))) : ℝ≥0)) :
    epsCA_curves (F := F)
        (ReedSolomon.code ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)) degBound
          : Set (Fin (2 ^ (n - N)) → F)) κ δ δ
      ≤ ((κ * roundError k s d (ω := ω) δ i : ℝ≥0) : ENNReal) := by
  have hre : roundError k s d (ω := ω) δ i
      = errorBound δ degBound ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)) := by
    subst hN hdeg
    rfl
  rw [hre]
  exact keystone_curves_bound_of_card_le hδ hq

end Fri.Spec

#print axioms Fri.Spec.perRound_epsCA_le_roundError_of_card_le
