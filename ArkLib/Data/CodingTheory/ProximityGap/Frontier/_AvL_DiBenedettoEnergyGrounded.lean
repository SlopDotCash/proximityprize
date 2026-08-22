/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy

/-!
# AvL di-Benedetto cubic energy grounded substrate (#444)

This module supplies the cubic char-zero energy bound consumed by
`_AvT3a_DiBenedettoBeatAssembly`. The bound is routed through the already-proven dyadic Wick energy
substrate: for `G ⊆ μ_{2^k}` in characteristic zero, `rEnergy G 3 ≤ 5‼ · |G|^3 = 15|G|^3`.

Honest scope: char-zero/dyadic energy only. The finite-field good-prime transfer remains the named
open input in the AvT3a consumer; this does not close CORE.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ProximityGap.Frontier.CharZeroWickEnergy

namespace ArkLib.ProximityGap.Frontier.AvLDiBenedettoEnergyGrounded

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- **Cubic dyadic char-zero energy bound.** For `G ⊆ μ_{2^k}` with negation closure and `k ≥ 1`,
`rEnergy G 3 ≤ 15·|G|³`. This is the `r = 3` specialization of the proven char-zero dyadic Wick
bound (`gaussianEnergyBound_dyadic`), with `5‼ = 15`. -/
theorem rEnergy_three_le_of_one_le {k : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (_h0 : (0 : L) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) (hroot : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (_hcard : 1 ≤ G.card) :
    (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
  have h := gaussianEnergyBound_dyadic (F := L) (k := k) hk G hroot hneg 3
  unfold ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound at h
  norm_num at h
  simpa using h

/-- **Cubic dyadic char-zero energy bound, consumer-compatible form.** The existing AvT3a consumer
passes `hcard` instead of `1 ≤ k`; under the stated `0 ∉ G`, negation-closure, root, and nonempty
hypotheses, the degenerate `k = 0` case is impossible in characteristic zero, so `1 ≤ k` follows and
the Wick bound applies. -/
theorem rEnergy_three_le {k : ℕ} (G : Finset L)
    (h0 : (0 : L) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) (hroot : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (hcard : 1 ≤ G.card) :
    (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
  have hk : 1 ≤ k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.succ_le_iff.mp hcard)
    have hzroot : z = 1 := by
      have := hroot z hz
      simpa [hk0] using this
    have hnegmem : -z ∈ G := hneg z hz
    have hnegroot : -z = 1 := by
      have := hroot (-z) hnegmem
      simpa [hk0] using this
    have hminus : (-1 : L) = 1 := by
      calc (-1 : L) = -z := by rw [hzroot]
        _ = 1 := hnegroot
    have hchar : (2 : L) = 0 := by
      calc (2 : L) = 1 + 1 := by norm_num
        _ = (-1 : L) + 1 := by rw [hminus]
        _ = 0 := by ring
    norm_num at hchar
  exact rEnergy_three_le_of_one_le (k := k) hk G h0 hneg hroot hcard

end ArkLib.ProximityGap.Frontier.AvLDiBenedettoEnergyGrounded

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.AvLDiBenedettoEnergyGrounded.rEnergy_three_le_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.AvLDiBenedettoEnergyGrounded.rEnergy_three_le
