/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# All-bands energy bound from the worst-case subgroup character sum (#389)

Combining the moment bridge `∑_b ‖η_b‖^{2r} = q·E_r(G)` (`SubgroupGaussSumMoment`) with the second
moment `∑_b ‖η_b‖² = q·|G|` (`SubgroupGaussSumSecondMoment`):

> **`rEnergy_le`** — if `‖η_b‖² ≤ M` for all `b ≠ 0`, then
> `q·E_r(G) ≤ |G|^{2r} + M^{r-1}·(q|G| − |G|²)`.

Splitting off the spike `b=0` (`‖η_0‖ = |G|`) and bounding `‖η_b‖^{2r} ≤ M^{r-1}·‖η_b‖²` off it.
Consequence for δ\*: in the deployed regime `q ≥ |G|²`, this gives `E_r(G) = O(|G|^r)` (the sharp
`r`-band supply bound, for *every* band `r`, not just the cubic `r=2`) **iff** the worst-case
incomplete sum obeys `|η_b| ≤ C√|G|`. So the single open Bourgain bound `M = O(|G|)` controls *all*
bands of the δ\* supply simultaneously. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **All-bands energy bound.** `q·E_r(G) ≤ |G|^{2r} + M^{r-1}·(q|G| − |G|²)` when `‖η_b‖² ≤ M`
for all `b ≠ 0`. -/
theorem rEnergy_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {M : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hM : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ M) :
    (Fintype.card F : ℝ) * rEnergy G r
      ≤ (G.card : ℝ) ^ (2 * r)
        + M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
  rw [← subgroup_gaussSum_moment hψ G r]
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn0 : ‖eta ψ G (0 : F)‖ = (G.card : ℝ) := by rw [h0, Complex.norm_natCast]
  have hM0 : (0 : ℝ) ≤ M := le_trans (sq_nonneg _) (hM 1 one_ne_zero)
  -- bound each off-zero term: `‖η_b‖^{2r} ≤ M^{r-1} · ‖η_b‖²`
  have hb : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖eta ψ G b‖ ^ (2 * r) ≤ M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := by
    intro b hbm
    have hbne : b ≠ 0 := (Finset.mem_erase.mp hbm).1
    have hsq := hM b hbne
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := sq_nonneg _
    have hr1 : r = (r - 1) + 1 := by omega
    calc ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by rw [pow_mul]
      _ = (‖eta ψ G b‖ ^ 2) ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := by rw [← pow_succ, ← hr1]
      _ ≤ M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := by gcongr
  -- second moment off zero
  have hsum2 : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    have h2 := subgroup_gaussSum_secondMoment hψ G
    have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 2
        = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hsp, hn0] at h2
    linarith [h2]
  calc ∑ b : F, ‖eta ψ G b‖ ^ (2 * r)
      = ‖eta ψ G 0‖ ^ (2 * r) + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ (2 * r) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    _ ≤ ‖eta ψ G 0‖ ^ (2 * r) + ∑ b ∈ Finset.univ.erase 0, M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := by
        have hsle := Finset.sum_le_sum hb; linarith
    _ = ‖eta ψ G 0‖ ^ (2 * r) + M ^ (r - 1) * ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (G.card : ℝ) ^ (2 * r)
          + M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
        rw [hn0, hsum2]

end ArkLib.ProximityGap.SubgroupGaussSumMomentBound

#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentBound.rEnergy_le
