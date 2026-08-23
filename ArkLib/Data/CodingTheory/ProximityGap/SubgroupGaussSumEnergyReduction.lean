/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder

/-!
# Energy ⟹ sup-norm reduction for the subgroup Gauss sum (#389)

The proximity-gap prize, in the smooth-domain RS regime, reduces to bounding the worst-case
*incomplete* subgroup Gauss-sum magnitude `max_{b≠0} ‖η_b‖`, where `η_b = ∑_{y∈G} ψ(b·y)` and
`G = μ_n`.  The moment ladder `∑_b ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`, pure
orthogonality, no Weil) localizes this to the `r`-fold additive energy `E_r(G) = energyR G r`.

This file records the single clean consequence of that ladder used in the reduction:

> **`eta_pow_le_energyR`** — for every nontrivial frequency `b`,
> `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`.

Subtracting the `b=0` spike (`‖η_0‖ = |G|`) from the moment ladder and bounding a single nonnegative
term by the sum.  Consequence: **any** bound on the `r`-fold additive energy of `μ_n` transfers
directly to a bound on the worst-case Gauss-sum magnitude — the prize quantity.  In particular the
optimal choice `r ≈ log q` turns the conjectured energy bound `E_r(μ_n) ≤ |G|^{2r}/q + (e·r·|G|)^r/q`
(no anomalous concentration beyond the random main term and the diagonal `r!·|G|^r`) into the prize
cancellation `max_{b≠0}‖η_b‖ ≤ C√(|G| log q)`.  The `r=2` energy is pinned in-tree
(`additiveEnergy_units_eq`, `rootsOfUnity_additiveEnergy_eq`) but gives only the trivial sup bound;
the open core is precisely `energyR (μ_n) r` for `r ≈ log q`.  Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Energy ⟹ sup-norm reduction.** For any nontrivial frequency `b`, the `2r`-th power of the
Gauss-sum magnitude is bounded by the `r`-fold additive energy:
`‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`.  This converts ANY bound on the `r`-fold additive energy
`energyR G r` into a bound on the worst-case subgroup Gauss-sum magnitude `max_{b≠0}‖η_b‖` — the
quantity the proximity-gap prize must control for `G = μ_n`.  Pure orthogonality (via
`subgroup_gaussSum_moment`); no Weil bound. -/
theorem eta_pow_le_energyR {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn0 : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [h0, Complex.norm_natCast]
  have hmom := subgroup_gaussSum_moment hψ G r
  have hsplit : ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r)
      = ‖eta ψ G (0 : F)‖ ^ (2 * r)
        + ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have herase : ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := by
    rw [hmom] at hsplit; rw [hn0] at hsplit; linarith
  have hmem : b ∈ univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hle : ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => pow_nonneg (norm_nonneg _) _) hmem
  rwa [herase] at hle

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
