/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterComplementaryCores
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateEighthFullWiring

/-!
# Bounding a rich family by two large secants

At an error allowance of `e`, each determined line contains at most `e+1` witnesses.
When each subfamily of size at least `e+2` determines a sufficiently large core, taking
a second secant among the points outside the first line covers the entire family.
-/

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.TwoLargeCoreCount

/-- A line with core size `z` spends at least one new coordinate per point, and at
least `t-z` new coordinates when its core falls short of the agreement target. -/
theorem occupancy_le_of_packing {L z t e : ℕ} (hp : L * max 1 (t - z) + z ≤ e + t) :
    L ≤ e + 1 := by
  by_cases hzt : t ≤ z
  · have hm : max 1 (t - z) = 1 := by omega
    rw [hm, Nat.mul_one] at hp
    omega
  · have hm : max 1 (t - z) = t - z := by omega
    rw [hm] at hp
    cases L with
    | zero => omega
    | succ m =>
      rw [Nat.succ_mul] at hp
      have h := Nat.mul_le_mul_left m (by omega : 1 ≤ t - z)
      rw [Nat.mul_one] at h
      omega

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- A line determined by two selected points has at most `e+1` selected points. -/
theorem line_occupancy_le (fam : BadScalarRichPointFamily dom k δ u) {t e : ℕ}
    (hn : Fintype.card ι = e + t) (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = t)
    {l : LineParameter F} (hl : l ∈ lineParameters fam) : (pointsOn fam l).card ≤ e + 1 := by
  have hp := pointsOn_card_mul_max_add_core_le fam hl
  rw [ht, hn] at hp
  exact occupancy_le_of_packing hp

/-- If every sufficiently large subfamily determines a large core, two secants cover
the family under the displayed agreement and degree inequality. -/
theorem card_le_two_mul_add_two (fam : BadScalarRichPointFamily dom k δ u)
    {e t zmin : ℕ} (hk : 1 ≤ k) (htpos : 0 < t)
    (hn : Fintype.card ι = e + t) (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = t)
    (hgeom : Fintype.card ι + 3 * (k - 1) < t + 2 * zmin)
    (hforce : ∀ H : Finset F, H ⊆ fam.G → e + 2 ≤ H.card →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ zmin ≤
        (jointCore dom (u 0) (u 1) (secantParameter fam a b).1 (secantParameter fam a b).2).card) :
    fam.G.card ≤ 2 * e + 2 := by
  classical
  by_contra! hgt
  obtain ⟨a, ha, b, hb, hab, hz₁⟩ := hforce fam.G (fun _ h => h) (by omega)
  let l₁ := secantParameter fam a b
  have hl₁ : l₁ ∈ lineParameters fam := secantParameter_mem_lineParameters fam ha hb hab
  have hcap₁ := line_occupancy_le fam hn ht hl₁
  let H := fam.G \ pointsOn fam l₁
  have hH : H ⊆ fam.G := Finset.sdiff_subset
  have hcard : H.card = fam.G.card - (pointsOn fam l₁).card :=
    Finset.card_sdiff_of_subset (pointsOn_subset_G fam l₁)
  obtain ⟨c, hc, d, hd, hcd, hz₂⟩ := hforce H hH (by omega)
  let l₂ := secantParameter fam c d
  have hl₂ : l₂ ∈ lineParameters fam := secantParameter_mem_lineParameters fam (hH hc) (hH hd) hcd
  have hne : l₁ ≠ l₂ := by
    intro heq
    have hmem : c ∈ pointsOn fam l₂ :=
      first_point_mem_pointsOn_secant fam (beta := d) (hH hc)
    apply (Finset.mem_sdiff.mp hc).2
    rwa [heq]
  let D₁ := jointCore dom (u 0) (u 1) l₁.1 l₁.2
  let D₂ := jointCore dom (u 0) (u 1) l₂.1 l₂.2
  have h₁ : zmin ≤ D₁.card := hz₁
  have h₂ : zmin ≤ D₂.card := hz₂
  have hi : (D₁ ∩ D₂).card ≤ k - 1 := jointCore_inter_card_le_degree_pred fam hk hl₁ hl₂ hne
  have hu := Finset.card_union_add_card_inter D₁ D₂
  have hmiss : (Finset.univ \ (D₁ ∪ D₂)).card + 2 * (k - 1) < t := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ (D₁ ∪ D₂)
    omega
  have hts : t - 1 + 1 = t := by omega
  have hcover := G_subset_two_lines_of_small_core_complement fam hk
    (h := t - 1) (by omega) l₁ l₂ hl₁ hl₂
    (by rw [hts]; exact hmiss)
  have hcounts := Finset.card_le_card hcover
  have hunion := Finset.card_union_le (pointsOn fam l₁) (pointsOn fam l₂)
  have hcap₂ := line_occupancy_le fam hn ht hl₂
  omega

end ArkLib.ProximityGap.Frontier.TwoLargeCoreCount

#print axioms ArkLib.ProximityGap.Frontier.TwoLargeCoreCount.card_le_two_mul_add_two
