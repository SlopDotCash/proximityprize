/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.IsSidonSetProperties
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The `r = 2` moment object equals the in-tree additive energy (#444, #389)

Two additive-energy objects coexist in the campaign:

* `SubgroupGaussSumMoment.rEnergy G 2 = #{(v,w) ∈ (Fin 2 → G)² : ∑ v = ∑ w}` — the `r = 2` slice
  of the Gauss-sum moment ladder, the object the swap floor + Sidon iff (`REnergySwapFloor*`) live on.
* `AdditiveEnergyRepBound.additiveEnergy G = ∑_{a,b∈G} repCount(a+b) = #{(a,b,c,d) ∈ G⁴ : a+b=c+d}`
  — the representation-count form the GV / Sidon-mod-negation bound (`AdditiveEnergySidonModNeg`) lives on.

They are the **same number**:

> **`rEnergy_two_eq_additiveEnergy`.**  `rEnergy G 2 = additiveEnergy G`.

so the swap-floor characterization transfers verbatim to the representation-count object:

> **`additiveEnergy_eq_swap_floor_iff_sidon`.**  `additiveEnergy G = 2|G|² − |G| ↔ IsSidonSet G`.
> **`additiveEnergy_affine_eq_swap_floor_iff_sidon`.**  The same exactness after a nonzero affine image.

This unifies the two parallel Sidon characterizations (the plain `2n² − n` minimum here and the
negation-closed `3n² − 3n` minimum in `AdditiveEnergySidonModNeg`) onto a single object.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.AdditiveEnergyRepBound (repCount additiveEnergy)

/-- Reindex a sum over `Fin 2 → G` as a double sum over `G`, via `v ↦ (v 0, v 1)`. -/
private theorem sum_piFinset_fin2 {M : Type*} [AddCommMonoid M] (G : Finset F)
    (f : (Fin 2 → F) → M) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G), f v
      = ∑ a ∈ G, ∑ b ∈ G, f ![a, b] := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun v => (v 0, v 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Fintype.mem_piFinset] at hv
    simp only [Finset.mem_product]; exact ⟨hv 0, hv 1⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    simp only [Fintype.mem_piFinset]; intro i; fin_cases i
    · simpa using hp.1
    · simpa using hp.2
  · intro v hv
    funext i; fin_cases i <;> rfl
  · intro p _; rfl
  · intro v hv
    congr 1
    funext i; fin_cases i <;> rfl

/-- `repCount G t = #{(c,d) ∈ G² : c + d = t}`, i.e. `∑_{c∈G} ∑_{d∈G} (if c+d=t then 1 else 0)`. -/
private theorem repCount_eq_double_sum (G : Finset F) (t : F) :
    repCount G t = ∑ c ∈ G, ∑ d ∈ G, (if c + d = t then (1 : ℕ) else 0) := by
  classical
  unfold repCount
  -- inner ∑_d [c+d=t] = if t-c ∈ G then 1 else 0 (at most one d works: d = t - c)
  have hinner : ∀ c ∈ G, (∑ d ∈ G, (if c + d = t then (1 : ℕ) else 0))
      = (if t - c ∈ G then 1 else 0) := by
    intro c _
    by_cases hmem : t - c ∈ G
    · rw [Finset.sum_eq_single (t - c)]
      · simp [hmem]
      · intro d _ hd
        have : c + d ≠ t := by intro h; apply hd; rw [← h]; ring
        simp [this]
      · intro h; exact absurd hmem h
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro d hd
      have : c + d ≠ t := by
        intro h; apply hmem; rw [← h]; simpa using hd
      simp [this]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_boole]
  simp [Finset.filter_congr (fun y _ => by rfl)]

/-- **The bridge.**  `rEnergy G 2 = additiveEnergy G`. -/
theorem rEnergy_two_eq_additiveEnergy (G : Finset F) :
    rEnergy G 2 = additiveEnergy G := by
  classical
  unfold rEnergy additiveEnergy
  -- LHS: reindex both v and w to G×G; inner sum ∑_w [∑v=∑w] = ∑_c∑_d [v0+v1 = c+d]
  rw [sum_piFinset_fin2 G (fun v => ∑ w ∈ Fintype.piFinset (fun _ : Fin 2 => G),
      (if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0))]
  -- RHS: repCount(a+b) = ∑_c∑_d [c+d = a+b]
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
  rw [repCount_eq_double_sum]
  -- inner over w (Fin 2 → G) reindexed to (c,d), with ∑![a,b] = a+b and ∑![c,d] = c+d
  rw [sum_piFinset_fin2 G (fun w => if ∑ i, (![a, b] : Fin 2 → F) i = ∑ i, w i then (1 : ℕ) else 0)]
  refine Finset.sum_congr rfl (fun c hc => Finset.sum_congr rfl (fun d hd => ?_))
  -- (if ∑![a,b] = ∑![c,d] then 1 else 0) = (if c+d = a+b then 1 else 0)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  by_cases h : c + d = a + b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- **The swap-floor characterization on the representation-count object.**
`additiveEnergy G = 2|G|² − |G| ↔ IsSidonSet G`. -/
theorem additiveEnergy_eq_swap_floor_iff_sidon (G : Finset F) :
    additiveEnergy G = 2 * G.card ^ 2 - G.card ↔ IsSidonSet G := by
  rw [← rEnergy_two_eq_additiveEnergy]
  exact (isSidonSet_iff_rEnergy_two_eq_swap_floor).symm

/-- **Affine-normalized swap-floor characterization.**  The representation-count additive
energy of the nonzero affine image `u + tG` hits the plain Sidon swap floor exactly iff the
original set `G` is Sidon.  This packages affine normalization/de-normalization for the
`additiveEnergy` face; no upper bound or CORE claim is involved. -/
theorem additiveEnergy_affine_eq_swap_floor_iff_sidon (G : Finset F) (u : F) {t : F}
    (ht : t ≠ 0) :
    additiveEnergy (G.map (affineEmbeddingOfNe u t ht)) = 2 * G.card ^ 2 - G.card
      ↔ IsSidonSet G := by
  have hcard : (G.map (affineEmbeddingOfNe u t ht)).card = G.card := by
    simp
  rw [← hcard]
  rw [additiveEnergy_eq_swap_floor_iff_sidon]
  exact isSidonSet_map_affine_iff G u ht

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_eq_additiveEnergy
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_eq_swap_floor_iff_sidon
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_affine_eq_swap_floor_iff_sidon
