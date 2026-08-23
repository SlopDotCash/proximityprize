/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SliceLocusCount

/-!
# Issue #232 — the level-2 counting law: tower profiles are level-1 merged sets

The O115 census retired the tower iteration as a counting mechanism and named
its positive residue: the per-profile space of joint (level-1, level-2) locus
constraints is again an exact `q`-power, via REDUCTION to level 1 at the merged
sets `S = Z₁ ∪ √Z₂`.  This file lands that law:

* `card_polysDegLT_slices_vanishing_asym` — the asymmetric per-slice count
  (the missing primitive): `#{f : deg < k, evenSlice ⊨ S_e, oddSlice ⊨ S_o}
  = q^((k+1)/2 − |S_e|) · q^(k/2 − |S_o|)` — the O96 bijection with
  independent loci per slice;
* `slices_eval_sq_zero_iff` — **the level-2 transport**: both slices of `h`
  vanish at `v²` iff `h` vanishes at `v` and `−v` (char ≠ 2, `v ≠ 0`) — the
  reason forced level-2 loci are antipodal-pair shadows of level-1 loci;
* `card_level_two_profile` — **the O115 law**: the joint count of a level-1
  locus `Z₁` plus level-2 loci `{v² : v ∈ V_e}` / `{v² : v ∈ V_o}` equals the
  asymmetric count at the merged sets `Z₁ ∪ V_e ∪ (−V_e)` / `Z₁ ∪ V_o ∪ (−V_o)`
  — dimensions multiply iff the merged sets are disjoint unions; each overlap
  refunds one dimension, exactly as censused.
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The asymmetric per-slice count**: independent loci for the two slices. -/
theorem card_polysDegLT_slices_vanishing_asym (h2 : (2 : F) ≠ 0) {k : ℕ}
    (Se So : Finset F) (hSe : Se.card ≤ (k + 1) / 2) (hSo : So.card ≤ k / 2) :
    ((polysDegLT (F := F) k).filter (fun f =>
        (∀ z ∈ Se, (evenSlice f).eval z = 0) ∧
        (∀ z ∈ So, (oddSlice f).eval z = 0))).card
      = Fintype.card F ^ ((k + 1) / 2 - Se.card)
        * Fintype.card F ^ (k / 2 - So.card) := by
  rw [← card_polysDegLT_vanishing (F := F) (d := (k + 1) / 2) Se hSe,
    ← card_polysDegLT_vanishing (F := F) (d := k / 2) So hSo,
    ← Finset.card_product]
  refine Finset.card_bij' (fun f _ => (evenSlice f, oddSlice f))
    (fun p _ => C (2 : F)⁻¹ *
      (Polynomial.expand F 2 p.1 + X * Polynomial.expand F 2 p.2))
    ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨hfd, hfe, hfo⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨evenSlice_mem hfd, hfe⟩,
       Finset.mem_filter.mpr ⟨oddSlice_mem hfd, hfo⟩⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1d, hp1z⟩ := Finset.mem_filter.mp hp1
    obtain ⟨hp2d, hp2z⟩ := Finset.mem_filter.mp hp2
    refine Finset.mem_filter.mpr ⟨build_mem hp1d hp2d, ?_, ?_⟩
    · intro z hz
      rw [evenSlice_C_mul, evenSlice_build, C_inv_two_mul_two h2]
      exact hp1z z hz
    · intro z hz
      rw [oddSlice_C_mul, oddSlice_build, C_inv_two_mul_two h2]
      exact hp2z z hz
  · intro f _
    show C (2:F)⁻¹ * (Polynomial.expand F 2 (evenSlice f)
      + X * Polynomial.expand F 2 (oddSlice f)) = f
    rw [recompose_slices f, C_inv_two_mul_two h2]
  · intro p _
    refine Prod.ext ?_ ?_
    · show evenSlice (C (2:F)⁻¹ * _) = p.1
      rw [evenSlice_C_mul, evenSlice_build, C_inv_two_mul_two h2]
    · show oddSlice (C (2:F)⁻¹ * _) = p.2
      rw [oddSlice_C_mul, oddSlice_build, C_inv_two_mul_two h2]

omit [Fintype F] [DecidableEq F] in
/-- **The level-2 transport**: both slices of `h` vanish at `v²` iff `h`
vanishes at both `v` and `−v` — forced level-2 deadness is exactly the
antipodal-pair shadow of level-1 deadness (the O115 mechanism). -/
theorem slices_eval_sq_zero_iff (h2 : (2 : F) ≠ 0) (h : F[X]) {v : F}
    (hv : v ≠ 0) :
    ((evenSlice h).eval (v ^ 2) = 0 ∧ (oddSlice h).eval (v ^ 2) = 0) ↔
      (h.eval v = 0 ∧ h.eval (-v) = 0) := by
  have he := eval_evenSlice h v
  have ho := eval_oddSlice h v
  constructor
  · rintro ⟨hee, hoo⟩
    rw [hee] at he
    rw [hoo, mul_zero] at ho
    have hsum : h.eval v + h.eval (-v) = 0 := he.symm
    have hdiff : h.eval v - h.eval (-v) = 0 := ho.symm
    constructor
    · have : (2 : F) * h.eval v = 0 := by linear_combination hsum + hdiff
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' h2
      · exact h'
    · have : (2 : F) * h.eval (-v) = 0 := by linear_combination hsum - hdiff
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' h2
      · exact h'
  · rintro ⟨hpos, hneg⟩
    constructor
    · rw [hpos, hneg, add_zero] at he
      exact he
    · have hz : v * (oddSlice h).eval (v ^ 2) = 0 := by
        rw [ho, hpos, hneg, sub_zero]
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hv
      · exact h'

/-- The merged set of a level-1 locus and a chosen-root level-2 locus. -/
def mergedLocus (Z₁ V : Finset F) : Finset F :=
  Z₁ ∪ V ∪ V.image (fun v => -v)

omit [Fintype F] in
/-- Vanishing on the merged set ⟺ level-1 vanishing on `Z₁` plus level-2
vanishing (both sub-slices) at every `v²`, `v ∈ V`. -/
theorem vanish_mergedLocus_iff (h2 : (2 : F) ≠ 0) (h : F[X]) {Z₁ V : Finset F}
    (hV0 : (0 : F) ∉ V) :
    (∀ z ∈ mergedLocus Z₁ V, h.eval z = 0) ↔
      ((∀ z ∈ Z₁, h.eval z = 0) ∧
        ∀ v ∈ V, (evenSlice h).eval (v ^ 2) = 0 ∧
          (oddSlice h).eval (v ^ 2) = 0) := by
  constructor
  · intro hall
    refine ⟨fun z hz => hall z (by simp [mergedLocus, hz]), fun v hv => ?_⟩
    have hv0 : v ≠ 0 := fun h0 => hV0 (h0 ▸ hv)
    rw [slices_eval_sq_zero_iff h2 h hv0]
    have hmem : -v ∈ mergedLocus Z₁ V := by
      simp only [mergedLocus, Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact ⟨hall v (by simp [mergedLocus, hv]), hall (-v) hmem⟩
  · rintro ⟨hZ, hV⟩ z hz
    simp only [mergedLocus, Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · exact hZ z hz
    · have hv0 : z ≠ 0 := fun h0 => hV0 (h0 ▸ hz)
      exact ((slices_eval_sq_zero_iff h2 h hv0).mp (hV z hz)).1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have hv0 : v ≠ 0 := fun h0 => hV0 (h0 ▸ hv)
      exact ((slices_eval_sq_zero_iff h2 h hv0).mp (hV v hv)).2

/-- **THE O115 LAW**: the joint (level-1, level-2) per-profile count is an
exact `q`-power — the level-2 constraints reduce to level-1 vanishing at the
merged sets.  Dimensions multiply iff the merged unions are disjoint; each
overlap refunds one dimension. -/
theorem card_level_two_profile (h2 : (2 : F) ≠ 0) {k : ℕ}
    (Z₁ Ve Vo : Finset F) (hVe0 : (0 : F) ∉ Ve) (hVo0 : (0 : F) ∉ Vo)
    (hce : (mergedLocus Z₁ Ve).card ≤ (k + 1) / 2)
    (hco : (mergedLocus Z₁ Vo).card ≤ k / 2) :
    ((polysDegLT (F := F) k).filter (fun f =>
        ((∀ z ∈ Z₁, (evenSlice f).eval z = 0) ∧
          ∀ v ∈ Ve, (evenSlice (evenSlice f)).eval (v ^ 2) = 0 ∧
            (oddSlice (evenSlice f)).eval (v ^ 2) = 0) ∧
        ((∀ z ∈ Z₁, (oddSlice f).eval z = 0) ∧
          ∀ v ∈ Vo, (evenSlice (oddSlice f)).eval (v ^ 2) = 0 ∧
            (oddSlice (oddSlice f)).eval (v ^ 2) = 0))).card
      = Fintype.card F ^ ((k + 1) / 2 - (mergedLocus Z₁ Ve).card)
        * Fintype.card F ^ (k / 2 - (mergedLocus Z₁ Vo).card) := by
  rw [← card_polysDegLT_slices_vanishing_asym h2 (mergedLocus Z₁ Ve)
    (mergedLocus Z₁ Vo) hce hco]
  congr 1
  apply Finset.filter_congr
  intro f _
  rw [vanish_mergedLocus_iff h2 (evenSlice f) hVe0,
    vanish_mergedLocus_iff h2 (oddSlice f) hVo0]

end LamLeungTwoPow
