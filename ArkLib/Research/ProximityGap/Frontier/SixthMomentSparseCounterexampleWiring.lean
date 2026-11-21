/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SixthMomentSparseCounterexample
import ArkLib.Research.ProximityGap.Frontier.NormalizedTripleEnergy

/-! # The exact sixth-moment excess for the order-64 subgroup of the field of 173249 elements

The literal table enumerates every ordered pair from the subgroup once. Its key for
a pair is the standard representative of the field signature, so counts transport
directly to the normalized profile and to the ordered additive energy.
-/

namespace ArkLib.ProximityGap.Frontier.SixthMomentSparseCounterexample
open Finset Polynomial NormalizedTripleEnergy
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 180000
/-- The prime field of the counterexample. -/
abbrev F := ZMod p
private def elements : List F := roots.map Nat.cast
/-- The actual subgroup consisting of all sixty-fourth roots of unity. -/
noncomputable abbrev H := Polynomial.nthRootsFinset n (1 : F)

private theorem elements_eq : elements.toFinset = H := by
  ext x
  simp only [elements, roots, List.mem_toFinset, List.mem_map, List.mem_range,
    Polynomial.mem_nthRootsFinset (by decide : 0<n), Nat.powMod_def]
  constructor
  · rintro ⟨_, ⟨i, _, rfl⟩, rfl⟩
    rw [ZMod.natCast_mod, Nat.cast_pow, ← pow_mul, Nat.mul_comm, pow_mul, primitive.pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := primitive.eq_pow_of_pow_eq_one hx
    exact ⟨g^i % p, ⟨i, hi, rfl⟩, by simp [ZMod.natCast_mod]⟩

private theorem elements_nodup : elements.Nodup := by
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (elements : Multiset F))).mp
  change elements.toFinset.card = elements.length
  rw [elements_eq, primitive.card_nthRootsFinset]
  simp [elements, roots]

private theorem signature_val (x y : ℕ) :
    ((1+(x:F)+(y:F))^n).val = signature (1+x+y) := by
  rw [signature, Nat.powMod_def, ← ZMod.val_natCast]
  simp

private theorem sums_pairs :
    (elements ×ˢ elements).map (fun z => ((1+z.1+z.2)^n).val) = sums := by
  simp [elements, SProd.sprod, List.product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    sums, signature_val]

/-- The normalized pair count is the multiplicity of the representative in the literal table. -/
theorem profile_eq_count (u : F) : profile H n u = sums.count u.val := by
  have hp : (elements ×ˢ elements).toFinset = H ×ˢ H := by
    ext ⟨a,b⟩
    simp only [← elements_eq, List.mem_toFinset, Finset.mem_product, List.mem_product]
  have h := (elements_nodup.product elements_nodup).card_eq_countP
    (P := fun z : F × F => (1+z.1+z.2)^n=u)
  rw [hp] at h
  rw [profile, h, ← sums_pairs, List.count, List.countP_map]
  congr 1

private theorem sums_bdd {v : ℕ} (hv : v ∈ sums) : v < p := by
  rw [← sums_pairs, List.mem_map] at hv
  obtain ⟨z, _, rfl⟩ := hv
  exact ZMod.val_lt _

private theorem representative_sum {m : ℕ} [NeZero m] (xs : List ℕ) (hb : ∀ v ∈ xs, v < m) :
    ∑ u : ZMod m, (xs.count u.val)^2 = ∑ v ∈ xs.toFinset, xs.count v ^ 2 := by
  let S := xs.toFinset.image (fun v : ℕ => (v:ZMod m))
  calc
    ∑ u : ZMod m, (xs.count u.val)^2 = ∑ u ∈ S, (xs.count u.val)^2 := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro u _ hu
      have hv : u.val ∉ xs := by
        intro h
        apply hu
        exact Finset.mem_image.mpr ⟨u.val, List.mem_toFinset.mpr h,ZMod.natCast_zmod_val _⟩
      simp [List.count_eq_zero.mpr hv]
    _ = ∑ v ∈ xs.toFinset, xs.count v ^ 2 := by
      have hval (v : ℕ) (hv : v ∈ xs.toFinset) : (v:ZMod m).val = v :=
        ZMod.val_natCast_of_lt (hb v (List.mem_toFinset.mp hv))
      dsimp only [S]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro v hv
        rw [hval v hv]
      · intro v hv w hw he
        simpa [hval v hv, hval w hw] using congrArg ZMod.val he

private theorem profile_on_support_sum :
    ∑ u : F, (profile H n u)^2 = ∑ v ∈ sums.toFinset, sums.count v ^ 2 := by
  simp_rw [profile_eq_count]
  exact representative_sum sums (fun _ => sums_bdd)

private theorem zero_count_of_absent (xs : List ℕ) (h : xs.contains 0 = false) : xs.count 0 = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  have hh := List.contains_iff_mem.mpr hm
  rw [h] at hh
  contradiction

private theorem profile_zero : profile H n 0 = 0 :=
  (profile_eq_count 0).trans (zero_count_of_absent sums table.2.1)

/-- Sum of the squared normalized pair counts over the whole prime field. -/
theorem profile_square_sum : ∑ u : F, (profile H n u)^2 = 68320 :=
  profile_on_support_sum.trans sum_squares

private theorem drop_zero {K : Type*} [Fintype K] [DecidableEq K] [Zero K]
    (f : K → ℕ) {v : ℕ} (hz : f 0 = 0) (hs : ∑ u, f u ^ 2 = v) :
    ∑ u ∈ (univ : Finset K).erase 0, f u ^ 2 = v := by
  have he := Finset.add_sum_erase (univ : Finset K) (fun u => (f u)^2) (mem_univ 0)
  simpa only [hz, zero_pow (by decide : 2 ≠ 0), Nat.zero_add, hs] using he

private theorem profile_nonzero_sum : ∑ u ∈ (univ : Finset F).erase 0, (profile H n u)^2 = 68320 :=
  drop_zero (profile H n) profile_zero profile_square_sum

private theorem substituted {z s c : ℕ} (hz : z = 0) (hs : s = 68320) (hc : c = n) :
    (c*z)^2 + c*s = n*68320 := by simp only [hz, hs, hc, Nat.mul_zero, Nat.zero_add, zero_pow (by decide : 2 ≠ 0)]

/-- Value of the ordered triple additive energy. -/
theorem exact_energy : SubgroupGaussSumSixthMoment.addEnergy3 H = n * 68320 :=
  (addEnergy3_nthRoots (by decide : 0<n) primitive).trans
    (substituted profile_zero profile_nonzero_sum rfl)

/-- Value of the production ordered energy at depth three. -/
theorem exact_rEnergy : SubgroupGaussSumMoment.rEnergy H 3 = n * 68320 :=
  (rEnergy_three_eq_profile (by decide : 0<n) (H := H)
    (fun x => Polynomial.mem_nthRootsFinset (by decide : 0<n) (1:F) (x := x))).trans
    (substituted profile_zero profile_nonzero_sum primitive.card_nthRootsFinset)

/-- Exact excess after removing the zero frequency and clearing the field-size denominator. -/
theorem centered_excess : p * SubgroupGaussSumMoment.rEnergy H 3 =
    n^6 + p*(15*n^3) + 7565522944 := (congrArg (p * ·) exact_rEnergy).trans strict_excess

/-- All the repeated-entry exclusions coexist with strict failure of the centered
unit-Gaussian depth-three comparison. -/
theorem sparse_counterexample :
    SixthMomentAntipodalShape.FourTermConditions {x : F | x^n=1} ∧
    n^6 + p*(15*n^3) < p * SubgroupGaussSumMoment.rEnergy H 3 :=
  ⟨fourTermConditions, centered_excess.symm ▸ Nat.lt_add_of_pos_right (by decide)⟩

#print axioms sparse_counterexample
#print axioms profile_eq_count
#print axioms profile_square_sum
#print axioms exact_energy
#print axioms exact_rEnergy
#print axioms centered_excess

end ArkLib.ProximityGap.Frontier.SixthMomentSparseCounterexample
