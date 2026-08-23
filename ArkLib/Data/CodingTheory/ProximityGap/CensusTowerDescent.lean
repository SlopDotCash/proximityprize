/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusClassificationCharZero

/-!
# The 2-adic tower descent, depth 2: two vanishing power sums force quartic-fiber structure

`CensusClassificationCharZero.lean` proved depth 1: a subset of the `2^m`-th roots of unity
(char 0) with `∑ x = 0` is antipodal-closed (a union of square-map fibers). This file proves
**depth 2** of the tower induction (G2-2; probe-verified exactly: the stride-4 system on μ₁₆
has precisely the 6 unions of two quartic fibers as its field-independent solutions at every
prime tested, zero halo):

* `antipodal_sq_sum` — the descent transfer: for an antipodal-closed `T` (char 0, `0 ∉ T`),
  `∑_{x∈T} x² = 2·∑_{y∈T²} y` where `T²` is the image of squaring (each fiber is exactly
  `{x, −x}`).
* `quartic_closed_of_sum_sq_zero` — **depth 2**: a set `T` of `2^m`-th roots of unity
  (`m ≥ 2`, char 0) with `∑ x = 0` and `∑ x² = 0` is closed under multiplication by the
  order-4 root `i = ζ^{2^{m−2}}` — a union of fibers of `x ↦ x⁴`. Proof: depth 1 makes `T`
  antipodal; the transfer pushes the second vanishing down to the squares; depth 1 at level
  `m−1` makes the squares antipodal; pulling `−x² ∈ T²` back gives `w ∈ T` with `w = ±ix`,
  and antipodality finishes.

The full tower statement (depth `j` from `j` vanishing power sums along the 2-adic
filtration) follows the same induction; depth 2 covers every stride-4 instance in the
classification table and is the template for the rest.

## References
* Issue #357 (G2-2); DISPROOF_LOG O145/O150.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Finset

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **The descent transfer.** For an antipodal-closed finite set `T` not containing `0`
in a char-0 field, the squaring map is exactly 2-to-1 onto its image, so
`∑_{x∈T} x² = 2·∑_{y ∈ T.image (·²)} y`. -/
theorem antipodal_sq_sum (T : Finset L) (hanti : ∀ x ∈ T, -x ∈ T) (h0 : (0 : L) ∉ T) :
    ∑ x ∈ T, x ^ 2 = 2 * ∑ y ∈ T.image (fun x => x ^ 2), y := by
  classical
  have hmaps : ∀ x ∈ T, (fun x => x ^ 2) x ∈ T.image (fun x => x ^ 2) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => x ^ 2)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y hy
  obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
  have hxne : x ≠ 0 := fun h => h0 (h ▸ hxT)
  have hxnneg : x ≠ -x := by
    intro h
    have h2x : (2 : L) * x = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2x with h2 | hx
    · exact two_ne_zero h2
    · exact hxne hx
  have hfilter : T.filter (fun z => z ^ 2 = x ^ 2) = {x, -x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzT, hz⟩
      have hzz : (z - x) * (z + x) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp hzz with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (rfl | rfl)
      · exact ⟨hxT, rfl⟩
      · exact ⟨hanti x hxT, by ring⟩
  rw [hfilter]
  rw [Finset.sum_insert (by simpa using hxnneg), Finset.sum_singleton]
  ring

/-- **Depth 2 of the tower descent.** A set of `2^m`-th roots of unity (`m ≥ 2`,
characteristic zero) whose first two power sums vanish is closed under multiplication by
the order-4 root `i = ζ^{2^{m−2}}` — i.e. it is a union of quartic fibers. -/
theorem quartic_closed_of_sum_sq_zero {ζ : L} {m : ℕ} (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (T : Finset L) (hT : ∀ x ∈ T, x ^ (2 ^ m) = 1)
    (hsum : ∑ x ∈ T, x = 0) (hsum2 : ∑ x ∈ T, x ^ 2 = 0) :
    ∀ x ∈ T, ζ ^ (2 ^ (m - 2)) * x ∈ T := by
  classical
  have hm1 : 1 ≤ m := by omega
  have h0 : (0 : L) ∉ T := by
    intro h
    have := hT 0 h
    rw [zero_pow (by positivity : 2 ^ m ≠ 0)] at this
    exact zero_ne_one this
  -- Depth 1: `T` is antipodal-closed.
  have hanti : ∀ x ∈ T, -x ∈ T := subset_neg_mem_of_sum_zero hm1 hζ T hT hsum
  -- Transfer the second vanishing down to the squares.
  set T' : Finset L := T.image (fun x => x ^ 2) with hT'def
  have hsum' : ∑ y ∈ T', y = 0 := by
    have h := antipodal_sq_sum T hanti h0
    rw [hsum2] at h
    rcases mul_eq_zero.mp h.symm with h2 | hOK
    · exact absurd h2 two_ne_zero
    · exact hOK
  -- Depth 1 at level `m − 1`: the squares are antipodal-closed.
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m - 1)) := by
    have h := hζ.pow (n := 2 ^ m) (by positivity) (show 2 ^ m = 2 * 2 ^ (m - 1) by
      rw [← pow_succ']
      congr 1
      omega)
    simpa using h
  have hT'roots : ∀ y ∈ T', y ^ (2 ^ (m - 1)) = 1 := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
    have := hT x hxT
    rw [← pow_mul]
    rw [show 2 * 2 ^ (m - 1) = 2 ^ m by rw [← pow_succ']; congr 1; omega]
    exact this
  have hanti' : ∀ y ∈ T', -y ∈ T' :=
    subset_neg_mem_of_sum_zero (by omega) hζ2 T' hT'roots hsum'
  -- Pull back: for `x ∈ T`, `−x² ∈ T'` is some `w²` with `w ∈ T`; then `w = ±ix`.
  intro x hxT
  set i : L := ζ ^ (2 ^ (m - 2)) with hidef
  have hi2 : i ^ 2 = -1 := by
    rw [hidef, ← pow_mul]
    rw [show 2 ^ (m - 2) * 2 = 2 ^ (m - 1) by rw [← pow_succ]; congr 1; omega]
    exact R12.pow_half_eq_neg_one hm1 hζ
  have hx2 : x ^ 2 ∈ T' := Finset.mem_image_of_mem _ hxT
  have hnegx2 : -(x ^ 2) ∈ T' := hanti' _ hx2
  obtain ⟨w, hwT, hw2⟩ := Finset.mem_image.mp hnegx2
  -- `w² = −x² = (ix)²`.
  have hfac : (w - i * x) * (w + i * x) = 0 := by
    have : w ^ 2 = -(x ^ 2) := hw2
    have hix2 : (i * x) ^ 2 = -(x ^ 2) := by
      rw [mul_pow, hi2]
      ring
    linear_combination this - hix2
  rcases mul_eq_zero.mp hfac with h | h
  · -- `w = ix`.
    have : i * x = w := (sub_eq_zero.mp h).symm
    rw [this]
    exact hwT
  · -- `w = −ix`, so `ix = −w ∈ T`.
    have : i * x = -w := by linear_combination h
    rw [this]
    exact hanti w hwT

/-- **The generalized descent transfer.** The fiber argument of `antipodal_sq_sum` never
used the specific summand: for any `g`, summing `g (x²)` over an antipodal-closed set is
twice the sum of `g` over the squares. -/
theorem antipodal_fiber_sum (g : L → L) (T : Finset L)
    (hanti : ∀ x ∈ T, -x ∈ T) (h0 : (0 : L) ∉ T) :
    ∑ x ∈ T, g (x ^ 2) = 2 * ∑ y ∈ T.image (fun x => x ^ 2), g y := by
  classical
  have hmaps : ∀ x ∈ T, (fun x => x ^ 2) x ∈ T.image (fun x => x ^ 2) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => g (x ^ 2))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y hy
  obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
  have hxne : x ≠ 0 := fun h => h0 (h ▸ hxT)
  have hxnneg : x ≠ -x := by
    intro h
    have h2x : (2 : L) * x = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2x with h2 | hx
    · exact two_ne_zero h2
    · exact hxne hx
  have hfilter : T.filter (fun z => z ^ 2 = x ^ 2) = {x, -x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzT, hz⟩
      have hzz : (z - x) * (z + x) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp hzz with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (rfl | rfl)
      · exact ⟨hxT, rfl⟩
      · exact ⟨hanti x hxT, by ring⟩
  rw [hfilter]
  rw [Finset.sum_insert (by simpa using hxnneg), Finset.sum_singleton]
  have hnegsq : (-x) ^ 2 = x ^ 2 := by ring
  rw [hnegsq]
  ring

/-- **THE FULL 2-ADIC TOWER DESCENT.** A set of `2^m`-th roots of unity (char 0) whose
first `j` dyadic power sums vanish (`∑ x^{2^i} = 0` for all `i < j ≤ m`) is closed under
multiplication by the order-`2^j` root `ζ^{2^{m−j}}` — i.e. it is a union of fibers of
`x ↦ x^{2^j}`. Depth 1 is the subset Lam–Leung theorem; depth 2 is
`quartic_closed_of_sum_sq_zero`; the induction iterates the transfer and the `w = ±ωx`
pullback. This is the complete characteristic-zero classification of dyadic-stride
gap-band solutions: the field-independent census of every stride-`2^j` two-monomial
stack is exactly its fiber census. -/
theorem tower_closed_of_dyadic_sums_zero :
    ∀ (j m : ℕ), j ≤ m → ∀ {ζ : L}, IsPrimitiveRoot ζ (2 ^ m) → ∀ (T : Finset L),
      (∀ x ∈ T, x ^ (2 ^ m) = 1) →
      (∀ i, i < j → ∑ x ∈ T, x ^ (2 ^ i) = 0) →
      ∀ x ∈ T, ζ ^ (2 ^ (m - j)) * x ∈ T := by
  intro j
  induction j with
  | zero =>
    intro m _ ζ hζ T hT _ x hx
    have h1 : ζ ^ (2 ^ (m - 0)) = 1 := by
      simpa using hζ.pow_eq_one
    rw [h1, one_mul]
    exact hx
  | succ j ih =>
    intro m hjm ζ hζ T hT hsums x hxT
    have hm1 : 1 ≤ m := by omega
    have h0 : (0 : L) ∉ T := by
      intro h
      have := hT 0 h
      rw [zero_pow (by positivity : 2 ^ m ≠ 0)] at this
      exact zero_ne_one this
    -- antipodal from the `i = 0` sum
    have hanti : ∀ y ∈ T, -y ∈ T := by
      refine subset_neg_mem_of_sum_zero hm1 hζ T hT ?_
      have := hsums 0 (by omega)
      simpa using this
    -- descend to the squares
    set T' : Finset L := T.image (fun x => x ^ 2) with hT'def
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m - 1)) := by
      have h := hζ.pow (n := 2 ^ m) (by positivity) (show 2 ^ m = 2 * 2 ^ (m - 1) by
        rw [← pow_succ']
        congr 1
        omega)
      simpa using h
    have hT'roots : ∀ y ∈ T', y ^ (2 ^ (m - 1)) = 1 := by
      intro y hy
      obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp hy
      rw [← pow_mul, show 2 * 2 ^ (m - 1) = 2 ^ m by rw [← pow_succ']; congr 1; omega]
      exact hT z hzT
    have hsums' : ∀ i, i < j → ∑ y ∈ T', y ^ (2 ^ i) = 0 := by
      intro i hi
      have htr := antipodal_fiber_sum (fun y => y ^ (2 ^ i)) T hanti h0
      have hpow : ∀ z : L, (z ^ 2) ^ (2 ^ i) = z ^ (2 ^ (i + 1)) := by
        intro z
        rw [← pow_mul]
        congr 1
        rw [pow_succ']
      simp only [hpow] at htr
      rw [hsums (i + 1) (by omega)] at htr
      rcases mul_eq_zero.mp htr.symm with h2 | hOK
      · exact absurd h2 two_ne_zero
      · exact hOK
    -- induction hypothesis one level down
    have hIH := ih (m - 1) (by omega) hζ2 T' hT'roots hsums'
    -- pullback: `(ωx)² = (ζ²-closure element)·x² ∈ T'`
    have hx2 : x ^ 2 ∈ T' := Finset.mem_image_of_mem _ hxT
    have hclosed := hIH (x ^ 2) hx2
    -- `(ζ²)^{2^{(m−1)−j}} · x² = (ζ^{2^{m−(j+1)}} · x)²`
    have hexp : ((ζ ^ 2) ^ (2 ^ (m - 1 - j))) * x ^ 2
        = (ζ ^ (2 ^ (m - (j + 1))) * x) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      have : m - 1 - j = m - (j + 1) := by omega
      rw [this]
      ring
    rw [hexp] at hclosed
    obtain ⟨w, hwT, hw2⟩ := Finset.mem_image.mp hclosed
    have hfac : (w - ζ ^ (2 ^ (m - (j + 1))) * x) * (w + ζ ^ (2 ^ (m - (j + 1))) * x) = 0 := by
      linear_combination hw2
    rcases mul_eq_zero.mp hfac with h | h
    · rw [← sub_eq_zero.mp h]
      exact hwT
    · have : ζ ^ (2 ^ (m - (j + 1))) * x = -w := by linear_combination h
      rw [this]
      exact hanti w hwT

/-! ## Source audit -/

#print axioms antipodal_sq_sum
#print axioms quartic_closed_of_sum_sq_zero
#print axioms antipodal_fiber_sum
#print axioms tower_closed_of_dyadic_sums_zero

end ArkLib.ProximityGap.KKH26
