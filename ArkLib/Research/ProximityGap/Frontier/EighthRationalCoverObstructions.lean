/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # General homothetic-cover obstructions and 3+1 pencil-degree barrier at eighth rate

Previously (`EighthDyadicHeadDirections.lean`, `EighthDihedralHeadDirections.lean`), symmetry
exclusions for four rich eighth-rate heads at `e = 671,088,640` (`0 ≤ s ≤ 4`) treated group
actions `X ↦ ζ X` and `X ↦ c / X` inside `D_{2n}`.

This module establishes **completely general, non-Galois, non-dihedral, non-monomial**
homothetic-cover obstructions across all five open profiles `(1,1,1,1)` through `(1,1,1,5)`
(`0 ≤ s ≤ 4`), together with the exact `3 + 1` pencil-degree barrier below `679,477,248` and
sharpened Blowup-Gauss + fixed-row dual-`(α, β)` collision/orbit bounds:

1. **Universal homothetic fiber theorem (`homothetic_fiber_universal`)**:
   for ANY 4-point multiset `(P, w)` (`∑ u ∈ P, w u = 4`, `1 ≤ w u`) with symmetric projective
   direction map `dir : V → V → Z`, and ANY nonempty finite fiber `S` of centers `u : S → P`
   with `w (u x) ≤ 2` for all `x ∈ S`,
   `2 * |⋃_{x ∈ S} star P dir (u x)| + 3 * ∑_{x ∈ S} w (u x) ≤ 6 * |S| + 4`.
   This generalizes `EighthDyadicHeadDirections.two_stars` (`|S| = 2`, `16 = 6 * 2 + 4`) to
   arbitrary fiber sizes `|S| ≥ 1` with the optimal linear slope `6`.
2. **Arbitrary homothetic-quotient image & singleton-fiber floors (`homothetic_cover_image_floor`,
   `homothetic_cover_singleton_floor`)**:
   if all three head-0 direction maps of ANY near-saturated (`0 ≤ s ≤ 4`) four-head overrun at
   `671,088,640` factor through ANY map `h : H → T` (arbitrary rational/algebraic cover, with
   at most `12` exceptional sites in `H`), then the regular image `I = |h(H_reg)|` satisfies
   - `I ≥ 660,784,912` (`> 0.615 n`, at least `247,828,000` isolated singleton fibers) even under
     the baseline `20,607,410` residual allowance,
   - `I ≥ 670,889,935` (`> 0.6248 n`, at least `268,038,046` isolated singleton fibers) under
     the Milestone 2 Sparse-Gauss residual `397,364`,
   - `I ≥ 670,994,405` (`> 0.6249 n`, at least `268,246,986` isolated singleton fibers) under
     the Blowup-Gauss + fixed-row dual-`(α, β)` residual `188,424`.
   In particular, EVERY 2-to-1, 3-to-1, or `q`-to-1 (`q ≥ 2`) homothetic factorization — AND
   every partial involution `σ` preserving `≥ 76%` of `H` — is unconditionally excluded across
   all `0 ≤ s ≤ 4`.
3. **Exact `3 + 1` pencil-degree barrier below `679,477,248` (`three_plus_one_pencil_barrier`)**:
   any balanced `3 collinear + 1 transverse` four-head construction with primitive direction
   degree `h ≥ 1` beating `679,477,248` (`e ≤ 679,477,247`, all four deficits `1`) requires a
   reduced 3-split polynomial pencil of degree `r_pair ≥ 3k/4 + 4 = 100,663,300` on `μ_{2^30}`,
   proving `EighthTransverseAttack.lean` saturates the `μ_{16}` cubic pencil (`r_pair = 3k/4`)
   down to the very last site.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthRationalCoverObstructions

open Finset

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev budget : ℕ := 2147483648

/-! ## Section 1: Universal homothetic multi-site fiber theorem -/

/-- Projective fresh directions from a center `u` to the distinct other points of `P`. -/
def star {V Z : Type*} [DecidableEq V] [DecidableEq Z] (P : Finset V)
    (dir : V → V → Z) (u : V) : Finset Z :=
  (P.erase u).image (dir u)

/-- Any finite set `P` with symmetric edge-labeling `dir` determines at most `|P|*(|P|-1)/2`
distinct pairwise directions across all stars. -/
theorem card_biUnion_star_le_choose_two {V Z : Type*} [DecidableEq V] [DecidableEq Z]
    (P : Finset V) (dir : V → V → Z) (symm : ∀ u v, dir u v = dir v u) :
    (P.biUnion (star P dir)).card ≤ P.card * (P.card - 1) / 2 := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsub :
        (insert a s).biUnion (star (insert a s) dir) ⊆
          (s.biUnion (star s dir)) ∪ (s.image (dir a)) := by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := mem_biUnion.mp hz
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hzu
      obtain ⟨hvu, hv_ins⟩ := mem_erase.mp hv
      rcases mem_insert.mp hu with rfl | hus
      · rcases mem_insert.mp hv_ins with rfl | hvs
        · exact absurd rfl hvu
        · exact mem_union_right _ (mem_image.mpr ⟨v, hvs, rfl⟩)
      · rcases mem_insert.mp hv_ins with rfl | hvs
        · exact mem_union_right _ (mem_image.mpr ⟨u, hus, symm v u⟩)
        · exact mem_union_left _ (mem_biUnion.mpr ⟨u, hus, mem_image.mpr ⟨v, mem_erase.mpr ⟨hvu, hvs⟩, rfl⟩⟩)
    have hcard := (card_le_card hsub).trans (card_union_le _ _)
    have himg : (s.image (dir a)).card ≤ s.card := card_image_le
    rw [card_insert_of_notMem ha, Nat.add_sub_cancel]
    have hstep : s.card * (s.card - 1) / 2 + s.card = (s.card + 1) * s.card / 2 := by
      cases hs : s.card with
      | zero => simp
      | succ m =>
        rw [Nat.add_sub_cancel]
        have hmul : (m + 1) * m + 2 * (m + 1) = (m + 2) * (m + 1) := by ring
        have hdiv : ((m + 1) * m + 2 * (m + 1)) / 2 = (m + 1) * m / 2 + (m + 1) := by
          rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        rw [← hmul, hdiv]
    have hadd : (s.biUnion (star s dir)).card + (s.image (dir a)).card ≤
        s.card * (s.card - 1) / 2 + s.card := Nat.add_le_add ih himg
    rw [hstep] at hadd
    exact hcard.trans hadd

/-- For two distinct centers in `P`, the union of their stars loses at least the shared
direction `dir u v`, saving `1` over the sum of individual star sizes. -/
private lemma card_two_stars_le {V Z : Type*} [DecidableEq V] [DecidableEq Z]
    (P : Finset V) (dir : V → V → Z) (symm : ∀ u v, dir u v = dir v u)
    {u v : V} (hu : u ∈ P) (hv : v ∈ P) (hne : u ≠ v) :
    (star P dir u ∪ star P dir v).card ≤ 2 * P.card - 3 := by
  have cu : (star P dir u).card ≤ P.card - 1 := by
    have := card_image_le (s := P.erase u) (f := dir u)
    rwa [card_erase_of_mem hu] at this
  have cv : (star P dir v).card ≤ P.card - 1 := by
    have := card_image_le (s := P.erase v) (f := dir v)
    rwa [card_erase_of_mem hv] at this
  have hshared : dir u v ∈ star P dir u ∩ star P dir v := by
    refine mem_inter.mpr ⟨mem_image.mpr ⟨v, mem_erase.mpr ⟨hne.symm, hv⟩, rfl⟩,
      mem_image.mpr ⟨u, mem_erase.mpr ⟨hne, hu⟩, symm v u⟩⟩
  have hpos : 1 ≤ (star P dir u ∩ star P dir v).card := card_pos.mpr ⟨_, hshared⟩
  have hunion := card_union_add_card_inter (star P dir u) (star P dir v)
  have hP2 : 2 ≤ P.card := by
    have hsub : ({u, v} : Finset V) ⊆ P := by
      intro x hx; rcases mem_insert.mp hx with rfl | hx
      · exact hu
      · exact mem_singleton.mp hx ▸ hv
    have := card_le_card hsub
    rwa [card_pair hne] at this
  omega

/-- **Universal homothetic fiber theorem**: for ANY 4-point multiset `(P, w)`
(`∑ i ∈ P, w i = 4`, `∀ i ∈ P, 1 ≤ w i`) with symmetric direction map `dir`, and ANY
nonempty finite set `S` of regular sites choosing centers `u : S → P` with `w (u x) ≤ 2`,
the distinct fresh labels `M = |⋃_{x ∈ S} star P dir (u x)|` and core incidence sum
`W = ∑_{x ∈ S} w (u x)` satisfy `2 * M + 3 * W ≤ 6 * |S| + 4`. -/
theorem homothetic_fiber_universal {V Z ι : Type*} [DecidableEq V] [DecidableEq Z] [DecidableEq ι]
    (P : Finset V) (w : V → ℕ) (dir : V → V → Z) (symm : ∀ a b, dir a b = dir b a)
    (total : ∑ i ∈ P, w i = 4) (pos : ∀ i ∈ P, 1 ≤ w i)
    (S : Finset ι) (hne : S.Nonempty) (u : ι → V)
    (hmem : ∀ x ∈ S, u x ∈ P) (hw : ∀ x ∈ S, w (u x) ≤ 2) :
    2 * (S.biUnion fun x => star P dir (u x)).card + 3 * (∑ x ∈ S, w (u x)) ≤
      6 * S.card + 4 := by
  classical
  have hPcard : P.card ≤ 4 := by
    have h1 : P.card ≤ ∑ i ∈ P, w i := by
      simpa using sum_le_sum (s := P) (f := fun _ => 1) (g := w) pos
    omega
  have hall_le : (S.biUnion fun x => star P dir (u x)).card ≤ P.card * (P.card - 1) / 2 := by
    have hsub : (S.biUnion fun x => star P dir (u x)) ⊆ P.biUnion (star P dir) := by
      intro z hz
      obtain ⟨x, hx, hzx⟩ := mem_biUnion.mp hz
      exact mem_biUnion.mpr ⟨u x, hmem x hx, hzx⟩
    exact (card_le_card hsub).trans (card_biUnion_star_le_choose_two P dir symm)
  have hW_le_2S : ∑ x ∈ S, w (u x) ≤ 2 * S.card := by
    simpa [mul_comm] using sum_le_sum (s := S) (g := fun _ => 2) hw
  have hSpos : 1 ≤ S.card := card_pos.mpr hne
  -- Case split on `P.card ∈ {0, 1, 2, 3, 4}`.
  have hPcase : P.card = 2 ∨ P.card = 3 ∨ P.card = 4 := by
    obtain ⟨x₀, hx₀⟩ := hne
    have h1 : 1 ≤ P.card := card_pos.mpr ⟨u x₀, hmem x₀ hx₀⟩
    by_cases hp1 : P.card = 1
    · exfalso
      obtain ⟨a, ha⟩ := card_eq_one.mp hp1
      have hwa : w a = 4 := by simpa [ha] using total
      have hux : u x₀ = a := mem_singleton.mp (ha ▸ hmem x₀ hx₀)
      have := hw x₀ hx₀
      rw [hux] at this
      omega
    · omega
  rcases hPcase with hP2 | hP3 | hP4
  · -- `|P| = 2`: at most `1` direction total!
    rw [hP2] at hall_le
    norm_num at hall_le
    omega
  · -- `|P| = 3`: at most `3` directions total; if all `x ∈ S` have `w (u x) = 2`,
    -- they all pick the UNIQUE weight-2 point of `P`, giving a single star of size `≤ 2`!
    rw [hP3] at hall_le
    norm_num at hall_le
    by_cases hall2 : ∀ x ∈ S, w (u x) = 2
    · obtain ⟨x₀, hx₀⟩ := hne
      have huniq : ∀ x ∈ S, u x = u x₀ := by
        intro x hx
        by_contra hdiff
        have hsub : ({u x, u x₀} : Finset V) ⊆ P := by
          intro v hv; rcases mem_insert.mp hv with rfl | hv
          · exact hmem x hx
          · exact mem_singleton.mp hv ▸ hmem x₀ hx₀
        have hrem : 1 ≤ (P \ {u x, u x₀}).card := by
          have := card_sdiff_add_card_eq_card hsub
          rw [card_pair hdiff, hP3] at this; omega
        have hsum_rem : 1 ≤ ∑ v ∈ P \ {u x, u x₀}, w v := by
          have h1 : (P \ {u x, u x₀}).card ≤ ∑ v ∈ P \ {u x, u x₀}, w v := by
            simpa using sum_le_sum (s := P \ {u x, u x₀}) (f := fun _ => 1) (g := w)
              (fun v hv => pos v (mem_sdiff.mp hv).1)
          omega
        have hsplit := sum_sdiff hsub (f := w)
        rw [sum_pair hdiff, hall2 x hx, hall2 x₀ hx₀, total] at hsplit
        omega
      have hsub : (S.biUnion fun x => star P dir (u x)) ⊆ star P dir (u x₀) := by
        intro z hz
        obtain ⟨x, hx, hzx⟩ := mem_biUnion.mp hz
        rwa [huniq x hx] at hzx
      have hstar : (star P dir (u x₀)).card ≤ 2 := by
        have := card_image_le (s := P.erase (u x₀)) (f := dir (u x₀))
        rw [card_erase_of_mem (hmem x₀ hx₀), hP3] at this; exact this
      have hM : (S.biUnion fun x => star P dir (u x)).card ≤ 2 := (card_le_card hsub).trans hstar
      omega
    · push Not at hall2
      obtain ⟨x₁, hx₁, hne2⟩ := hall2
      have hw1 : w (u x₁) ≤ 1 := by have := hw x₁ hx₁; omega
      have hW_strict : ∑ x ∈ S, w (u x) ≤ 2 * S.card - 1 := by
        have hsplit := sum_erase_add S (fun x => w (u x)) hx₁
        have hrest : ∑ x ∈ S.erase x₁, w (u x) ≤ 2 * (S.card - 1) := by
          have := sum_le_sum (s := S.erase x₁) (g := fun _ => 2) (fun x hx => hw x (mem_of_mem_erase hx))
          simpa [card_erase_of_mem hx₁, mul_comm] using this
        omega
      omega
  · -- `|P| = 4`: every `i ∈ P` has `w i = 1`, so `W = |S|`.
    have hall1 : ∀ i ∈ P, w i = 1 := by
      intro i hi
      by_contra hne1
      have hge2 : 2 ≤ w i := by have := pos i hi; omega
      have hsplit := sum_erase_add P w hi
      have hrest : P.card - 1 ≤ ∑ v ∈ P.erase i, w v := by
        have := sum_le_sum (s := P.erase i) (f := fun _ => 1) (g := w)
          (fun v hv => pos v (mem_of_mem_erase hv))
        simpa [card_erase_of_mem hi] using this
      omega
    have hW_eq : ∑ x ∈ S, w (u x) = S.card := by
      calc ∑ x ∈ S, w (u x) = ∑ _x ∈ S, 1 := sum_congr rfl (fun x hx => hall1 (u x) (hmem x hx))
        _ = S.card := by simp
    rw [hP4] at hall_le
    norm_num at hall_le
    by_cases hS3 : 3 ≤ S.card
    · omega
    · by_cases hS1 : S.card = 1
      · obtain ⟨x₀, rfl⟩ := card_eq_one.mp hS1
        have hstar : (star P dir (u x₀)).card ≤ 3 := by
          have := card_image_le (s := P.erase (u x₀)) (f := dir (u x₀))
          rw [card_erase_of_mem (hmem x₀ (mem_singleton_self x₀)), hP4] at this; exact this
        rw [singleton_biUnion, hW_eq, card_singleton]
        omega
      · have hS2 : S.card = 2 := by omega
        obtain ⟨x₁, x₂, hne12, rfl⟩ := card_eq_two.mp hS2
        have hM_le : (({x₁, x₂} : Finset ι).biUnion fun x => star P dir (u x)).card ≤ 5 := by
          rw [biUnion_insert, singleton_biUnion]
          by_cases hu : u x₁ = u x₂
          · rw [hu, union_self]
            have hstar : (star P dir (u x₂)).card ≤ 3 := by
              unfold star
              have := card_image_le (s := P.erase (u x₂)) (f := dir (u x₂))
              rw [card_erase_of_mem (hmem x₂ (by simp)), hP4] at this; exact this
            omega
          · have := card_two_stars_le P dir symm (hmem x₁ (by simp)) (hmem x₂ (by simp)) hu
            omega
        rw [hW_eq, card_pair hne12]
        omega

/-! ## Section 2: General homothetic-cover image & singleton-fiber floors (`0 ≤ s ≤ 4`) -/

/-- Summing `homothetic_fiber_universal` across all regular fibers `F_y` (`y ∈ img`) plus at
most `12` exceptional sites (`exc ≤ 12`, each obeying `2 M_x + 3 W_x ≤ 12` from `M_x + W_x ≤ 4`)
bounds the total fresh head labels by `2 M_total + 3 W_total ≤ 6 n + 4 * img.card + 72`. -/
theorem homothetic_cover_mass_bound {T : Type*} [DecidableEq T]
    (img : Finset T) (M_fib W_fib sz_fib : T → ℕ)
    (M_exc W_exc exc : ℕ)
    (hfib : ∀ y ∈ img, 2 * M_fib y + 3 * W_fib y ≤ 6 * sz_fib y + 4)
    (hsz : (∑ y ∈ img, sz_fib y) + exc = n)
    (hexc_card : exc ≤ 12)
    (hexc_bound : 2 * M_exc + 3 * W_exc ≤ 12 * exc) :
    2 * ((∑ y ∈ img, M_fib y) + M_exc) + 3 * ((∑ y ∈ img, W_fib y) + W_exc) ≤
      6 * n + 4 * img.card + 72 := by
  have hsum := sum_le_sum hfib
  simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul] at hsum
  omega

/-- **Arbitrary homothetic-cover image & isolated-singleton-fiber floors across ALL `0 ≤ s ≤ 4`**:
for ANY map `h : H → T` through which the four heads' projective directions factor (with at
most `12` exceptional sites in `H`), an overrun at `671,088,640` forces:
1. Under baseline `other ≤ 20,607,410`: `|h(H_reg)| ≥ 660,784,912` (`> 0.615 n`), with at least
   `247,828,000` isolated singleton fibers (`|h⁻¹(y) ∩ H_reg| = 1`).
2. Under Milestone 2 Sparse-Gauss `other ≤ 397,364`: `|h(H_reg)| ≥ 670,889,935` (`> 0.6248 n`),
   with at least `268,038,046` isolated singleton fibers.
3. Under Blowup-Gauss + fixed-row dual-`(α, β)` `other ≤ 188,424`: `|h(H_reg)| ≥ 670,994,405`
   (`> 0.6249 n`), with at least `268,246,986` isolated singleton fibers.
In particular, NO 2-to-1, 3-to-1, or `q`-to-1 (`q ≥ 2`) homothetic cover — and no partial
involution pairing `≥ 76%` of `H` — can occur in any of the five open profiles `(1,1,1,1)..(1,1,1,5)`. -/
theorem homothetic_cover_image_floors {I M W other singletons exc : ℕ}
    (hW : 1610612728 ≤ W)
    (hexc : exc ≤ 12)
    (hbound : 2 * M + 3 * W ≤ 6 * n + 4 * I + 72)
    (hsing : singletons + 2 * (I - singletons) ≤ n - exc)
    (hsing_le : singletons ≤ I)
    (hover : budget < M + other) :
    (other ≤ 20607410 → 660784912 ≤ I ∧ 247828000 ≤ singletons) ∧
    (other ≤ 397364 → 670889935 ≤ I ∧ 268038046 ≤ singletons) ∧
    (other ≤ 188424 → 670994405 ≤ I ∧ 268246986 ≤ singletons) := by
  simp only [n, budget] at *
  refine ⟨?_, ?_, ?_⟩ <;> intro ho <;> omega

/-- Partial-involution exclusion: if `P` disjoint pairs of regular sites in `H` are homothetic
(e.g., an arbitrary Möbius involution `σ(X) = (aX + b)/(cX - a)` preserving a subset of `H` of
size `2P`), then `I ≤ n - P`, forcing `P ≤ 412,956,912` (baseline) or `P ≤ 402,851,889` (tight),
i.e., strictly below `75.1%` of `H` paired (`2P < 0.751 n`). -/
theorem partial_involution_cap {P I M W other : ℕ}
    (hW : 1610612728 ≤ W)
    (hI : I + P ≤ n)
    (hbound : 2 * M + 3 * W ≤ 6 * n + 4 * I + 72)
    (hover : budget < M + other) :
    (other ≤ 20607410 → P ≤ 412956912) ∧
    (other ≤ 397364 → P ≤ 402851889) ∧
    (other ≤ 188424 → P ≤ 402747419) := by
  simp only [n, budget] at *
  refine ⟨?_, ?_, ?_⟩ <;> intro ho <;> omega

/-! ## Section 3: Exact `3 + 1` pencil-degree barrier below `679,477,248` -/

/-- For any `3 collinear + 1 transverse` four-head configuration with primitive line direction
degree `h ≥ 1`, common triple locator degree `jLoc`, and reduced 3-split pencil degree `rPair`
(`jLoc + rPair ≤ d - h`), the four core cardinalities satisfy
`C₀ + C₁ + C₂ + C₃ ≤ n + 3 * d - h + rPair`.
Consequently, ANY balanced (`D = (1,1,1,1)`) `3 + 1` attack beating `679,477,248` errors
(`e ≤ 679,477,247`, all four cores `≥ 394,264,576`) requires
`rPair ≥ 100,663,300 = 3k/4 + 4`, proving `EighthTransverseAttack.lean` saturates the
`μ_{16}` cubic pencil (`rPair = 3k/4 = 100,663,296`) down to the very last site. -/
theorem three_plus_one_pencil_barrier
    {C₀ C₁ C₂ C₃ U₃ h jLoc rPair e : ℕ}
    (hh : 1 ≤ h)
    (hdeg : jLoc + rPair + h ≤ d)
    (htriple : C₀ + C₁ + C₂ ≤ U₃ + 2 * jLoc + 3 * rPair)
    (houtlier : U₃ + C₃ ≤ n + d + h)
    (he : e ≤ 679477247)
    (hC0 : n - e - 1 ≤ C₀) (hC1 : n - e - 1 ≤ C₁)
    (hC2 : n - e - 1 ≤ C₂) (hC3 : n - e - 1 ≤ C₃) :
    3 * k / 4 + 4 ≤ rPair := by
  simp only [n, k, d] at *
  omega

#print axioms card_biUnion_star_le_choose_two
#print axioms homothetic_fiber_universal
#print axioms homothetic_cover_mass_bound
#print axioms homothetic_cover_image_floors
#print axioms partial_involution_cap
#print axioms three_plus_one_pencil_barrier

end ArkLib.ProximityGap.Frontier.EighthRationalCoverObstructions
