/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Individual Pairwise Direction-Map Image Floors for Eighth-Rate Four-Head Profiles

At the eighth-rate second-prime successor `e = 671,088,640` (`n = 2^30`, `k = 2^27`, `d = 2^27 - 1`,
`t = 3k`, `B₂ = 2^31`), every surviving overrun is a noncollinear four-head quartet with sorted
fresh-site deficits `(1, 1, 1, q)` for `q ∈ {1, 2, 3, 4, 5}` (`0 ≤ s ≤ q - 1`).

Whereas `EighthRationalCoverObstructions` bounds a *joint* map `h : H → T` factoring all four heads'
directions simultaneously, this module proves **individual** image-size lower bounds on each
pairwise direction map `z_{ij} : H → Z` (`0 ≤ i < j ≤ 3`) directly from fresh-label disjointness
(`G_i ∩ G_j = ∅`) and core-overlap degrees (`|C_i ∩ C_j| ≤ d`, triangle
`|C_0∩C_1|+|C_0∩C_2|+|C_1∩C_2| ≤ 2d + 2(q - 1)` from `y_2 + 2 y_3 ≤ 2d` and `y_3 ≤ 2(q - 1)`),
requiring **no** symmetry, monomial, or opposite-side assumptions (except the constant involution `J`
for the saturated `q = 1` profile):

1. **Universal multi-slot subset image lemma (`multi_slot_subset_image_ge`)**:
   for any head `C ⊆ H` with deficit `q ≥ 1` whose assigned labels `G` each have `≥ q` fresh sites
   in `H \ C`, any subset `A ⊆ H \ C` on which `L = z` obeys
   `A.card + q * G.card ≤ (H \ C).card + q * (G ∩ A.image z).card`.
2. **Pairwise disjointness image bounds (`pair_direction_image_ge`, `head3_pair_direction_image_ge`)**:
   combining two heads `i, j` on `C_j \ C_i` and `C_i \ C_j` (landing in disjoint sets `G_i, G_j`)
   gives exact image floors on `z_{ij}(H)` with zero `ℕ`-subtraction truncation.
3. **Exact production floors at `671,088,640` (`res4 ≤ 189,082` Blowup-Dual, and `res4 ≤ 397,364` Sparse-Gauss)**:
   - **`q = 5`**: every `z_{01}, z_{02}, z_{12}` has `|z_{ij}(H)| ≥ 536,681,827` (`> 0.4998 n > n/3`),
     at least one has **`≥ 626,223,335`** (`> 0.5832 n > n/2`, ruling out `X^2` or any 2-to-1 cover),
     and every `z_{03}, z_{13}, z_{23}` has **`≥ 321,933,459`** (`> 0.2998 n > n/4`, ruling out `X^4`
     or any 4-to-1 cover for **all six** pairwise direction maps).
   - **`q = 4`**: every `z_{01}, z_{02}, z_{12}` has `≥ 503,127,395` (`> 0.4686 n > n/3`), and at least
     one has **`≥ 603,853,715`** (`> 0.5624 n > n/2`, ruling out any 2-to-1 cover).
   - **`q = 3`**: every `z_{01}, z_{02}, z_{12}` has `≥ 447,203,342` (`> 0.4165 n > n/3`), and at least
     one has **`≥ 566,571,014`** (`> 0.5277 n > n/2`, ruling out any 2-to-1 cover).
   - **`q = 2`**: every `z_{01}, z_{02}, z_{12}` has `≥ 335,355,235` (`> 0.3123 n > n/4`), and at least
     one has **`≥ 492,005,611`** (`> 0.4582 n > n/3`, ruling out any 3-to-1 cover).
   - **`q = 1`** (saturated `(1,1,1,1)` with constant involution `J`): the three opposite-pair maps
     satisfy `|z_1(H)| + |z_2(H)| + |z_3(H)| ≥ 1,073,458,195` (`> 0.9997 n`), each `|z_a(H)| ≥ 268,340,914`,
     and at least one has **`≥ 357,819,399`** (`> 0.3332 n > n/4`, ruling out all three factoring through `X^4`).
4. **General `r`-to-1 factorization exclusion (`no_r_to_one_of_image_gt`)**:
   if `z` factors through any map `h : ι → T` with `r * |h(H)| ≤ |H|`, then `r * |z(H)| ≤ |H|`.
   Thus no individual map above `n / r` can factor through `X^r` or any `r`-to-1 map on `H`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthDirectionImageFloors

open Finset

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev e5k : ℕ := 671088640
abbrev budget : ℕ := 2147483648

/-! ## Section 1: Universal Finset multi-slot image and disjointness lemmas -/

/-- **Universal multi-slot subset image bound**: if every label `w ∈ G` has at least `q` fresh
sites in `H \ C` under `L`, and `A ⊆ H \ C` is a subset on which `L = z`, then
`A.card + q * G.card ≤ (H \ C).card + q * (G ∩ A.image z).card`. -/
theorem multi_slot_subset_image_ge {ι Z : Type*} [DecidableEq ι] [DecidableEq Z]
    (H C A : Finset ι) (G : Finset Z) (L z : ι → Z) (q : ℕ)
    (hA : A ⊆ H \ C)
    (hLz : ∀ x ∈ A, L x = z x)
    (hslot : ∀ w ∈ G, q ≤ ((H \ C).filter fun x => L x = w).card) :
    A.card + q * G.card ≤ (H \ C).card + q * (G ∩ A.image z).card := by
  let Gout := G \ A.image z
  let Uout := (H \ C).filter fun x => L x ∈ Gout
  have hdisj : Disjoint A Uout := by
    rw [Finset.disjoint_left]
    intro x hxA hxU
    have hxGout : L x ∈ Gout := (mem_filter.mp hxU).2
    have hnot : L x ∉ A.image z := (mem_sdiff.mp hxGout).2
    rw [hLz x hxA] at hnot
    exact hnot (mem_image_of_mem z hxA)
  have hsub : A ∪ Uout ⊆ H \ C := union_subset hA (filter_subset _ _)
  have hcard_union : A.card + Uout.card ≤ (H \ C).card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card hsub
  have hUout_ge : q * Gout.card ≤ Uout.card := by
    have hbi : Gout.biUnion (fun w => (H \ C).filter fun x => L x = w) ⊆ Uout := by
      intro x hx
      obtain ⟨w, hw, hxw⟩ := mem_biUnion.mp hx
      obtain ⟨hxHC, hLx⟩ := mem_filter.mp hxw
      exact mem_filter.mpr ⟨hxHC, hLx.symm ▸ hw⟩
    have hpw : (Gout : Set Z).PairwiseDisjoint (fun w => (H \ C).filter fun x => L x = w) := by
      intro w₁ _ w₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hne ((mem_filter.mp hx1).2.symm.trans (mem_filter.mp hx2).2)
    have hsum : ∑ w ∈ Gout, ((H \ C).filter fun x => L x = w).card ≤ Uout.card := by
      rw [← card_biUnion hpw]
      exact card_le_card hbi
    have hq : q * Gout.card ≤ ∑ w ∈ Gout, ((H \ C).filter fun x => L x = w).card := by
      calc q * Gout.card = ∑ _w ∈ Gout, q := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ Gout, ((H \ C).filter fun x => L x = w).card :=
          sum_le_sum (fun w hw => hslot w (mem_sdiff.mp hw).1)
    exact hq.trans hsum
  have hGsplit : (G ∩ A.image z).card + Gout.card = G.card := card_inter_add_card_sdiff G (A.image z)
  have hmul : q * (G ∩ A.image z).card + q * Gout.card = q * G.card := by
    rw [← Nat.mul_add, hGsplit]
  omega

/-- **Pairwise direction-map image lower bound for two general-deficit heads (`q_i, q_j`)**:
combining `C_j \ C_i ⊆ H \ C_i` (landing in `G_i`) and `C_i \ C_j ⊆ H \ C_j` (landing in `G_j`,
disjoint from `G_i`) bounds `z_ij(H)` from below without any symmetry assumption. -/
theorem pair_direction_image_ge {ι Z : Type*} [DecidableEq ι] [DecidableEq Z]
    (H Ci Cj : Finset ι) (Gi Gj : Finset Z) (Li Lj zij : ι → Z) (qi qj : ℕ)
    (hCi : Ci ⊆ H) (hCj : Cj ⊆ H)
    (hdisj : Disjoint Gi Gj)
    (hLi : ∀ x ∈ Cj \ Ci, Li x = zij x)
    (hLj : ∀ x ∈ Ci \ Cj, Lj x = zij x)
    (hsi : ∀ w ∈ Gi, qi ≤ ((H \ Ci).filter fun x => Li x = w).card)
    (hsj : ∀ w ∈ Gj, qj ≤ ((H \ Cj).filter fun x => Lj x = w).card) :
    qj * (Cj \ Ci).card + qi * (Ci \ Cj).card + qi * qj * (Gi.card + Gj.card) ≤
      qj * (H \ Ci).card + qi * (H \ Cj).card + qi * qj * (H.image zij).card := by
  have hsub_ji : Cj \ Ci ⊆ H \ Ci := sdiff_subset_sdiff hCj Subset.rfl
  have hsub_ij : Ci \ Cj ⊆ H \ Cj := sdiff_subset_sdiff hCi Subset.rfl
  have hi := multi_slot_subset_image_ge H Ci (Cj \ Ci) Gi Li zij qi hsub_ji hLi hsi
  have hj := multi_slot_subset_image_ge H Cj (Ci \ Cj) Gj Lj zij qj hsub_ij hLj hsj
  set Si := Gi ∩ (Cj \ Ci).image zij
  set Sj := Gj ∩ (Ci \ Cj).image zij
  have hdisjS : Disjoint Si Sj := hdisj.mono inter_subset_left inter_subset_left
  have hsubS : Si ∪ Sj ⊆ H.image zij := by
    refine union_subset ?_ ?_
    · exact inter_subset_right.trans (image_subset_image (sdiff_subset.trans hCj))
    · exact inter_subset_right.trans (image_subset_image (sdiff_subset.trans hCi))
  have hcardS : Si.card + Sj.card ≤ (H.image zij).card := by
    rw [← card_union_of_disjoint hdisjS]
    exact card_le_card hsubS
  have hi' := Nat.mul_le_mul_left qj hi
  have hj' := Nat.mul_le_mul_left qi hj
  have hS' := Nat.mul_le_mul_left (qi * qj) hcardS
  have h1 : qj * ((Cj \ Ci).card + qi * Gi.card) = qj * (Cj \ Ci).card + qi * qj * Gi.card := by ring
  have h2 : qj * ((H \ Ci).card + qi * Si.card) = qj * (H \ Ci).card + qi * qj * Si.card := by ring
  have h3 : qi * ((Ci \ Cj).card + qj * Gj.card) = qi * (Ci \ Cj).card + qi * qj * Gj.card := by ring
  have h4 : qi * ((H \ Cj).card + qj * Sj.card) = qi * (H \ Cj).card + qi * qj * Sj.card := by ring
  have h5 : qi * qj * (Gi.card + Gj.card) = qi * qj * Gi.card + qi * qj * Gj.card := by ring
  have h6 : qi * qj * (Si.card + Sj.card) = qi * qj * Si.card + qi * qj * Sj.card := by ring
  omega

/-- Specialization of `pair_direction_image_ge` to two deficit-1 heads (`q_i = q_j = 1`). -/
theorem unit_pair_direction_image_ge {ι Z : Type*} [DecidableEq ι] [DecidableEq Z]
    (H Ci Cj : Finset ι) (Gi Gj : Finset Z) (Li Lj zij : ι → Z)
    (hCi : Ci ⊆ H) (hCj : Cj ⊆ H)
    (hdisj : Disjoint Gi Gj)
    (hLi : ∀ x ∈ Cj \ Ci, Li x = zij x)
    (hLj : ∀ x ∈ Ci \ Cj, Lj x = zij x)
    (hsi : ∀ w ∈ Gi, 1 ≤ ((H \ Ci).filter fun x => Li x = w).card)
    (hsj : ∀ w ∈ Gj, 1 ≤ ((H \ Cj).filter fun x => Lj x = w).card) :
    (Cj \ Ci).card + (Ci \ Cj).card + Gi.card + Gj.card ≤
      (H \ Ci).card + (H \ Cj).card + (H.image zij).card := by
  have h := pair_direction_image_ge H Ci Cj Gi Gj Li Lj zij 1 1 hCi hCj hdisj hLi hLj hsi hsj
  omega

/-- **Opposite-pair involution image bound** for saturated `(1, 1, 1, 1)`: when four deficit-1
heads have pairwise disjoint assigned sets `G_0, G_1, G_2, G_3` and an involution `J : Z → Z`
satisfies `z_{23}(x) = J (z_{01}(x))` on `H`, then `G_0 ∪ G_1` and `G_2 ∪ G_3` land in
`z_{01}(H) ∪ J(z_{01}(H))`, giving `2 * |z_{01}(H)|` bounded from below by both symmetric
differences minus the total deficit across all four heads. -/
theorem opposite_pair_involution_image_ge {ι Z : Type*} [DecidableEq ι] [DecidableEq Z]
    (H C0 C1 C2 C3 : Finset ι) (G0 G1 G2 G3 : Finset Z)
    (L0 L1 L2 L3 z01 : ι → Z) (J : Z → Z)
    (hC0 : C0 ⊆ H) (hC1 : C1 ⊆ H) (hC2 : C2 ⊆ H) (hC3 : C3 ⊆ H)
    (hd01 : Disjoint G0 G1) (hd02 : Disjoint G0 G2) (hd03 : Disjoint G0 G3)
    (hd12 : Disjoint G1 G2) (hd13 : Disjoint G1 G3) (hd23 : Disjoint G2 G3)
    (hL0 : ∀ x ∈ C1 \ C0, L0 x = z01 x)
    (hL1 : ∀ x ∈ C0 \ C1, L1 x = z01 x)
    (hL2 : ∀ x ∈ C3 \ C2, L2 x = J (z01 x))
    (hL3 : ∀ x ∈ C2 \ C3, L3 x = J (z01 x))
    (hs0 : ∀ w ∈ G0, 1 ≤ ((H \ C0).filter fun x => L0 x = w).card)
    (hs1 : ∀ w ∈ G1, 1 ≤ ((H \ C1).filter fun x => L1 x = w).card)
    (hs2 : ∀ w ∈ G2, 1 ≤ ((H \ C2).filter fun x => L2 x = w).card)
    (hs3 : ∀ w ∈ G3, 1 ≤ ((H \ C3).filter fun x => L3 x = w).card) :
    (C1 \ C0).card + (C0 \ C1).card + (C3 \ C2).card + (C2 \ C3).card +
        G0.card + G1.card + G2.card + G3.card ≤
      (H \ C0).card + (H \ C1).card + (H \ C2).card + (H \ C3).card +
        2 * (H.image z01).card := by
  have h0 := multi_slot_subset_image_ge H C0 (C1 \ C0) G0 L0 z01 1
    (sdiff_subset_sdiff hC1 Subset.rfl) hL0 hs0
  have h1 := multi_slot_subset_image_ge H C1 (C0 \ C1) G1 L1 z01 1
    (sdiff_subset_sdiff hC0 Subset.rfl) hL1 hs1
  have h2 := multi_slot_subset_image_ge H C2 (C3 \ C2) G2 L2 (J ∘ z01) 1
    (sdiff_subset_sdiff hC3 Subset.rfl) hL2 hs2
  have h3 := multi_slot_subset_image_ge H C3 (C2 \ C3) G3 L3 (J ∘ z01) 1
    (sdiff_subset_sdiff hC2 Subset.rfl) hL3 hs3
  set S0 := G0 ∩ (C1 \ C0).image z01
  set S1 := G1 ∩ (C0 \ C1).image z01
  set S2 := G2 ∩ (C3 \ C2).image (J ∘ z01)
  set S3 := G3 ∩ (C2 \ C3).image (J ∘ z01)
  have h01 : Disjoint S0 S1 := hd01.mono inter_subset_left inter_subset_left
  have h23 : Disjoint S2 S3 := hd23.mono inter_subset_left inter_subset_left
  have h01_23 : Disjoint (S0 ∪ S1) (S2 ∪ S3) := by
    refine disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact disjoint_union_right.mpr
        ⟨hd02.mono inter_subset_left inter_subset_left, hd03.mono inter_subset_left inter_subset_left⟩
    · exact disjoint_union_right.mpr
        ⟨hd12.mono inter_subset_left inter_subset_left, hd13.mono inter_subset_left inter_subset_left⟩
  have hsubU : (S0 ∪ S1) ∪ (S2 ∪ S3) ⊆ (H.image z01) ∪ ((H.image z01).image J) := by
    refine union_subset (union_subset ?_ ?_) (union_subset ?_ ?_)
    · exact (inter_subset_right.trans (image_subset_image (sdiff_subset.trans hC1))).trans subset_union_left
    · exact (inter_subset_right.trans (image_subset_image (sdiff_subset.trans hC0))).trans subset_union_left
    · have himg : (C3 \ C2).image (J ∘ z01) ⊆ (H.image z01).image J := by
        rw [← Finset.image_image]
        exact image_subset_image (image_subset_image (sdiff_subset.trans hC3))
      exact (inter_subset_right.trans himg).trans subset_union_right
    · have himg : (C2 \ C3).image (J ∘ z01) ⊆ (H.image z01).image J := by
        rw [← Finset.image_image]
        exact image_subset_image (image_subset_image (sdiff_subset.trans hC2))
      exact (inter_subset_right.trans himg).trans subset_union_right
  have hcard : S0.card + S1.card + S2.card + S3.card ≤ 2 * (H.image z01).card := by
    have hu1 : ((S0 ∪ S1) ∪ (S2 ∪ S3)).card = S0.card + S1.card + (S2.card + S3.card) := by
      rw [card_union_of_disjoint h01_23, card_union_of_disjoint h01, card_union_of_disjoint h23]
    have hu2 : ((H.image z01) ∪ ((H.image z01).image J)).card ≤ 2 * (H.image z01).card := by
      have hle := card_union_le (H.image z01) ((H.image z01).image J)
      have hJ : ((H.image z01).image J).card ≤ (H.image z01).card := card_image_le
      omega
    have := card_le_card hsubU
    omega
  omega

/-- **General `r`-to-1 factorization exclusion**: if a direction map `z : ι → Z` factors through
any map `h : ι → T` (`∀ x ∈ H, z x = f (h x)`) whose image on `H` has size `r * |h(H)| ≤ |H|`
(for example `h(x) = x^r` on a subgroup `H` of order divisible by `r`), then `r * |z(H)| ≤ |H|`. -/
theorem image_card_mul_le_of_factor {ι T Z : Type*} [DecidableEq T] [DecidableEq Z]
    (H : Finset ι) (z : ι → Z) (h : ι → T) (f : T → Z) (r : ℕ)
    (hfac : ∀ x ∈ H, z x = f (h x))
    (hr : r * (H.image h).card ≤ H.card) :
    r * (H.image z).card ≤ H.card := by
  have hsub : H.image z ⊆ (H.image h).image f := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
    rw [hfac x hx]
    exact mem_image_of_mem f (mem_image_of_mem h hx)
  have hle : (H.image z).card ≤ (H.image h).card := (card_le_card hsub).trans card_image_le
  exact (Nat.mul_le_mul_left r hle).trans hr

/-! ## Section 2: Exact production image floors across all five `(1,1,1,q)` profiles (`671,088,640`) -/

/-- **Individual direction-map image floors across `(1, 1, 1, 2)` through `(1, 1, 1, 5)`** at
`e = 671,088,640` under Blowup-Dual residual `other ≤ 189,082` (using the unconditional triple-overlap
triangle bound `m01 + m02 + m12 = y_2 + 3 y_3 ≤ 2 d + 2 (q - 1)`):
- **`q = 5`**: every `z_{01}, z_{02}, z_{12}` has `|z_{ij}(H)| ≥ 536,681,827` (`> n/3`),
  at least one has **`≥ 626,223,335`** (`> 0.5832 n > n/2`, excluding any 2-to-1 factorization),
  and every `z_{03}, z_{13}, z_{23}` has **`≥ 321,933,459`** (`> 0.2998 n > n/4`, excluding any
  4-to-1 factorization for all six pairwise direction maps).
- **`q = 4`**: every `z_{01}, z_{02}, z_{12}` has `≥ 503,127,395` (`> n/3`), and at least one
  has **`≥ 603,853,715`** (`> 0.5624 n > n/2`, excluding any 2-to-1 factorization).
- **`q = 3`**: every `z_{01}, z_{02}, z_{12}` has `≥ 447,203,342` (`> n/3`), and at least one
  has **`≥ 566,571,014`** (`> 0.5277 n > n/2`, excluding any 2-to-1 factorization).
- **`q = 2`**: every `z_{01}, z_{02}, z_{12}` has `≥ 335,355,235` (`> n/4`), and at least one
  has **`≥ 492,005,611`** (`> 0.4582 n > n/3`, excluding any 3-to-1 factorization). -/
theorem profile_q2_to_q5_image_floors
    (q : ℕ) (hq2 : 2 ≤ q) (hq5 : q ≤ 5)
    (g0 g1 g2 g3 other : ℕ)
    (m01 m02 m12 m03 m13 m23 : ℕ)
    (z01 z02 z12 z03 z13 z23 : ℕ)
    (hother : other ≤ 189082)
    (hover : budget < g0 + g1 + g2 + g3 + other)
    (hg0 : g0 ≤ e5k + 1) (hg1 : g1 ≤ e5k + 1) (hg2 : g2 ≤ e5k + 1)
    (hg3 : g3 ≤ 1 + e5k / q)
    (hm01 : m01 ≤ d) (hm02 : m02 ≤ d) (hm12 : m12 ≤ d)
    (hm03 : m03 ≤ d) (hm13 : m13 ≤ d) (hm23 : m23 ≤ d)
    (htri : m01 + m02 + m12 ≤ 2 * d + 2 * (q - 1))
    -- From `unit_pair_direction_image_ge` on `C_i` (`3k - 1`), `H \ C_i` (`5k + 1`):
    (hz01 : 2 * (3 * k - 1 - m01) + g0 + g1 ≤ 2 * (e5k + 1) + z01)
    (hz02 : 2 * (3 * k - 1 - m02) + g0 + g2 ≤ 2 * (e5k + 1) + z02)
    (hz12 : 2 * (3 * k - 1 - m12) + g1 + g2 ≤ 2 * (e5k + 1) + z12)
    -- From `pair_direction_image_ge` (`q_i = 1, q_j = q`) on `C_i` (`3k - 1`), `C_3` (`3k - q`):
    (hz03 : q * (3 * k - q - m03) + (3 * k - 1 - m03) + q * (g0 + g3) ≤
      q * (e5k + 1) + (e5k + q) + q * z03)
    (hz13 : q * (3 * k - q - m13) + (3 * k - 1 - m13) + q * (g1 + g3) ≤
      q * (e5k + 1) + (e5k + q) + q * z13)
    (hz23 : q * (3 * k - q - m23) + (3 * k - 1 - m23) + q * (g2 + g3) ≤
      q * (e5k + 1) + (e5k + q) + q * z23) :
    (q = 5 →
      536681827 ≤ min z01 (min z02 z12) ∧
      626223335 ≤ max z01 (max z02 z12) ∧
      n < 2 * max z01 (max z02 z12) ∧
      321933459 ≤ min z03 (min z13 z23) ∧
      n < 4 * min z03 (min z13 z23)) ∧
    (q = 4 →
      503127395 ≤ min z01 (min z02 z12) ∧
      603853715 ≤ max z01 (max z02 z12) ∧
      n < 2 * max z01 (max z02 z12)) ∧
    (q = 3 →
      447203342 ≤ min z01 (min z02 z12) ∧
      566571014 ≤ max z01 (max z02 z12) ∧
      n < 2 * max z01 (max z02 z12)) ∧
    (q = 2 →
      335355235 ≤ min z01 (min z02 z12) ∧
      492005611 ≤ max z01 (max z02 z12) ∧
      n < 3 * max z01 (max z02 z12)) := by
  simp only [n, k, d, e5k, budget] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    norm_num at hg3 hz03 hz13 hz23
    omega
  · rintro rfl
    norm_num at hg3
    omega
  · rintro rfl
    norm_num at hg3
    omega
  · rintro rfl
    norm_num at hg3
    omega

/-- **Individual direction-map image floors for saturated `(1, 1, 1, 1)`** at `e = 671,088,640`
under Blowup-Dual residual `other ≤ 189,082` (using `opposite_pair_involution_image_ge` across
the three opposite direction pairs `z_1 = z_{01}`, `z_2 = z_{02}`, `z_3 = z_{03}`):
- Sum of the three individual images: **`|z_1(H)| + |z_2(H)| + |z_3(H)| ≥ 1,073,458,195`** (`> 0.9997 n`).
- Every individual map obeys **`|z_a(H)| ≥ 268,340,914`** (`> 0.2499 n`).
- At least one of `z_1, z_2, z_3` obeys **`|z_a(H)| ≥ 357,819,399 > n/4`** (`> 0.3332 n`, ruling
  out all three direction maps simultaneously factoring through `X^4` or any 4-to-1 cover). -/
theorem profile_q1_saturated_image_floors
    (g0 g1 g2 g3 other : ℕ)
    (p1 p2 p3 z1 z2 z3 : ℕ)
    (hother : other ≤ 189082)
    (hover : budget < g0 + g1 + g2 + g3 + other)
    -- `p_a = |C_i ∩ C_j| + |C_k ∩ C_l| ≤ 2d` for each opposite pair, summing to `4d`:
    (hp1 : p1 ≤ 2 * d) (hp2 : p2 ≤ 2 * d) (hp3 : p3 ≤ 2 * d)
    (hpsum : p1 + p2 + p3 ≤ 4 * d)
    -- From `opposite_pair_involution_image_ge` with `|C_i| = 3k - 1`, `|H \ C_i| = 5k + 1`:
    (hz1 : 4 * (3 * k - 1) - 2 * p1 + g0 + g1 + g2 + g3 ≤ 4 * (e5k + 1) + 2 * z1)
    (hz2 : 4 * (3 * k - 1) - 2 * p2 + g0 + g1 + g2 + g3 ≤ 4 * (e5k + 1) + 2 * z2)
    (hz3 : 4 * (3 * k - 1) - 2 * p3 + g0 + g1 + g2 + g3 ≤ 4 * (e5k + 1) + 2 * z3) :
    1073458195 ≤ z1 + z2 + z3 ∧
    268340914 ≤ min z1 (min z2 z3) ∧
    357819399 ≤ max z1 (max z2 z3) ∧
    n < 4 * max z1 (max z2 z3) := by
  simp only [n, k, d, e5k, budget] at *
  omega

#print axioms multi_slot_subset_image_ge
#print axioms pair_direction_image_ge
#print axioms unit_pair_direction_image_ge
#print axioms opposite_pair_involution_image_ge
#print axioms image_card_mul_le_of_factor
#print axioms profile_q2_to_q5_image_floors
#print axioms profile_q1_saturated_image_floors

end ArkLib.ProximityGap.Frontier.EighthDirectionImageFloors
