/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorListEquivalence
import ArkLib.Research.ProximityGap.Frontier.PuncturedFourWordProfile
import ArkLib.Research.ProximityGap.Frontier.QuarterSplitWronskianSuborbits

/-! # Coupled odd split-pencil reduction, Wronskian collapse, and `n = 16, p = 97` barrier for `p₁` half-rate `268,435,457`

Formalizes the complete algebraic and Wronskian reduction of the `p₁` half-rate first named
successor (`δ₁ = 268,435,457 / 2^30`, `HasPuncturedList`):

1. **Exact algebraic reduction to coupled odd 3-split pencils (`exists_coupled_pencils_of_punctured_list`
   and `hasPuncturedList_yields_coupled_odd_pencils`):**
   From `PuncturedFourWordProfile.polynomial_profile` on a punctured domain `B` (`|B| + 1 = 4h`,
   `h ≥ 2`), EVERY one of the three possible error patterns `(0, 5, 0)`, `(1, 6, 0)`, `(0, 3, 1)`
   admits at least two distinct good triples `(a, b, u)` and `(a, b, v)` (forming a permutation of
   `Fin 4`), each yielding an exact degree-`(h - 1)` 3-split polynomial pencil
     `c₀ * ∏_{x ∈ S₀} (X - D x) + c₁ * ∏_{x ∈ S₁} (X - D x) + c₂ * ∏_{x ∈ S₂} (X - D x) = 0`
   on three pairwise disjoint `(h - 1)`-subsets of `B`, coupled by sharing at least `h - 2` roots
   in each of their first two fibers. At production `h = 2^28`, this gives coupled odd-degree
   `D_half = 268,435,455 = 2^28 - 1` 3-split pencils on `μ_{2^30}`.

2. **Unconditional trivial deck symmetry (`h = 1`):**
   * `no_scaling_symmetry_of_coprime`: `gcd(2^30, 268435455) = 1` kills every nontrivial scaling
     `x ↦ u * x` (`u ∈ μ_{2^30}`) preserving a fiber of size `268,435,455`.
   * `no_reciprocal_involution_three_odd_fibers`: `x ↦ u / x` has at most 2 fixed points in any
     field `F`, so it can never preserve three pairwise disjoint odd-size subsets of `Fˣ`.

3. **Sharp Wronskian collapse for `D_half = 268,435,455`:**
   * Subdegree floor `44,739,242 ≤ a` (`half_subdegree_floor`).
   * At most 6 nontrivial suborbits and permutation rank at most `7` (`half_orbit_count_sharp`),
     using `singleton ≤ 1` from trivial deck symmetry `h = 1`.
   * Prime factorization `268,435,455 = 3 · 5 · 29 · 43 · 113 · 127` (64 total divisors, 62 proper
     nontrivial divisors) and elimination of **60 of 62** proper nontrivial divisors, leaving only
     `t ∈ {53,687,091, 89,478,485, 268,435,455}` (`half_inner_degree_only_three`).
   * Exact rational orbifold excess and pair-curve genus floors for all three surviving stages,
     unconditional full-pencil excess `E_R ≥ 536,870,870 / 1,342,177,289 > 0.399999966`,
     excluded branch signatures, and characteristic headroom `2 * 2^30 * 268,435,455 < 2^59 < p₁ < p₂`.

4. **Exact `n = 16, p = 97` barrier witness (`barrier_n16_p97`):**
   Kernel-verified punctured 4-word list at `n = 16` (`h = 4`, `D = 3`) over `ZMod 97` with
   `w = 8` (`orderOf 8 = 16`), 4 distinct degree-6 polynomials agreeing with a common received word
   on 10 of 15 punctured points, error profile `(0, 5, 0)`, and characteristic `97 > 2 * 16 * 3 = 96`
   already meeting the Wronskian headroom hypothesis — showing that single-pencil degree/Wronskian
   methods alone cannot rule out `HasPuncturedList` without coupling or larger `n`.
-/

set_option autoImplicit false
noncomputable section

open Finset Polynomial
open ProximityGap.PuncturedFourWordProfile
open ProximityGap.QuarterSplitWronskianSuborbits

namespace ArkLib.ProximityGap.Frontier.HalfSuccessorSplitWronskian

/-! ## Section 1: Exact algebraic reduction to coupled odd 3-split pencils -/

section PencilReduction

variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- Monic nodal polynomial vanishing on `D(S)`. -/
def nodalPoly (D : I ↪ F) (S : Finset I) : F[X] :=
  ∏ x ∈ S, (Polynomial.X - C (D x))

omit [DecidableEq F] [Fintype I] [DecidableEq I] in
theorem monic_nodalPoly (D : I ↪ F) (S : Finset I) : (nodalPoly D S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C (D x))

omit [DecidableEq F] [Fintype I] [DecidableEq I] in
theorem nodalPoly_ne_zero (D : I ↪ F) (S : Finset I) : nodalPoly D S ≠ 0 :=
  (monic_nodalPoly D S).ne_zero

omit [DecidableEq F] [Fintype I] [DecidableEq I] in
theorem natDegree_nodalPoly (D : I ↪ F) (S : Finset I) : (nodalPoly D S).natDegree = S.card := by
  unfold nodalPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C (D x))]
  simp

omit [DecidableEq F] [Fintype I] in
theorem nodalPoly_union {D : I ↪ F} {S T : Finset I} (hdisj : Disjoint S T) :
    nodalPoly D (S ∪ T) = nodalPoly D S * nodalPoly D T :=
  Finset.prod_union hdisj

omit [DecidableEq F] [Fintype I] [DecidableEq I] in
/-- Any nonzero polynomial of degree at most `|S|` vanishing on `D(S)` is a nonzero scalar
multiple of `nodalPoly D S`. -/
theorem eq_const_mul_nodalPoly {D : I ↪ F} {f : F[X]} {S : Finset I}
    (hf : f ≠ 0) (hdeg : f.natDegree ≤ S.card) (hzero : ∀ x ∈ S, f.eval (D x) = 0) :
    ∃ c : F, c ≠ 0 ∧ f = C c * nodalPoly D S := by
  have hdvd : nodalPoly D S ∣ f := by
    unfold nodalPoly
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro x _ y _ hxy
      exact Polynomial.pairwise_coprime_X_sub_C D.injective hxy
    · intro x hx
      exact Polynomial.dvd_iff_isRoot.mpr (hzero x hx)
  obtain ⟨q, hq⟩ := hdvd
  have hq_ne : q ≠ 0 := fun hz => hf (by rw [hq, hz, mul_zero])
  have hdeg_eq : f.natDegree = (nodalPoly D S).natDegree + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul (nodalPoly_ne_zero D S) hq_ne]
  rw [natDegree_nodalPoly] at hdeg_eq
  have hq_deg0 : q.natDegree = 0 := by omega
  have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
  refine ⟨q.coeff 0, fun hc => hq_ne (by rw [hqC, hc, map_zero]), ?_⟩
  conv_lhs => rw [hq, hqC, mul_comm]

/-- A 3-split polynomial pencil of degree `d` on an embedded domain `D : I ↪ F`: three pairwise
disjoint `d`-element subsets `S₀, S₁, S₂ ⊆ I` and nonzero scalars `c₀, c₁, c₂ ∈ Fˣ` satisfying
`c₀ * ∏_{S₀} (X - D x) + c₁ * ∏_{S₁} (X - D x) + c₂ * ∏_{S₂} (X - D x) = 0`. -/
structure SplitPencil (D : I ↪ F) (d : ℕ) where
  S₀ : Finset I
  S₁ : Finset I
  S₂ : Finset I
  card₀ : S₀.card = d
  card₁ : S₁.card = d
  card₂ : S₂.card = d
  disj₀₁ : Disjoint S₀ S₁
  disj₁₂ : Disjoint S₁ S₂
  disj₂₀ : Disjoint S₂ S₀
  c₀ : F
  c₁ : F
  c₂ : F
  hc₀ : c₀ ≠ 0
  hc₁ : c₁ ≠ 0
  hc₂ : c₂ ≠ 0
  pencil_eq : C c₀ * nodalPoly D S₀ + C c₁ * nodalPoly D S₁ + C c₂ * nodalPoly D S₂ = 0

/-- Extract a degree-`(h - 1)` 3-split pencil from any triple `(i, j, k)` of distinct polynomials
whose error sets have size `h + 1`, pairwise overlaps of size `1`, and empty triple intersection. -/
theorem splitPencil_of_good_triple {D : I ↪ F} {q : Fin 4 → F[X]} {w : I → F} {h : ℕ}
    (hh : 2 ≤ h) (hn : Fintype.card I + 1 = 4 * h)
    (hinj : Function.Injective q) (hdeg : ∀ m, (q m).natDegree ≤ 2 * h - 2)
    (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (E : Fin 4 → Finset I) (hEdef : ∀ m, E m = univ.filter (fun x : I => (q m).eval (D x) ≠ w x))
    (hEcard : ∀ m, (E m).card = h + 1)
    (hij1 : (E i ∩ E j).card = 1) (hjk1 : (E j ∩ E k).card = 1) (hki1 : (E k ∩ E i).card = 1)
    (htriple : E i ∩ E j ∩ E k = ∅) :
    ∃ P : SplitPencil D (h - 1),
      P.S₀ = E i \ (E j ∪ E k) ∧ P.S₁ = E j \ (E k ∪ E i) ∧ P.S₂ = E k \ (E i ∪ E j) := by
  let S₀ := E i \ (E j ∪ E k)
  let S₁ := E j \ (E k ∪ E i)
  let S₂ := E k \ (E i ∪ E j)
  let C_com := (univ : Finset I) \ (E i ∪ E j ∪ E k)
  have hcard_sdiff_pair : ∀ (A B C : Finset I), A.card = h + 1 → (A ∩ B).card = 1 →
      (A ∩ C).card = 1 → A ∩ B ∩ C = ∅ → (A \ (B ∪ C)).card = h - 1 := by
    intro A B C hA hAB hAC hABC
    have hdisj : Disjoint (A ∩ B) (A ∩ C) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨hxA, hxB⟩, ⟨_, hxC⟩⟩
      have : x ∈ A ∩ B ∩ C := Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxA, hxB⟩, hxC⟩
      rw [hABC] at this; exact Finset.notMem_empty x this
    have hinter_card : (A ∩ (B ∪ C)).card = 2 := by
      rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj, hAB, hAC]
    have hsd := Finset.card_sdiff_add_card_inter A (B ∪ C)
    omega
  have hS₀_card : S₀.card = h - 1 := hcard_sdiff_pair (E i) (E j) (E k) (hEcard i) hij1
    (by rw [Finset.inter_comm]; exact hki1) htriple
  have hS₁_card : S₁.card = h - 1 := hcard_sdiff_pair (E j) (E k) (E i) (hEcard j) hjk1
    (by rw [Finset.inter_comm]; exact hij1) (by
      ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨hxj, hxk⟩, hxi⟩
      have : x ∈ E i ∩ E j ∩ E k := Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxi, hxj⟩, hxk⟩
      rw [htriple] at this; exact Finset.notMem_empty x this)
  have hS₂_card : S₂.card = h - 1 := hcard_sdiff_pair (E k) (E i) (E j) (hEcard k) hki1
    (by rw [Finset.inter_comm]; exact hjk1) (by
      ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨hxk, hxi⟩, hxj⟩
      have : x ∈ E i ∩ E j ∩ E k := Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxi, hxj⟩, hxk⟩
      rw [htriple] at this; exact Finset.notMem_empty x this)
  have hdisj₀₁ : Disjoint S₀ S₁ := Finset.disjoint_left.mpr fun x h0 h1 =>
    (Finset.mem_sdiff.mp h0).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h1).1)
  have hdisj₁₂ : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun x h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h2).1)
  have hdisj₂₀ : Disjoint S₂ S₀ := Finset.disjoint_left.mpr fun x h2 h0 =>
    (Finset.mem_sdiff.mp h2).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h0).1)
  -- Express each pairwise agreement set `U_{ab} = univ \ (E a ∪ E b)` as `C_com ∪ S_c`.
  have hU_ij : (univ : Finset I) \ (E i ∪ E j) = C_com ∪ S₂ ∧ Disjoint C_com S₂ := by
    constructor
    · ext x; simp only [C_com, S₂, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]; intro x hxC hxS
      simp only [C_com, S₂, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hxC hxS
      tauto
  have hU_jk : (univ : Finset I) \ (E j ∪ E k) = C_com ∪ S₀ ∧ Disjoint C_com S₀ := by
    constructor
    · ext x; simp only [C_com, S₀, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]; intro x hxC hxS
      simp only [C_com, S₀, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hxC hxS
      tauto
  have hU_ki : (univ : Finset I) \ (E k ∪ E i) = C_com ∪ S₁ ∧ Disjoint C_com S₁ := by
    constructor
    · ext x; simp only [C_com, S₁, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]; intro x hxC hxS
      simp only [C_com, S₁, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hxC hxS
      tauto
  -- Factor `q a - q b` for each pair `{i,j}, {j,k}, {k,i}`.
  have hpair_fac : ∀ (a b : Fin 4), a ≠ b → (E a ∩ E b).card = 1 →
      ∃ c : F, c ≠ 0 ∧ q a - q b = C c * nodalPoly D ((univ : Finset I) \ (E a ∪ E b)) := by
    intro a b hab h1
    have hUcard : ((univ : Finset I) \ (E a ∪ E b)).card = 2 * h - 2 := by
      have hu := Finset.card_union_add_card_inter (E a) (E b)
      have ha := hEcard a
      have hb := hEcard b
      have hsub := Finset.card_sdiff_of_subset (Finset.subset_univ (E a ∪ E b))
      rw [Finset.card_univ] at hsub
      omega
    have hne : q a - q b ≠ 0 := sub_ne_zero.mpr (hinj.ne hab)
    have hdeg_ab : (q a - q b).natDegree ≤ ((univ : Finset I) \ (E a ∪ E b)).card := by
      rw [hUcard]
      exact (Polynomial.natDegree_sub_le (q a) (q b)).trans (max_le (hdeg a) (hdeg b))
    have hzero : ∀ x ∈ (univ : Finset I) \ (E a ∪ E b), (q a - q b).eval (D x) = 0 := by
      intro x hx
      have hnot := (Finset.mem_sdiff.mp hx).2
      have hna : x ∉ E a := fun h => hnot (Finset.mem_union_left _ h)
      have hnb : x ∉ E b := fun h => hnot (Finset.mem_union_right _ h)
      rw [hEdef a] at hna; rw [hEdef b] at hnb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hna hnb
      rw [Polynomial.eval_sub, hna, hnb, sub_self]
    exact eq_const_mul_nodalPoly hne hdeg_ab hzero
  obtain ⟨c_ij, hc_ij, hq_ij⟩ := hpair_fac i j hij hij1
  obtain ⟨c_jk, hc_jk, hq_jk⟩ := hpair_fac j k hjk hjk1
  obtain ⟨c_ki, hc_ki, hq_ki⟩ := hpair_fac k i hki hki1
  rw [hU_ij.1, nodalPoly_union hU_ij.2] at hq_ij
  rw [hU_jk.1, nodalPoly_union hU_jk.2] at hq_jk
  rw [hU_ki.1, nodalPoly_union hU_ki.2] at hq_ki
  have hsum0 : (q j - q k) + (q k - q i) + (q i - q j) = 0 := by ring
  rw [hq_jk, hq_ki, hq_ij] at hsum0
  have hfac0 : nodalPoly D C_com *
      (C c_jk * nodalPoly D S₀ + C c_ki * nodalPoly D S₁ + C c_ij * nodalPoly D S₂) = 0 := by
    linear_combination hsum0
  have hpencil : C c_jk * nodalPoly D S₀ + C c_ki * nodalPoly D S₁ + C c_ij * nodalPoly D S₂ = 0 :=
    (mul_eq_zero.mp hfac0).resolve_left (nodalPoly_ne_zero D C_com)
  exact ⟨{
    S₀ := S₀, S₁ := S₁, S₂ := S₂
    card₀ := hS₀_card, card₁ := hS₁_card, card₂ := hS₂_card
    disj₀₁ := hdisj₀₁, disj₁₂ := hdisj₁₂, disj₂₀ := hdisj₂₀
    c₀ := c_jk, c₁ := c_ki, c₂ := c_ij
    hc₀ := hc_jk, hc₁ := hc_ki, hc₂ := hc_ij
    pencil_eq := hpencil }, rfl, rfl, rfl⟩

omit [Field F] [DecidableEq F] [Fintype I] in
private theorem multiplicity_eq_sum_ite (E : Fin 4 → Finset I) (x : I) :
    ProximityGap.PuncturedFourWordProfile.multiplicity E x =
    (if x ∈ E 0 then 1 else 0) + (if x ∈ E 1 then 1 else 0) +
    (if x ∈ E 2 then 1 else 0) + (if x ∈ E 3 then 1 else 0) :=
  rfl

omit [Field F] [DecidableEq F] [Fintype I] in
private theorem three_le_multiplicity_of_mem_three {E : Fin 4 → Finset I} {x : I}
    {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : x ∈ E i) (hj : x ∈ E j) (hk : x ∈ E k) :
    3 ≤ ProximityGap.PuncturedFourWordProfile.multiplicity E x := by
  rw [multiplicity_eq_sum_ite]
  have hcard : ({i, j, k} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hki.symm]),
      Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  have hsub : ({i, j, k} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun m : Fin 4 => x ∈ E m) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hm with rfl | rfl | rfl <;> assumption
  have hsum : (Finset.univ.filter (fun m : Fin 4 => x ∈ E m)).card =
      (if x ∈ E 0 then 1 else 0) + (if x ∈ E 1 then 1 else 0) +
      (if x ∈ E 2 then 1 else 0) + (if x ∈ E 3 then 1 else 0) := by
    have hb : (∑ m : Fin 4, if x ∈ E m then 1 else 0) =
        (Finset.univ.filter (fun m : Fin 4 => x ∈ E m)).card := by
      simp [Finset.sum_boole]
    rw [← hb, Fin.sum_univ_four]
  have hle := Finset.card_le_card hsub
  omega

omit [Field F] [DecidableEq F] [Fintype I] in
private theorem multiplicity_le_four (E : Fin 4 → Finset I) (x : I) :
    ProximityGap.PuncturedFourWordProfile.multiplicity E x ≤ 4 := by
  rw [multiplicity_eq_sum_ite]
  by_cases h0 : x ∈ E 0 <;> by_cases h1 : x ∈ E 1 <;>
    by_cases h2 : x ∈ E 2 <;> by_cases h3 : x ∈ E 3 <;>
    simp [h0, h1, h2, h3]

omit [Field F] [DecidableEq F] in
/-- Combinatorial core: in every one of the three patterns `(0, 5, 0)`, `(1, 6, 0)`, `(0, 3, 1)`
from `PuncturedFourWordProfile.classify`, there exists a permutation `(a, b, u, v)` of `Fin 4`
such that BOTH triples `(a, b, u)` and `(a, b, v)` have all pairwise overlaps of size `1` and
empty triple intersection, and their shared fibers overlap in at least `h - 2` elements. -/
theorem exists_two_coupled_good_triples {E : Fin 4 → Finset I} {h : ℕ}
    (_hh : 2 ≤ h) (hn : Fintype.card I + 1 = 4 * h)
    (hw : ∀ i, (E i).card ≤ h + 1)
    (hd : ∀ i j, i ≠ j → 2 * h + 1 ≤ (E i ∪ E j).card) :
    ∃ a b u v : Fin 4,
      a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ u ≠ v ∧
      (∀ m, (E m).card = h + 1) ∧
      (E a ∩ E b).card = 1 ∧ (E b ∩ E u).card = 1 ∧ (E u ∩ E a).card = 1 ∧ E a ∩ E b ∩ E u = ∅ ∧
      (E b ∩ E v).card = 1 ∧ (E v ∩ E a).card = 1 ∧ E a ∩ E b ∩ E v = ∅ ∧
      h - 2 ≤ ((E a \ (E b ∪ E u)) ∩ (E a \ (E b ∪ E v))).card ∧
      h - 2 ≤ ((E b \ (E u ∪ E a)) ∩ (E b \ (E v ∪ E a))).card := by
  obtain ⟨hEcard, hL4, hpat⟩ := classify E h hn hw hd
  have hinter_le1 : ∀ i j : Fin 4, i ≠ j → (E i ∩ E j).card ≤ 1 := by
    intro i j hij
    have hu := Finset.card_union_add_card_inter (E i) (E j)
    have h1 := hEcard i; have h2 := hEcard j; have h3 := hd i j hij
    omega
  -- Sum of all 6 pairwise intersection sizes equals `level E 2 + 3 * level E 3 + 6 * level E 4`.
  have hsum_inter : (E 0 ∩ E 1).card + (E 0 ∩ E 2).card + (E 0 ∩ E 3).card +
      (E 1 ∩ E 2).card + (E 1 ∩ E 3).card + (E 2 ∩ E 3).card =
      level E 2 + 3 * level E 3 + 6 * level E 4 := by
    have hpt : ∀ x : I,
        (if x ∈ E 0 ∩ E 1 then 1 else 0) + (if x ∈ E 0 ∩ E 2 then 1 else 0) +
        (if x ∈ E 0 ∩ E 3 then 1 else 0) + (if x ∈ E 1 ∩ E 2 then 1 else 0) +
        (if x ∈ E 1 ∩ E 3 then 1 else 0) + (if x ∈ E 2 ∩ E 3 then 1 else 0) =
        (if ProximityGap.PuncturedFourWordProfile.multiplicity E x = 2 then 1 else 0) +
        3 * (if ProximityGap.PuncturedFourWordProfile.multiplicity E x = 3 then 1 else 0) +
        6 * (if ProximityGap.PuncturedFourWordProfile.multiplicity E x = 4 then 1 else 0) := by
      intro x
      rw [multiplicity_eq_sum_ite]
      by_cases h0 : x ∈ E 0 <;> by_cases h1 : x ∈ E 1 <;>
        by_cases h2 : x ∈ E 2 <;> by_cases h3 : x ∈ E 3 <;>
        simp [h0, h1, h2, h3]
    have hsum := Finset.sum_congr (rfl : (univ : Finset I) = univ) fun x _ => hpt x
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Nat.cast_id] at hsum
    simpa only [level] using hsum
  -- Helper: shared fiber overlap `|(A \ (B ∪ U)) ∩ (A \ (B ∪ V))| ≥ h - 2` whenever `|A| = h+1`
  -- and `|A ∩ B| = |A ∩ U| = |A ∩ V| = 1`.
  have hshared_ge : ∀ (A B U V : Finset I), A.card = h + 1 →
      (A ∩ B).card ≤ 1 → (A ∩ U).card ≤ 1 → (A ∩ V).card ≤ 1 →
      h - 2 ≤ ((A \ (B ∪ U)) ∩ (A \ (B ∪ V))).card := by
    intro A B U V hA hAB hAU hAV
    have heq : (A \ (B ∪ U)) ∩ (A \ (B ∪ V)) = A \ ((A ∩ B) ∪ (A ∩ U) ∪ (A ∩ V)) := by
      ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]; tauto
    rw [heq]
    have hsub : (A ∩ B) ∪ (A ∩ U) ∪ (A ∩ V) ⊆ A :=
      Finset.union_subset (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
        Finset.inter_subset_left
    rw [Finset.card_sdiff_of_subset hsub]
    have hu1 := Finset.card_union_le ((A ∩ B) ∪ (A ∩ U)) (A ∩ V)
    have hu2 := Finset.card_union_le (A ∩ B) (A ∩ U)
    omega
  -- Helper: when `level E 3 = 0` and `level E 4 = 0`, every triple intersection of distinct indices is empty.
  have htriple_empty_of_L30 : level E 3 = 0 → ∀ i j k : Fin 4, i ≠ j → j ≠ k → k ≠ i →
      E i ∩ E j ∩ E k = ∅ := by
    intro hL3 i j k hij hjk hki
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hxi, hxj⟩, hxk⟩
    have hmult_ge3 := three_le_multiplicity_of_mem_three hij hjk hki hxi hxj hxk
    have hmult_le4 := multiplicity_le_four E x
    rcases show ProximityGap.PuncturedFourWordProfile.multiplicity E x = 3 ∨
        ProximityGap.PuncturedFourWordProfile.multiplicity E x = 4 by omega with h3 | h4
    · have : x ∈ univ.filter (fun y => ProximityGap.PuncturedFourWordProfile.multiplicity E y = 3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩
      have := Finset.card_pos.mpr ⟨x, this⟩
      change 0 < level E 3 at this; omega
    · have : x ∈ univ.filter (fun y => ProximityGap.PuncturedFourWordProfile.multiplicity E y = 4) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h4⟩
      have := Finset.card_pos.mpr ⟨x, this⟩
      change 0 < level E 4 at this; omega
  have hshared_ge_right : ∀ (A B U V : Finset I), A.card = h + 1 →
      (A ∩ B).card ≤ 1 → (A ∩ U).card ≤ 1 → (A ∩ V).card ≤ 1 →
      h - 2 ≤ ((A \ (U ∪ B)) ∩ (A \ (V ∪ B))).card := by
    intro A B U V hA hAB hAU hAV
    rw [Finset.union_comm U B, Finset.union_comm V B]
    exact hshared_ge A B U V hA hAB hAU hAV
  have finish_perm : ∀ (a b u v : Fin 4),
      a ≠ b → a ≠ u → a ≠ v → b ≠ u → b ≠ v → u ≠ v →
      (E a ∩ E b).card = 1 → (E b ∩ E u).card = 1 → (E u ∩ E a).card = 1 → E a ∩ E b ∩ E u = ∅ →
      (E b ∩ E v).card = 1 → (E v ∩ E a).card = 1 → E a ∩ E b ∩ E v = ∅ →
      ∃ a' b' u' v' : Fin 4,
        a' ≠ b' ∧ a' ≠ u' ∧ a' ≠ v' ∧ b' ≠ u' ∧ b' ≠ v' ∧ u' ≠ v' ∧
        (∀ m, (E m).card = h + 1) ∧
        (E a' ∩ E b').card = 1 ∧ (E b' ∩ E u').card = 1 ∧ (E u' ∩ E a').card = 1 ∧ E a' ∩ E b' ∩ E u' = ∅ ∧
        (E b' ∩ E v').card = 1 ∧ (E v' ∩ E a').card = 1 ∧ E a' ∩ E b' ∩ E v' = ∅ ∧
        h - 2 ≤ ((E a' \ (E b' ∪ E u')) ∩ (E a' \ (E b' ∪ E v'))).card ∧
        h - 2 ≤ ((E b' \ (E u' ∪ E a')) ∩ (E b' \ (E v' ∪ E a'))).card := by
    intro a b u v hab hau hav hbu hbv huv h1 h2 h3 h4 h5 h6 h7
    exact ⟨a, b, u, v, hab, hau, hav, hbu, hbv, huv, hEcard, h1, h2, h3, h4, h5, h6, h7,
      hshared_ge (E a) (E b) (E u) (E v) (hEcard a) (hinter_le1 a b hab) (hinter_le1 a u hau) (hinter_le1 a v hav),
      hshared_ge_right (E b) (E a) (E u) (E v) (hEcard b) (hinter_le1 b a hab.symm) (hinter_le1 b u hbu) (hinter_le1 b v hbv)⟩
  have h01 := hinter_le1 0 1 (by decide)
  have h02 := hinter_le1 0 2 (by decide)
  have h03 := hinter_le1 0 3 (by decide)
  have h12 := hinter_le1 1 2 (by decide)
  have h13 := hinter_le1 1 3 (by decide)
  have h23 := hinter_le1 2 3 (by decide)
  rcases hpat with ⟨_, hL2, hL3⟩ | ⟨_, hL2, hL3⟩ | ⟨_, hL2, hL3⟩
  · -- Pattern 1: `(0, 5, 0)` — exactly 5 of 6 pairs have size 1, 1 pair has size 0.
    have hte := htriple_empty_of_L30 hL3
    have hcases : (E 0 ∩ E 1).card = 0 ∨ (E 0 ∩ E 2).card = 0 ∨ (E 0 ∩ E 3).card = 0 ∨
        (E 1 ∩ E 2).card = 0 ∨ (E 1 ∩ E 3).card = 0 ∨ (E 2 ∩ E 3).card = 0 := by omega
    rcases hcases with h0 | h0 | h0 | h0 | h0 | h0
    · exact finish_perm 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by rw [Finset.inter_comm]; omega) (by omega) (hte 2 3 0 (by decide) (by decide) (by decide))
        (by rw [Finset.inter_comm]; omega) (by omega) (hte 2 3 1 (by decide) (by decide) (by decide))
    · exact finish_perm 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by rw [Finset.inter_comm]; omega) (by omega) (hte 1 3 0 (by decide) (by decide) (by decide))
        (by rw [Finset.inter_comm]; omega) (by rw [Finset.inter_comm]; omega) (hte 1 3 2 (by decide) (by decide) (by decide))
    · exact finish_perm 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by rw [Finset.inter_comm]; omega) (by omega) (hte 1 2 0 (by decide) (by decide) (by decide))
        (by omega) (by rw [Finset.inter_comm]; omega) (hte 1 2 3 (by decide) (by decide) (by decide))
    · exact finish_perm 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by rw [Finset.inter_comm]; omega) (by rw [Finset.inter_comm]; omega) (hte 0 3 1 (by decide) (by decide) (by decide))
        (by rw [Finset.inter_comm]; omega) (by rw [Finset.inter_comm]; omega) (hte 0 3 2 (by decide) (by decide) (by decide))
    · exact finish_perm 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by rw [Finset.inter_comm]; omega) (by rw [Finset.inter_comm]; omega) (hte 0 2 1 (by decide) (by decide) (by decide))
        (by omega) (by rw [Finset.inter_comm]; omega) (hte 0 2 3 (by decide) (by decide) (by decide))
    · exact finish_perm 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by rw [Finset.inter_comm]; omega) (hte 0 1 2 (by decide) (by decide) (by decide))
        (by omega) (by rw [Finset.inter_comm]; omega) (hte 0 1 3 (by decide) (by decide) (by decide))
  · -- Pattern 2: `(1, 6, 0)` — ALL 6 pairs have size 1, and every triple intersection is empty!
    have hte := htriple_empty_of_L30 hL3
    exact finish_perm 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by rw [Finset.inter_comm]; omega) (hte 0 1 2 (by decide) (by decide) (by decide))
      (by omega) (by rw [Finset.inter_comm]; omega) (hte 0 1 3 (by decide) (by decide) (by decide))
  · -- Pattern 3: `(0, 3, 1)` — ALL 6 pairs have size 1, and there is a unique point `z` of
    -- multiplicity 3. Let `d` be the unique index with `z ∉ E d`; every triple containing `d` has
    -- empty triple intersection!
    have hall1 : ∀ i j : Fin 4, i ≠ j → (E i ∩ E j).card = 1 := by
      have he01 : (E 0 ∩ E 1).card = 1 := by omega
      have he02 : (E 0 ∩ E 2).card = 1 := by omega
      have he03 : (E 0 ∩ E 3).card = 1 := by omega
      have he12 : (E 1 ∩ E 2).card = 1 := by omega
      have he13 : (E 1 ∩ E 3).card = 1 := by omega
      have he23 : (E 2 ∩ E 3).card = 1 := by omega
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact he01
      · exact he02
      · exact he03
      · rw [Finset.inter_comm]; exact he01
      · exact (hij rfl).elim
      · exact he12
      · exact he13
      · rw [Finset.inter_comm]; exact he02
      · rw [Finset.inter_comm]; exact he12
      · exact (hij rfl).elim
      · exact he23
      · rw [Finset.inter_comm]; exact he03
      · rw [Finset.inter_comm]; exact he13
      · rw [Finset.inter_comm]; exact he23
      · exact (hij rfl).elim
    have hne3 : (univ.filter (fun x : I => ProximityGap.PuncturedFourWordProfile.multiplicity E x = 3)).Nonempty :=
      Finset.card_pos.mp (by change 0 < level E 3; omega)
    obtain ⟨z, hz⟩ := hne3
    have hz_mult : ProximityGap.PuncturedFourWordProfile.multiplicity E z = 3 := (Finset.mem_filter.mp hz).2
    have huniq3 : ∀ x : I, ProximityGap.PuncturedFourWordProfile.multiplicity E x = 3 → x = z := fun x hx =>
      Finset.card_le_one.mp (by change level E 3 ≤ 1; omega) x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩) z hz
    have hno4 : ∀ x : I, ProximityGap.PuncturedFourWordProfile.multiplicity E x ≠ 4 := fun x hx => by
      have hmem4 : x ∈ univ.filter (fun y : I => ProximityGap.PuncturedFourWordProfile.multiplicity E y = 4) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have := Finset.card_pos.mpr ⟨x, hmem4⟩
      change 0 < level E 4 at this; omega
    have htriple_of_not_z : ∀ (i j k : Fin 4), i ≠ j → j ≠ k → k ≠ i →
        (z ∉ E i ∨ z ∉ E j ∨ z ∉ E k) → E i ∩ E j ∩ E k = ∅ := by
      intro i j k hij hjk hki hnz
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hxi, hxj⟩, hxk⟩
      have hm3 := three_le_multiplicity_of_mem_three hij hjk hki hxi hxj hxk
      have hm4 := multiplicity_le_four E x
      have hxeq3 : ProximityGap.PuncturedFourWordProfile.multiplicity E x = 3 := by have := hno4 x; omega
      have hxz : x = z := huniq3 x hxeq3
      subst hxz
      rcases hnz with h | h | h <;> exact h (by assumption)
    have hmiss_ex : z ∉ E 0 ∨ z ∉ E 1 ∨ z ∉ E 2 ∨ z ∉ E 3 := by
      by_contra hall
      push Not at hall
      obtain ⟨h0, h1, h2, h3⟩ := hall
      have : ProximityGap.PuncturedFourWordProfile.multiplicity E z = 4 := by
        rw [multiplicity_eq_sum_ite]; simp [h0, h1, h2, h3]
      omega
    rcases hmiss_ex with hz0 | hz1 | hz2 | hz3
    · exact finish_perm 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hall1 1 0 (by decide)) (hall1 0 2 (by decide)) (hall1 2 1 (by decide))
        (htriple_of_not_z 1 0 2 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz0)))
        (hall1 0 3 (by decide)) (hall1 3 1 (by decide))
        (htriple_of_not_z 1 0 3 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz0)))
    · exact finish_perm 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hall1 0 1 (by decide)) (hall1 1 2 (by decide)) (hall1 2 0 (by decide))
        (htriple_of_not_z 0 1 2 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz1)))
        (hall1 1 3 (by decide)) (hall1 3 0 (by decide))
        (htriple_of_not_z 0 1 3 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz1)))
    · exact finish_perm 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hall1 0 2 (by decide)) (hall1 2 1 (by decide)) (hall1 1 0 (by decide))
        (htriple_of_not_z 0 2 1 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz2)))
        (hall1 2 3 (by decide)) (hall1 3 0 (by decide))
        (htriple_of_not_z 0 2 3 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz2)))
    · exact finish_perm 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hall1 0 3 (by decide)) (hall1 3 1 (by decide)) (hall1 1 0 (by decide))
        (htriple_of_not_z 0 3 1 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz3)))
        (hall1 3 2 (by decide)) (hall1 2 0 (by decide))
        (htriple_of_not_z 0 3 2 (by decide) (by decide) (by decide) (Or.inr (Or.inl hz3)))

/-- **Main algebraic reduction:** Any punctured 4-word list on `4h - 1` points (`h ≥ 2`) produces
two coupled degree-`(h - 1)` 3-split polynomial pencils sharing at least `h - 2` roots in each
of their first two fibers. -/
theorem exists_coupled_pencils_of_punctured_list {D : I ↪ F} {q : Fin 4 → F[X]} {w : I → F} {h : ℕ}
    (hh : 2 ≤ h) (hn : Fintype.card I + 1 = 4 * h)
    (hinj : Function.Injective q) (hdeg : ∀ i, (q i).natDegree ≤ 2 * h - 2)
    (hw : ∀ i, (univ.filter (fun x : I => (q i).eval (D x) ≠ w x)).card ≤ h + 1) :
    ∃ P₁ P₂ : SplitPencil D (h - 1),
      h - 2 ≤ (P₁.S₀ ∩ P₂.S₀).card ∧ h - 2 ≤ (P₁.S₁ ∩ P₂.S₁).card := by
  let E : Fin 4 → Finset I := fun i => univ.filter (fun x : I => (q i).eval (D x) ≠ w x)
  have hd : ∀ i j, i ≠ j → 2 * h + 1 ≤ (E i ∪ E j).card := fun i j hij =>
    error_union D (q i) (q j) w h hn (hinj.ne hij) (by have := hdeg i; omega) (by have := hdeg j; omega)
  obtain ⟨a, b, u, v, hab, hau, hav, hbu, hbv, _, hEcard, hab1, hbu1, hua1, hte1, hbv1, hva1, hte2,
      hov0, hov1⟩ := exists_two_coupled_good_triples hh hn hw hd
  obtain ⟨P₁, hP₁0, hP₁1, _⟩ := splitPencil_of_good_triple hh hn hinj hdeg a b u hab hbu hau.symm
    E (fun _ => rfl) hEcard hab1 hbu1 hua1 hte1
  obtain ⟨P₂, hP₂0, hP₂1, _⟩ := splitPencil_of_good_triple hh hn hinj hdeg a b v hab hbv hav.symm
    E (fun _ => rfl) hEcard hab1 hbv1 hva1 hte2
  refine ⟨P₁, P₂, ?_, ?_⟩
  · rw [hP₁0, hP₂0]; exact hov0
  · rw [hP₁1, hP₂1]; exact hov1

/-- Specialization to `HalfSuccessorListEquivalence.HasPuncturedList` at `n = 2^30`:
any punctured 4-word list yields two coupled odd-degree `268,435,455` (`2^28 - 1`) 3-split
polynomial pencils on the punctured domain sharing at least `268,435,454` roots in each of two
fibers. -/
theorem hasPuncturedList_yields_coupled_odd_pencils
    {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]
    {dom : I ↪ F} (hn : Fintype.card I = 1073741824)
    (hlist : ArkLib.ProximityGap.Frontier.HalfSuccessorListEquivalence.HasPuncturedList dom) :
    ∃ (a : I) (P₁ P₂ : SplitPencil ((Function.Embedding.subtype (· ∈ (univ : Finset I).erase a)).trans dom) 268435455),
      268435454 ≤ (P₁.S₀ ∩ P₂.S₀).card ∧ 268435454 ≤ (P₁.S₁ ∩ P₂.S₁).card := by
  classical
  obtain ⟨a, q, w, hinj, hdeg, hw⟩ := hlist
  let B := (univ : Finset I).erase a
  let incl : B ↪ I := Function.Embedding.subtype (· ∈ B)
  let D : B ↪ F := incl.trans dom
  have hBn : Fintype.card B + 1 = 4 * 268435456 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hn]
  have hmiss : ∀ i, (univ.filter (fun x : B => (q i).eval (D x) ≠ w x.val)).card ≤ 268435456 + 1 := by
    intro i
    let A := univ.filter (fun x : B => (q i).eval (D x) = w x.val)
    let Cores := univ.filter (fun x : I => x ≠ a ∧ (q i).eval (dom x) = w x)
    have hmap : A.map incl = Cores := by
      ext x; constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp y.property).1,
          (Finset.mem_filter.mp hy).2⟩
      · intro hx
        obtain ⟨_, hxa, hxq⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_map.mpr ⟨⟨x, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ _⟩⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxq⟩, rfl⟩
    have hAcard : A.card = Cores.card := (Finset.card_map _).symm.trans (congrArg card hmap)
    have hsum := (univ : Finset B).card_filter_add_card_filter_not (fun x => (q i).eval (D x) = w x.val)
    rw [Finset.card_univ] at hsum
    change A.card + (univ.filter (fun x : B => (q i).eval (D x) ≠ w x.val)).card = Fintype.card B at hsum
    have hc : 805306366 ≤ Cores.card := hw i
    omega
  obtain ⟨P₁, P₂, h1, h2⟩ := exists_coupled_pencils_of_punctured_list (h := 268435456)
    (by decide) hBn hinj (fun i => by have := hdeg i; omega) hmiss
  exact ⟨a, P₁, P₂, h1, h2⟩

end PencilReduction

/-! ## Section 2: Unconditional trivial deck symmetry (`h = 1`) for odd-degree 3-split pencils -/

section DeckSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- **No nontrivial scaling symmetry:** If `u ∈ F` satisfies `u ^ N = 1` and multiplication by `u`
preserves a finite set `S ⊆ F` of nonzero elements whose cardinality is coprime to `N`, then
`u = 1`. In particular, for `N = 2^30` and odd fiber size `268,435,455`, no nontrivial rotation
of `μ_{2^30}` preserves any fiber. -/
theorem no_scaling_symmetry_of_coprime {N : ℕ} (u : F) (S : Finset F)
    (hpow : u ^ N = 1) (hcop : Nat.Coprime N S.card)
    (hnonzero : ∀ x ∈ S, x ≠ 0) (hinv : S.image (fun x => u * x) = S) :
    u = 1 := by
  have hu_ne : u ≠ 0 := by
    intro hz
    have hNpos : N ≠ 0 := by
      rintro rfl
      have : S.card = 1 := by simpa [Nat.Coprime] using hcop
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp this
      have hmem : (0 : F) ∈ S := by
        rw [← hinv]
        exact Finset.mem_image.mpr ⟨x, by simp [hx], by simp [hz]⟩
      exact hnonzero 0 hmem rfl
    rw [hz, zero_pow hNpos] at hpow
    exact zero_ne_one hpow
  have hinj : Function.Injective (fun x : F => u * x) := mul_right_injective₀ hu_ne
  have hprod : ∏ x ∈ S, (u * x) = ∏ x ∈ S, x := by
    conv_rhs => rw [← hinv]
    rw [Finset.prod_image (fun a _ b _ h => hinj h)]
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hP_ne : (∏ x ∈ S, x) ≠ 0 := Finset.prod_ne_zero_iff.mpr hnonzero
  have hu_card : u ^ S.card = 1 := by
    apply mul_right_cancel₀ hP_ne
    simpa only [one_mul] using hprod
  have hdvd1 : orderOf u ∣ N := orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf u ∣ S.card := orderOf_dvd_of_pow_eq_one hu_card
  have hord1 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  exact orderOf_eq_one_iff.mp hord1

/-- Any involution on a finite set preserves cardinality parity modulo `2` with its fixed-point set. -/
theorem card_mod_two_eq_fixed_of_involution {α : Type*} [DecidableEq α] (S : Finset α)
    (τ : α → α) (hinv : ∀ x ∈ S, τ x ∈ S) (hinvol : ∀ x ∈ S, τ (τ x) = x) :
    (S.filter (fun x => τ x = x)).card % 2 = S.card % 2 := by
  classical
  -- Induct on `S.card` by peeling off either a fixed point or a 2-cycle `{x, τ x}`.
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h k ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp [← hn]
    · by_cases hfix : τ x = x
      · let S' := S.erase x
        have hk1 : 1 ≤ k := by rw [← hn]; exact Finset.card_pos.mpr ⟨x, hx⟩
        have hS'card : S'.card = k - 1 := by rw [Finset.card_erase_of_mem hx, hn]
        have hS'inv : ∀ y ∈ S', τ y ∈ S' := by
          intro y hy
          have hyS : y ∈ S := Finset.mem_of_mem_erase hy
          have hyx : y ≠ x := Finset.ne_of_mem_erase hy
          refine Finset.mem_erase.mpr ⟨fun heq => hyx ?_, hinv y hyS⟩
          calc y = τ (τ y) := (hinvol y hyS).symm
            _ = τ x := by rw [heq]
            _ = x := hfix
        have hS'invol : ∀ y ∈ S', τ (τ y) = y := fun y hy => hinvol y (Finset.mem_of_mem_erase hy)
        have hrec := ih S'.card (by omega) S' hS'inv hS'invol rfl
        have hfilt : S.filter (fun y => τ y = y) = insert x (S'.filter (fun y => τ y = y)) := by
          ext y; simp only [S', Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨hyS, hτy⟩
            by_cases hyx : y = x
            · exact Or.inl hyx
            · exact Or.inr ⟨⟨hyx, hyS⟩, hτy⟩
          · rintro (rfl | ⟨⟨_, hyS⟩, hτy⟩)
            · exact ⟨hx, hfix⟩
            · exact ⟨hyS, hτy⟩
        have hx_not : x ∉ S'.filter (fun y => τ y = y) := by simp [S']
        rw [hfilt, Finset.card_insert_of_notMem hx_not]
        rw [hS'card] at hrec
        omega
      · let S' := (S.erase x).erase (τ x)
        have hτx_mem : τ x ∈ S.erase x := Finset.mem_erase.mpr ⟨hfix, hinv x hx⟩
        have hk2 : 2 ≤ k := by
          have hpos := Finset.card_pos.mpr ⟨τ x, hτx_mem⟩
          rw [Finset.card_erase_of_mem hx, hn] at hpos
          omega
        have hS'card : S'.card = k - 2 := by
          rw [Finset.card_erase_of_mem hτx_mem, Finset.card_erase_of_mem hx, hn]
          omega
        have hS'inv : ∀ y ∈ S', τ y ∈ S' := by
          intro y hy
          have hy1 := Finset.mem_erase.mp hy
          have hy2 := Finset.mem_erase.mp hy1.2
          refine Finset.mem_erase.mpr ⟨fun h => hy2.1 ?_,
            Finset.mem_erase.mpr ⟨fun h => hy1.1 ?_, hinv y hy2.2⟩⟩
          · calc y = τ (τ y) := (hinvol y hy2.2).symm
              _ = τ (τ x) := by rw [h]
              _ = x := hinvol x hx
          · calc y = τ (τ y) := (hinvol y hy2.2).symm
              _ = τ x := by rw [h]
        have hS'invol : ∀ y ∈ S', τ (τ y) = y := fun y hy =>
          hinvol y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
        have hrec := ih S'.card (by omega) S' hS'inv hS'invol rfl
        have hfilt : S.filter (fun y => τ y = y) = S'.filter (fun y => τ y = y) := by
          ext y; simp only [S', Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hyS, hτy⟩
            refine ⟨⟨?_, ?_, hyS⟩, hτy⟩
            · intro h
              rw [h, hinvol x hx] at hτy
              exact hfix hτy.symm
            · intro h
              rw [h] at hτy
              exact hfix hτy
          · rintro ⟨⟨_, _, hyS⟩, hτy⟩
            exact ⟨hyS, hτy⟩
        rw [hfilt]
        rw [hS'card] at hrec
        omega

/-- **No reciprocal involution symmetry (`x ↦ u / x`) across three disjoint odd-size fibers:**
Since `x^2 = u` has at most 2 solutions in any field `F`, an involution `x ↦ u * x⁻¹` cannot
preserve three pairwise disjoint odd-cardinality subsets of `Fˣ`. Together with
`no_scaling_symmetry_of_coprime`, this forces unconditional trivial deck symmetry `h = 1` in
`D_{2^30}` for every odd-degree 3-split pencil on `μ_{2^30}`. -/
theorem no_reciprocal_involution_three_odd_fibers (u : F) (hu : u ≠ 0)
    (S₀ S₁ S₂ : Finset F)
    (hd01 : Disjoint S₀ S₁) (hd12 : Disjoint S₁ S₂) (hd20 : Disjoint S₂ S₀)
    (hnz0 : ∀ x ∈ S₀, x ≠ 0) (hnz1 : ∀ x ∈ S₁, x ≠ 0) (hnz2 : ∀ x ∈ S₂, x ≠ 0)
    (hodd0 : S₀.card % 2 = 1) (hodd1 : S₁.card % 2 = 1) (hodd2 : S₂.card % 2 = 1)
    (hinv0 : ∀ x ∈ S₀, u * x⁻¹ ∈ S₀)
    (hinv1 : ∀ x ∈ S₁, u * x⁻¹ ∈ S₁)
    (hinv2 : ∀ x ∈ S₂, u * x⁻¹ ∈ S₂) : False := by
  let τ : F → F := fun x => u * x⁻¹
  have hinvol : ∀ S : Finset F, (∀ x ∈ S, x ≠ 0) → ∀ x ∈ S, τ (τ x) = x := by
    intro S hnz x hx
    have hx0 := hnz x hx
    dsimp [τ]
    field_simp [hu, hx0]
  have hfix_ex : ∀ S : Finset F, (∀ x ∈ S, x ≠ 0) → S.card % 2 = 1 →
      (∀ x ∈ S, τ x ∈ S) → ∃ x ∈ S, x ^ 2 = u := by
    intro S hnz hodd hinv
    have hmod := card_mod_two_eq_fixed_of_involution S τ hinv (hinvol S hnz)
    have hpos : 0 < (S.filter (fun x => τ x = x)).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxS, hτx⟩ := Finset.mem_filter.mp hx
    have hx0 := hnz x hxS
    refine ⟨x, hxS, ?_⟩
    dsimp [τ] at hτx
    have : u = x * x := by
      calc u = u * x⁻¹ * x := by field_simp [hx0]
        _ = x * x := by rw [hτx]
    simpa [pow_two] using this.symm
  obtain ⟨x₀, hx₀, hsq₀⟩ := hfix_ex S₀ hnz0 hodd0 hinv0
  obtain ⟨x₁, hx₁, hsq₁⟩ := hfix_ex S₁ hnz1 hodd1 hinv1
  obtain ⟨x₂, hx₂, hsq₂⟩ := hfix_ex S₂ hnz2 hodd2 hinv2
  have h01 : x₀ ≠ x₁ := fun h => Finset.disjoint_left.mp hd01 hx₀ (h ▸ hx₁)
  have h12 : x₁ ≠ x₂ := fun h => Finset.disjoint_left.mp hd12 hx₁ (h ▸ hx₂)
  have h20 : x₂ ≠ x₀ := fun h => Finset.disjoint_left.mp hd20 hx₂ (h ▸ hx₀)
  have heq01 : (x₀ - x₁) * (x₀ + x₁) = 0 := by linear_combination hsq₀ - hsq₁
  have hsum01 : x₀ + x₁ = 0 := (mul_eq_zero.mp heq01).resolve_left (sub_ne_zero.mpr h01)
  have heq02 : (x₀ - x₂) * (x₀ + x₂) = 0 := by linear_combination hsq₀ - hsq₂
  have hsum02 : x₀ + x₂ = 0 := (mul_eq_zero.mp heq02).resolve_left (sub_ne_zero.mpr h20.symm)
  exact h12 (add_left_cancel (hsum01.trans hsum02.symm))

/-- Coprimality at production degree `D_half = 268,435,455` and order `n = 2^30`. -/
theorem production_coprime_and_odd :
    Nat.Coprime (2 ^ 30) 268435455 ∧ 268435455 % 2 = 1 := by
  decide

end DeckSymmetry

/-! ## Section 3: Sharp Wronskian collapse for `D_half = 268,435,455` -/

section HalfWronskianCollapse

/-- Subdegree floor for `D_half = 268,435,455` on `μ_{2^30}`:
`3 * 268,435,455 * a ≤ (2/3) * 2^30 * a + χ` with `χ ≤ 2 a^2` forces `44,739,242 ≤ a`. -/
theorem half_subdegree_floor {a : ℕ} (ha : 0 < a) (chi : ℝ)
    (wronskian : 3 * 268435455 * (a : ℝ) ≤ (2 / 3 : ℝ) * 1073741824 * a + chi)
    (adjunction : chi ≤ 2 * (a : ℝ) ^ 2) :
    44739242 ≤ a := by
  have h : (268435447 : ℝ) * a ≤ 6 * (a : ℝ) ^ 2 := by
    linarith only [wronskian, adjunction]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn : (268435447 : ℝ) ≤ 6 * a := by
    apply (mul_le_mul_iff_of_pos_right ha').mp
    nlinarith only [h]
  have hint : 268435447 ≤ 6 * a := by exact_mod_cast hn
  omega

/-- With trivial deck symmetry (`h = 1`, hence `singleton ≤ 1`), a degree-`268,435,455` odd
3-split pencil has at most `6` nontrivial suborbits and permutation rank at most `7`. -/
theorem half_orbit_count_sharp {nontrivial singleton : ℕ} (hs : singleton ≤ 1)
    (degrees : 44739242 * nontrivial + singleton ≤ 268435455) :
    nontrivial ≤ 6 ∧ nontrivial + singleton ≤ 7 := by
  omega

/-- Prime factorization of `D_half = 2^28 - 1 = 268,435,455 = 3 · 5 · 29 · 43 · 113 · 127`
(6 distinct odd primes ⇒ `2^6 = 64` total divisors and `62` proper nontrivial divisors). -/
theorem half_degree_factorization :
    268435455 = 3 * 5 * 29 * 43 * 113 * 127 ∧
    Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 29 ∧ Nat.Prime 43 ∧ Nat.Prime 113 ∧ Nat.Prime 127 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **60-of-62 proper-divisor elimination:**
Among all `64` divisors of `268,435,455` (`62` proper nontrivial divisors), the Wronskian
subdegree floor `44,739,242 ≤ t - 1` eliminates **60 of the 62** proper nontrivial divisors,
leaving only `t = 53,687,091` (`s = 5`), `t = 89,478,485` (`s = 3`), and the indecomposable
case `t = 268,435,455` (`s = 1`). -/
theorem half_inner_degree_only_three {t : ℕ} (hdvd : t ∣ 268435455)
    (hlarge : 44739242 ≤ t - 1) :
    t = 53687091 ∨ t = 89478485 ∨ t = 268435455 := by
  obtain ⟨s, hs⟩ := hdvd
  have hsb : s ≤ 6 := by
    by_contra! h
    have := Nat.mul_le_mul (show 44739243 ≤ t by omega) h
    omega
  have hs_pos : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hp
    · simp at hs
    · exact hp
  interval_cases s <;> omega

/-- Complete classification of the surviving `(outer degree s, primitive degree m)` pairs under
unconditional trivial deck symmetry `h = 1`. -/
theorem half_primitive_stage_classification {s m : ℕ}
    (hprod : s * m = 268435455) (hlarge : 44739242 ≤ m - 1) :
    (s = 5 ∧ m = 53687091) ∨
    (s = 3 ∧ m = 89478485) ∨
    (s = 1 ∧ m = 268435455) := by
  have hdvd : m ∣ 268435455 := ⟨s, by rw [← hprod, mul_comm]⟩
  rcases half_inner_degree_only_three hdvd hlarge with rfl | rfl | rfl
  · left; exact ⟨by omega, rfl⟩
  · right; left; exact ⟨by omega, rfl⟩
  · right; right; exact ⟨by omega, rfl⟩

/-- Wronskian-variance orbifold excess inequality for `D_half = 268,435,455` at `h = 1`. -/
theorem half_primitive_excess_wronskian {m E euler : ℝ} (hm : 1 < m) (hE : 0 ≤ E + 2)
    (wronskian : 3 * 268435455 * (m - 1) ≤
      (2 / 3 : ℝ) * 1073741824 * (m - 1) + (euler + 4 * (m - 1)))
    (genus : euler * (E + 2) ≤ 2 * (m - 1) ^ 2 * E) :
    536870870 ≤ (6 * (m + 1) - 268435447) * E := by
  have hsimple : (268435447 : ℝ) * (m - 1) ≤ 3 * (euler + 4 * (m - 1)) := by
    linarith only [wronskian]
  have hmul := mul_le_mul_of_nonneg_right hsimple hE
  have hg := mul_le_mul_of_nonneg_left genus (by norm_num : (0 : ℝ) ≤ 3)
  apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hm)).mp
  nlinarith only [hmul, hg]

/-- Exact rational orbifold excess lower bounds for the three surviving stages (`h = 1`):
* `s = 5, m = 53,687,091`: `E ≥ 107,374,174 / 10,737,421` (`> 9.9999966`)
* `s = 3, m = 89,478,485`: `E ≥ 536,870,870 / 268,435,469` (`> 1.9999997`)
* `s = 1, m = 268,435,455`: `E ≥ 536,870,870 / 1,342,177,289` (`> 0.39999996`). -/
theorem half_named_excess {m E : ℝ}
    (bound : 536870870 ≤ (6 * (m + 1) - 268435447) * E) :
    (m = 53687091 → (107374174 : ℝ) / 10737421 ≤ E) ∧
    (m = 89478485 → (536870870 : ℝ) / 268435469 ≤ E) ∧
    (m = 268435455 → (536870870 : ℝ) / 1342177289 ≤ E) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; linarith
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- Pair-curve genus floors `g(Y)` for the three surviving stages (`h = 1`). -/
theorem half_named_genus {m g : ℝ}
    (wronskian : 3 * 268435455 * (m - 1) ≤
      (2 / 3 : ℝ) * 1073741824 * (m - 1) + ((2 * g - 2) + 4 * (m - 1))) :
    (m = 53687091 → 2401919559672358 < g) ∧
    (m = 89478485 → 4003199295946756 < g) ∧
    (m = 268435455 → 12009597977318748 < g) := by
  have hsimple : (268435447 : ℝ) * (m - 1) ≤ 3 * ((2 * g - 2) + 4 * (m - 1)) := by
    linarith only [wronskian]
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; linarith
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- Unconditional orbifold excess lower bound for the full pencil `R` across all three surviving
stages (`s ∈ {5, 3, 1}`): `E_R ≥ 536,870,870 / 1,342,177,289 > 0.399999966`. -/
theorem half_full_cover_excess {s E full : ℝ} (transfer : E ≤ s * full)
    (cases : (s = 5 ∧ (107374174 : ℝ) / 10737421 ≤ E) ∨
             (s = 3 ∧ (536870870 : ℝ) / 268435469 ≤ E) ∨
             (s = 1 ∧ (536870870 : ℝ) / 1342177289 ≤ E)) :
    (536870870 : ℝ) / 1342177289 ≤ full := by
  rcases cases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> linarith

/-- Characteristic headroom for the `h = k = 1` Wronskian bound at `D_half = 268,435,455` on both
designated primes (nearly 100 bits of headroom). -/
theorem half_characteristic_headroom :
    2 * 1073741824 * 268435455 < 2 ^ 59 ∧
    2 ^ 59 < PrizeShapePrimeP30.P ∧
    2 ^ 59 < PrizeShapePrimeP30Second.P := by
  decide

end HalfWronskianCollapse

/-! ## Section 4: Exact `n = 16, p = 97` kernel-checked barrier witness -/

section BarrierN16P97

private local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- The `16`-th root of unity `8 ∈ ZMod 97` (`8^8 = -1`, `8^16 = 1`) and the multiplicative
domain `dom16 : Fin 16 ↪ ZMod 97`. -/
private def dom16Fun (k : Fin 16) : ZMod 97 := (8 : ZMod 97) ^ k.val

private theorem dom16Fun_injective : Function.Injective dom16Fun := by
  decide

def dom16 : Fin 16 ↪ ZMod 97 := ⟨dom16Fun, dom16Fun_injective⟩

/-- Helper to evaluate a degree-`≤ 6` polynomial from its coefficient tuple over `ZMod 97`. -/
private def poly6 (c : Fin 7 → ZMod 97) : (ZMod 97)[X] :=
  C (c 0) + C (c 1) * Polynomial.X + C (c 2) * Polynomial.X ^ 2 + C (c 3) * Polynomial.X ^ 3 +
  C (c 4) * Polynomial.X ^ 4 + C (c 5) * Polynomial.X ^ 5 + C (c 6) * Polynomial.X ^ 6

private def eval6 (c : Fin 7 → ZMod 97) (x : ZMod 97) : ZMod 97 :=
  c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3 + c 4 * x ^ 4 + c 5 * x ^ 5 + c 6 * x ^ 6

private theorem eval_poly6 (c : Fin 7 → ZMod 97) (x : ZMod 97) :
    (poly6 c).eval x = eval6 c x := by
  simp [poly6, eval6]

private theorem natDegree_poly6_le (c : Fin 7 → ZMod 97) : (poly6 c).natDegree ≤ 6 := by
  unfold poly6
  have h0 : (C (c 0)).natDegree ≤ 6 := by simp
  have h1 : (C (c 1) * Polynomial.X).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  have h2 : (C (c 2) * Polynomial.X ^ 2).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  have h3 : (C (c 3) * Polynomial.X ^ 3).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  have h4 : (C (c 4) * Polynomial.X ^ 4).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  have h5 : (C (c 5) * Polynomial.X ^ 5).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  have h6 : (C (c 6) * Polynomial.X ^ 6).natDegree ≤ 6 := (Polynomial.natDegree_mul_le).trans (by simp)
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans (max_le
          ((Polynomial.natDegree_add_le _ _).trans (max_le
            ((Polynomial.natDegree_add_le _ _).trans (max_le h0 h1)) h2)) h3)) h4)) h5)) h6)

private def barrierCoeffs : Fin 4 → Fin 7 → ZMod 97
  | 0 => ![0, 0, 0, 0, 0, 0, 0]
  | 1 => ![24, 26, 25, 89, 12, 8, 95]
  | 2 => ![89, 49, 88, 54, 81, 25, 70]
  | 3 => ![8, 45, 16, 48, 22, 45, 1]

/-- The four explicit degree-6 polynomials over `ZMod 97` witnessing the `n = 16, p = 97`
punctured four-word list barrier (`h = 4`, `D = 3`, pattern `(0, 5, 0)`). -/
def barrierPolys (i : Fin 4) : (ZMod 97)[X] := poly6 (barrierCoeffs i)

/-- The common received word on `Fin 16` for the `n = 16, p = 97` barrier witness. -/
def barrierWord : Fin 16 → ZMod 97 :=
  ![0, 84, 0, 0, 64, 0, 0, 0, 6, 0, 48, 0, 59, 0, 0, 0]

private theorem barrierPolys_injective : Function.Injective barrierPolys := by
  intro i j hij
  have heval : ∀ k : Fin 16, eval6 (barrierCoeffs i) (dom16Fun k) =
      eval6 (barrierCoeffs j) (dom16Fun k) := fun k => by
    have := congrArg (fun f : (ZMod 97)[X] => f.eval (dom16Fun k)) hij
    simpa only [barrierPolys, eval_poly6] using this
  have hdec : ∀ a b : Fin 4,
      (∀ k : Fin 16, eval6 (barrierCoeffs a) (dom16Fun k) = eval6 (barrierCoeffs b) (dom16Fun k)) →
      a = b := by decide
  exact hdec i j heval

/-- **Exact `n = 16, p = 97` barrier theorem:**
Over `ZMod 97` (prime, with `97 > 2 * 16 * 3 = 96` already meeting the Wronskian characteristic
headroom and `8 ∈ ZMod 97` of exact order `16`), there exist 4 distinct degree-`≤ 6` polynomials
on `μ_{16}` punctured at `1` (`k = 0`) each agreeing with a common word on `10` of `15` points
(`5 = h + 1` errors each), exhibiting exact error pattern `(0, 5, 0)`, and yielding two coupled
degree-`3` odd 3-split polynomial pencils on `μ_{16} \ {1}`. -/
theorem barrier_n16_p97 :
    Nat.Prime 97 ∧
    2 * 16 * 3 < 97 ∧
    (8 : ZMod 97) ^ 16 = 1 ∧
    (8 : ZMod 97) ^ 8 ≠ 1 ∧
    Function.Injective barrierPolys ∧
    (∀ i, (barrierPolys i).natDegree ≤ 6) ∧
    (∀ i, (univ.filter fun x : Fin 16 => x ≠ 0 ∧ (barrierPolys i).eval (dom16 x) = barrierWord x).card = 10) ∧
    (let B := (univ : Finset (Fin 16)).erase 0
     let D : B ↪ ZMod 97 := (Function.Embedding.subtype (· ∈ B)).trans dom16
     let E : Fin 4 → Finset B := fun i => univ.filter (fun x : B => (barrierPolys i).eval (D x) ≠ barrierWord x.val)
     level E 0 = 0 ∧ level E 2 = 5 ∧ level E 3 = 0 ∧ level E 4 = 0) ∧
    (∃ P₁ P₂ : SplitPencil ((Function.Embedding.subtype (· ∈ (univ : Finset (Fin 16)).erase 0)).trans dom16) 3,
      2 ≤ (P₁.S₀ ∩ P₂.S₀).card ∧ 2 ≤ (P₁.S₁ ∩ P₂.S₁).card) := by
  have hagree : ∀ i : Fin 4,
      (univ.filter fun x : Fin 16 => x ≠ 0 ∧ (barrierPolys i).eval (dom16 x) = barrierWord x).card = 10 := by
    have hdec : ∀ i : Fin 4,
        (univ.filter fun x : Fin 16 => x ≠ 0 ∧ eval6 (barrierCoeffs i) (dom16Fun x) = barrierWord x).card = 10 := by
      decide
    intro i
    have hsimp : (univ.filter fun x : Fin 16 => x ≠ 0 ∧ (barrierPolys i).eval (dom16 x) = barrierWord x) =
        (univ.filter fun x : Fin 16 => x ≠ 0 ∧ eval6 (barrierCoeffs i) (dom16Fun x) = barrierWord x) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, barrierPolys, dom16,
        Function.Embedding.coeFn_mk, eval_poly6]
    rw [hsimp]
    exact hdec i
  refine ⟨by decide, by decide, by decide, by decide, barrierPolys_injective,
    fun i => natDegree_poly6_le (barrierCoeffs i), hagree, ?_, ?_⟩
  · let B := (univ : Finset (Fin 16)).erase 0
    let D : B ↪ ZMod 97 := (Function.Embedding.subtype (· ∈ B)).trans dom16
    let E : Fin 4 → Finset B := fun i => univ.filter (fun x : B => (barrierPolys i).eval (D x) ≠ barrierWord x.val)
    let E' : Fin 4 → Finset B := fun i => univ.filter (fun x : B => eval6 (barrierCoeffs i) (dom16Fun x.val) ≠ barrierWord x.val)
    have hEE' : E = E' := by
      funext i; ext x
      simp only [E, E', D, Finset.mem_filter, Finset.mem_univ, true_and, barrierPolys, dom16,
        Function.Embedding.trans_apply, Function.Embedding.subtype_apply, Function.Embedding.coeFn_mk, eval_poly6]
    change level E 0 = 0 ∧ level E 2 = 5 ∧ level E 3 = 0 ∧ level E 4 = 0
    rw [hEE']
    decide
  let B := (univ : Finset (Fin 16)).erase 0
  let incl : B ↪ Fin 16 := Function.Embedding.subtype (· ∈ B)
  let D : B ↪ ZMod 97 := incl.trans dom16
  have hBn : Fintype.card B + 1 = 4 * 4 := by decide
  have hmiss : ∀ i, (univ.filter (fun x : B => (barrierPolys i).eval (D x) ≠ barrierWord x.val)).card ≤ 4 + 1 := by
    intro i
    let A := univ.filter (fun x : B => (barrierPolys i).eval (D x) = barrierWord x.val)
    let Cores := univ.filter (fun x : Fin 16 => x ≠ 0 ∧ (barrierPolys i).eval (dom16 x) = barrierWord x)
    have hmap : A.map incl = Cores := by
      ext x; constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp y.property).1,
          (Finset.mem_filter.mp hy).2⟩
      · intro hx
        obtain ⟨_, hxa, hxq⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_map.mpr ⟨⟨x, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ _⟩⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxq⟩, rfl⟩
    have hAcard : A.card = Cores.card := (Finset.card_map _).symm.trans (congrArg card hmap)
    have hsum := (univ : Finset B).card_filter_add_card_filter_not (fun x => (barrierPolys i).eval (D x) = barrierWord x.val)
    rw [Finset.card_univ] at hsum
    change A.card + (univ.filter (fun x : B => (barrierPolys i).eval (D x) ≠ barrierWord x.val)).card = Fintype.card B at hsum
    have hc : Cores.card = 10 := hagree i
    omega
  exact exists_coupled_pencils_of_punctured_list (h := 4) (by decide) hBn
    barrierPolys_injective (fun i => natDegree_poly6_le (barrierCoeffs i)) hmiss

end BarrierN16P97

#print axioms exists_coupled_pencils_of_punctured_list
#print axioms hasPuncturedList_yields_coupled_odd_pencils
#print axioms no_scaling_symmetry_of_coprime
#print axioms no_reciprocal_involution_three_odd_fibers
#print axioms half_subdegree_floor
#print axioms half_orbit_count_sharp
#print axioms half_degree_factorization
#print axioms half_inner_degree_only_three
#print axioms half_primitive_stage_classification
#print axioms half_primitive_excess_wronskian
#print axioms half_named_excess
#print axioms half_named_genus
#print axioms half_full_cover_excess
#print axioms half_characteristic_headroom
#print axioms barrier_n16_p97

end ArkLib.ProximityGap.Frontier.HalfSuccessorSplitWronskian
