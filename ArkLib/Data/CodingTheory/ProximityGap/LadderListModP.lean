/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairSumRigidityModP
import ArkLib.Data.CodingTheory.ProximityGap.LadderExactList

/-!
# THE LADDER LIST LAW OVER `F_p` (#389): the mod-`p` transfer of the rigidity half

`LadderExactList` proved the subset-sum fibre law's rigidity half at `m = 2` ladder
words in characteristic zero, through the antipodal closure of vanishing subset sums.
This file transfers it to prime fields above an explicit threshold, by the same weld
species as `PairSumRigidityModP`: fold, `ℓ¹`-mass, resultant engine.

* `subsetFolded ν E` — the general subset fold: the canonical degree-`< 2^{ν−1}`
  integer representative of `Σ_{a∈E} ζ^a` modulo `Φ_{2^ν}` (the `|E|`-term
  generalization of `pairSumFolded`), with coefficient law, degree bound, fold
  faithfulness at any field's primitive root, and `ℓ¹ ≤ |E|`.
* `shift_mem_of_subsetFolded_eq_zero` — **the fold trivializes Lam–Leung at
  2-powers**: a vanishing fold means each folded residue's `±` indicators cancel,
  i.e. the exponent set is closed under the half-shift `a ↦ a ± 2^{ν−1}` — no
  cyclotomic theory needed once the representative is canonical.
* `subset_neg_mem_of_sum_zero_modp` — **the mod-`p` subset antipodal closure**:
  over `ZMod p` with a primitive `2^ν`-th root, a vanishing subset sum of
  `μ_{2^ν}` with `|A|^{2^{ν−1}} < p` is antipodally closed.  Dichotomy: the fold
  either vanishes identically (⟹ half-shift closure ⟹ `A = −A` through
  `ζ^{2^{ν−1}} = −1`) or survives to a nonzero integer polynomial of degree
  `< 2^{ν−1}` and `ℓ¹ ≤ |A|`, which the resultant engine
  (`not_isRoot_of_l1On_pow_lt`) forbids from vanishing at `g` above the threshold.
* `ladder_explainer_fiber_modp` — **the headline**: the ladder exact list law over
  `ZMod p` for `p > (2r)^{2^{ν−1}}` — every codeword agreeing `≥ 2r` with
  `x^{2r} + λx^{2r−2}` is a subset-sum-fibre codeword, in production fields.

The threshold is the standard resultant-norm bound (pessimistic, as in
`pair_sum_rigidity_modp`'s `4^{2^{k−1}}`): the sharp statement is that violating
primes divide a folded-relation resultant — the O134 norm-divisibility surplus is
exactly the below-threshold exception class, as the #389 red-team note records.
Issue #389.
-/

open Finset Polynomial
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PairSumRigidityModP

namespace ProximityGap.LadderListModP

/-! ## The general subset fold -/

/-- The folded subset relation: the canonical degree-`< 2^{ν−1}` integer
representative of `Σ_{a∈E} ζ^a` modulo `Φ_{2^ν}`. -/
noncomputable def subsetFolded (ν : ℕ) (E : Finset ℕ) : Polynomial ℤ :=
  ∑ t ∈ Finset.range (2 ^ (ν - 1)), C (∑ a ∈ E, ind ν a t) * X ^ t

theorem subsetFolded_coeff (ν : ℕ) (E : Finset ℕ) (t : ℕ) :
    (subsetFolded ν E).coeff t
      = if t < 2 ^ (ν - 1) then ∑ a ∈ E, ind ν a t else 0 := by
  rw [subsetFolded, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases ht : t < 2 ^ (ν - 1)
  · rw [if_pos ht]
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_range.mpr ht)
      (fun s _ hst => by simp [Ne.symm hst])]
    simp
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hst : t ≠ s := fun h => ht (h ▸ Finset.mem_range.mp hs)
    simp [hst]

theorem subsetFolded_natDegree_lt (ν : ℕ) (E : Finset ℕ) :
    (subsetFolded ν E).natDegree < 2 ^ (ν - 1) := by
  by_cases h0 : subsetFolded ν E = 0
  · rw [h0]
    simpa using pow_pos (by norm_num : (0 : ℕ) < 2) (ν - 1)
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro t ht
    rw [subsetFolded_coeff]
    have hnot : ¬ t < 2 ^ (ν - 1) := not_lt.mpr (by exact_mod_cast ht)
    simp [hnot]

/-- **Fold faithfulness** for subset sums: evaluating the folded relation at a
primitive `2^ν`-th root of any field recovers `Σ_{a∈E} ζ^a`. -/
theorem subsetFolded_eval {L : Type*} [Field L] {ν : ℕ} (hν : 1 ≤ ν) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ ν)) {E : Finset ℕ} (hE : ∀ a ∈ E, a < 2 ^ ν) :
    ((subsetFolded ν E).map (Int.castRingHom L)).eval ζ = ∑ a ∈ E, ζ ^ a := by
  have hLHS : ((subsetFolded ν E).map (Int.castRingHom L)).eval ζ
      = ∑ t ∈ Finset.range (2 ^ (ν - 1)), ((∑ a ∈ E, ind ν a t : ℤ) : L) * ζ ^ t := by
    rw [subsetFolded, Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow,
      eval_C, eval_X]
    norm_cast
  rw [hLHS]
  have hsplit : ∀ t, ((∑ a ∈ E, ind ν a t : ℤ) : L) * ζ ^ t
      = ∑ a ∈ E, ((ind ν a t : ℤ) : L) * ζ ^ t := by
    intro t
    push_cast
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a ha => sum_ind_mul hν hζ (hE a ha)

/-- The `ℓ¹` mass of the subset fold is at most `|E|`. -/
theorem l1On_subsetFolded_le {ν : ℕ} (hν : 1 ≤ ν) {E : Finset ℕ}
    (hE : ∀ a ∈ E, a < 2 ^ ν) :
    l1On (2 ^ (ν - 1)) (subsetFolded ν E) ≤ E.card := by
  rw [l1On]
  calc ∑ j ∈ Finset.range (2 ^ (ν - 1)), ((subsetFolded ν E).coeff j).natAbs
      ≤ ∑ j ∈ Finset.range (2 ^ (ν - 1)), ∑ a ∈ E, (ind ν a j).natAbs := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [subsetFolded_coeff, if_pos (Finset.mem_range.mp hj)]
        exact Int.natAbs_sum_le _ _
    _ = ∑ a ∈ E, ∑ j ∈ Finset.range (2 ^ (ν - 1)), (ind ν a j).natAbs :=
        Finset.sum_comm
    _ ≤ ∑ _a ∈ E, 1 :=
        Finset.sum_le_sum fun a ha => sum_natAbs_ind_le hν (hE a ha)
    _ = E.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-! ## The vanishing dichotomy: a zero fold is a half-shift closure -/

/-- **The fold trivializes Lam–Leung at 2-powers**: if the subset fold vanishes
identically, the exponent set is closed under the half-shift `a ↦ a ± 2^{ν−1}`. -/
theorem shift_mem_of_subsetFolded_eq_zero {ν : ℕ} (hν : 1 ≤ ν) {E : Finset ℕ}
    (hE : ∀ a ∈ E, a < 2 ^ ν) (h0 : subsetFolded ν E = 0) {a : ℕ} (ha : a ∈ E) :
    (if a < 2 ^ (ν - 1) then a + 2 ^ (ν - 1) else a - 2 ^ (ν - 1)) ∈ E := by
  classical
  have hsplit : 2 ^ (ν - 1) + 2 ^ (ν - 1) = 2 ^ ν := by
    have h := pow_succ 2 (ν - 1)
    rw [Nat.sub_add_cancel hν] at h
    omega
  set t : ℕ := if a < 2 ^ (ν - 1) then a else a - 2 ^ (ν - 1) with htdef
  have ht : t < 2 ^ (ν - 1) := by
    have haE := hE a ha
    rw [htdef]
    by_cases hcase : a < 2 ^ (ν - 1)
    · rwa [if_pos hcase]
    · rw [if_neg hcase]
      omega
  have hcoeff : (∑ b ∈ E, ind ν b t) = 0 := by
    have hc := subsetFolded_coeff ν E t
    rw [h0, coeff_zero, if_pos ht] at hc
    exact hc.symm
  have hsum : (∑ b ∈ E, ind ν b t)
      = (if t ∈ E then (1 : ℤ) else 0)
        - (if t + 2 ^ (ν - 1) ∈ E then (1 : ℤ) else 0) := by
    simp only [ind]
    rw [Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_ite_eq' E t (fun _ => (1 : ℤ))
    · exact Finset.sum_ite_eq' E (t + 2 ^ (ν - 1)) (fun _ => (1 : ℤ))
  rw [hsum] at hcoeff
  by_cases hcase : a < 2 ^ (ν - 1)
  · rw [if_pos hcase]
    have hta : t = a := by rw [htdef, if_pos hcase]
    have htmem : t ∈ E := hta ▸ ha
    rw [if_pos htmem] at hcoeff
    by_cases hmem : t + 2 ^ (ν - 1) ∈ E
    · rwa [hta] at hmem
    · rw [if_neg hmem] at hcoeff
      norm_num at hcoeff
  · rw [if_neg hcase]
    have hta : t = a - 2 ^ (ν - 1) := by rw [htdef, if_neg hcase]
    have htshift : t + 2 ^ (ν - 1) = a := by
      rw [hta]
      omega
    have hmem2 : t + 2 ^ (ν - 1) ∈ E := htshift ▸ ha
    rw [if_pos hmem2] at hcoeff
    by_cases hmem : t ∈ E
    · rwa [hta] at hmem
    · rw [if_neg hmem] at hcoeff
      norm_num at hcoeff

/-! ## The mod-`p` subset antipodal closure -/

open Classical in
/-- **THE MOD-`p` SUBSET ANTIPODAL CLOSURE**: over `ZMod p` with a primitive
`2^ν`-th root, any vanishing subset sum of `μ_{2^ν}` with `|A|^{2^{ν−1}} < p` is
antipodally closed — the finite-field form of the subset Lam–Leung engine, above
the explicit resultant threshold. -/
theorem subset_neg_mem_of_sum_zero_modp {p : ℕ} [Fact p.Prime] {ν : ℕ} (hν : 1 ≤ ν)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ ν))
    {A : Finset (ZMod p)} (hA : ∀ x ∈ A, x ^ (2 ^ ν) = 1)
    (hsum : ∑ x ∈ A, x = 0) (hp : A.card ^ 2 ^ (ν - 1) < p) :
    ∀ x ∈ A, -x ∈ A := by
  classical
  haveI : NeZero (2 ^ ν) := ⟨(Nat.two_pow_pos ν).ne'⟩
  -- discrete logarithms
  have hlog : ∀ x ∈ A, ∃ a, a < 2 ^ ν ∧ g ^ a = x := by
    intro x hx
    obtain ⟨i, hi, hgi⟩ := hg.eq_pow_of_pow_eq_one (hA x hx)
    exact ⟨i, hi, hgi⟩
  choose! f hf using hlog
  set E : Finset ℕ := A.image f with hE
  have hEbound : ∀ a ∈ E, a < 2 ^ ν := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (hf x hx).1
  have hfinj : ∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y := by
    intro x hx y hy hxy
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  have hEcard : E.card = A.card := Finset.card_image_of_injOn hfinj
  have hgE : ∀ a ∈ E, g ^ a ∈ A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    rw [(hf x hx).2]
    exact hx
  -- the fold vanishes at `g`
  have hevalg : ((subsetFolded ν E).map (Int.castRingHom (ZMod p))).eval g = 0 := by
    rw [subsetFolded_eval hν hg hEbound, hE, Finset.sum_image hfinj,
      Finset.sum_congr rfl (fun x hx => (hf x hx).2)]
    exact hsum
  -- the engine dichotomy: the fold vanishes identically
  have hF0 : subsetFolded ν E = 0 := by
    by_contra hne
    have hl1 : l1On (2 ^ (ν - 1)) (subsetFolded ν E) ≤ A.card :=
      hEcard ▸ l1On_subsetFolded_le hν hEbound
    have hth : l1On (2 ^ (ν - 1)) (subsetFolded ν E) ^ 2 ^ (ν - 1) < p :=
      lt_of_le_of_lt (Nat.pow_le_pow_left hl1 _) hp
    exact not_isRoot_of_l1On_pow_lt hν hg hne (subsetFolded_natDegree_lt ν E) hth hevalg
  -- antipodal conclusion through the half-shift
  intro x hx
  have hhalf : g ^ (2 ^ (ν - 1)) = -1 := pow_half_eq_neg_one_field hν hg
  have hshift := shift_mem_of_subsetFolded_eq_zero hν hEbound hF0
    (Finset.mem_image_of_mem f hx)
  by_cases hcase : f x < 2 ^ (ν - 1)
  · rw [if_pos hcase] at hshift
    have hmem : g ^ (f x + 2 ^ (ν - 1)) ∈ A := hgE _ hshift
    rwa [pow_add, (hf x hx).2, hhalf, mul_neg_one] at hmem
  · rw [if_neg hcase] at hshift
    have hmem : g ^ (f x - 2 ^ (ν - 1)) ∈ A := hgE _ hshift
    have hx' : x = -(g ^ (f x - 2 ^ (ν - 1))) := by
      have hsplit : f x - 2 ^ (ν - 1) + 2 ^ (ν - 1) = f x := by
        have := hEbound (f x) (Finset.mem_image_of_mem f hx)
        omega
      calc x = g ^ (f x) := ((hf x hx).2).symm
        _ = g ^ (f x - 2 ^ (ν - 1)) * g ^ (2 ^ (ν - 1)) := by
            rw [← pow_add, hsplit]
        _ = -(g ^ (f x - 2 ^ (ν - 1))) := by rw [hhalf, mul_neg_one]
    rw [hx', neg_neg]
    exact hmem

/-! ## The headline: the ladder exact list law over `F_p` -/

open Classical in
/-- **THE LADDER EXACT LIST LAW OVER `F_p`**: for `p > (2r)^{2^{ν−1}}`, every
codeword of `rsCode dom k` (`k ≤ 2r−2`) over the 2-power domain `μ_n ⊂ F_p`
agreeing with the ladder word on `≥ 2r` points is a subset-sum-fibre codeword —
the fibre law's rigidity half in production fields, above the explicit
resultant threshold. -/
theorem ladder_explainer_fiber_modp {p : ℕ} [Fact p.Prime] {n ν r k : ℕ}
    {g lam : ZMod p} {dom : Fin n ↪ ZMod p}
    (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν)) (hn : n = 2 ^ ν)
    (hroot : ∀ i, (dom i) ^ n = 1) (hk : 1 ≤ k) (hk2 : k ≤ 2 * r - 2)
    (hp : (2 * r) ^ 2 ^ (ν - 1) < p)
    {c : Fin n → ZMod p}
    (hc : c ∈ (ProximityGap.SpikeFloor.rsCode dom k :
      Submodule (ZMod p) (Fin n → ZMod p)))
    (hagr : 2 * r ≤ (Finset.univ.filter
      (fun i => c i = ProximityGap.LadderList.ladderWord dom r lam i)).card) :
    ∃ T : Finset (ZMod p), T.card = r ∧ (∀ t ∈ T, t ^ (n / 2) = 1) ∧
      (∑ t ∈ T, t = -lam) ∧
      ∀ i, c i = ProximityGap.LadderList.ladderWord dom r lam i
        - ∏ t ∈ T, ((dom i) ^ 2 - t) := by
  have hr3 : 3 ≤ 2 * r := by omega
  have hth3 : 3 ≤ (2 * r) ^ 2 ^ (ν - 1) :=
    le_trans hr3 (Nat.le_self_pow (Nat.two_pow_pos (ν - 1)).ne' _)
  refine ProximityGap.LadderList.ladder_explainer_fiber_of_closure ?_ ?_ hroot ?_
    hk hk2 hc (by convert hagr using 2; exact Finset.filter_congr_decidable _ _ _)
  · -- `2 ≠ 0` in `ZMod p`: the threshold forces `p > 3`
    intro h2
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2'
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rw [hn]
    exact dvd_pow_self 2 (by omega)
  · intro A hcard hAroots hsum
    refine subset_neg_mem_of_sum_zero_modp hν hg ?_ hsum ?_
    · intro x hx
      rw [← hn]
      exact hAroots x hx
    · rw [hcard]
      exact hp

end ProximityGap.LadderListModP

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderListModP.subsetFolded_eval
#print axioms ProximityGap.LadderListModP.l1On_subsetFolded_le
#print axioms ProximityGap.LadderListModP.shift_mem_of_subsetFolded_eq_zero
#print axioms ProximityGap.LadderListModP.subset_neg_mem_of_sum_zero_modp
#print axioms ProximityGap.LadderListModP.ladder_explainer_fiber_modp
