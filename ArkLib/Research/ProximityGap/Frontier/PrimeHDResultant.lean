/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Prime-Field Hidden-Derivative Resultant Infrastructure (`PrimeHDResultant`)

Characteristic-free Sylvester resultant valuation, bivariate multiplicity, weighted degree descent,
and `O(1)` common-root cap theorems for the prime-field hidden-derivative list-decoding engine
(`char K = p > k - 1`), completely avoiding any `τ = 2D - 3` Taylor-clearing blowup.

Adapted cleanly to Lean 4.35 / ArkLib from the characteristic-free core of `B6401ResultantOrd`,
`B6401KerDOrders` (Part 1), and `B6401ResLineOrd` (Parts 1–4, 6) in the Apache-2.0
`proximity-prize/proximity-prize` reference repository.

## Main statements

1. **Weighted & Exact Sylvester Valuation Bounds (any commutative ring `R`):**
   - `pow_dvd_resultant_of_weighted_ord`: if `t^(m_f - w * i) ∣ f.coeff i` and
     `t^(m_g - w * j) ∣ g.coeff j`, then
     `t^(resOrdWeighted df mf dg mg w) ∣ Polynomial.resultant f g df dg`.
   - `pow_dvd_resultant_exact`: exact unweighted (`w = 1`) bound with the
     `+(df - mf) * (dg - mg)` surplus term.
2. **Bivariate Multiplicity & Shift Invariance on `BiPoly A = A[X][Y]`:**
   - `resultant_shiftBi`: exact translation covariance
     `resultant (shiftBi x₀ y₀ f) (shiftBi x₀ y₀ g) df dg = (resultant f g df dg).comp (C x₀ + X)`.
   - `pow_dvd_resultant_of_biMultGE` & `X_sub_C_pow_dvd_resultant_of_biMultGE`:
     2D multiplicities `mf, mg` at `(x₀, y₀)` force `(X - C x₀)^(resOrdExact df mf dg mg)` to divide
     `Polynomial.resultant f g df dg`.
   - `sum_resOrdExact_le_natDegree_resultant`: over distinct sites `x : ι → K` in a field `K`,
     a nonzero resultant satisfies `∑ i, resOrdExact df (mf i) dg (mg i) ≤ (resultant f g df dg).natDegree`.
3. **Zero-`τ` Contact Resultant Elimination on `ContactPoly A = A[X][Y₀][Y₁]`:**
   - `resultant_ne_zero_of_not_dvd_scalar` and `resultant_ne_zero_of_not_dvd`:
     irreducibility of `F` and `F ∤ G` force `Polynomial.resultant F G d s ≠ 0`.
   - `biWeightedDeg_resultant_le`:
     `biWeightedDeg (resultant F G d s) wY ≤ d * W + s * (W_F - d * (wY - 1))`.
   - `natDegree_le_biWeightedDeg_div`: `Φ.natDegree ≤ biWeightedDeg Φ wY / wY`.
   - `degZ_resultant_le`: parametric `Z`-degree descent `≤ d * D_Z' + s * D_ZF`.
   - `evalBi_resultant_eq_zero` & `triEval_resultant_eq_zero`: common contact-root vanishing.
   - `card_common_roots_le_of_resultant_scalar` & `card_common_roots_le_of_resultant`:
     `O(1)` root count bound `T.card ≤ (d * W + s * (W_F - d * (wY - 1))) / wY`.
-/

set_option autoImplicit false
set_option linter.style.longFile 1800
set_option maxHeartbeats 1200000

namespace ArkLib.ProximityGap.Frontier.PrimeHDResultant

open Polynomial Matrix
open scoped BigOperators

/-! ### Part 1: Weighted & Exact Sylvester Resultant Valuation Bounds -/

section SylvesterOrd

/-- Step gain `max(0, m - w * i) - max(0, m - w * (i + 1))` in `ℕ`. -/
def stepGain (m w i : ℕ) : ℕ :=
  (m - w * i) - (m - w * (i + 1))

theorem stepGain_sum (m w k : ℕ) :
    ∑ i ∈ Finset.range k, stepGain m w i = m - (m - w * k) := by
  induction k with
  | zero => simp [stepGain]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold stepGain
    have h1 : m - w * (k + 1) ≤ m - w * k :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left w (Nat.le_succ k)) m
    have h2 : m - w * k ≤ m := Nat.sub_le m (w * k)
    omega

theorem max_sub_eq_sub_sum_stepGain (m w k : ℕ) :
    m - w * k + ∑ i ∈ Finset.range k, stepGain m w i = m := by
  rw [stepGain_sum]
  have : m - w * k ≤ m := Nat.sub_le m (w * k)
  omega

/-- All `2 * df * dg` step gains sorted in descending order. -/
def allGainsSorted (df mf dg mg w : ℕ) : List ℕ :=
  let gf : List ℕ := (List.range df).flatMap fun i => List.replicate dg (stepGain mf w i)
  let gg : List ℕ := (List.range dg).flatMap fun j => List.replicate df (stepGain mg w j)
  (gf ++ gg).mergeSort (· ≥ ·)

/-- Exact weighted Sylvester resultant order lower bound
`dg * mf + df * mg - sum(top df * dg gains)`. -/
def resOrdWeighted (df mf dg mg w : ℕ) : ℕ :=
  if df = 0 then dg * mf
  else if dg = 0 then df * mg
  else dg * mf + df * mg - ((allGainsSorted df mf dg mg w).take (df * dg)).sum

/-- Exact unweighted (`w = 1`) Sylvester resultant order lower bound in closed form.
Adds `(df - mf) * (dg - mg)` before subtracting `df * dg` so `ℕ` subtraction never truncates. -/
def resOrdExact (df mf dg mg : ℕ) : ℕ :=
  if df = 0 then dg * mf
  else if dg = 0 then df * mg
  else dg * mf + df * mg + (df - mf) * (dg - mg) - df * dg

private lemma list_flatMap_sublist {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, (f x).Sublist (g x)) : (l.flatMap f).Sublist (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih fun y hy => h y (by simp [hy]))

private lemma list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.flatMap_cons, List.sum_append, ih]

/-- The sum of any sublist `s` of `l` is at most the sum of the top `s.length` elements of
`l.mergeSort (· ≥ ·)`. -/
theorem sum_sublist_le_sum_take_sorted {s l : List ℕ} (hsub : s.Sublist l) :
    s.sum ≤ ((l.mergeSort (· ≥ ·)).take s.length).sum := by
  have hperm : (l.mergeSort (· ≥ ·)).Perm l := List.mergeSort_perm l (· ≥ ·)
  have hsorted : (l.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.pairwise_mergeSort' (· ≥ ·) l
  have haux : ∀ (L : List ℕ), L.Pairwise (· ≥ ·) →
      ∀ (S : Multiset ℕ), S ≤ (L : Multiset ℕ) → S.sum ≤ (L.take (Multiset.card S)).sum := by
    intro L hL
    induction L with
    | nil =>
      intro S hS
      have : S = 0 := Multiset.le_zero.mp hS
      simp [this]
    | cons a t ih =>
      intro S hS
      have ht : t.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
      have ha : ∀ x ∈ t, a ≥ x := (List.pairwise_cons.mp hL).1
      by_cases hS0 : S = 0
      · simp [hS0]
      · by_cases haS : a ∈ S
        · obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem haS
          have hS'le : S' ≤ (t : Multiset ℕ) := by
            rw [← Multiset.cons_le_cons_iff a]
            exact hS
          have hcard : Multiset.card (a ::ₘ S') = Multiset.card S' + 1 := Multiset.card_cons a S'
          rw [hcard, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
          exact Nat.add_le_add_left (ih ht S' hS'le) a
        · obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hS0
          obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem hb
          have hSle_t : b ::ₘ S' ≤ (t : Multiset ℕ) := by
            have hle : ∀ x, Multiset.count x (b ::ₘ S') ≤ Multiset.count x (t : Multiset ℕ) := by
              intro x
              have hcx := Multiset.le_iff_count.mp hS x
              change Multiset.count x (b ::ₘ S') ≤ Multiset.count x (a ::ₘ (t : Multiset ℕ)) at hcx
              by_cases hxa : x = a
              · subst hxa
                have h0 : Multiset.count x (b ::ₘ S') = 0 := Multiset.count_eq_zero.mpr haS
                omega
              · rw [Multiset.count_cons_of_ne hxa] at hcx
                exact hcx
            exact Multiset.le_iff_count.mpr hle
          have hS'le_t : S' ≤ (t : Multiset ℕ) := (Multiset.le_cons_self S' b).trans hSle_t
          have hb_mem_t : b ∈ t := by
            have : b ∈ (t : Multiset ℕ) :=
              Multiset.mem_of_le hSle_t (Multiset.mem_cons_self b S')
            simpa using this
          have hba : b ≤ a := ha b hb_mem_t
          have hcard : Multiset.card (b ::ₘ S') = Multiset.card S' + 1 := Multiset.card_cons b S'
          rw [hcard, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
          exact Nat.add_le_add hba (ih ht S' hS'le_t)
  have hle : (s : Multiset ℕ) ≤ ((l.mergeSort (· ≥ ·)) : Multiset ℕ) := by
    rw [Multiset.coe_eq_coe.mpr hperm]
    exact Multiset.coe_le.mpr hsub.subperm
  simpa using haux (l.mergeSort (· ≥ ·)) hsorted (s : Multiset ℕ) hle

/-- Every valid Sylvester permutation tuple `(ir, jr)` with `0 ≤ ir r ≤ df`, `0 ≤ jr r' ≤ dg`,
and `∑ ir + ∑ jr = df * dg` satisfies
`resOrdWeighted df mf dg mg w ≤ ∑ (mf - w * ir r) + ∑ (mg - w * jr r')`. -/
theorem sylvester_tuple_val_ge (df mf dg mg w : ℕ)
    (ir : Fin dg → ℕ) (jr : Fin df → ℕ)
    (hi : ∀ r, ir r ≤ df) (hj : ∀ r', jr r' ≤ dg)
    (hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg) :
    resOrdWeighted df mf dg mg w ≤
      (∑ r : Fin dg, (mf - w * ir r)) + (∑ r' : Fin df, (mg - w * jr r')) := by
  by_cases hdf : df = 0
  · subst hdf
    simp only [resOrdWeighted, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have hi0 : ∀ r : Fin dg, ir r = 0 := fun r => Nat.eq_zero_of_le_zero (hi r)
    simp [hi0]
  by_cases hdg : dg = 0
  · subst hdg
    simp only [resOrdWeighted, hdf, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    have hj0 : ∀ r' : Fin df, jr r' = 0 := fun r' => Nat.eq_zero_of_le_zero (hj r')
    simp [hj0]
  unfold resOrdWeighted
  simp only [hdf, hdg, ↓reduceIte]
  have hEqF : (∑ r : Fin dg, (mf - w * ir r)) +
      (∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u) = dg * mf := by
    rw [← Finset.sum_add_distrib]
    simp_rw [max_sub_eq_sub_sum_stepGain]
    simp
  have hEqG : (∑ r' : Fin df, (mg - w * jr r')) +
      (∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v) = df * mg := by
    rw [← Finset.sum_add_distrib]
    simp_rw [max_sub_eq_sub_sum_stepGain]
    simp
  let sF : List ℕ := (List.range df).flatMap fun u =>
    List.replicate ((Finset.univ.filter fun r : Fin dg => u < ir r).card) (stepGain mf w u)
  let sG : List ℕ := (List.range dg).flatMap fun v =>
    List.replicate ((Finset.univ.filter fun r' : Fin df => v < jr r').card) (stepGain mg w v)
  let gF : List ℕ := (List.range df).flatMap fun u => List.replicate dg (stepGain mf w u)
  let gG : List ℕ := (List.range dg).flatMap fun v => List.replicate df (stepGain mg w v)
  have hsubF : sF.Sublist gF := list_flatMap_sublist fun u _ =>
    (List.replicate_sublist_replicate _).mpr (by
      have := Finset.card_le_univ (Finset.univ.filter fun r : Fin dg => u < ir r)
      simpa using this)
  have hsubG : sG.Sublist gG := list_flatMap_sublist fun v _ =>
    (List.replicate_sublist_replicate _).mpr (by
      have := Finset.card_le_univ (Finset.univ.filter fun r' : Fin df => v < jr r')
      simpa using this)
  have hsub : (sF ++ sG).Sublist (gF ++ gG) := hsubF.append hsubG
  have hlenF : sF.length = ∑ r : Fin dg, ir r := by
    have h1 : sF.length =
        ∑ u ∈ Finset.range df, (Finset.univ.filter fun r : Fin dg => u < ir r).card := by
      simp only [sF, List.length_flatMap, List.length_replicate]
      exact list_sum_map_range df _
    rw [h1]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    have : (∑ u ∈ Finset.range df, if u < ir r then 1 else 0) = (Finset.range (ir r)).card := by
      rw [← Finset.card_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hi r), h⟩⟩
    rw [this, Finset.card_range]
  have hlenG : sG.length = ∑ r' : Fin df, jr r' := by
    have h1 : sG.length =
        ∑ v ∈ Finset.range dg, (Finset.univ.filter fun r' : Fin df => v < jr r').card := by
      simp only [sG, List.length_flatMap, List.length_replicate]
      exact list_sum_map_range dg _
    rw [h1]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r' _
    have : (∑ v ∈ Finset.range dg, if v < jr r' then 1 else 0) = (Finset.range (jr r')).card := by
      rw [← Finset.card_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hj r'), h⟩⟩
    rw [this, Finset.card_range]
  have hsumF : sF.sum = ∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u := by
    have h1 : sF.sum = ∑ u ∈ Finset.range df,
        (Finset.univ.filter fun r : Fin dg => u < ir r).card * stepGain mf w u := by
      rw [show sF.sum = ((List.range df).map fun u =>
            (List.replicate ((Finset.univ.filter fun r : Fin dg => u < ir r).card)
              (stepGain mf w u)).sum).sum from list_sum_flatMap _ _]
      simp only [List.sum_replicate, smul_eq_mul]
      exact list_sum_map_range df _
    rw [h1]
    have h2 : ∀ u, (Finset.univ.filter fun r : Fin dg => u < ir r).card * stepGain mf w u =
        ∑ r : Fin dg, if u < ir r then stepGain mf w u else 0 := fun u => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hi r), h⟩⟩
  have hsumG : sG.sum = ∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v := by
    have h1 : sG.sum = ∑ v ∈ Finset.range dg,
        (Finset.univ.filter fun r' : Fin df => v < jr r').card * stepGain mg w v := by
      rw [show sG.sum = ((List.range dg).map fun v =>
            (List.replicate ((Finset.univ.filter fun r' : Fin df => v < jr r').card)
              (stepGain mg w v)).sum).sum from list_sum_flatMap _ _]
      simp only [List.sum_replicate, smul_eq_mul]
      exact list_sum_map_range dg _
    rw [h1]
    have h2 : ∀ v, (Finset.univ.filter fun r' : Fin df => v < jr r').card * stepGain mg w v =
        ∑ r' : Fin df, if v < jr r' then stepGain mg w v else 0 := fun v => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r' _
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hj r'), h⟩⟩
  have hbound := sum_sublist_le_sum_take_sorted hsub
  rw [List.length_append, hlenF, hlenG, hsum, List.sum_append, hsumF, hsumG] at hbound
  change (∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u) +
      (∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v) ≤
      ((allGainsSorted df mf dg mg w).take (df * dg)).sum at hbound
  omega

/-- **Weighted Sylvester Resultant Valuation Theorem (over any commutative ring `R`):**
If `t^(mf - w * i) ∣ f.coeff i` and `t^(mg - w * j) ∣ g.coeff j`, then
`t^(resOrdWeighted df mf dg mg w) ∣ Polynomial.resultant f g df dg`. -/
theorem pow_dvd_resultant_of_weighted_ord {R : Type*} [CommRing R] (t : R)
    (f g : R[X]) (df mf dg mg w : ℕ)
    (_hfd : f.natDegree ≤ df) (_hgd : g.natDegree ≤ dg)
    (hf : ∀ i, t ^ (mf - w * i) ∣ f.coeff i)
    (hg : ∀ j, t ^ (mg - w * j) ∣ g.coeff j) :
    t ^ resOrdWeighted df mf dg mg w ∣ Polynomial.resultant f g df dg := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hzero : ∃ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (df + dg), Polynomial.sylvester f g df dg (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0]
    exact dvd_zero _
  · push Not at hzero
    let jr : Fin df → ℕ := fun r' => (σ (Fin.castAdd dg r')).val - r'.val
    let ir : Fin dg → ℕ := fun r => (σ (Fin.natAdd df r)).val - r.val
    have hbounds :
      (∀ r' : Fin df, r'.val ≤ (σ (Fin.castAdd dg r')).val ∧
        (σ (Fin.castAdd dg r')).val ≤ r'.val + dg ∧
        Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r') =
          g.coeff (jr r')) ∧
      (∀ r : Fin dg, r.val ≤ (σ (Fin.natAdd df r)).val ∧
        (σ (Fin.natAdd df r)).val ≤ r.val + df ∧
        Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r) =
          f.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd dg r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd df r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hi : ∀ r, ir r ≤ df := fun r => by
      have h1 := (hbounds.2 r).1; have h2 := (hbounds.2 r).2.1; dsimp [ir]; omega
    have hj : ∀ r', jr r' ≤ dg := fun r' => by
      have h1 := (hbounds.1 r').1; have h2 := (hbounds.1 r').2.1; dsimp [jr]; omega
    have hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg := by
      have hperm_sum : ∑ k : Fin (df + dg), (σ k).val = ∑ k : Fin (df + dg), k.val :=
        Equiv.sum_comp σ (fun k : Fin (df + dg) => k.val)
      have hsplit_σ : ∑ k : Fin (df + dg), (σ k).val =
          (∑ r' : Fin df, (σ (Fin.castAdd dg r')).val) +
          (∑ r : Fin dg, (σ (Fin.natAdd df r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (df + dg), k.val =
          (∑ r' : Fin df, r'.val) + (∑ r : Fin dg, (df + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin df, jr r') + (∑ r' : Fin df, r'.val) =
          ∑ r' : Fin df, (σ (Fin.castAdd dg r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin dg, ir r) + (∑ r : Fin dg, r.val) =
          ∑ r : Fin dg, (σ (Fin.natAdd df r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin dg, (df + r.val) = dg * df + ∑ r : Fin dg, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
      have hcomm : dg * df = df * dg := mul_comm dg df
      omega
    have hdvd_prod :
        t ^ ((∑ r : Fin dg, (mf - w * ir r)) + (∑ r' : Fin df, (mg - w * jr r'))) ∣
          ∏ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j := by
      rw [Fin.prod_univ_add, add_comm, pow_add, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_pow_eq_pow_sum]
      apply mul_dvd_mul
      · apply Finset.prod_dvd_prod_of_dvd
        intro r' _
        simpa [(hbounds.1 r').2.2] using hg (jr r')
      · apply Finset.prod_dvd_prod_of_dvd
        intro r _
        simpa [(hbounds.2 r).2.2] using hf (ir r)
    exact (pow_dvd_pow t (sylvester_tuple_val_ge df mf dg mg w ir jr hi hj hsum)).trans hdvd_prod

/-- **Exact unweighted (`w = 1`) Sylvester Resultant Valuation Theorem (with
`+(df - mf) * (dg - mg)` surplus):** if `t^(mf - i) ∣ f.coeff i` and `t^(mg - j) ∣ g.coeff j`,
then `t^(resOrdExact df mf dg mg) ∣ Polynomial.resultant f g df dg`. -/
theorem pow_dvd_resultant_exact {R : Type*} [CommRing R] (t : R)
    (f g : R[X]) (df mf dg mg : ℕ)
    (_hfd : f.natDegree ≤ df) (_hgd : g.natDegree ≤ dg)
    (hf : ∀ i, t ^ (mf - i) ∣ f.coeff i)
    (hg : ∀ j, t ^ (mg - j) ∣ g.coeff j) :
    t ^ resOrdExact df mf dg mg ∣ Polynomial.resultant f g df dg := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hzero : ∃ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (df + dg), Polynomial.sylvester f g df dg (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0]
    exact dvd_zero _
  · push Not at hzero
    let jr : Fin df → ℕ := fun r' => (σ (Fin.castAdd dg r')).val - r'.val
    let ir : Fin dg → ℕ := fun r => (σ (Fin.natAdd df r)).val - r.val
    have hbounds :
      (∀ r' : Fin df, r'.val ≤ (σ (Fin.castAdd dg r')).val ∧
        (σ (Fin.castAdd dg r')).val ≤ r'.val + dg ∧
        Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r') =
          g.coeff (jr r')) ∧
      (∀ r : Fin dg, r.val ≤ (σ (Fin.natAdd df r)).val ∧
        (σ (Fin.natAdd df r)).val ≤ r.val + df ∧
        Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r) =
          f.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd dg r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd df r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg := by
      have hperm_sum : ∑ k : Fin (df + dg), (σ k).val = ∑ k : Fin (df + dg), k.val :=
        Equiv.sum_comp σ (fun k : Fin (df + dg) => k.val)
      have hsplit_σ : ∑ k : Fin (df + dg), (σ k).val =
          (∑ r' : Fin df, (σ (Fin.castAdd dg r')).val) +
          (∑ r : Fin dg, (σ (Fin.natAdd df r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (df + dg), k.val =
          (∑ r' : Fin df, r'.val) + (∑ r : Fin dg, (df + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin df, jr r') + (∑ r' : Fin df, r'.val) =
          ∑ r' : Fin df, (σ (Fin.castAdd dg r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin dg, ir r) + (∑ r : Fin dg, r.val) =
          ∑ r : Fin dg, (σ (Fin.natAdd df r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin dg, (df + r.val) = dg * df + ∑ r : Fin dg, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
      have hcomm : dg * df = df * dg := mul_comm dg df
      omega
    have hdvd_prod : t ^ ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r'))) ∣
        ∏ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j := by
      rw [Fin.prod_univ_add, add_comm, pow_add, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_pow_eq_pow_sum]
      apply mul_dvd_mul
      · apply Finset.prod_dvd_prod_of_dvd; intro r' _
        simpa [(hbounds.1 r').2.2] using hg (jr r')
      · apply Finset.prod_dvd_prod_of_dvd; intro r _
        simpa [(hbounds.2 r).2.2] using hf (ir r)
    have hexp : resOrdExact df mf dg mg ≤
        (∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) := by
      by_cases hdf : df = 0
      · subst hdf
        simp only [resOrdExact, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        have hi0 : ∀ r : Fin dg, ir r = 0 := fun r => by
          have h1 := (hbounds.2 r).1; have h2 := (hbounds.2 r).2.1; dsimp [ir]; omega
        simp [hi0]
      by_cases hdg : dg = 0
      · subst hdg
        simp only [resOrdExact, hdf, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
        have hj0 : ∀ r' : Fin df, jr r' = 0 := fun r' => by
          have h1 := (hbounds.1 r').1
          have h2 := (hbounds.1 r').2.1
          change (σ (Fin.castAdd 0 r')).val - r'.val = 0
          omega
        simp [hj0]
      unfold resOrdExact; simp only [hdf, hdg, ↓reduceIte]
      have hZ_split : ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) =
          (dg * mf + df * mg - df * dg : ℤ) +
          ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
        have hF : (∑ r : Fin dg, ((mf - ir r : ℕ) : ℤ)) -
            (∑ r : Fin dg, ((ir r - mf : ℕ) : ℤ)) =
            (dg : ℤ) * mf - ∑ r : Fin dg, (ir r : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          have : ∀ r : Fin dg, ((mf - ir r : ℕ) : ℤ) - ((ir r - mf : ℕ) : ℤ) =
              (mf : ℤ) - ir r := fun r => by omega
          simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
        have hG : (∑ r' : Fin df, ((mg - jr r' : ℕ) : ℤ)) -
            (∑ r' : Fin df, ((jr r' - mg : ℕ) : ℤ)) =
            (df : ℤ) * mg - ∑ r' : Fin df, (jr r' : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          have : ∀ r' : Fin df, ((mg - jr r' : ℕ) : ℤ) - ((jr r' - mg : ℕ) : ℤ) =
              (mg : ℤ) - jr r' := fun r' => by omega
          simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
        have hsumZ : (∑ r : Fin dg, (ir r : ℤ)) + (∑ r' : Fin df, (jr r' : ℤ)) =
            (df : ℤ) * dg := by exact_mod_cast hsum
        push_cast at hF hG ⊢; linarith only [hF, hG, hsumZ]
      by_cases hsmall : mf < df ∧ mg < dg
      · rcases hsmall with ⟨hmf, hmg⟩
        let a := df - mf
        let b := dg - mg
        let Aset := Finset.univ.filter fun r' : Fin df => mf + mg ≤ (σ (Fin.castAdd dg r')).val
        let Bset := Finset.univ.filter fun r : Fin dg => mf + mg ≤ (σ (Fin.natAdd df r)).val
        let Top := Finset.univ.filter fun i : Fin (df + dg) => mf + mg ≤ i.val
        have hcard_top : Top.card = a + b := by
          have : Top = (Finset.Ico (mf + mg) (df + dg)).attach.image
              (fun x => ⟨x.1, (Finset.mem_Ico.mp x.2).2⟩) := by
            ext i; simp only [Top, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_attach, Subtype.exists, Finset.mem_Ico]
            exact ⟨fun h => ⟨i.val, ⟨h, i.isLt⟩, rfl⟩, fun ⟨_, ⟨hv, _⟩, h⟩ => h ▸ hv⟩
          rw [this, Finset.card_image_of_injective _ (fun _ _ h => Subtype.ext (congrArg Fin.val h)),
            Finset.card_attach, Nat.card_Ico]; omega
        have hsum_top : 2 * (∑ i ∈ Top, i.val) = (a + b) * (2 * (mf + mg) + (a + b) - 1) := by
          have hbij : ∑ i ∈ Top, i.val = ∑ t ∈ Finset.range (a + b), (mf + mg + t) := by
            refine Finset.sum_bij (fun i _ => i.val - (mf + mg)) ?_ ?_ ?_ ?_
            · intro i hi; rw [Finset.mem_range]; have h1 := (Finset.mem_filter.mp hi).2
              dsimp only [a, b]; omega
            · intro i1 hi1 i2 hi2 h; apply Fin.ext
              have h1 := (Finset.mem_filter.mp hi1).2; have h2 := (Finset.mem_filter.mp hi2).2
              omega
            · intro t ht; rw [Finset.mem_range] at ht
              refine ⟨⟨mf + mg + t, by dsimp only [a, b] at ht; omega⟩, ?_, by simp⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
            · intro i hi; have h1 := (Finset.mem_filter.mp hi).2; omega
          rw [hbij, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
          have htri : 2 * ∑ t ∈ Finset.range (a + b), t = (a + b) * (a + b - 1) := by
            have := Finset.sum_range_id_mul_two (a + b); linarith only [this]
          have h1 : 1 ≤ a + b := by dsimp only [a, b]; omega
          have h2 : 1 ≤ 2 * (mf + mg) + (a + b) := by omega
          zify [h1, h2] at htri ⊢
          nlinarith only [htri]
        let Pre := Finset.univ.filter fun j : Fin (df + dg) => mf + mg ≤ (σ j).val
        have hPre_eq : Pre = Aset.image (Fin.castAdd dg) ∪ Bset.image (Fin.natAdd df) := by
          ext j; induction j using Fin.addCases with
          | left r' =>
            simp only [Pre, Aset, Bset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · intro h; left; exact ⟨r', h, rfl⟩
            · rintro (⟨r'', hr'', heq⟩ | ⟨r, _, heq⟩)
              · have : r'' = r' := Fin.castAdd_injective df dg heq; subst this; exact hr''
              · exfalso; have := congrArg Fin.val heq; simp at this; omega
          | right r =>
            simp only [Pre, Aset, Bset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · intro h; right; exact ⟨r, h, rfl⟩
            · rintro (⟨r', _, heq⟩ | ⟨r'', hr'', heq⟩)
              · exfalso; have := congrArg Fin.val heq; simp at this; omega
              · have : r'' = r := Fin.natAdd_injective dg df heq; subst this; exact hr''
        have hPre_disj : Disjoint (Aset.image (Fin.castAdd dg)) (Bset.image (Fin.natAdd df)) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          rcases Finset.mem_image.mp h1 with ⟨r', _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨r, _, heq⟩
          have := congrArg Fin.val heq; simp at this; omega
        have hPre_card : Pre.card = Aset.card + Bset.card := by
          rw [hPre_eq, Finset.card_union_of_disjoint hPre_disj,
            Finset.card_image_of_injective _ (Fin.castAdd_injective df dg),
            Finset.card_image_of_injective _ (Fin.natAdd_injective dg df)]
        have hPre_top : Pre.image σ = Top := by
          ext i; simp only [Pre, Top, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨_, hj, h⟩ => h ▸ hj, fun hi => ⟨σ.symm i, by simpa using hi, by simp⟩⟩
        have hkl : Aset.card + Bset.card = a + b := by
          rw [← hPre_card, ← Finset.card_image_of_injective Pre σ.injective, hPre_top, hcard_top]
        have hsum_AB : (∑ r' ∈ Aset, (σ (Fin.castAdd dg r')).val) +
            (∑ r ∈ Bset, (σ (Fin.natAdd df r)).val) = ∑ i ∈ Top, i.val := by
          rw [← hPre_top, Finset.sum_image (fun _ _ _ _ h => σ.injective h), hPre_eq,
            Finset.sum_union hPre_disj,
            Finset.sum_image (fun _ _ _ _ h => Fin.castAdd_injective df dg h),
            Finset.sum_image (fun _ _ _ _ h => Fin.natAdd_injective dg df h)]
        have hsum_sub_max : ∀ (n : ℕ) (S : Finset (Fin n)),
            2 * (∑ x ∈ S, x.val) + S.card * (S.card + 1) ≤ 2 * S.card * n := by
          intro n S
          have hrev : ∑ t ∈ Finset.range S.card, t ≤ ∑ x ∈ S, (n - 1 - x.val) := by
            have hT : (S.image (fun x : Fin n => n - 1 - x.val)).card = S.card :=
              Finset.card_image_of_injective _ (fun x y h => Fin.ext (by omega))
            have hsum_img : ∑ y ∈ S.image (fun x : Fin n => n - 1 - x.val), y =
                ∑ x ∈ S, (n - 1 - x.val) :=
              Finset.sum_image (fun x _ y _ h => Fin.ext (by omega))
            rw [← hsum_img]
            generalize hU : S.image (fun x : Fin n => n - 1 - x.val) = U
            rw [hU] at hT; rw [← hT]
            clear hT hsum_img hU S n
            induction U using Finset.strongInduction with
            | H U ih =>
              by_cases hU0 : U = ∅
              · subst hU0; simp
              · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0
                let m := U.max' hne
                have hm : m ∈ U := Finset.max'_mem U hne
                let U' := U.erase m
                have hsub : U' ⊂ U := Finset.erase_ssubset hm
                have hcard : U.card = U'.card + 1 := (Finset.card_erase_add_one hm).symm
                have hge : U'.card ≤ m := by
                  have hsub_range : U' ⊆ Finset.range m := by
                    intro x hx
                    rw [Finset.mem_range]
                    have hxU : x ∈ U := Finset.mem_of_mem_erase hx
                    have hne' : x ≠ m := (Finset.mem_erase.mp hx).1
                    exact lt_of_le_of_ne (Finset.le_max' U x hxU) hne'
                  exact (Finset.card_le_card hsub_range).trans (by simp)
                rw [hcard, Finset.sum_range_succ, ← Finset.add_sum_erase U (fun y => y) hm]
                have := ih U' hsub
                dsimp only [U', m] at this hge ⊢; omega
          have htri : 2 * ∑ t ∈ Finset.range S.card, t = S.card * (S.card - 1) := by
            have := Finset.sum_range_id_mul_two S.card; linarith only [this]
          have hadd : (∑ x ∈ S, x.val) + (∑ x ∈ S, (n - 1 - x.val)) = S.card * (n - 1) := by
            rw [← Finset.sum_add_distrib]
            have : ∀ x ∈ S, x.val + (n - 1 - x.val) = n - 1 := fun x _ => by omega
            rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
          by_cases hS0 : S.card = 0
          · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0; subst hSe; simp
          · have hn1 : 1 ≤ n := by
              obtain ⟨x, _⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hS0)
              have hx := x.isLt; omega
            zify [hn1, show 1 ≤ S.card by omega] at hrev htri hadd ⊢
            nlinarith only [hrev, htri, hadd]
        have hA_bound := hsum_sub_max df Aset
        have hB_bound := hsum_sub_max dg Bset
        have hge_AB : (∑ r ∈ Bset, ((ir r : ℤ) - mf)) + (∑ r' ∈ Aset, ((jr r' : ℤ) - mg)) ≤
            ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
          have h1 : ∑ r ∈ Bset, ((ir r : ℤ) - mf) ≤ ∑ r : Fin dg, ((ir r - mf : ℕ) : ℤ) := by
            refine (Finset.sum_le_sum fun r _ =>
              (by omega : ((ir r : ℤ) - mf) ≤ ((ir r - mf : ℕ) : ℤ))).trans ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
          have h2 : ∑ r' ∈ Aset, ((jr r' : ℤ) - mg) ≤ ∑ r' : Fin df, ((jr r' - mg : ℕ) : ℤ) := by
            refine (Finset.sum_le_sum fun r' _ =>
              (by omega : ((jr r' : ℤ) - mg) ≤ ((jr r' - mg : ℕ) : ℤ))).trans ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
          push_cast; linarith only [h1, h2]
        have hAB_val : (∑ r ∈ Bset, ((ir r : ℤ) - mf)) + (∑ r' ∈ Aset, ((jr r' : ℤ) - mg)) =
            (∑ i ∈ Top, (i.val : ℤ)) - (∑ r ∈ Bset, (r.val : ℤ)) - (∑ r' ∈ Aset, (r'.val : ℤ)) -
            (Bset.card : ℤ) * mf - (Aset.card : ℤ) * mg := by
          have h1 : ∑ r ∈ Bset, ((ir r : ℤ) - mf) =
              (∑ r ∈ Bset, ((σ (Fin.natAdd df r)).val : ℤ)) - (∑ r ∈ Bset, (r.val : ℤ)) -
                (Bset.card : ℤ) * mf := by
            have : ∀ r ∈ Bset, ((ir r : ℤ) - mf) = ((σ (Fin.natAdd df r)).val : ℤ) - r.val - mf :=
              fun r _ => by have h1 := (hbounds.2 r).1; dsimp [ir]; omega
            rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_const, nsmul_eq_mul]
          have h2 : ∑ r' ∈ Aset, ((jr r' : ℤ) - mg) =
              (∑ r' ∈ Aset, ((σ (Fin.castAdd dg r')).val : ℤ)) - (∑ r' ∈ Aset, (r'.val : ℤ)) -
                (Aset.card : ℤ) * mg := by
            have : ∀ r' ∈ Aset, ((jr r' : ℤ) - mg) =
                ((σ (Fin.castAdd dg r')).val : ℤ) - r'.val - mg :=
              fun r' _ => by have h1 := (hbounds.1 r').1; dsimp [jr]; omega
            rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_const, nsmul_eq_mul]
          have hsumZ : (∑ r' ∈ Aset, ((σ (Fin.castAdd dg r')).val : ℤ)) +
              (∑ r ∈ Bset, ((σ (Fin.natAdd df r)).val : ℤ)) = ∑ i ∈ Top, (i.val : ℤ) := by
            exact_mod_cast hsum_AB
          linarith only [h1, h2, hsumZ]
        have hexcess : (a : ℤ) * b ≤
            ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
          have hsq : (0 : ℤ) ≤ ((Aset.card : ℤ) - a) ^ 2 := sq_nonneg _
          have htopZ : 2 * (∑ i ∈ Top, (i.val : ℤ)) =
              ((a : ℤ) + b) * (2 * ((mf : ℤ) + mg) + ((a : ℤ) + b) - 1) := by
            have h2 : 1 ≤ 2 * (mf + mg) + (a + b) := by dsimp only [a, b]; omega
            zify [h2] at hsum_top
            exact hsum_top
          have hAZ : 2 * (∑ r' ∈ Aset, (r'.val : ℤ)) + (Aset.card : ℤ) * ((Aset.card : ℤ) + 1) ≤
              2 * (Aset.card : ℤ) * df := by exact_mod_cast hA_bound
          have hBZ : 2 * (∑ r ∈ Bset, (r.val : ℤ)) + (Bset.card : ℤ) * ((Bset.card : ℤ) + 1) ≤
              2 * (Bset.card : ℤ) * dg := by exact_mod_cast hB_bound
          have hklZ : (Aset.card : ℤ) + (Bset.card : ℤ) = (a : ℤ) + b := by exact_mod_cast hkl
          have hdfZ : (df : ℤ) = mf + a := by dsimp only [a]; omega
          have hdgZ : (dg : ℤ) = mg + b := by dsimp only [b]; omega
          nlinarith only [hsq, htopZ, hAZ, hBZ, hklZ, hdfZ, hdgZ, hAB_val, hge_AB]
        have hsub_ge : df * dg ≤ dg * mf + df * mg + a * b := by
          have hdfZ : (df : ℤ) = mf + a := by dsimp only [a]; omega
          have hdgZ : (dg : ℤ) = mg + b := by dsimp only [b]; omega
          zify
          nlinarith only [hdfZ, hdgZ]
        have hgoalZ : ((dg * mf + df * mg + (df - mf) * (dg - mg) - df * dg : ℕ) : ℤ) ≤
            ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) := by
          rw [Nat.cast_sub hsub_ge]
          push_cast at hZ_split hexcess ⊢
          dsimp only [a, b] at hexcess
          linarith only [hZ_split, hexcess]
        exact_mod_cast hgoalZ
      · have hprod0 : (df - mf) * (dg - mg) = 0 := by
          rcases not_and_or.mp hsmall with h1 | h2
          · rw [Nat.sub_eq_zero_of_le (not_lt.mp h1), zero_mul]
          · rw [Nat.sub_eq_zero_of_le (not_lt.mp h2), mul_zero]
        rw [hprod0, add_zero]
        have hnn : (0 : ℤ) ≤
            ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by positivity
        by_cases hsub : df * dg ≤ dg * mf + df * mg
        · have hgoalZ : ((dg * mf + df * mg - df * dg : ℕ) : ℤ) ≤
              ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) := by
            rw [Nat.cast_sub hsub]
            push_cast at hZ_split hnn ⊢
            linarith only [hZ_split, hnn]
          exact_mod_cast hgoalZ
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hsub)]; exact Nat.zero_le _
    exact (pow_dvd_pow t hexp).trans hdvd_prod

end SylvesterOrd

/-! ### Part 2: Bivariate Multiplicity & Shift Invariance on `BiPoly A = A[X][Y]` -/

/-- Bivariate polynomial ring `A[X][Y]`. -/
abbrev BiPoly (A : Type*) [CommRing A] := Polynomial (Polynomial A)

/-- First-order contact polynomial ring `A[X][Y₀][Y₁]`. -/
abbrev ContactPoly (A : Type*) [CommRing A] := Polynomial (BiPoly A)

section BivarOrd

variable {A : Type*} [CommRing A]

/-- Shifted bivariate polynomial `f(x₀ + s, y₀ + v)` in `A[s][v]`. -/
noncomputable def shiftBi (x0 y0 : A) (f : BiPoly A) : BiPoly A :=
  (f.map (Polynomial.compRingHom (C x0 + X))).comp (C (C y0) + X)

/-- Total 2D multiplicity at `(x₀, y₀)` is at least `m`: every `s^i v^j` with `i + j < m`
vanishes in `shiftBi x₀ y₀ f`. -/
def biMultGE (x0 y0 : A) (f : BiPoly A) (m : ℕ) : Prop :=
  ∀ i j, i + j < m → ((shiftBi x0 y0 f).coeff j).coeff i = 0

/-- Weighted `(s, V)`-order of `P(s, V) ∈ A[s][V]` (with `w(s) = 1`, `w(V) = w`) is at least `m`:
for every `j`, `s^(m - w * j) ∣ P.coeff j`. -/
def weightedOrdGE (w m : ℕ) (P : BiPoly A) : Prop :=
  ∀ j, X ^ (m - w * j) ∣ P.coeff j

theorem biMultGE_iff_weightedOrdGE_one (x0 y0 : A) (f : BiPoly A) (m : ℕ) :
    biMultGE x0 y0 f m ↔ weightedOrdGE 1 m (shiftBi x0 y0 f) := by
  constructor
  · intro h j
    rw [X_pow_dvd_iff]
    intro i hi
    exact h i j (by omega)
  · intro h i j hij
    have hd := (X_pow_dvd_iff).mp (h j)
    exact hd i (by omega)

theorem shiftBi_add (x0 y0 : A) (f g : BiPoly A) :
    shiftBi x0 y0 (f + g) = shiftBi x0 y0 f + shiftBi x0 y0 g := by
  unfold shiftBi; simp [Polynomial.map_add, add_comp]

theorem shiftBi_mul (x0 y0 : A) (f g : BiPoly A) :
    shiftBi x0 y0 (f * g) = shiftBi x0 y0 f * shiftBi x0 y0 g := by
  unfold shiftBi; simp [Polynomial.map_mul, mul_comp]

theorem shiftBi_C (x0 y0 : A) (p : Polynomial A) :
    shiftBi x0 y0 (C p) = C (p.comp (C x0 + X)) := by
  unfold shiftBi; simp [map_C, C_comp]

theorem shiftBi_X (x0 y0 : A) :
    shiftBi x0 y0 (X : BiPoly A) = C (C y0) + X := by
  unfold shiftBi; simp

theorem shiftBi_pow (x0 y0 : A) (f : BiPoly A) (n : ℕ) :
    shiftBi x0 y0 (f ^ n) = (shiftBi x0 y0 f) ^ n := by
  unfold shiftBi; simp [Polynomial.map_pow, pow_comp]

/-- Exact `resOrdExact` lower bound for `Res_Y(shiftBi f, shiftBi g)` from 2D multiplicities at
`(x₀, y₀)`. -/
theorem pow_dvd_resultant_of_biMultGE (x0 y0 : A) (f g : BiPoly A) (df mf dg mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg)
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg) :
    X ^ resOrdExact df mf dg mg ∣
      Polynomial.resultant (shiftBi x0 y0 f) (shiftBi x0 y0 g) df dg := by
  have h1 : weightedOrdGE 1 mf (shiftBi x0 y0 f) :=
    (biMultGE_iff_weightedOrdGE_one x0 y0 f mf).mp hf
  have h2 : weightedOrdGE 1 mg (shiftBi x0 y0 g) :=
    (biMultGE_iff_weightedOrdGE_one x0 y0 g mg).mp hg
  have hdeg1 : (shiftBi x0 y0 f).natDegree ≤ df := by
    unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have hmap : (f.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ df :=
      natDegree_map_le.trans hdegf
    have hX : (C (C y0) + X : BiPoly A).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [hmap, hX]
  have hdeg2 : (shiftBi x0 y0 g).natDegree ≤ dg := by
    unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have hmap : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg :=
      natDegree_map_le.trans hdegg
    have hX : (C (C y0) + X : BiPoly A).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [hmap, hX]
  exact pow_dvd_resultant_exact (X : Polynomial A) (shiftBi x0 y0 f) (shiftBi x0 y0 g)
    df mf dg mg hdeg1 hdeg2 (fun i => by simpa using h1 i) (fun j => by simpa using h2 j)

/-- Exact shift covariance of the `Y`-resultant under `(X, Y) ↦ (x₀ + X, y₀ + Y)`. -/
theorem resultant_shiftBi (x0 y0 : A) (f g : BiPoly A) (df dg : ℕ)
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg) :
    Polynomial.resultant (shiftBi x0 y0 f) (shiftBi x0 y0 g) df dg =
      (Polynomial.resultant f g df dg).comp (C x0 + X) := by
  unfold shiftBi
  let φ : Polynomial A →+* Polynomial A := Polynomial.compRingHom (C x0 + X)
  have hmap : Polynomial.resultant (f.map φ) (g.map φ) df dg =
      φ (Polynomial.resultant f g df dg) := Polynomial.resultant_map_map f g df dg φ
  have htrans : ∀ (p q : BiPoly A) (c : Polynomial A),
      p.natDegree ≤ df → q.natDegree ≤ dg →
      Polynomial.resultant (p.comp (C c + X)) (q.comp (C c + X)) df dg =
        Polynomial.resultant p q df dg := by
    intro p q c hp hq
    let M (k : ℕ) : Matrix (Fin k) (Fin k) (Polynomial A) :=
      Matrix.of fun i j =>
        if i.val ≤ j.val then ((Nat.choose j.val i.val : ℕ) : Polynomial A) * c ^ (j.val - i.val)
        else 0
    have hdetM : ∀ k, (M k).det = 1 := by
      intro k
      have htri : (M k).BlockTriangular id := by
        intro i j hij; dsimp [M]; rw [ite_eq_right (by change j.val < i.val at hij; omega)]
      rw [Matrix.det_of_isUpperTriangular htri]
      apply Finset.prod_eq_one; intro i _
      dsimp [M]; simp [Nat.choose_self]
    have hcomp_coeff : ∀ (k : ℕ) (h : BiPoly A), (∀ d ≥ k, h.coeff d = 0) →
        ∀ i : Fin k, (h.comp (C c + X)).coeff i.val = ∑ j : Fin k, M k i j * h.coeff j.val := by
      intro k h hh i
      have hsum : h = ∑ j : Fin k, monomial j.val (h.coeff j.val) := by
        apply Polynomial.ext; intro d; rw [finsetSum_coeff]
        by_cases hd : d < k
        · rw [Finset.sum_eq_single ⟨d, hd⟩]
          · simp
          · intro j _ hne
            have : j.val ≠ d := fun he => hne (Fin.ext he)
            simp [coeff_monomial, this]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · rw [hh d (by omega)]
          symm; apply Finset.sum_eq_zero; intro j _
          have : j.val ≠ d := by have := j.isLt; omega
          simp [coeff_monomial, this]
      conv_lhs => rw [hsum]
      rw [sum_comp, finsetSum_coeff]
      apply Finset.sum_congr rfl; intro j _
      rw [monomial_comp, coeff_C_mul, mul_comm]
      congr 1
      rw [add_comm, add_pow, finsetSum_coeff]
      dsimp [M]
      by_cases hij : i.val ≤ j.val
      · rw [ite_eq_left hij, Finset.sum_eq_single i.val]
        · rw [show X ^ i.val * C c ^ (j.val - i.val) * (Nat.choose j.val i.val : BiPoly A) =
              C (((Nat.choose j.val i.val : ℕ) : Polynomial A) * c ^ (j.val - i.val)) *
                X ^ i.val by
            rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
          rw [coeff_C_mul_X_pow, ite_eq_left rfl]
        · intro l _ hne
          rw [show X ^ l * C c ^ (j.val - l) * (Nat.choose j.val l : BiPoly A) =
              C (((Nat.choose j.val l : ℕ) : Polynomial A) * c ^ (j.val - l)) * X ^ l by
            rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
          rw [coeff_C_mul_X_pow, ite_eq_right hne.symm]
        · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · rw [ite_eq_right hij]
        apply Finset.sum_eq_zero; intro l hl
        have hne : l ≠ i.val := by have := Finset.mem_range.mp hl; omega
        rw [show X ^ l * C c ^ (j.val - l) * (Nat.choose j.val l : BiPoly A) =
            C (((Nat.choose j.val l : ℕ) : Polynomial A) * c ^ (j.val - l)) * X ^ l by
          rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
        rw [coeff_C_mul_X_pow, ite_eq_right hne.symm]
    let B : Matrix (Fin (df + dg)) (Fin (df + dg)) (Polynomial A) :=
      (Matrix.fromBlocks (M df) 0 0 (M dg)).reindex finSumFinEquiv finSumFinEquiv
    have hdetB : B.det = 1 := by
      change ((Matrix.fromBlocks (M df) 0 0 (M dg)).reindex finSumFinEquiv finSumFinEquiv).det = 1
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hdetM, hdetM, mul_one]
    have hSylMul : M (df + dg) * Polynomial.sylvester p q df dg =
        Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg * B := by
      apply Matrix.ext; intro i j
      have hcol_g : ∀ (r' : Fin df) (k : Fin (df + dg)),
          Polynomial.sylvester p q df dg k (Fin.castAdd dg r') = (X ^ r'.val * q).coeff k.val := by
        intro r' k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc,
          coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hcol_f : ∀ (r : Fin dg) (k : Fin (df + dg)),
          Polynomial.sylvester p q df dg k (Fin.natAdd df r) = (X ^ r.val * p).coeff k.val := by
        intro r k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc,
          coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hp_comp : (p.comp (C c + X)).natDegree ≤ df :=
        natDegree_comp_le.trans (by
          have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
            (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
          nlinarith only [hp, h1])
      have hq_comp : (q.comp (C c + X)).natDegree ≤ dg :=
        natDegree_comp_le.trans (by
          have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
            (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
          nlinarith only [hq, h1])
      have hcol_gc : ∀ (r' : Fin df) (k : Fin (df + dg)),
          Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg k (Fin.castAdd dg r') =
            (X ^ r'.val * q.comp (C c + X)).coeff k.val := by
        intro r' k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc,
          coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hcol_fc : ∀ (r : Fin dg) (k : Fin (df + dg)),
          Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg k (Fin.natAdd df r) =
            (X ^ r.val * p.comp (C c + X)).coeff k.val := by
        intro r k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc,
          coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      induction j using Fin.addCases with
      | left r' =>
        rw [Matrix.mul_apply, Matrix.mul_apply]
        have hLHS : (∑ k : Fin (df + dg),
            M (df + dg) i k * Polynomial.sylvester p q df dg k (Fin.castAdd dg r')) =
            ((X ^ r'.val * q).comp (C c + X)).coeff i.val := by
          simp_rw [hcol_g]
          symm; apply hcomp_coeff
          intro d hd
          exact coeff_eq_zero_of_natDegree_lt
            ((natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le r'.val) hq)).trans_lt
              (by have := r'.isLt; omega))
        have hRHS : (∑ k : Fin (df + dg),
            Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i k *
              B k (Fin.castAdd dg r')) =
            ∑ l : Fin df, (X ^ l.val * q.comp (C c + X)).coeff i.val * M df l r' := by
          rw [Fin.sum_univ_add]
          have h0 : (∑ l : Fin dg,
              Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i
                (Fin.natAdd df l) * B (Fin.natAdd df l) (Fin.castAdd dg r')) = 0 := by
            apply Finset.sum_eq_zero; intro l _
            simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
          rw [h0, add_zero]
          apply Finset.sum_congr rfl; intro l _
          rw [hcol_gc]
          simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
        rw [hLHS, hRHS, mul_comp, pow_comp, X_comp]
        have hpow_r : (C c + X : BiPoly A) ^ r'.val = ∑ l : Fin df, C (M df l r') * X ^ l.val := by
          apply Polynomial.ext; intro d; rw [finsetSum_coeff]
          have h := hcomp_coeff df (X ^ r'.val) (fun d' hd' => by
            rw [coeff_X_pow]; exact ite_eq_right (by have := r'.isLt; omega))
          by_cases hd : d < df
          · have hd' := h ⟨d, hd⟩
            rw [pow_comp, X_comp] at hd'
            rw [hd', Finset.sum_eq_single r']
            · simp only [coeff_X_pow, ↓reduceIte, mul_one]
              rw [Finset.sum_eq_single ⟨d, hd⟩]
              · simp
              · intro l _ hne; have : d ≠ l.val := fun he => hne (Fin.ext he.symm)
                simp [this]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro j _ hne; have : j.val ≠ r'.val := fun he => hne (Fin.ext he)
              simp [coeff_X_pow, this]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · have h0 : ((C c + X : BiPoly A) ^ r'.val).coeff d = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
                (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
              exact (natDegree_pow_le.trans (by nlinarith only [h1])).trans_lt
                (by have := r'.isLt; omega)
            rw [h0]; symm; apply Finset.sum_eq_zero; intro l _
            rw [coeff_C_mul_X_pow, ite_eq_right (by have := l.isLt; omega)]
        rw [hpow_r, Finset.sum_mul, finsetSum_coeff]
        apply Finset.sum_congr rfl; intro l _
        rw [mul_assoc, coeff_C_mul, mul_comm]
      | right r =>
        rw [Matrix.mul_apply, Matrix.mul_apply]
        have hLHS : (∑ k : Fin (df + dg),
            M (df + dg) i k * Polynomial.sylvester p q df dg k (Fin.natAdd df r)) =
            ((X ^ r.val * p).comp (C c + X)).coeff i.val := by
          simp_rw [hcol_f]
          symm; apply hcomp_coeff
          intro d hd
          exact coeff_eq_zero_of_natDegree_lt
            ((natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le r.val) hp)).trans_lt
              (by have := r.isLt; omega))
        have hRHS : (∑ k : Fin (df + dg),
            Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i k *
              B k (Fin.natAdd df r)) =
            ∑ l : Fin dg, (X ^ l.val * p.comp (C c + X)).coeff i.val * M dg l r := by
          rw [Fin.sum_univ_add]
          have h0 : (∑ l : Fin df,
              Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i
                (Fin.castAdd dg l) * B (Fin.castAdd dg l) (Fin.natAdd df r)) = 0 := by
            apply Finset.sum_eq_zero; intro l _
            simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
          rw [h0, zero_add]
          apply Finset.sum_congr rfl; intro l _
          rw [hcol_fc]
          simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
        rw [hLHS, hRHS, mul_comp, pow_comp, X_comp]
        have hpow_r : (C c + X : BiPoly A) ^ r.val = ∑ l : Fin dg, C (M dg l r) * X ^ l.val := by
          apply Polynomial.ext; intro d; rw [finsetSum_coeff]
          have h := hcomp_coeff dg (X ^ r.val) (fun d' hd' => by
            rw [coeff_X_pow]; exact ite_eq_right (by have := r.isLt; omega))
          by_cases hd : d < dg
          · have hd' := h ⟨d, hd⟩
            rw [pow_comp, X_comp] at hd'
            rw [hd', Finset.sum_eq_single r]
            · simp only [coeff_X_pow, ↓reduceIte, mul_one]
              rw [Finset.sum_eq_single ⟨d, hd⟩]
              · simp
              · intro l _ hne; have : d ≠ l.val := fun he => hne (Fin.ext he.symm)
                simp [this]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro j _ hne; have : j.val ≠ r.val := fun he => hne (Fin.ext he)
              simp [coeff_X_pow, this]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · have h0 : ((C c + X : BiPoly A) ^ r.val).coeff d = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
                (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
              exact (natDegree_pow_le.trans (by nlinarith only [h1])).trans_lt
                (by have := r.isLt; omega)
            rw [h0]; symm; apply Finset.sum_eq_zero; intro l _
            rw [coeff_C_mul_X_pow, ite_eq_right (by have := l.isLt; omega)]
        rw [hpow_r, Finset.sum_mul, finsetSum_coeff]
        apply Finset.sum_congr rfl; intro l _
        rw [mul_assoc, coeff_C_mul, mul_comm]
    have hdet := congrArg Matrix.det hSylMul
    rw [Matrix.det_mul, Matrix.det_mul, hdetM, hdetB, one_mul, mul_one] at hdet
    exact hdet.symm
  have h1 := htrans (f.map φ) (g.map φ) (C y0)
    (natDegree_map_le.trans hdegf) (natDegree_map_le.trans hdegg)
  rw [h1, hmap]
  rfl

/-- Direct `(X - C x₀)`-power divisibility of `Polynomial.resultant f g df dg` from 2D
multiplicities `mf, mg` at `(x₀, y₀)`. -/
theorem X_sub_C_pow_dvd_resultant_of_biMultGE (x0 y0 : A) (f g : BiPoly A) (df mf dg mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg)
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg) :
    (X - C x0) ^ resOrdExact df mf dg mg ∣ Polynomial.resultant f g df dg := by
  have hdvd := pow_dvd_resultant_of_biMultGE x0 y0 f g df mf dg mg hf hg hdegf hdegg
  rw [resultant_shiftBi x0 y0 f g df dg hdegf hdegg] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q.comp (X - C x0), ?_⟩
  have hcomp := congrArg (fun p : Polynomial A => p.comp (X - C x0)) hq
  simp only [mul_comp, pow_comp, X_comp, Polynomial.comp_assoc, add_comp, C_comp] at hcomp
  have hid : (C x0 + (X - C x0) : Polynomial A) = X := by ring
  rw [hid, Polynomial.comp_X] at hcomp
  exact hcomp

/-- Over a field `K`, distinct sites `x : ι → K` with 2D multiplicities `mf i, mg i` of `f, g` at
`(x i, y i)` satisfy `∑ i, resOrdExact df (mf i) dg (mg i) ≤ (resultant f g df dg).natDegree`
whenever `Polynomial.resultant f g df dg ≠ 0`. Directly feeds the `Res_{Y₀}(A, B)` LP! -/
theorem sum_resOrdExact_le_natDegree_resultant {K ι : Type*} [Field K] [Fintype ι]
    (x y : ι → K) (hx : Function.Injective x)
    (f g : BiPoly K) (df dg : ℕ) (mf mg : ι → ℕ)
    (hf : ∀ i, biMultGE (x i) (y i) f (mf i))
    (hg : ∀ i, biMultGE (x i) (y i) g (mg i))
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg)
    (hres : Polynomial.resultant f g df dg ≠ 0) :
    ∑ i : ι, resOrdExact df (mf i) dg (mg i) ≤ (Polynomial.resultant f g df dg).natDegree := by
  classical
  have hprod_dvd :
      (∏ i : ι, (X - C (x i)) ^ resOrdExact df (mf i) dg (mg i)) ∣
        Polynomial.resultant f g df dg := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      have hne : x i ≠ x j := fun h => hij (hx h)
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit).pow
    · intro i _
      exact X_sub_C_pow_dvd_resultant_of_biMultGE (x i) (y i) f g df (mf i) dg (mg i)
        (hf i) (hg i) hdegf hdegg
  have hdeg_le := Polynomial.natDegree_le_of_dvd hprod_dvd hres
  have hprod_deg : (∏ i : ι, (X - C (x i)) ^ resOrdExact df (mf i) dg (mg i)).natDegree =
      ∑ i : ι, resOrdExact df (mf i) dg (mg i) := by
    rw [Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero (x i)))]
    apply Finset.sum_congr rfl; intro i _
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  omega

end BivarOrd

/-! ### Part 3: Zero-`τ` Contact Resultant Elimination on `ContactPoly A = A[X][Y₀][Y₁]` -/

section WeightedSupportDeg

variable {A : Type*} [CommRing A]

/-- Weighted support degree of a bivariate polynomial `p ∈ A[X][Y]` with `wt(X) = 1`, `wt(Y) = wY`:
`sup_{j ∈ p.support} ((p.coeff j).natDegree + wY * j)`. -/
noncomputable def biWeightedDeg (p : BiPoly A) (wY : ℕ) : ℕ :=
  p.support.sup fun j => (p.coeff j).natDegree + wY * j

/-- Weighted support degree of a contact polynomial `Q ∈ A[X][Y₀][Y₁]` with
`wt(X) = 1`, `wt(Y₀) = wY`, `wt(Y₁) = wY - 1`. -/
noncomputable def contactWDeg (wY : ℕ) (Q : ContactPoly A) : ℕ :=
  Q.support.sup fun k => biWeightedDeg (Q.coeff k) wY + k * (wY - 1)

theorem biWeightedDeg_zero (wY : ℕ) : biWeightedDeg (0 : BiPoly A) wY = 0 := by
  simp [biWeightedDeg]

theorem biWeightedDeg_one (wY : ℕ) : biWeightedDeg (1 : BiPoly A) wY = 0 := by
  classical
  apply Nat.le_zero.mp
  unfold biWeightedDeg
  apply Finset.sup_le; intro j hj
  have hj0 : j = 0 := by
    by_contra hne
    have : (1 : BiPoly A).coeff j = 0 := by simp [coeff_one, hne]
    exact (Polynomial.mem_support_iff.mp hj) this
  subst hj0; simp

theorem biWeightedDeg_neg (p : BiPoly A) (wY : ℕ) :
    biWeightedDeg (-p) wY = biWeightedDeg p wY := by
  unfold biWeightedDeg
  rw [Polynomial.support_neg]
  apply Finset.sup_congr rfl; intro j _
  simp [Polynomial.coeff_neg, Polynomial.natDegree_neg]

theorem coeffWeight_le_biWeightedDeg (p : BiPoly A) (wY j : ℕ) (hj : p.coeff j ≠ 0) :
    (p.coeff j).natDegree + wY * j ≤ biWeightedDeg p wY :=
  Finset.le_sup (f := fun j => (p.coeff j).natDegree + wY * j) (Polynomial.mem_support_iff.mpr hj)

theorem biWeightedDeg_add_le (p q : BiPoly A) (wY : ℕ) :
    biWeightedDeg (p + q) wY ≤ max (biWeightedDeg p wY) (biWeightedDeg q wY) := by
  classical
  conv_lhs => unfold biWeightedDeg
  apply Finset.sup_le; intro j hj
  have hnz : p.coeff j + q.coeff j ≠ 0 := by
    rw [← Polynomial.coeff_add]; exact Polynomial.mem_support_iff.mp hj
  rw [Polynomial.coeff_add]
  by_cases hp : p.coeff j = 0
  · rw [hp, zero_add]
    have hq : q.coeff j ≠ 0 := by simpa [hp] using hnz
    exact (coeffWeight_le_biWeightedDeg q wY j hq).trans (le_max_right _ _)
  · by_cases hq : q.coeff j = 0
    · rw [hq, add_zero]
      exact (coeffWeight_le_biWeightedDeg p wY j hp).trans (le_max_left _ _)
    · have hadd : (p.coeff j + q.coeff j).natDegree ≤
          max (p.coeff j).natDegree (q.coeff j).natDegree := Polynomial.natDegree_add_le _ _
      have hp' := coeffWeight_le_biWeightedDeg p wY j hp
      have hq' := coeffWeight_le_biWeightedDeg q wY j hq
      omega

theorem biWeightedDeg_zsmul_le (u : ℤˣ) (p : BiPoly A) (wY : ℕ) :
    biWeightedDeg (u • p) wY ≤ biWeightedDeg p wY := by
  rw [Units.smul_def]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [biWeightedDeg_neg]

theorem biWeightedDeg_sum_le {α : Type*} (S : Finset α) (f : α → BiPoly A) (wY B : ℕ)
    (hf : ∀ x ∈ S, biWeightedDeg (f x) wY ≤ B) :
    biWeightedDeg (∑ x ∈ S, f x) wY ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [biWeightedDeg_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (biWeightedDeg_add_le _ _ wY).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem biWeightedDeg_mul_le (p q : BiPoly A) (wY : ℕ) :
    biWeightedDeg (p * q) wY ≤ biWeightedDeg p wY + biWeightedDeg q wY := by
  classical
  conv_lhs => unfold biWeightedDeg
  apply Finset.sup_le; intro j hj
  rw [Polynomial.mem_support_iff, Polynomial.coeff_mul] at hj
  obtain ⟨x0, hx0, hne0⟩ : ∃ x ∈ Finset.antidiagonal j, p.coeff x.1 * q.coeff x.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (Finset.sum_eq_zero h)
  have hw_le : wY * j ≤ biWeightedDeg p wY + biWeightedDeg q wY := by
    have h1 := coeffWeight_le_biWeightedDeg p wY x0.1 (left_ne_zero_of_mul hne0)
    have h2 := coeffWeight_le_biWeightedDeg q wY x0.2 (right_ne_zero_of_mul hne0)
    have hsum : x0.1 + x0.2 = j := Finset.mem_antidiagonal.mp hx0
    have hw : wY * j = wY * x0.1 + wY * x0.2 := by rw [← hsum, Nat.mul_add]
    omega
  rw [Polynomial.coeff_mul]
  have hdeg : (∑ x ∈ Finset.antidiagonal j, p.coeff x.1 * q.coeff x.2).natDegree ≤
      biWeightedDeg p wY + biWeightedDeg q wY - wY * j := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro x hx
    by_cases h0 : p.coeff x.1 * q.coeff x.2 = 0
    · simp [h0]
    · have h1 := coeffWeight_le_biWeightedDeg p wY x.1 (left_ne_zero_of_mul h0)
      have h2 := coeffWeight_le_biWeightedDeg q wY x.2 (right_ne_zero_of_mul h0)
      have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
      have hw : wY * j = wY * x.1 + wY * x.2 := by rw [← hsum, Nat.mul_add]
      have hmul := Polynomial.natDegree_mul_le (p := p.coeff x.1) (q := q.coeff x.2)
      omega
  omega

theorem biWeightedDeg_prod_le {α : Type*} (S : Finset α) (f : α → BiPoly A) (wY : ℕ) :
    biWeightedDeg (∏ x ∈ S, f x) wY ≤ ∑ x ∈ S, biWeightedDeg (f x) wY := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [biWeightedDeg_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (biWeightedDeg_mul_le _ _ wY).trans (Nat.add_le_add_left ih _)

theorem biWeightedDeg_coeff_add_le_of_contactWDeg (Q : ContactPoly A) (wY W k : ℕ)
    (hw : contactWDeg wY Q ≤ W) (hk : Q.coeff k ≠ 0) :
    biWeightedDeg (Q.coeff k) wY + k * (wY - 1) ≤ W :=
  (Finset.le_sup (f := fun k => biWeightedDeg (Q.coeff k) wY + k * (wY - 1))
    (Polynomial.mem_support_iff.mpr hk)).trans hw

/-- **Weighted Support Degree Descent under `Y₁`-Resultant:**
`biWeightedDeg (resultant F G d s) wY ≤ d * W + s * (W_F - d * (wY - 1))`. -/
theorem biWeightedDeg_resultant_le (Fpoly Gpoly : ContactPoly A)
    (wY W_F W d s : ℕ)
    (hFw : contactWDeg wY Fpoly ≤ W_F) (hGw : contactWDeg wY Gpoly ≤ W)
    (hWF_ge : d * (wY - 1) ≤ W_F) :
    biWeightedDeg (Polynomial.resultant Fpoly Gpoly d s) wY ≤
      d * W + s * (W_F - d * (wY - 1)) := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply biWeightedDeg_sum_le
  intro σ _
  refine (biWeightedDeg_zsmul_le _ _ wY).trans ?_
  by_cases hzero : ∃ j : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0, biWeightedDeg_zero]; exact Nat.zero_le _
  · push Not at hzero
    let jr : Fin d → ℕ := fun r' => (σ (Fin.castAdd s r')).val - r'.val
    let ir : Fin s → ℕ := fun r => (σ (Fin.natAdd d r)).val - r.val
    have hbounds :
      (∀ r' : Fin d, r'.val ≤ (σ (Fin.castAdd s r')).val ∧
        (σ (Fin.castAdd s r')).val ≤ r'.val + s ∧
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.castAdd s r')) (Fin.castAdd s r') =
          Gpoly.coeff (jr r')) ∧
      (∀ r : Fin s, r.val ≤ (σ (Fin.natAdd d r)).val ∧
        (σ (Fin.natAdd d r)).val ≤ r.val + d ∧
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.natAdd d r)) (Fin.natAdd d r) =
          Fpoly.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd s r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd d r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin s, ir r) + (∑ r' : Fin d, jr r') = d * s := by
      have hperm_sum : ∑ k : Fin (d + s), (σ k).val = ∑ k : Fin (d + s), k.val :=
        Equiv.sum_comp σ (fun k : Fin (d + s) => k.val)
      have hsplit_σ : ∑ k : Fin (d + s), (σ k).val =
          (∑ r' : Fin d, (σ (Fin.castAdd s r')).val) +
          (∑ r : Fin s, (σ (Fin.natAdd d r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (d + s), k.val =
          (∑ r' : Fin d, r'.val) + (∑ r : Fin s, (d + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin d, jr r') + (∑ r' : Fin d, r'.val) =
          ∑ r' : Fin d, (σ (Fin.castAdd s r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin s, ir r) + (∑ r : Fin s, r.val) =
          ∑ r : Fin s, (σ (Fin.natAdd d r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin s, (d + r.val) = s * d + ∑ r : Fin s, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
      have hcomm : s * d = d * s := mul_comm s d
      omega
    have hprod_le : biWeightedDeg
          (∏ j : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ j) j) wY ≤
        (∑ r' : Fin d, biWeightedDeg (Gpoly.coeff (jr r')) wY) +
        (∑ r : Fin s, biWeightedDeg (Fpoly.coeff (ir r)) wY) := by
      rw [Fin.prod_univ_add]
      refine (biWeightedDeg_mul_le _ _ wY).trans ?_
      apply Nat.add_le_add
      · refine (biWeightedDeg_prod_le _ _ wY).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r' _; rw [(hbounds.1 r').2.2]
      · refine (biWeightedDeg_prod_le _ _ wY).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r _; rw [(hbounds.2 r).2.2]
    have hsumG : (∑ r' : Fin d, biWeightedDeg (Gpoly.coeff (jr r')) wY) +
        (∑ r' : Fin d, jr r') * (wY - 1) ≤ d * W := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc _ ≤ ∑ _r' : Fin d, W := Finset.sum_le_sum fun r' _ => by
            have hne : Gpoly.coeff (jr r') ≠ 0 := by
              rw [← (hbounds.1 r').2.2]; exact hzero (Fin.castAdd s r')
            exact biWeightedDeg_coeff_add_le_of_contactWDeg Gpoly wY W (jr r') hGw hne
        _ = d * W := by simp
    have hsumF : (∑ r : Fin s, biWeightedDeg (Fpoly.coeff (ir r)) wY) +
        (∑ r : Fin s, ir r) * (wY - 1) ≤ s * W_F := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc _ ≤ ∑ _r : Fin s, W_F := Finset.sum_le_sum fun r _ => by
            have hne : Fpoly.coeff (ir r) ≠ 0 := by
              rw [← (hbounds.2 r).2.2]; exact hzero (Fin.natAdd d r)
            exact biWeightedDeg_coeff_add_le_of_contactWDeg Fpoly wY W_F (ir r) hFw hne
        _ = s * W_F := by simp
    have hmul_sub : s * (W_F - d * (wY - 1)) + d * s * (wY - 1) = s * W_F := by
      have h1 : s * (W_F - d * (wY - 1)) = s * W_F - s * (d * (wY - 1)) :=
        Nat.mul_sub_left_distrib s _ _
      have h2 : s * (d * (wY - 1)) ≤ s * W_F := Nat.mul_le_mul_left s hWF_ge
      have h3 : d * s * (wY - 1) = s * (d * (wY - 1)) := by ring
      omega
    have htot_wt : ((∑ r : Fin s, ir r) + (∑ r' : Fin d, jr r')) * (wY - 1) = d * s * (wY - 1) := by
      rw [hsum]
    rw [Nat.add_mul] at htot_wt
    omega

/-- Any bivariate polynomial `Φ` satisfies `Φ.natDegree ≤ biWeightedDeg Φ wY / wY` for `wY > 0`. -/
theorem natDegree_le_biWeightedDeg_div (Φ : BiPoly A) (wY : ℕ) (hwY : 0 < wY) :
    Φ.natDegree ≤ biWeightedDeg Φ wY / wY := by
  by_cases hΦ : Φ = 0
  · simp [hΦ]
  · have hlead : Φ.coeff Φ.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hΦ
    have hw := coeffWeight_le_biWeightedDeg Φ wY Φ.natDegree hlead
    rw [Nat.le_div_iff_mul_le hwY]
    have : Φ.natDegree * wY = wY * Φ.natDegree := Nat.mul_comm _ _
    omega

end WeightedSupportDeg

/-! ### Part 4: Non-Vanishing, `Z`-Degree Bound, Evaluation, and `O(1)` Root Cap -/

section ContactResultant

variable {F : Type*} [Field F]

/-- Evaluate `Φ ∈ BiPoly F = F[X][Y₀]` at `Y₀ = P ∈ F[X]`. -/
noncomputable def evalBiHom (P : Polynomial F) : BiPoly F →+* Polynomial F :=
  Polynomial.evalRingHom P

/-- Evaluate `H ∈ ContactPoly F = F[X][Y₀][Y₁]` at `(Y₀, Y₁) = (P, P')`. -/
noncomputable def evalContact (H : ContactPoly F) (P : Polynomial F) : Polynomial F :=
  (H.map (evalBiHom P)).eval P.derivative

/-- Specialize the `Z` variable of `Φ ∈ BiPoly (F[Z])` at `z ∈ F`. -/
noncomputable def specializeZ (z : F) : BiPoly (Polynomial F) →+* BiPoly F :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z))

/-- Specialize the `Z` variable of `H ∈ ContactPoly (F[Z])` at `z ∈ F`. -/
noncomputable def evalZContact (z : F) : ContactPoly (Polynomial F) →+* ContactPoly F :=
  Polynomial.mapRingHom (specializeZ z)

/-- Evaluate `Φ ∈ BiPoly (F[Z])` at `(Z, Y₀) = (z, P)`. -/
noncomputable def triEvalHom (z : F) (P : Polynomial F) : BiPoly (Polynomial F) →+* Polynomial F :=
  (evalBiHom P).comp (specializeZ z)

/-- Lift `BiPoly (F[Z]) →+* BiPoly (RatFunc F)` coefficientwise along `F[Z] ↪ F(Z)`. -/
noncomputable def liftBiRat : BiPoly (Polynomial F) →+* BiPoly (RatFunc F) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))

/-- Lift `ContactPoly (F[Z]) →+* ContactPoly (RatFunc F)`. -/
noncomputable def liftCRat : ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F) :=
  Polynomial.mapRingHom (liftBiRat (F := F))

theorem liftBiRat_injective : Function.Injective (liftBiRat (F := F)) :=
  Polynomial.map_injective _ (Polynomial.map_injective _
    (IsFractionRing.injective (Polynomial F) (RatFunc F)))

theorem liftCRat_injective : Function.Injective (liftCRat (F := F)) :=
  Polynomial.map_injective _ (liftBiRat_injective (F := F))

/-- **Scalar Non-Vanishing Theorem (over any field `F`):**
If `Fpoly, Gpoly : ContactPoly F` satisfy `Irreducible Fpoly`, `Fpoly.natDegree = d ≥ 1`,
`Gpoly.natDegree ≤ s`, and `¬ Fpoly ∣ Gpoly`, then `Polynomial.resultant Fpoly Gpoly d s ≠ 0`. -/
theorem resultant_ne_zero_of_not_dvd_scalar
    (Fpoly Gpoly : ContactPoly F) (d s : ℕ)
    (hirr : Irreducible Fpoly) (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s) (hndvd : ¬ Fpoly ∣ Gpoly) :
    Polynomial.resultant Fpoly Gpoly d s ≠ 0 := by
  classical
  let A := BiPoly F
  let K := FractionRing A
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hprim : Fpoly.IsPrimitive := hirr.isPrimitive (by rw [hFd]; omega)
  let FK : K[X] := Fpoly.map (algebraMap A K)
  let GK : K[X] := Gpoly.map (algebraMap A K)
  have hirrK : Irreducible FK := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hndvdK : ¬ FK ∣ GK := fun h => hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
  have hcop : IsCoprime FK GK := by
    let g := EuclideanDomain.gcd FK GK
    have hg_u : IsUnit g := by
      rcases EuclideanDomain.gcd_dvd_left FK GK with ⟨v, hv⟩
      rcases hirrK.isUnit_or_isUnit hv with hu | hu
      · exact hu
      · exfalso; apply hndvdK
        rcases EuclideanDomain.gcd_dvd_right FK GK with ⟨w, hw⟩
        obtain ⟨u, rfl⟩ := hu
        exact ⟨(u⁻¹ : K[X]ˣ) * w, by
          calc GK = g * w := hw
            _ = (g * ↑u) * (↑u⁻¹ * w) := by rw [mul_assoc, Units.mul_inv_cancel_left]
            _ = FK * (↑u⁻¹ * w) := by rw [← hv]⟩
    obtain ⟨u, hu⟩ := hg_u
    refine ⟨EuclideanDomain.gcdA FK GK * (u⁻¹ : K[X]ˣ),
      EuclideanDomain.gcdB FK GK * (u⁻¹ : K[X]ˣ), ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab FK GK
    change g = _ at hbez
    rw [← hu] at hbez
    calc EuclideanDomain.gcdA FK GK * ↑u⁻¹ * FK + EuclideanDomain.gcdB FK GK * ↑u⁻¹ * GK
        = (FK * EuclideanDomain.gcdA FK GK + GK * EuclideanDomain.gcdB FK GK) * ↑u⁻¹ := by ring
      _ = ↑u * ↑u⁻¹ := by rw [← hbez]
      _ = 1 := Units.mul_inv u
  have hresK_std : FK.resultant GK ≠ 0 := Polynomial.resultant_ne_zero FK GK hcop
  have hFKdeg : FK.natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective hinjAK, hFd]
  have hGKdeg_le : GK.natDegree ≤ s := by
    rw [Polynomial.natDegree_map_eq_of_injective hinjAK]; exact hGd
  have hFK_lead : FK.coeff d ≠ 0 := by
    rw [← hFKdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hirrK.ne_zero
  have hresK : FK.resultant GK d s ≠ 0 := by
    have hs_eq : GK.natDegree + (s - GK.natDegree) = s := Nat.add_sub_of_le hGKdeg_le
    rw [← hs_eq, Polynomial.resultant_add_right_deg]
    · refine mul_ne_zero (pow_ne_zero _ hFK_lead) ?_
      rw [← hFKdeg]
      exact hresK_std
    · exact le_rfl
  intro h0
  apply hresK
  have hmap := Polynomial.resultant_map_map Fpoly Gpoly d s (algebraMap A K)
  rw [h0, map_zero] at hmap
  exact hmap

/-- **Parametric Non-Vanishing Theorem (`ContactPoly (F[Z])`, any field `F`):**
If `Irreducible (liftCRat Fpoly)`, `Fpoly.natDegree = d ≥ 1`, `Gpoly.natDegree ≤ s`, and
`¬ liftCRat Fpoly ∣ liftCRat Gpoly`, then `Polynomial.resultant Fpoly Gpoly d s ≠ 0`. -/
theorem resultant_ne_zero_of_not_dvd
    (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s : ℕ)
    (hirr : Irreducible (liftCRat Fpoly))
    (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s)
    (hndvd : ¬ liftCRat Fpoly ∣ liftCRat Gpoly) :
    Polynomial.resultant Fpoly Gpoly d s ≠ 0 := by
  have hFd' : (liftCRat Fpoly).natDegree = d := by
    rw [show liftCRat Fpoly = Fpoly.map liftBiRat from rfl,
      Polynomial.natDegree_map_eq_of_injective liftBiRat_injective, hFd]
  have hGd' : (liftCRat Gpoly).natDegree ≤ s := by
    rw [show liftCRat Gpoly = Gpoly.map liftBiRat from rfl,
      Polynomial.natDegree_map_eq_of_injective liftBiRat_injective]
    exact hGd
  have hne := resultant_ne_zero_of_not_dvd_scalar (liftCRat Fpoly) (liftCRat Gpoly) d s
    hirr hFd' hd hGd' hndvd
  intro h0
  apply hne
  have hmap := Polynomial.resultant_map_map Fpoly Gpoly d s (liftBiRat (F := F))
  rw [h0, map_zero] at hmap
  exact hmap

/-- Every coefficient `((Q.coeff j).coeff a)` in `F[Z]` has `natDegree ≤ D`. -/
def DegZLe (Q : BiPoly (Polynomial F)) (D : ℕ) : Prop :=
  ∀ j a, ((Q.coeff j).coeff a).natDegree ≤ D

private lemma degZLe_zero (D : ℕ) : DegZLe (F := F) 0 D := by
  intro j a; simp

private lemma degZLe_one : DegZLe (F := F) 1 0 := by
  intro j a
  by_cases hj : j = 0
  · subst hj; by_cases ha : a = 0
    · subst ha; simp
    · simp [Polynomial.coeff_one, ha]
  · simp [Polynomial.coeff_one, hj]

private lemma degZLe_add {P Q : BiPoly (Polynomial F)} {D : ℕ}
    (hP : DegZLe P D) (hQ : DegZLe Q D) : DegZLe (P + Q) D := by
  intro j a
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP j a) (hQ j a))

private lemma degZLe_neg {P : BiPoly (Polynomial F)} {D : ℕ} (hP : DegZLe P D) :
    DegZLe (-P) D := by
  intro j a
  rw [Polynomial.coeff_neg, Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hP j a

private lemma degZLe_zsmul (u : ℤˣ) {P : BiPoly (Polynomial F)} {D : ℕ} (hP : DegZLe P D) :
    DegZLe (u • P) D := by
  rw [Units.smul_def]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hP
  · rw [Units.val_neg, Units.val_one, neg_one_zsmul]
    exact degZLe_neg hP

private lemma degZLe_sum {α : Type*} (S : Finset α) (f : α → BiPoly (Polynomial F)) (D : ℕ)
    (hf : ∀ x ∈ S, DegZLe (f x) D) : DegZLe (∑ x ∈ S, f x) D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [degZLe_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact degZLe_add (hf a (Finset.mem_insert_self a s))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

private lemma degZLe_mul {P Q : BiPoly (Polynomial F)} {D1 D2 : ℕ}
    (hP : DegZLe P D1) (hQ : DegZLe Q D2) : DegZLe (P * Q) (D1 + D2) := by
  intro j a
  rw [Polynomial.coeff_mul, finsetSum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun xy _ => ?_)
  dsimp only [Function.comp_apply]
  rw [Polynomial.coeff_mul]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun uv _ => ?_)
  dsimp only [Function.comp_apply]
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP xy.1 uv.1) (hQ xy.2 uv.2))

private lemma degZLe_prod_const {α : Type*} (S : Finset α) (f : α → BiPoly (Polynomial F))
    (D : ℕ) (hf : ∀ x ∈ S, DegZLe (f x) D) : DegZLe (∏ x ∈ S, f x) (S.card * D) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using degZLe_one (F := F)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm]
    exact degZLe_mul (hf a (Finset.mem_insert_self a s))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

/-- **Parametric `Z`-Degree Bound:**
`deg_Z(Res_{Y₁}(F, G)) ≤ d * D_Z' + s * D_ZF`. -/
theorem degZ_resultant_le (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s D_ZF D_Z' : ℕ)
    (hFZ : ∀ k j a, (((Fpoly.coeff k).coeff j).coeff a).natDegree ≤ D_ZF)
    (hGZ : ∀ k j a, (((Gpoly.coeff k).coeff j).coeff a).natDegree ≤ D_Z') :
    ∀ j a, (((Polynomial.resultant Fpoly Gpoly d s).coeff j).coeff a).natDegree ≤
      d * D_Z' + s * D_ZF := by
  classical
  change DegZLe (Polynomial.resultant Fpoly Gpoly d s) (d * D_Z' + s * D_ZF)
  rw [Polynomial.resultant, Matrix.det_apply]
  apply degZLe_sum
  intro σ _
  apply degZLe_zsmul
  rw [Fin.prod_univ_add]
  apply degZLe_mul
  · have hprod := degZLe_prod_const (Finset.univ : Finset (Fin d))
      (fun r' : Fin d =>
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.castAdd s r')) (Fin.castAdd s r')) D_Z'
      (fun r' _ => by
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc]
        split_ifs
        · exact hGZ _
        · exact degZLe_zero D_Z')
    simpa only [Finset.card_univ, Fintype.card_fin] using hprod
  · have hprod := degZLe_prod_const (Finset.univ : Finset (Fin s))
      (fun r : Fin s =>
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.natAdd d r)) (Fin.natAdd d r)) D_ZF
      (fun r _ => by
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc]
        split_ifs
        · exact hFZ _
        · exact degZLe_zero D_ZF)
    simpa only [Finset.card_univ, Fintype.card_fin] using hprod

/-- **Common Contact-Root Vanishing (Scalar):**
If `evalContact Fpoly P = 0` and `evalContact Gpoly P = 0`, then
`evalBiHom P (Polynomial.resultant Fpoly Gpoly d s) = 0`. -/
theorem evalBi_resultant_eq_zero (Fpoly Gpoly : ContactPoly F) (d s : ℕ)
    (hFd : Fpoly.natDegree ≤ d) (hGd : Gpoly.natDegree ≤ s) (hpos : 0 < d + s)
    (P : Polynomial F)
    (hFvan : evalContact Fpoly P = 0) (hGvan : evalContact Gpoly P = 0) :
    evalBiHom P (Polynomial.resultant Fpoly Gpoly d s) = 0 := by
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let χ : BiPoly F →+* RatFunc F := ψ.comp (evalBiHom P)
  have hFmap : (Fpoly.map χ).eval (ψ P.derivative) = 0 := by
    dsimp only [χ]
    rw [← Polynomial.map_map, Polynomial.eval_map_apply]
    change ψ (evalContact Fpoly P) = 0
    rw [hFvan, map_zero]
  have hGmap : (Gpoly.map χ).eval (ψ P.derivative) = 0 := by
    dsimp only [χ]
    rw [← Polynomial.map_map, Polynomial.eval_map_apply]
    change ψ (evalContact Gpoly P) = 0
    rw [hGvan, map_zero]
  have hres0 : Polynomial.resultant (Fpoly.map χ) (Gpoly.map χ) d s = 0 := by
    have hPdeg : (Fpoly.map χ).natDegree ≤ d := Polynomial.natDegree_map_le.trans hFd
    have hHdeg : (Gpoly.map χ).natDegree ≤ s := Polynomial.natDegree_map_le.trans hGd
    by_cases hne : Fpoly.map χ ≠ 0 ∨ Gpoly.map χ ≠ 0
    · have hstd : Polynomial.resultant (Fpoly.map χ) (Gpoly.map χ) = 0 := by
        rw [Polynomial.resultant_eq_zero_iff]
        refine ⟨hne, ?_⟩
        rintro ⟨a, b, hab⟩
        have heval := congrArg (fun q : (RatFunc F)[X] => q.eval (ψ P.derivative)) hab
        simp [Polynomial.eval_add, Polynomial.eval_mul, hFmap, hGmap] at heval
      have hm : (Fpoly.map χ).natDegree + (d - (Fpoly.map χ).natDegree) = d :=
        Nat.add_sub_of_le hPdeg
      have hn : (Gpoly.map χ).natDegree + (s - (Gpoly.map χ).natDegree) = s :=
        Nat.add_sub_of_le hHdeg
      rw [← hm, ← hn, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
        Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
      simp [hstd]
    · push Not at hne
      rcases hne with ⟨h0F, h0G⟩
      rw [h0F, h0G]
      rcases d with _ | d' <;> rcases s with _ | s' <;> simp_all
  have hcomm := Polynomial.resultant_map_map Fpoly Gpoly d s χ
  rw [hres0] at hcomm
  have hψ : ψ (evalBiHom P (Polynomial.resultant Fpoly Gpoly d s)) = 0 := hcomm.symm
  exact (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by rw [map_zero]; exact hψ)

/-- **Common Contact-Root Vanishing (Parametric `F[Z]`):**
If `evalContact (evalZContact z Fpoly) P = 0` and `evalContact (evalZContact z Gpoly) P = 0`, then
`triEvalHom z P (Polynomial.resultant Fpoly Gpoly d s) = 0`. -/
theorem triEval_resultant_eq_zero (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s : ℕ)
    (hFd : Fpoly.natDegree ≤ d) (hGd : Gpoly.natDegree ≤ s) (hpos : 0 < d + s)
    (z : F) (P : Polynomial F)
    (hFvan : evalContact (evalZContact z Fpoly) P = 0)
    (hGvan : evalContact (evalZContact z Gpoly) P = 0) :
    triEvalHom z P (Polynomial.resultant Fpoly Gpoly d s) = 0 := by
  have hmap := Polynomial.resultant_map_map Fpoly Gpoly d s (specializeZ z)
  have h1 : triEvalHom z P (Polynomial.resultant Fpoly Gpoly d s) =
      evalBiHom P (Polynomial.resultant (evalZContact z Fpoly) (evalZContact z Gpoly) d s) := by
    change evalBiHom P (specializeZ z (Polynomial.resultant Fpoly Gpoly d s)) = _
    rw [← hmap]; rfl
  rw [h1]
  exact evalBi_resultant_eq_zero (evalZContact z Fpoly) (evalZContact z Gpoly) d s
    (Polynomial.natDegree_map_le.trans hFd) (Polynomial.natDegree_map_le.trans hGd) hpos P
    hFvan hGvan

/-- Any nonzero `Φ ∈ BiPoly F` of `Y₀`-degree `≤ B` vanishes on at most `B` distinct polynomials
`P ∈ F[X]`. -/
theorem card_roots_le_of_biPoly_ne_zero (Φ : BiPoly F) (B : ℕ)
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B)
    (T : Finset (Polynomial F)) (hvan : ∀ P ∈ T, evalBiHom P Φ = 0) :
    T.card ≤ B := by
  classical
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ_inj : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  let ΦK : Polynomial (RatFunc F) := Φ.map ψ
  have hΦK_ne : ΦK ≠ 0 := (Polynomial.map_ne_zero_iff hψ_inj).mpr hΦ
  have hΦK_deg : ΦK.natDegree ≤ B := Polynomial.natDegree_map_le.trans hB
  have hsub : T.image ψ ⊆ ΦK.roots.toFinset := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨P, hP, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦK_ne, Polynomial.IsRoot.def,
      Polynomial.eval_map_apply]
    change ψ (evalBiHom P Φ) = 0
    rw [hvan P hP, map_zero]
  calc T.card = (T.image ψ).card := (Finset.card_image_of_injective T hψ_inj).symm
    _ ≤ ΦK.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ ΦK.roots.card := Multiset.toFinset_card_le ΦK.roots
    _ ≤ ΦK.natDegree := Polynomial.card_roots' ΦK
    _ ≤ B := hΦK_deg

/-- **Zero-`τ` `O(1)` Common-Root Cap (Scalar `ContactPoly F`, any field `F`):**
For any irreducible `Fpoly` of `Y₁`-degree `d ≥ 1` and `Gpoly` of `Y₁`-degree `≤ s` with
`¬ Fpoly ∣ Gpoly`, at most `(d * W + s * (W_F - d * (wY - 1))) / wY` polynomials `P ∈ F[X]`
satisfy `Fpoly(X, P, P') = 0 ∧ Gpoly(X, P, P') = 0`! -/
theorem card_common_roots_le_of_resultant_scalar
    (Fpoly Gpoly : ContactPoly F) (wY W_F W d s : ℕ)
    (hwY : 1 ≤ wY)
    (hirr : Irreducible Fpoly) (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s)
    (hFw : contactWDeg wY Fpoly ≤ W_F) (hGw : contactWDeg wY Gpoly ≤ W)
    (hWF_ge : d * (wY - 1) ≤ W_F)
    (hndvd : ¬ Fpoly ∣ Gpoly)
    (T : Finset (Polynomial F))
    (hvan : ∀ P ∈ T, evalContact Fpoly P = 0 ∧ evalContact Gpoly P = 0) :
    T.card ≤ (d * W + s * (W_F - d * (wY - 1))) / wY := by
  let Φ := Polynomial.resultant Fpoly Gpoly d s
  have hΦ : Φ ≠ 0 :=
    resultant_ne_zero_of_not_dvd_scalar Fpoly Gpoly d s hirr hFd hd hGd hndvd
  have hWΦ : biWeightedDeg Φ wY ≤ d * W + s * (W_F - d * (wY - 1)) :=
    biWeightedDeg_resultant_le Fpoly Gpoly wY W_F W d s hFw hGw hWF_ge
  have hB : Φ.natDegree ≤ (d * W + s * (W_F - d * (wY - 1))) / wY :=
    (natDegree_le_biWeightedDeg_div Φ wY (by omega)).trans (Nat.div_le_div_right hWΦ)
  exact card_roots_le_of_biPoly_ne_zero Φ _ hΦ hB T fun P hP =>
    evalBi_resultant_eq_zero Fpoly Gpoly d s (le_of_eq hFd) hGd (by omega) P
      (hvan P hP).1 (hvan P hP).2

/-- **Zero-`τ` `O(1)` Common-Root Cap (Parametric `deg_Z = 0`, any field `F`):** -/
theorem card_common_roots_le_of_resultant
    (Fpoly Gpoly : ContactPoly (Polynomial F)) (wY W_F W d s : ℕ)
    (hwY : 1 ≤ wY)
    (hirr : Irreducible (liftCRat Fpoly)) (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s)
    (hFw : contactWDeg wY Fpoly ≤ W_F) (hGw : contactWDeg wY Gpoly ≤ W)
    (hWF_ge : d * (wY - 1) ≤ W_F)
    (hFZ0 : ∀ k j a, (((Fpoly.coeff k).coeff j).coeff a).natDegree ≤ 0)
    (hGZ0 : ∀ k j a, (((Gpoly.coeff k).coeff j).coeff a).natDegree ≤ 0)
    (hndvd : ¬ liftCRat Fpoly ∣ liftCRat Gpoly)
    (T : Finset (Polynomial F))
    (hvan : ∀ P ∈ T,
      evalContact (evalZContact 0 Fpoly) P = 0 ∧ evalContact (evalZContact 0 Gpoly) P = 0) :
    T.card ≤ (d * W + s * (W_F - d * (wY - 1))) / wY := by
  let Φ := Polynomial.resultant Fpoly Gpoly d s
  have hΦ : Φ ≠ 0 := resultant_ne_zero_of_not_dvd Fpoly Gpoly d s hirr hFd hd hGd hndvd
  have hWΦ : biWeightedDeg Φ wY ≤ d * W + s * (W_F - d * (wY - 1)) :=
    biWeightedDeg_resultant_le Fpoly Gpoly wY W_F W d s hFw hGw hWF_ge
  have hB : Φ.natDegree ≤ (d * W + s * (W_F - d * (wY - 1))) / wY :=
    (natDegree_le_biWeightedDeg_div Φ wY (by omega)).trans (Nat.div_le_div_right hWΦ)
  have hZ0 : ∀ j a, ((Φ.coeff j).coeff a).natDegree = 0 := fun j a =>
    Nat.eq_zero_of_le_zero (by simpa using degZ_resultant_le Fpoly Gpoly d s 0 0 hFZ0 hGZ0 j a)
  let Φ0 : BiPoly F := specializeZ 0 Φ
  have hΦ0_ne : Φ0 ≠ 0 := by
    intro h0; apply hΦ
    refine Polynomial.ext fun j => Polynomial.ext fun a => ?_
    have hj : (Φ0.coeff j).coeff a = 0 := by rw [h0]; simp
    have heval0 : ((Φ.coeff j).coeff a).eval 0 = 0 := by
      simpa [Φ0, specializeZ] using hj
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (hZ0 j a)
    have hcoeff0 : ((Φ.coeff j).coeff a).coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using heval0
    rw [hC, hcoeff0, map_zero, Polynomial.coeff_zero, Polynomial.coeff_zero]
  have hΦ0_deg : Φ0.natDegree ≤ (d * W + s * (W_F - d * (wY - 1))) / wY :=
    Polynomial.natDegree_map_le.trans hB
  exact card_roots_le_of_biPoly_ne_zero Φ0 _ hΦ0_ne hΦ0_deg T fun P hP =>
    triEval_resultant_eq_zero Fpoly Gpoly d s (le_of_eq hFd) hGd (by omega) 0 P
      (hvan P hP).1 (hvan P hP).2

end ContactResultant

#print axioms pow_dvd_resultant_of_weighted_ord
#print axioms pow_dvd_resultant_exact
#print axioms resultant_shiftBi
#print axioms pow_dvd_resultant_of_biMultGE
#print axioms X_sub_C_pow_dvd_resultant_of_biMultGE
#print axioms sum_resOrdExact_le_natDegree_resultant
#print axioms resultant_ne_zero_of_not_dvd_scalar
#print axioms resultant_ne_zero_of_not_dvd
#print axioms biWeightedDeg_resultant_le
#print axioms degZ_resultant_le
#print axioms card_common_roots_le_of_resultant_scalar
#print axioms card_common_roots_le_of_resultant

end ArkLib.ProximityGap.Frontier.PrimeHDResultant
