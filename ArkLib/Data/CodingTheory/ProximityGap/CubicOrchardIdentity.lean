/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSupplyGeneral

/-!
# THE CUBIC ORCHARD IDENTITY: an exact sub-Johnson list size (#389)

The first slice of the exact sub-Johnson list-size question (`k = 2`, agreement `3` —
strictly sub-Johnson once `9 < n`): the graph points `(a, a³), (b, b³), (c, c³)` are
collinear **iff `a + b + c = 0`** (the slope identity `(a³−b³)/(a−b) = a²+ab+b²` cancels
to `(a−c)(a+b+c) = 0`), and no affine line meets the cubic's graph four times (two
zero-sum triples sharing a pair force equal third elements).  Hence, EXACTLY:

> **`cubic_list_eq_zeroSum`** — for `w = x³` on ANY domain:
> `#{c ∈ rsCode(dom, 2) : |agreeSet(c, w)| ≥ 3} = #{T ⊆ dom : |T| = 3, Σ T = 0}`.

On smooth domains the right side is a subgroup zero-sum count — an exact character-sum
object (probe: `14, 20, 20, 24` at `(29,14), (31,15), (41,20), (37,18)`, matching the
codeword census bit-exactly).  General cubics `c₃x³ + c₂x² + …` sweep the sum-`s`
fibers (`Σ T = −c₂/c₃`), so the cubic family's exact list profile is the triple-sum
fiber distribution of the domain — the finite-field orchard problem (Green–Tao's
real-plane `⌊n(n−3)/6⌋+1` cap is attained by exactly such cubics).  HONEST CAVEAT
(probe, deep hill-climb): over `F_q` cubics are NOT globally extremal — measured
global maxima `21 > 14` at `(29,14)` and `25 > 20` at `(31,15)` exceed the best cubic
fiber (real-plane Sylvester–Gallai rigidity does not transfer); the `F_q` orchard
number remains the open extremal core, between the best cubic fiber and the pair
bound `⌊n(n−1)/6⌋`.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] in
/-- **Cubic collinearity** (backward): if `a + b + c = 0`, the three cubic graph
points lie on the line `Y = (a² + ab + b²)·X − ab·(a+b)`. -/
theorem cubic_collinear_of_sum_zero {a b c : F} (h : a + b + c = 0) :
    ∀ x ∈ ({a, b, c} : Finset F),
      x ^ 3 = (a ^ 2 + a * b + b ^ 2) * x - a * b * (a + b) := by
  have hc : c = -(a + b) := by linear_combination h
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · ring
  rcases Finset.mem_insert.mp hx with rfl | hx
  · ring
  · rw [Finset.mem_singleton.mp hx, hc]
    ring

omit [Fintype F] [DecidableEq F] in
/-- **Cubic collinearity** (forward): three distinct points of the cubic graph on a
common affine line have zero sum. -/
theorem sum_zero_of_cubic_collinear {a b c A B : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ^ 3 = A * a + B) (hb : b ^ 3 = A * b + B) (hc : c ^ 3 = A * c + B) :
    a + b + c = 0 := by
  have h1 : (a - b) * (a ^ 2 + a * b + b ^ 2 - A) = 0 := by linear_combination ha - hb
  have h2 : (a - c) * (a ^ 2 + a * c + c ^ 2 - A) = 0 := by linear_combination ha - hc
  have e1 : a ^ 2 + a * b + b ^ 2 = A := by
    have := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hab)
    linear_combination this
  have e2 : a ^ 2 + a * c + c ^ 2 = A := by
    have := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hac)
    linear_combination this
  have h3 : (b - c) * (a + b + c) = 0 := by linear_combination e1 - e2
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hbc)

open Classical in
/-- **THE CUBIC ORCHARD IDENTITY** — the exact sub-Johnson list size of the cubic word
at agreement `3` for the dimension-`2` code: it equals the domain's zero-sum triple
count, on EVERY domain. -/
theorem cubic_list_eq_zeroSum (dom : Fin n ↪ F) :
    ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode dom 2 : Submodule F (Fin n → F))
          ∧ 3 ≤ (agreeSet c (fun i => (dom i) ^ 3)).card)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
          (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  -- any three distinct agreement points of a listed codeword have zero dom-sum
  have hagree_card : ∀ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
      ∀ i₁ ∈ agreeSet c (fun i => (dom i) ^ 3),
      ∀ i₂ ∈ agreeSet c (fun i => (dom i) ^ 3),
      ∀ i₃ ∈ agreeSet c (fun i => (dom i) ^ 3),
      i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ → dom i₁ + dom i₂ + dom i₃ = 0 := by
    intro c hc i₁ h₁ i₂ h₂ i₃ h₃ h12 h13 h23
    obtain ⟨P, hPdeg, rfl⟩ := hc
    have hP1 : P.natDegree ≤ 1 := by
      rcases eq_or_ne P 0 with rfl | hP0
      · simp
      · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
        omega
    have hPform : ∀ x : F, P.eval x = P.coeff 1 * x + P.coeff 0 := by
      intro x
      conv_lhs => rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp
      ring
    have e1 : P.eval (dom i₁) = (dom i₁) ^ 3 := (Finset.mem_filter.mp h₁).2
    have e2 : P.eval (dom i₂) = (dom i₂) ^ 3 := (Finset.mem_filter.mp h₂).2
    have e3 : P.eval (dom i₃) = (dom i₃) ^ 3 := (Finset.mem_filter.mp h₃).2
    rw [hPform] at e1 e2 e3
    exact sum_zero_of_cubic_collinear
      (fun h => h12 (dom.injective h)) (fun h => h13 (dom.injective h))
      (fun h => h23 (dom.injective h))
      (by rw [← e1]) (by rw [← e2]) (by rw [← e3])
  -- agreement of a listed codeword is EXACTLY 3
  have hcard3 : ∀ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
      3 ≤ (agreeSet c (fun i => (dom i) ^ 3)).card →
      (agreeSet c (fun i => (dom i) ^ 3)).card = 3 := by
    intro c hmem hge
    refine le_antisymm ?_ hge
    by_contra hgt
    push Not at hgt
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq
      (by omega : 4 ≤ (agreeSet c (fun i => (dom i) ^ 3)).card)
    obtain ⟨j₁, hj1⟩ := Finset.card_pos.mp (by omega : 0 < S4.card)
    obtain ⟨j₂, hj2, hj12s⟩ := Finset.exists_mem_ne (by omega : 1 < S4.card) j₁
    have hj12 : j₁ ≠ j₂ := hj12s.symm
    have herase2 : 1 < ((S4.erase j₁).erase j₂).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj12s, hj2⟩),
        Finset.card_erase_of_mem hj1]
      omega
    obtain ⟨j₃, hj3e, hj31⟩ := Finset.exists_mem_ne herase2 j₁
    obtain ⟨j₄, hj4e, hj43⟩ := Finset.exists_mem_ne herase2 j₃
    have hj3 : j₃ ∈ S4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj3e)
    have hj4 : j₄ ∈ S4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj4e)
    have hj13 : j₁ ≠ j₃ := fun h => hj31 h.symm
    have hj23 : j₂ ≠ j₃ := fun h => (Finset.mem_erase.mp hj3e).1 h.symm
    have hj14 : j₁ ≠ j₄ := fun h =>
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj4e)).1 h.symm
    have hj24 : j₂ ≠ j₄ := fun h => (Finset.mem_erase.mp hj4e).1 h.symm
    have hsum3 := hagree_card c hmem j₁ (hS4sub hj1) j₂ (hS4sub hj2)
      j₃ (hS4sub hj3) hj12 hj13 hj23
    have hsum4 := hagree_card c hmem j₁ (hS4sub hj1) j₂ (hS4sub hj2)
      j₄ (hS4sub hj4) hj12 hj14 hj24
    have : dom j₃ = dom j₄ := by linear_combination hsum3 - hsum4
    exact hj43 (dom.injective this).symm
  refine Finset.card_bij (fun c _ => agreeSet c (fun i => (dom i) ^ 3)) ?_ ?_ ?_
  · -- maps into the zero-sum triples
    intro c hc
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    have hexact := hcard3 c hmem hge
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, hSeq⟩ := Finset.card_eq_three.mp hexact
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hexact⟩, ?_⟩
    have hm1 : i₁ ∈ agreeSet c (fun i => (dom i) ^ 3) := by
      rw [hSeq]; exact Finset.mem_insert_self _ _
    have hm2 : i₂ ∈ agreeSet c (fun i => (dom i) ^ 3) := by
      rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hm3 : i₃ ∈ agreeSet c (fun i => (dom i) ^ 3) := by
      rw [hSeq]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))
    show ∑ i ∈ agreeSet c (fun i => (dom i) ^ 3), dom i = 0
    rw [hSeq, Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]), Finset.sum_singleton]
    linear_combination hagree_card c hmem i₁ hm1 i₂ hm2 i₃ hm3 h12 h13 h23
  · -- injective: two agreement points interpolate the line
    intro c hc cb hcb heq
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hmemb, -⟩ := Finset.mem_filter.mp hcb
    have heqA : agreeSet c (fun i => (dom i) ^ 3)
        = agreeSet cb (fun i => (dom i) ^ 3) := heq
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (by omega : 2 ≤ (agreeSet c (fun i => (dom i) ^ 3)).card)
    have hTsubB : T ⊆ agreeSet cb (fun i => (dom i) ^ 3) := by
      rw [← heqA]; exact hTsub
    refine explainable_core_explainer_unique (k := 2) dom
      (le_of_eq hTcard.symm) hmem hmemb
      (fun i hi => (Finset.mem_filter.mp (hTsub hi)).2)
      (fun i hi => (Finset.mem_filter.mp (hTsubB hi)).2)
  · -- surjective: each zero-sum triple is realized by its chord line
    intro T hT
    obtain ⟨hTmem, hTsum⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, hTeq⟩ := Finset.card_eq_three.mp hTcard
    have hsum : dom i₁ + dom i₂ + dom i₃ = 0 := by
      have hs := hTsum
      rw [hTeq, Finset.sum_insert (by simp [h12, h13]),
        Finset.sum_insert (by simp [h23]), Finset.sum_singleton] at hs
      linear_combination hs
    set c0 : Fin n → F := fun i =>
      ((dom i₁) ^ 2 + (dom i₁) * (dom i₂) + (dom i₂) ^ 2) * (dom i)
        - (dom i₁) * (dom i₂) * ((dom i₁) + (dom i₂)) with hc0
    have hc0mem : c0 ∈ (rsCode dom 2 : Submodule F (Fin n → F)) := by
      refine ⟨Polynomial.C ((dom i₁) ^ 2 + (dom i₁) * (dom i₂) + (dom i₂) ^ 2)
        * Polynomial.X
        - Polynomial.C ((dom i₁) * (dom i₂) * ((dom i₁) + (dom i₂))), ?_, ?_⟩
      · refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
        · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
          calc (Polynomial.C ((dom i₁) ^ 2 + (dom i₁) * (dom i₂)
                  + (dom i₂) ^ 2)).degree
                + (Polynomial.X : Polynomial F).degree
              ≤ 0 + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
          _ < 2 := by
              rw [zero_add]
              exact_mod_cast one_lt_two
        · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast two_pos)
      · funext i
        simp [hc0]
    have hagr : ∀ i ∈ T, c0 i = (dom i) ^ 3 := by
      intro i hi
      have hcol := cubic_collinear_of_sum_zero (c := dom i₃) hsum
      have hmem3 : dom i ∈ ({dom i₁, dom i₂, dom i₃} : Finset F) := by
        rw [hTeq] at hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [Finset.mem_singleton.mp hi]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_singleton_self _))
      have hval := hcol (dom i) hmem3
      show ((dom i₁) ^ 2 + (dom i₁) * (dom i₂) + (dom i₂) ^ 2) * (dom i)
        - (dom i₁) * (dom i₂) * ((dom i₁) + (dom i₂)) = (dom i) ^ 3
      exact hval.symm
    have hTsubA : T ⊆ agreeSet c0 (fun i => (dom i) ^ 3) := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagr i hi⟩
    have hge0 : 3 ≤ (agreeSet c0 (fun i => (dom i) ^ 3)).card := by
      calc (3 : ℕ) = T.card := hTcard.symm
      _ ≤ _ := Finset.card_le_card hTsubA
    refine ⟨c0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0mem, hge0⟩, ?_⟩
    have hexact0 := hcard3 c0 hc0mem hge0
    exact (Finset.eq_of_subset_of_card_le hTsubA (by omega)).symm

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.cubic_collinear_of_sum_zero
#print axioms ProximityGap.PairRank.sum_zero_of_cubic_collinear
#print axioms ProximityGap.PairRank.cubic_list_eq_zeroSum
