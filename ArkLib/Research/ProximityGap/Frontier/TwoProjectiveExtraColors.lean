/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoProjectiveExtraWitness

/-! # Four disjoint split fibers supply the two extra projective witnesses -/
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoProjectiveExtraColors

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Coincidence pattern of the zero polynomial, the second head and the two
outside polynomials on the four root fibers, the common locator, and the remaining sites. -/
def pattern : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 0, 2, 3], ![0, 1, 0, 0], ![0, 1, 1, 3], ![0, 1, 2, 1], ![0, 0, 0, 0],
    ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]

/-- Each of the four split fibers has D sites. R is the shared locator size. -/
def weight (D R P T : ℕ) : Fin 8 → ℕ := ![D, D, D, D, R, P + D, P, T]

private def owners (j : Fin 2) : Fin 8 → Fin 4 := ![0, 0, 1, 1, 0, 0, 1, if j = 0 then 2 else 3]
private def head (j : Fin 2) : Fin 4 := ![0, 1] j
private def extra (j : Fin 2) : Fin 4 := ![2, 3] j
private def cores : Fin 2 → Finset (Fin 8) := ![{0, 1, 4, 5}, {0, 2, 3, 4, 6}]
private def supports : Fin 2 → Finset (Fin 8) := ![{1, 2, 4, 7}, {1, 3, 4, 7}]

/-- A finite table of coincidence classes, received-row owners and prescribed supports. -/
structure Layout (n : ℕ) where
  pattern : Fin n → Fin 4 → Fin 4
  owners : Fin 2 → Fin n → Fin 4
  cores : Fin 2 → Finset (Fin n)
  supports : Fin 2 → Finset (Fin n)
  outside : Fin n
  horizontal : Fin n
  vertical : Fin n

/-- These finite conditions verify both full cores and the two conflicting projected supports. -/
abbrev Layout.Valid {n : ℕ} (a : Layout n) : Prop :=
  (∀ j c, a.pattern c (head j) = a.pattern c (a.owners 0 c) ↔ c ∈ a.cores j) ∧
  (∀ j c, c ∈ a.cores j → a.pattern c (a.owners 1 c) = a.pattern c (a.owners 0 c)) ∧
  (∀ j c, a.pattern c (a.owners 1 c) = a.pattern c (head j) → c ∈ a.cores j) ∧
  (∀ c, c ∉ a.cores 0 → c ∉ a.cores 1 → c = a.outside) ∧
  (∀ j l, a.pattern a.outside j = a.pattern a.outside l → j = l) ∧
  a.owners 0 a.outside = 2 ∧ a.owners 1 a.outside = 3 ∧
  (∀ j, a.outside ∈ a.supports j) ∧
  (∀ j c, c ∈ a.supports j → a.pattern c (extra j) = a.pattern c (a.owners j c)) ∧
  a.horizontal ∈ a.supports 0 ∧ a.horizontal ∉ a.cores 0 ∧
  a.pattern a.horizontal (extra 1) ≠ a.pattern a.horizontal (a.owners 1 a.horizontal) ∧
  a.vertical ∈ a.supports 1 ∧
  a.pattern a.vertical (extra 0) ≠ a.pattern a.vertical (a.owners 0 a.vertical)

/-- Lift a verified table on site classes to a simultaneous MCA mass lower bound. -/
theorem Layout.mass {n : ℕ} (L : Layout n) (valid : L.Valid) (dom : I ↪ F)
    (k M : ℕ) (δ : ℝ≥0) (f : Fin 4 → F[X]) (col : I → Fin n) (w : Fin n → ℕ)
    (deg : ∀ j, (f j).natDegree + 1 < k)
    (eq : ∀ j l i, (f j).eval (dom i) = (f l).eval (dom i) ↔
      L.pattern (col i) j = L.pattern (col i) l)
    (count : ∀ j, (univ.filter (fun i => col i = j)).card = w j)
    (csize : ∀ j, ∑ c ∈ L.cores j, w c = M)
    (rank : k ≤ M) (hc : k ≤ w L.outside)
    (big : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((M + 1 : ℕ) : ℝ≥0))
    (height : ∀ j, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((∑ c ∈ L.supports j, w c : ℕ) : ℝ≥0))
    (hh : 0 < w L.horizontal) (hv : 0 < w L.vertical)
    (hq : (2 * (Fintype.card I - M) + 1).choose 2 < Fintype.card F)
    (room : 2 * (Fintype.card I - M) + 1 < Fintype.card F) :
    ((2 * (Fintype.card I - M) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  obtain ⟨core₀, core₁, fresh₁, outside, distinct, own₀, own₁, incl, extra_ok,
    in₀, out₀, different₀, in₁, different₁⟩ := valid
  let sel (J : Finset (Fin n)) := univ.filter fun i => col i ∈ J
  let val (j : Fin 4) (i : I) := (f j).eval (dom i)
  let row (j : Fin 2) (i : I) := val (L.owners j (col i)) i
  have card (J : Finset (Fin n)) : (sel J).card = ∑ j ∈ J, w j := by
    rw [← sum_card_fiberwise_eq_card_filter univ J col]
    exact sum_congr rfl fun j _ => count j
  have nr (j : Fin 2) : (sel (L.cores j)).card = M := (card _).trans (csize j)
  have exists_fiber (j : Fin n) (h : 0 < w j) : ∃ i, col i = j := by
    obtain ⟨i, hi⟩ := card_pos.mp ((count j).symm ▸ h)
    exact ⟨i, (mem_filter.mp hi).2⟩
  let a : TwoProjectiveExtraWitness.Arrangement dom k δ := {
    head := fun j => f (head j)
    extra := fun j => f (extra j)
    row := row
    core := fun j => sel (L.cores j)
    support := fun j => sel (L.supports j)
    common := sel {L.outside}
    degree := fun j => deg _
    extra_degree := fun j => deg _
    rank := fun j => (nr j).symm ▸ rank
    size := fun j => (nr j).symm ▸ big
    core_agrees := by
      intro j i
      change val _ i = val _ i ↔ _
      rw [show ∀ a b, val a i = val b i ↔ _ from fun a b => eq a b i]
      simp only [sel, mem_filter, mem_univ, true_and]
      exact core₀ j _
    common_rows := by
      intro j i hi
      apply (eq _ _ i).mpr
      exact core₁
        j _ (mem_filter.mp hi).2
    fresh := by
      intro j i hi e
      have h := (eq _ _ i).mp e
      apply hi
      exact mem_filter.mpr ⟨mem_univ _, fresh₁ j _ h⟩
    slopes := by
      intro i h₀ h₁
      have c : col i = L.outside := outside _
        (fun h => h₀ (mem_filter.mpr ⟨mem_univ _, h⟩)) (fun h => h₁ (mem_filter.mpr ⟨mem_univ _, h⟩))
      have ne (j l : Fin 4) (h : j ≠ l) : val j i ≠ val l i := fun e => h (by
        have t := (eq j l i).mp e
        rw [c] at t
        exact distinct j l t)
      change (val (L.owners 1 (col i)) i - val (head 0) i) / _ ≠ _
      simp only [row, c, own₀, own₁]
      change (val 3 i - val 0 i) / (val 2 i - val 0 i) ≠ (val 3 i - val 1 i) / (val 2 i - val 1 i)
      intro h
      have hx := (div_eq_div_iff (sub_ne_zero.mpr (ne 2 0 (by decide)))
        (sub_ne_zero.mpr (ne 2 1 (by decide)))).mp h
      have bad : (val 0 i - val 1 i) * (val 2 i - val 3 i) = 0 := by linear_combination -hx
      exact (mul_ne_zero (sub_ne_zero.mpr (ne 0 1 (by decide))) (sub_ne_zero.mpr (ne 2 3 (by decide)))) bad
    common_rank := by simpa [card] using hc
    common_in := by
      intro j i hi
      exact mem_filter.mpr ⟨mem_univ _, (mem_singleton.mp (mem_filter.mp hi).2).symm ▸ incl j⟩
    extra_agrees := by
      intro j i hi
      apply (eq _ _ i).mpr
      exact extra_ok
        j _ (mem_filter.mp hi).2
    support_size := fun j => (card _).symm ▸ height j
    first_mismatch := by
      obtain ⟨i, hi⟩ := exists_fiber _ hh
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, hi ▸ in₀⟩, ?_, ?_⟩
      · exact fun h => out₀ (hi ▸ (mem_filter.mp h).2)
      · intro e
        have a := (eq _ _ i).mp e
        rw [hi] at a
        exact different₀ a
    second_mismatch := by
      obtain ⟨i, hi⟩ := exists_fiber _ hv
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, hi ▸ in₁⟩, fun e => ?_⟩
      have a := (eq _ _ i).mp e
      rw [hi] at a
      exact different₁ a }
  have cnt : 2 * (Fintype.card I - M) = ∑ j, (a.core j)ᶜ.card := by
    change _ = ∑ j, (sel (L.cores j))ᶜ.card
    simp [card_compl, nr, two_mul]
  obtain ⟨u, G, hcard, good⟩ := TwoProjectiveExtraWitness.witnesses a _ cnt hq room
  rw [← hcard]
  exact MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ u G good

/-- Two full secants and both row directions give a sharp simultaneous count for
the eight-class construction, with a single received pair. -/
theorem mass (dom : I ↪ F) (k D R P T : ℕ) (δ : ℝ≥0) (f : Fin 4 → F[X]) (col : I → Fin 8)
    (deg : ∀ j, (f j).natDegree + 1 < k)
    (eq : ∀ j l i, (f j).eval (dom i) = (f l).eval (dom i) ↔ pattern (col i) j = pattern (col i) l)
    (count : ∀ j, (univ.filter (fun i => col i = j)).card = weight D R P T j)
    (hd : 0 < D) (rank : k ≤ R + 3 * D + P) (hc : k ≤ T)
    (big : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((R + 3 * D + P + 1 : ℕ) : ℝ≥0))
    (height : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((R + 2 * D + T : ℕ) : ℝ≥0))
    (hq : (2 * (Fintype.card I - (R + 3 * D + P)) + 1).choose 2 < Fintype.card F)
    (room : 2 * (Fintype.card I - (R + 3 * D + P)) + 1 < Fintype.card F) :
    ((2 * (Fintype.card I - (R + 3 * D + P)) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  let L : Layout 8 := ⟨pattern, owners, cores, supports, 7, 2, 3⟩
  refine L.mass (by decide) dom k _ δ f col (weight D R P T) deg eq count ?_ rank hc big ?_ hd hd hq room
  · intro j
    fin_cases j <;> simp [L, cores, weight] <;> omega
  · intro j
    convert height using 1
    congr 1
    fin_cases j <;> simp [L, supports, weight] <;> omega

#print axioms mass
end ArkLib.ProximityGap.Frontier.TwoProjectiveExtraColors
