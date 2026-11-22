/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadResidualSecant
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper

/-! # Outside witnesses at the three-head successor dimensions

A fourth affine head contributes either all the selected outside labels at a
site of its joint core, or at most one. Combining this alternative with the
four face multiplicities gives an incidence bound at the integer boundary.
-/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorIncidence

/-- Total multiplicity charged to the four triangle determinants at one site. -/
def faceCost (w : ℕ) := if w = 4 then 8 else if w = 3 then 5 else if w = 2 then 2 else 0

private theorem local_mix (m j b y : ℕ) (hm : 3 ≤ m) (hj : j ≤ 3) (hb : b ≤ 1)
    (out : b = 0 → y ≤ 1) (onCore : b = 1 → y = m) :
    4 * y + (4 * m - 2) * j ≤
      4 * m + 2 * (m - 1) * (j - 1) + 2 * j * y + (m - 1) * faceCost (j + b) := by
  interval_cases j <;> interval_cases b <;> simp [faceCost] at * <;> omega

private theorem local_nine (j b y : ℕ) (hj : j ≤ 3) (hb : b ≤ 1)
    (out : b = 0 → y ≤ 1) (onCore : b = 1 → y = 9) :
    17 * j + 2 * y ≤ 6 * (j + b) + 12 + 8 * (j - 1) + j * y + faceCost (j + b) := by
  interval_cases j <;> interval_cases b <;> simp [faceCost] at * <;> omega

/-- Site counts for three old heads and a selected collection on one fourth
head. The root constraint uses the actual fold incidences weighted by the
number of old cores at the site. -/
structure Counts (I : Type*) [Fintype I] (m d t : ℕ) where
  old : I → ℕ
  fourth : I → ℕ
  folds : I → ℕ
  old_le : ∀ x, old x ≤ 3
  fourth_le : ∀ x, fourth x ≤ 1
  outside : ∀ x, fourth x = 0 → folds x ≤ 1
  onCore : ∀ x, fourth x = 1 → folds x = m
  rich : 3 * (t - 1) ≤ ∑ x, old x
  agreements : m * t ≤ ∑ x, folds x
  oldTriangle : (∑ x, (old x - 1)) ≤ 2 * d
  foldRoots : (∑ x, old x * folds x) ≤ 3 * m * d
  faces : (∑ x, faceCost (old x + fourth x)) ≤ 8 * d

/-- A mixed bound on the same physical incidences, valid for any number of
outside labels at least three and for arbitrary degree and block length. -/
theorem mixed_bound {I : Type*} [Fintype I] {m d t : ℕ} (C : Counts I m d t) (hm : 3 ≤ m) :
    4 * (m * t) + (4 * m - 2) * (3 * (t - 1)) ≤ 4 * m * Fintype.card I +
      2 * (m - 1) * (2 * d) + 2 * (3 * m * d) + (m - 1) * (8 * d) := by
  have h := sum_le_sum (s := (univ : Finset I)) (fun x _ =>
    local_mix _ _ _ _ hm (C.old_le x) (C.fourth_le x) (C.outside x) (C.onCore x))
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul] at h
  have hw : (∑ x, 2 * C.old x * C.folds x) = 2 * ∑ x, C.old x * C.folds x := by
    simp [mul_sum, mul_assoc]
  rw [hw, Nat.mul_comm (Fintype.card I) m, ← Nat.mul_assoc 4 m] at h
  exact (Nat.add_le_add (Nat.mul_le_mul_left _ C.agreements) (Nat.mul_le_mul_left _ C.rich)).trans
    (h.trans (by gcongr <;> first | exact C.oldTriangle | exact C.foldRoots | exact C.faces))

/-- Nine outside labels force saturation of all four triangle budgets at the
last dimension where the mixed bound alone leaves the cell undecided. -/
theorem nine_saturation {I : Type*} [Fintype I] (n : Fintype.card I = 1073741824)
    (C : Counts I 9 71582791 357913945)
    (ceiling : (∑ x, (C.old x + C.fourth x)) ≤ 1360072988) :
    (∑ x, (C.old x + C.fourth x)) = 1360072988 ∧ (∑ x, C.old x) = 1073741832 := by
  have h := sum_le_sum (s := (univ : Finset I)) (fun x _ =>
    local_nine _ _ _ (C.old_le x) (C.fourth_le x) (C.outside x) (C.onCore x))
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul, n] at h
  rw [sum_add_distrib] at ceiling ⊢
  have h₁ := C.rich
  have h₂ := C.agreements
  have h₃ := C.oldTriangle
  have h₄ := C.foldRoots
  have h₅ := C.faces
  omega

/-- The integer mixed-incidence obstructions at the two intermediate steps. -/
theorem impossible_cells {I : Type*} [Fintype I] (n : Fintype.card I = 1073741824) :
    IsEmpty (Counts I 10 71582791 357913945) ∧ IsEmpty (Counts I 12 73688167 357913946) := by
  constructor <;> constructor <;> intro C
  all_goals have h := mixed_bound C (by decide); rw [n] at h; norm_num at h

/-- In the nine-label equality case, fifteen of the required fourth-head slots
are on old doubles. A nonsingular opposite pairing supplies at most nine
different old labels on them. -/
theorem nine_double_slots {markedDoubles chosenOld : ℕ}
    (fourth : 9 * 71582789 ≤ 644245086 + markedDoubles)
    (opposite : chosenOld ≤ 9) : chosenOld + 6 ≤ markedDoubles := by omega

open HalfPredecessorThirdMomentUpper

/-- A supporting line for the discrete third binomial moment forces a true
triple with more than a degree's worth of common complementary sites. -/
theorem popular_triple {P J : Type*} [DecidableEq J] [Fintype J]
    (G : Finset P) (A : P → Finset J) (p q d τ cap : ℕ)
    (sites : Fintype.card J ≤ cap) (rich : ∀ z ∈ G, τ ≤ (A z).card)
    (support : ∀ w ≤ G.card, p * w ≤ w.choose 3 + q)
    (gap : G.card.choose 3 * d + cap * q < p * (G.card * τ)) :
    ∃ T ∈ G.powersetCard 3, d < (commonCoordinates A T).card := by
  classical
  let w (x : J) := (G.filter fun z => x ∈ A z).card
  have inc : (∑ x, w x) = ∑ z ∈ G, (A z).card := by
    simp only [w, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    simp
  have hi : G.card * τ ≤ ∑ x, w x := by
    rw [inc]
    simpa using sum_le_sum (s := G) rich
  by_contra! small
  have h₀ := sum_le_sum (s := (univ : Finset J)) (fun x _ =>
    support (w x) (card_filter_le ..))
  rw [← mul_sum, sum_add_distrib] at h₀
  simp only [sum_const, card_univ, smul_eq_mul] at h₀
  have ht := sum_le_sum (s := G.powersetCard 3) small
  simp only [sum_const, card_powersetCard, smul_eq_mul] at ht
  have moment := sum_choose_incidence_eq_sum_commonCoordinates_card G A
  change (∑ x, (w x).choose 3) = _ at moment
  have h₁ := Nat.mul_le_mul_left p hi
  have h₂ := Nat.mul_le_mul_right q sites
  omega

/-- Outside the joint core of a line, at most one of its three witnesses can
agree. Every nonmember meets the joint core on at most its degree in sites. -/
theorem three_force_line {τ s d joint : ℕ} (three : 3 * τ ≤ s + 2 * joint)
    (off : τ + joint ≤ s + d) (gap : 3 * s + 2 * d < 5 * τ) : False := by omega

/-- Weighted intersections use the same physical site, so a fold matching two
old cores at a double spends two polynomial root incidences. -/
theorem fold_intersections {I P : Type*} [Fintype I] [DecidableEq I]
    (G : Finset P) (core : Fin 3 → Finset I) (A : P → Finset I) (d : ℕ)
    (roots : ∀ z ∈ G, ∀ i, (core i ∩ A z).card ≤ d) :
    (∑ x, (univ.filter (fun i => x ∈ core i)).card *
      (G.filter (fun z => x ∈ A z)).card) ≤ 3 * G.card * d := by
  classical
  have pair (z : P) (i : Fin 3) :
      (∑ x : I, (if x ∈ core i then 1 else 0 : ℕ) * (if x ∈ A z then 1 else 0)) =
        (core i ∩ A z).card := by
    calc
      _ = ∑ x : I, if x ∈ core i ∩ A z then 1 else 0 := by
        apply sum_congr rfl
        intro x _
        by_cases h : x ∈ core i <;> by_cases h' : x ∈ A z <;> simp [h, h']
      _ = _ := by
        simp only [sum_boole, Nat.cast_id]
        congr 1
        ext x
        simp
  have eq : (∑ x, (univ.filter (fun i => x ∈ core i)).card *
      (G.filter (fun z => x ∈ A z)).card) =
      ∑ i, ∑ z ∈ G, (core i ∩ A z).card := by
    conv_lhs => simp only [card_eq_sum_ones, sum_filter, sum_mul, mul_sum]
    rw [sum_comm, Finset.sum_comm (s := (univ : Finset (Fin 3))) (t := G)]
    apply sum_congr rfl
    intro z _
    rw [sum_comm]
    exact sum_congr rfl (fun i _ => pair z i)
  rw [eq]
  have bounds (i : Fin 3) : (∑ z ∈ G, (core i ∩ A z).card) ≤ G.card * d := by
    simpa using sum_le_sum (s := G) (fun z hz => roots z hz i)
  simpa [Nat.mul_assoc] using sum_le_sum (s := univ) (fun i _ => bounds i)

/-- One double interpolant suffices for every endpoint in the successor table. -/
theorem common_surface {F I : Type} [Field F] [Fintype I] (dom : I ↪ F)
    (v w : I → F) (hn : Fintype.card I = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 7 ∧ i + j ≤ 25 ∧ a + j * 77807385 < 2 * 357913944) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ 77807385 → ∀ S : Finset I, 357913944 ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = v i + z * w i) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  classical
  open SecondPrimeQuarticInterpolation in
    obtain ⟨c, hc, hall⟩ := exists_curve_double (s := 25) (v := 7) (d := 77807385) (t := 357913944)
      dom v w (by decide) (by decide) (by
        rw [hn]
        simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
        norm_num [Fin.sum_univ_succ])
    exact ⟨SecondPrimeQuarticInterpolation.surface c, surface_ne_zero hc,
      fun _ _ _ h => surface_support c h, fun z q hq S hS ha => by
        rw [surface_eval]; exact hall z q hq S hS ha⟩

/-- Seven endpoints where the fourth-head capacity overrules all outside
witnesses, after the discrete third moment gives a common line. -/
def momentCell : Fin 7 → ℕ × ℕ :=
  ![(715827877,76695849), (715827876,77650736), (715827875,77686750),
    (715827874,77734912), (715827873,77768621), (715827872,77782878), (715827871,77807385)]

/-- Discrete supporting-line and fresh-site inequalities for the seven cells. -/
theorem moment_cells : ∀ i : Fin 7,
    let n := 1073741824
    let (e, d) := momentCell i
    let t := n - e
    let c := t - 1
    let m := 2 * n + 1 - 3 * (e + 1)
    let s := n + 2 * d - 3 * c
    let τ := t - 3 * d
    let h := m * τ / s
    let p := h.choose 2
    let q := h * p - h.choose 3
    (∀ a : Fin (m + 1), p * a.val ≤ a.val.choose 3 + q) ∧
      m.choose 3 * d + s * q < p * (m * τ) ∧ 3 * s + 2 * d < 5 * τ ∧
      n + (m - 1) * (n + 4 * d - 3 * c) < m * t := by decide

#print axioms fold_intersections
#print axioms common_surface
#print axioms moment_cells
#print axioms mixed_bound
#print axioms nine_saturation
#print axioms impossible_cells
#print axioms nine_double_slots
#print axioms popular_triple
#print axioms three_force_line
end ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorIncidence
