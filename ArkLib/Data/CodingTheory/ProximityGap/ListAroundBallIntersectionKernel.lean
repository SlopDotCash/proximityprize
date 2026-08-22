/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming

/-!
  List-vs-radius bound from weight structure (ANGLE 2).

  Self-contained, imports only Mathlib.
-/

open scoped Classical
open Finset

namespace ArkLib.CodingTheory.Round13BallInter
noncomputable section

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The list of codewords within Hamming radius `r` of a received word `w`. -/
def listAround (C : Finset (Fin n → F)) (w : Fin n → F) (r : ℕ) : Finset (Fin n → F) :=
  C.filter (fun c => hammingDist w c ≤ r)

/-- A subtraction-closed ("linear") code: contains `0` and is closed under pointwise
subtraction.  This is the algebraic hypothesis behind the weight ↔ distance correspondence. -/
structure LinCode (C : Finset (Fin n → F)) : Prop where
  zero_mem : (0 : Fin n → F) ∈ C
  sub_mem : ∀ a ∈ C, ∀ b ∈ C, (a - b) ∈ C

/-- Minimum distance `d`: any two distinct codewords differ in at least `d` coordinates. -/
def HasMinDist (C : Finset (Fin n → F)) (d : ℕ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ hammingDist a b

/-- For a linear code, the minimum distance equals the minimum weight: a nonzero codeword
has Hamming norm at least `d`. -/
theorem hammingNorm_ge_of_minDist {C : Finset (Fin n → F)} (hC : LinCode C)
    {d : ℕ} (hd : HasMinDist C d) {x : Fin n → F} (hx : x ∈ C) (hx0 : x ≠ 0) :
    d ≤ hammingNorm x := by
  have : hammingDist x 0 = hammingNorm x := hammingDist_zero_right x
  rw [← this]
  exact hd x hx 0 hC.zero_mem hx0

/-- **(i) Codeword-centered triviality.**  For a code with minimum distance `d`, the list of
codewords within radius `r < d` of a *codeword* `c` is exactly `{c}`.  Equivalently, via the
bijection `c' ↦ c' - c`, the only codeword of weight `< d` is `0`.  This is the precise sense in
which the weight enumerator controls the codeword-centered list only trivially below the
minimum distance `d = n - k + 1 ~ (1-ρ)n`. -/
theorem listAround_codeword_eq_singleton {C : Finset (Fin n → F)} {d : ℕ}
    (hd : HasMinDist C d) {c : Fin n → F} (hc : c ∈ C) {r : ℕ} (hr : r < d) :
    listAround C c r = {c} := by
  ext x
  simp only [listAround, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hxC, hdist⟩
    by_contra hxc
    have hne : c ≠ x := fun h => hxc h.symm
    have : d ≤ hammingDist c x := hd c hc x hxC hne
    omega
  · rintro rfl
    exact ⟨hc, by simp [hammingDist_self]⟩

/-- **(i'), cardinality form.**  The codeword-centered list has cardinality exactly `1` for
radius below the minimum distance. -/
theorem listAround_codeword_card_eq_one {C : Finset (Fin n → F)} {d : ℕ}
    (hd : HasMinDist C d) {c : Fin n → F} (hc : c ∈ C) {r : ℕ} (hr : r < d) :
    (listAround C c r).card = 1 := by
  rw [listAround_codeword_eq_singleton hd hc hr, card_singleton]

/-- The Hamming ball of radius `r` around `c`, as a finset of all words (the ambient
`Fin n → F` is finite since `F` is). -/
def hammingBall (c : Fin n → F) (r : ℕ) : Finset (Fin n → F) :=
  Finset.univ.filter (fun w => hammingDist c w ≤ r)

/-- **(ii) Union-bound / count identity (basic).**  For an arbitrary received word `w`, the
radius-`r` list is exactly the set of codewords whose distance to `w` is `≤ r`; hence its
cardinality is the count of such codewords.  This is the union-bound localization: the list size
is a *count over codewords*, controlled by how many codewords land in the ball `B(w,r)`. -/
theorem listAround_card_eq_count (C : Finset (Fin n → F)) (w : Fin n → F) (r : ℕ) :
    (listAround C w r).card = (C.filter (fun c => hammingDist w c ≤ r)).card := rfl

/-- Membership in the list, in ball form. -/
theorem mem_listAround {C : Finset (Fin n → F)} {w c : Fin n → F} {r : ℕ} :
    c ∈ listAround C w r ↔ c ∈ C ∧ w ∈ hammingBall c r := by
  simp only [listAround, hammingBall, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hc, hd⟩; exact ⟨hc, by rwa [hammingDist_comm]⟩
  · rintro ⟨hc, hd⟩; exact ⟨hc, by rwa [hammingDist_comm]⟩

/-- **(ii) First moment — double counting.**  Summing the list size over *all* received words `w`
equals the total ball mass `∑_{c ∈ C} |B(c,r)|`.  (Each pair `(c, w)` with `dist(w,c) ≤ r` is
counted once on each side.)  This is the elementary identity behind the averaging/covering
argument. -/
theorem sum_listAround_card (C : Finset (Fin n → F)) (r : ℕ) :
    (∑ w : Fin n → F, (listAround C w r).card) = ∑ c ∈ C, (hammingBall c r).card := by
  -- Count pairs `(w, c)` with `c ∈ C` and `w ∈ B(c,r)` two ways.
  simp only [listAround, hammingBall, card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : hammingDist c w ≤ r
  · simp only [h, if_true]
    rw [if_pos (hammingDist_comm c w ▸ h : hammingDist w c ≤ r)]
  · have hwc : ¬ hammingDist w c ≤ r := by rwa [hammingDist_comm]
    simp only [h, hwc, if_false]

/-- The list size as a sum of indicators over codewords. -/
theorem listAround_card_eq_sum_indicator (C : Finset (Fin n → F)) (w : Fin n → F) (r : ℕ) :
    (listAround C w r).card = ∑ c ∈ C, (if w ∈ hammingBall c r then 1 else 0) := by
  rw [listAround, card_filter]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [hammingBall, mem_filter, mem_univ, true_and]
  by_cases h : hammingDist w c ≤ r
  · rw [if_pos h, if_pos (hammingDist_comm w c ▸ h : hammingDist c w ≤ r)]
  · rw [if_neg h, if_neg (by rwa [hammingDist_comm] : ¬ hammingDist c w ≤ r)]

/-- **(ii) Second moment = ball-intersection sum (the #82 kernel).**  The sum of *squared* list
sizes over all received words equals the double sum of ball intersections
`∑_{c,c' ∈ C} |B(c,r) ∩ B(c',r)|`.  This identity is exactly why the ball-intersection second
moment is the object controlling list sizes for a *general* (non-codeword) center: by Cauchy–
Schwarz / Paley–Zygmund, a uniform upper bound on `∑_{c,c'} |B(c,r) ∩ B(c',r)|` yields the sharp
list-size control past the Johnson radius.  This double-counting identity is proven here; the
*sharp upper bound on the right-hand side* for explicit RS is the open prize kernel. -/
theorem sum_sq_listAround_eq_ball_inter (C : Finset (Fin n → F)) (r : ℕ) :
    (∑ w : Fin n → F, (listAround C w r).card ^ 2)
      = ∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card := by
  -- Expand each squared list size as a double indicator sum, then swap orders.
  have hexp : ∀ w : Fin n → F, (listAround C w r).card ^ 2
      = ∑ c ∈ C, ∑ c' ∈ C,
          (if w ∈ hammingBall c r then 1 else 0) * (if w ∈ hammingBall c' r then 1 else 0) := by
    intro w
    rw [sq, listAround_card_eq_sum_indicator C w r, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c' hc'
  -- `∑_w [w∈B(c)]·[w∈B(c')] = |B(c) ∩ B(c')|`.
  have key : ∀ w : Fin n → F,
      (if w ∈ hammingBall c r then (1:ℕ) else 0) * (if w ∈ hammingBall c' r then 1 else 0)
        = (if w ∈ hammingBall c r ∩ hammingBall c' r then 1 else 0) := by
    intro w
    by_cases h1 : w ∈ hammingBall c r <;> by_cases h2 : w ∈ hammingBall c' r <;>
      simp [Finset.mem_inter, h1, h2]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

#check @sum_sq_listAround_eq_ball_inter

end
end ArkLib.CodingTheory.Round13BallInter
#print axioms ArkLib.CodingTheory.Round13BallInter.sum_sq_listAround_eq_ball_inter
#print axioms ArkLib.CodingTheory.Round13BallInter.listAround_codeword_card_eq_one
