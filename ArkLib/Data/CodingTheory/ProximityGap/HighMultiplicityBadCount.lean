/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# High-multiplicity bad-scalar counting on an affine error line (face (iv) sharpening, #389)

`BadGammaAffineCount.lean` proves the *unique-decoding-regime* bound: the scalars `γ` for which
`e₀ + γ·e₁` vanishes at **at least one** coordinate of `supp e₁` number `≤ weight(e₁)`
(`badGamma_affine_card_le`).  That `∃`-bound is the right object below the unique-decoding radius,
but the **mutual-correlated-agreement window** (`δ` past Johnson) needs the dual count: scalars
`γ` for which `e₀ + γ·e₁` vanishes at **many** coordinates (high agreement = low weight).  This
file supplies that sharper, dual bound — the genuine face-(iv) line–ball incidence engine — by a
clean double-count / pigeonhole, and isolates the *degree-collapse* lever it exposes.

Fix `e₀, e₁ : ι → F`.  For each scalar `γ`, the **multiplicity**
`mult(γ) = #{ i : e₁ i ≠ 0 ∧ e₀ i + γ·e₁ i = 0 }` is the number of support coordinates where the
line word `e₀ + γ·e₁` vanishes (each such `i` pins the unique root `γ = −e₀ i / e₁ i`).  Then:

* `sum_mult_eq_weight` — **the conservation law**: `∑_γ mult(γ) = weight(e₁)`.  Each support
  coordinate contributes its single root to exactly one `γ`.
* `card_highMult_mul_le` / `card_highMult_le` — **pigeonhole**: at most `weight(e₁) / μ₀` scalars
  achieve multiplicity `≥ μ₀`.  Precisely, `μ₀ · #{γ : mult(γ) ≥ μ₀} ≤ weight(e₁)`.
* `highMult_empty_of_lt` — **the degree-collapse lever**: if every multiplicity is `≤ D` (e.g.
  `D` = the degree of the ratio rational function `i ↦ −e₀ i / e₁ i` on a structured domain), then
  `μ₀ > D ⟹ no scalar has multiplicity ≥ μ₀`.  This is the face-(iv) vanishing criterion: when the
  required agreement exceeds the ratio-function degree, the per-codeword-pair bad set is empty.

These are bounds **per fixed error line** `(e₀, e₁)` — i.e. per pair of nearby codewords.  Summed
over the list of codeword pairs within the radius they give the bad-scalar count; that list size is
the open sub-Johnson supply core (this file does NOT bound it).  The machinery here is the
elementary, unconditional, reusable incidence layer the list bound multiplies against.  See
`docs/kb/deltastar-literature-findings-2026-06-13.md` (faces (iii)/(iv), the ratio-multiplicity
route) and `FarCosetExplosion.lean` (`epsMCA_ge_far_incidence`).
-/

open Finset

namespace ArkLib.ProximityGap.HighMultiplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **multiplicity** of a scalar `γ` on the affine error line `e₀ + γ·e₁`: the number of
support coordinates of `e₁` where the line word vanishes.  Each such coordinate forces the unique
root `γ = −e₀ i / e₁ i`, so `mult` measures the agreement of `e₀ + γ·e₁` with the zero word on
`supp e₁`. -/
def mult (e₀ e₁ : ι → F) (γ : F) : ℕ :=
  (univ.filter (fun i => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card

omit [Fintype ι] [DecidableEq ι] in
/-- For a fixed support coordinate `i` with `e₁ i ≠ 0`, exactly one scalar `γ` makes the line word
vanish at `i`, namely the root `γ = −e₀ i / e₁ i`. -/
theorem card_root_eq_one {e₀ e₁ : ι → F} {i : ι} (hi : e₁ i ≠ 0) :
    (univ.filter (fun γ : F => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card = 1 := by
  rw [card_eq_one]
  refine ⟨-e₀ i / e₁ i, ?_⟩
  ext γ
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rw [eq_div_iff hi]
    linear_combination h
  · rintro rfl
    refine ⟨hi, ?_⟩
    field_simp
    ring

omit [DecidableEq ι] in
/-- **Conservation law.**  Summed over all scalars, the multiplicity totals the Hamming weight of
`e₁`: `∑_γ mult(γ) = weight(e₁)`.  Each of the `weight(e₁)` support coordinates contributes its
single root to exactly one scalar. -/
theorem sum_mult_eq_weight (e₀ e₁ : ι → F) :
    ∑ γ : F, mult e₀ e₁ γ = (univ.filter (fun i => e₁ i ≠ 0)).card := by
  classical
  simp only [mult, card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : e₁ i ≠ 0
  · rw [if_pos hi, ← card_filter, card_root_eq_one hi]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro γ _
    rw [if_neg (fun h => hi h.1)]

omit [DecidableEq ι] in
/-- **Pigeonhole (multiplicative form).**  `μ₀ · #{γ : mult(γ) ≥ μ₀} ≤ weight(e₁)`. -/
theorem card_highMult_mul_le (e₀ e₁ : ι → F) (μ₀ : ℕ) :
    μ₀ * (univ.filter (fun γ : F => μ₀ ≤ mult e₀ e₁ γ)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := by
  classical
  rw [← sum_mult_eq_weight e₀ e₁]
  calc μ₀ * (univ.filter (fun γ : F => μ₀ ≤ mult e₀ e₁ γ)).card
      = (univ.filter (fun γ : F => μ₀ ≤ mult e₀ e₁ γ)).card • μ₀ := by
        rw [smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ univ.filter (fun γ : F => μ₀ ≤ mult e₀ e₁ γ), mult e₀ e₁ γ :=
        Finset.card_nsmul_le_sum _ _ _ (fun γ hγ => (mem_filter.mp hγ).2)
    _ ≤ ∑ γ : F, mult e₀ e₁ γ :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

omit [DecidableEq ι] in
/-- **The degree-collapse lever.**  If every scalar's multiplicity is `≤ D` — for instance `D` =
the degree of the ratio rational function `i ↦ −e₀ i / e₁ i` restricted to a structured evaluation
domain, whose level sets are root sets — then requiring multiplicity `> D` leaves **no** bad
scalar.  Equivalently: once the demanded agreement exceeds the ratio-function degree, the per-pair
bad set is empty. -/
theorem highMult_empty_of_lt (e₀ e₁ : ι → F) {D μ₀ : ℕ}
    (hD : ∀ γ : F, mult e₀ e₁ γ ≤ D) (hμ : D < μ₀) :
    univ.filter (fun γ : F => μ₀ ≤ mult e₀ e₁ γ) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro γ _
  exact fun hge => absurd (lt_of_lt_of_le hμ hge) (not_lt.mpr (hD γ))

/-! ### Bridge to Hamming weight: the multiplicity *is* the agreement deficit

The bad-scalar event for mutual correlated agreement is phrased by weight: `γ` is bad when the
line word `e₀ + γ·e₁` has *low* weight (high agreement with the code, after subtracting the nearby
codeword pair).  These lemmas turn the abstract multiplicity into that weight, making the
pigeonhole bound a genuine bad-scalar-by-weight bound — with no dependence on the
`{e₁ = 0 ∧ e₀ = 0}` count (it cancels). -/

omit [DecidableEq ι] [Fintype F] in
/-- **Exact affine-line weight decomposition.**  For every scalar `γ`, the line-word weight plus
the root multiplicity on `supp e₁` is constant:

`weight(e₀ + γ·e₁) + mult(γ) = weight(e₁) + #{i : e₁ i = 0 ∧ e₀ i ≠ 0}`.

On coordinates where `e₁ ≠ 0`, each position contributes either to the root multiplicity or to
the line weight, but not both; on coordinates where `e₁ = 0`, the line contributes exactly the
fixed `e₀ ≠ 0` positions. This is the ratio-census identity behind the high-multiplicity
incidence bounds below. -/
theorem weightLine_add_mult_eq_weightE1_add_zeroE1Nonzero (e₀ e₁ : ι → F) (γ : F) :
    (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card + mult e₀ e₁ γ =
      (univ.filter (fun i => e₁ i ≠ 0)).card +
        (univ.filter (fun i => e₁ i = 0 ∧ e₀ i ≠ 0)).card := by
  classical
  let Z : Finset ι := univ.filter (fun i => e₁ i = 0 ∧ e₀ i ≠ 0)
  let S : Finset ι := univ.filter (fun i => e₁ i ≠ 0)
  let R : Finset ι := univ.filter (fun i => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)
  let NZ : Finset ι := univ.filter (fun i => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i ≠ 0)
  have hline : univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0) = Z ∪ NZ := by
    ext i
    by_cases h1 : e₁ i = 0
    · simp [Z, NZ, h1]
    · simp [Z, NZ, h1]
  have hdisj_line : Disjoint Z NZ := by
    rw [Finset.disjoint_left]
    intro i hiZ hiNZ
    have hz : e₁ i = 0 ∧ e₀ i ≠ 0 := by simpa [Z] using hiZ
    have hnz : e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i ≠ 0 := by simpa [NZ] using hiNZ
    exact hnz.1 hz.1
  have hS : S = R ∪ NZ := by
    ext i
    by_cases hzero : e₀ i + γ * e₁ i = 0
    · simp [S, R, NZ, hzero]
    · simp [S, R, NZ, hzero]
  have hdisj_S : Disjoint R NZ := by
    rw [Finset.disjoint_left]
    intro i hiR hiNZ
    have hr : e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 := by simpa [R] using hiR
    have hnz : e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i ≠ 0 := by simpa [NZ] using hiNZ
    exact hnz.2 hr.2
  have hlinecard : (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card =
      Z.card + NZ.card := by
    rw [hline, Finset.card_union_of_disjoint hdisj_line]
  have hScard : S.card = R.card + NZ.card := by
    rw [hS, Finset.card_union_of_disjoint hdisj_S]
  change (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card + R.card = S.card + Z.card
  rw [hlinecard, hScard]
  ac_rfl

omit [DecidableEq ι] [Fintype F] in
/-- **The agreement identity (one inequality).**  The weight of `e₁` is at most the multiplicity
plus the weight of the line word: `weight(e₁) ≤ mult(γ) + weight(e₀ + γ·e₁)`.  Within `supp e₁`,
every coordinate is either a root of the line word (counted by `mult`) or a nonzero of the line
word (counted by its weight).  The `{e₁ = 0}` coordinates drop out entirely. -/
theorem weight_e1_le_mult_add_weightLine (e₀ e₁ : ι → F) (γ : F) :
    (univ.filter (fun i => e₁ i ≠ 0)).card
      ≤ mult e₀ e₁ γ + (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card := by
  classical
  have hsplit :
      (univ.filter (fun i => e₁ i ≠ 0)).card
        = ((univ.filter (fun i => e₁ i ≠ 0)).filter
              (fun i => e₀ i + γ * e₁ i = 0)).card
          + ((univ.filter (fun i => e₁ i ≠ 0)).filter
              (fun i => ¬ (e₀ i + γ * e₁ i = 0))).card :=
    (Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun i => e₁ i ≠ 0)) (fun i => e₀ i + γ * e₁ i = 0)).symm
  rw [hsplit, Finset.filter_filter, Finset.filter_filter]
  have hmult : (univ.filter (fun i => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card = mult e₀ e₁ γ := rfl
  rw [hmult]
  refine Nat.add_le_add_left ?_ _
  apply Finset.card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.2

omit [DecidableEq ι] [Fintype F] in
/-- **Bad-by-weight ⟹ high multiplicity.**  If the line word `e₀ + γ·e₁` has weight `≤ w`, then its
multiplicity is at least `weight(e₁) − w`.  Hence the bad-by-weight scalars sit inside the
high-multiplicity set with threshold `μ₀ = weight(e₁) − w`. -/
theorem weightLine_le_imp_highMult (e₀ e₁ : ι → F) (w : ℕ) (γ : F)
    (hw : (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card ≤ w) :
    (univ.filter (fun i => e₁ i ≠ 0)).card - w ≤ mult e₀ e₁ γ := by
  have h := weight_e1_le_mult_add_weightLine e₀ e₁ γ
  omega

omit [DecidableEq ι] in
/-- **The bad-scalar-by-weight bound (per error line).**  Writing `s = weight(e₁)` and
`μ₀ = s − w > 0`, the scalars `γ` for which the line word `e₀ + γ·e₁` has weight `≤ w` number at
most `s / μ₀`: precisely, `(s − w) · #{γ : weight(e₀+γ·e₁) ≤ w} ≤ s`.  This is the pigeonhole
incidence bound in directly consumable, weight-phrased form — the per-codeword-pair bad-scalar
count for mutual correlated agreement.  Summed over the in-window codeword list it yields the
total bad-scalar count; that list size is the open sub-Johnson supply core. -/
theorem badWeight_card_mul_le (e₀ e₁ : ι → F) (w : ℕ) :
    ((univ.filter (fun i => e₁ i ≠ 0)).card - w)
        * (univ.filter (fun γ : F =>
            (univ.filter (fun i => e₀ i + γ * e₁ i ≠ 0)).card ≤ w)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := by
  classical
  set s := (univ.filter (fun i => e₁ i ≠ 0)).card with hs
  refine le_trans ?_ (card_highMult_mul_le e₀ e₁ (s - w))
  refine Nat.mul_le_mul_left _ ?_
  apply Finset.card_le_card
  intro γ hγ
  simp only [mem_filter, mem_univ, true_and] at hγ ⊢
  exact weightLine_le_imp_highMult e₀ e₁ w γ hγ

#print axioms weightLine_add_mult_eq_weightE1_add_zeroE1Nonzero

end ArkLib.ProximityGap.HighMultiplicity
