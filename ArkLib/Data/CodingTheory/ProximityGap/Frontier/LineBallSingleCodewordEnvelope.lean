/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.CurveAgreementThreshold

/-!
# The line–ball incidence O(n) envelope against a single codeword (#407 survivor #2)

This file proves the **residual** flagged as ATTACK survivor #2 ("Line-ball incidence
`O(n)` (deep-band extra-point)"): the genuine `O(n)` envelope on the per-codeword far-line
incidence, by a **degree-1 / disjoint-fibre** argument — NOT the refuted `±` coset-rigidity
shortcut.

## The object

Fix the smooth multiplicative domain `μ = μ_n = {ζ : ζⁿ = 1}` (or any finite root set with
`0 ∉ μ`), a *line* of polynomials `γ ↦ Q₀ + γ·Q₁` (the far-coset pencil
`epsMCA_ge_far_incidence` reduces to), and a **single fixed codeword** `w = eval(W)` (a single
curve in the codeword family).  The *per-codeword incidence at agreement level `a`* is

  `I_W(a) := #{ γ ∈ F : (Q₀ + γ·Q₁ - W) vanishes on ≥ a points of μ }`.

## The result — the `O(n)` envelope

The key observation that makes this `O(n)` (and dodges the W4/BGK/moment walls entirely) is
that for a **fixed** codeword `W`, the per-coordinate value is *affine in the scalar `γ`*:

  `P_ζ(γ) := Q₁(ζ)·γ + (Q₀(ζ) − W(ζ))`   has degree `≤ 1` in `γ`.

So `curve_agreement_card_le` (the degree-`D` curve list bound) applies at `D = 1`, giving

  `I_W(a) · (a − b) ≤ 1 · n`,    i.e.   `I_W(a) ≤ n / (a − b)`,

where `b = #{ζ : Q₁(ζ) = 0 ∧ Q₀(ζ) = W(ζ)}` is the count of coordinates on which the line is
*constant and already equal to `W`* (the identically-`0` affine slots).  This is the genuine
deep-band extra-point mechanism: when there are `a − b` "moving" agreement coordinates beyond
the constant part, each pins `γ` to at most one value, and a double count over the `≤ n` moving
coordinates yields `I_W(a) ≤ n/(a−b)` — **linear in `n`, independent of `|F|`**.

This is the in-tree handle behind the line-ball O(n) envelope (`epsMCA_ge_far_incidence`):
the full far-line incidence is a union of `I_W` over codewords `W`, and this brick bounds each
term by the resultant-free degree-1 count.  Specializing `Q₁ = Xᵏ` (`0 ∉ μ`, so `Q₁` is the
non-vanishing deep-band direction) gives `b = 0` and the clean `I_W(a) ≤ n/a`.

All results `sorry`-free; the axiom audit at the bottom must read
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset Polynomial

namespace ProximityGap.Frontier.LineBallEnvelope

variable {F : Type*} [Field F]

/-- The affine-in-`γ` per-coordinate polynomial of the line `Q₀ + γ·Q₁` against a fixed
codeword `W`, evaluated at the domain point `ζ`: `P_ζ(γ) = Q₁(ζ)·γ + (Q₀(ζ) − W(ζ))`.
It has degree `≤ 1` in `γ` because `Q₀, Q₁, W` are all evaluated to *constants* at `ζ`. -/
noncomputable def coordPoly (Q0 Q1 W : F[X]) (ζ : F) : Polynomial F :=
  Polynomial.C (Q1.eval ζ) * Polynomial.X + Polynomial.C (Q0.eval ζ - W.eval ζ)

/-- The per-coordinate polynomial has degree `≤ 1` in the scalar variable. -/
theorem coordPoly_natDegree_le (Q0 Q1 W : F[X]) (ζ : F) :
    (coordPoly Q0 Q1 W ζ).natDegree ≤ 1 := by
  unfold coordPoly
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [Nat.max_le]
  refine ⟨?_, ?_⟩
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X]
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1

/-- **The pinning evaluation identity.** `coordPoly Q0 Q1 W ζ` vanishes at the scalar `γ`
iff the line `Q₀ + γ·Q₁` agrees with the codeword `W` at the domain point `ζ`:
`(coordPoly … ζ).eval γ = (Q₀ + γ·Q₁ − W).eval ζ`. -/
theorem coordPoly_eval (Q0 Q1 W : F[X]) (ζ γ : F) :
    (coordPoly Q0 Q1 W ζ).eval γ = (Q0 + Polynomial.C γ * Q1 - W).eval ζ := by
  unfold coordPoly
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub]
  ring

/-- **THE LINE–BALL O(n) ENVELOPE (per single codeword).**
For a line of polynomials `Q₀ + γ·Q₁` over a finite domain `μ`, and a **single fixed**
degree-`<k` codeword `W`, the number of scalars `γ` for which the line agrees with `W` on at
least `a` points of `μ`, times the moving-slack `(a − b)`, is at most `1 · |μ|` — where
`b = #{ζ ∈ μ : Q₁(ζ) = 0 ∧ Q₀(ζ) = W(ζ)}` is the constant-and-agreeing slot count.

This is the genuine deep-band extra-point mechanism: each *moving* agreement coordinate pins
`γ` to a single value (the affine slot is degree `1`), so a double count over the `≤ |μ|`
moving coordinates gives `#bad · (a − b) ≤ |μ|`.  Linear in `n`, independent of `|F|` — no
coset-rigidity, no character sum, just the degree-1 curve list bound. -/
theorem line_ball_single_codeword_card_mul_le
    [Fintype F] [DecidableEq F]
    (Q0 Q1 W : F[X]) (μ : Finset F) {a b : ℕ}
    (hb : (μ.filter (fun ζ => Q1.eval ζ = 0 ∧ Q0.eval ζ = W.eval ζ)).card = b)
    (hab : b < a) :
    (univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + Polynomial.C γ * Q1 - W).eval ζ = 0)).card)).card
        * (a - b)
      ≤ μ.card := by
  classical
  -- Instantiate `curve_agreement_card_le` over the index type `ι := ↥μ` (the subtype),
  -- with the affine-in-`γ` family `P i := coordPoly Q0 Q1 W i.1`.
  let P : (↥μ) → Polynomial F := fun i => coordPoly Q0 Q1 W i.1
  have hdeg : ∀ i, (P i).natDegree ≤ 1 := fun i => coordPoly_natDegree_le Q0 Q1 W i.1
  -- (1) the identically-zero coordinate set: `P i = 0 ↔ Q1(i)=0 ∧ Q0(i)=W(i)`.
  have hzero_iff : ∀ i : (↥μ), P i = 0 ↔ (Q1.eval i.1 = 0 ∧ Q0.eval i.1 = W.eval i.1) := by
    intro i
    constructor
    · intro h0
      have h0' : coordPoly Q0 Q1 W i.1 = 0 := h0
      have hc1 : Q1.eval i.1 = 0 := by
        simpa [coordPoly] using congrArg (fun P : F[X] => P.coeff 1) h0'
      have hc0 : Q0.eval i.1 - W.eval i.1 = 0 := by
        simpa [coordPoly] using congrArg (fun P : F[X] => P.coeff 0) h0'
      exact ⟨hc1, sub_eq_zero.mp hc0⟩
    · rintro ⟨hQ1, hQ0⟩
      have : coordPoly Q0 Q1 W i.1 = 0 := by
        unfold coordPoly; rw [hQ1, hQ0, sub_self]; simp
      exact this
  -- (2) vanishing of `P i` at `γ` ↔ line-agreement with `W` at `i.1`.
  have hev : ∀ (γ : F) (i : ↥μ),
      (P i).eval γ = 0 ↔ (Q0 + Polynomial.C γ * Q1 - W).eval i.1 = 0 := by
    intro γ i
    have : (P i).eval γ = (coordPoly Q0 Q1 W i.1).eval γ := rfl
    rw [this, coordPoly_eval]
  -- subtype filter → base filter, for any predicate on the underlying value.
  have htrans : ∀ (q : F → Prop) [DecidablePred q],
      (univ.filter (fun i : ↥μ => q i.1)).card = (μ.filter q).card := by
    intro q _
    apply Finset.card_bij (fun (i : ↥μ) _ => (i.1 : F))
    · intro i hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_filter.mpr ⟨i.2, hi.2⟩
    · intro i _ j _ h; exact Subtype.ext h
    · intro x hx
      exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
        by simp [(Finset.mem_filter.mp hx).2], rfl⟩
  have hbsub : (univ.filter (fun i : ↥μ => P i = 0)).card = b := by
    have heq : (univ.filter (fun i : ↥μ => P i = 0))
        = (univ.filter (fun i : ↥μ => (Q1.eval i.1 = 0 ∧ Q0.eval i.1 = W.eval i.1))) :=
      Finset.filter_congr (fun i _ => hzero_iff i)
    rw [heq, htrans (fun ζ => Q1.eval ζ = 0 ∧ Q0.eval ζ = W.eval ζ), hb]
  have hcount : ∀ γ : F,
      (univ.filter (fun i : ↥μ => (P i).eval γ = 0)).card
        = (μ.filter (fun ζ => (Q0 + Polynomial.C γ * Q1 - W).eval ζ = 0)).card := by
    intro γ
    have heq : (univ.filter (fun i : ↥μ => (P i).eval γ = 0))
        = (univ.filter (fun i : ↥μ => (Q0 + Polynomial.C γ * Q1 - W).eval i.1 = 0)) :=
      Finset.filter_congr (fun i _ => hev γ i)
    rw [heq, htrans (fun ζ => (Q0 + Polynomial.C γ * Q1 - W).eval ζ = 0)]
  -- apply the curve list bound at D = 1.
  have hmain := curve_agreement_card_le (ι := ↥μ) (F := F) P hdeg hbsub hab
  rw [Fintype.card_coe] at hmain
  have heqHeavy : (univ.filter (fun γ : F =>
        a ≤ (univ.filter (fun i : ↥μ => (P i).eval γ = 0)).card))
      = (univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + Polynomial.C γ * Q1 - W).eval ζ = 0)).card)) :=
    Finset.filter_congr (fun γ _ => by rw [hcount γ])
  rw [← heqHeavy]
  exact le_trans hmain (by rw [one_mul])

/-- **Explicit O(n) form.** `#bad ≤ |μ| / (a − b)` — the per-codeword line-ball incidence is
linear in `n = |μ|` and independent of `|F|`. -/
theorem line_ball_single_codeword_card_le
    [Fintype F] [DecidableEq F]
    (Q0 Q1 W : F[X]) (μ : Finset F) {a b : ℕ}
    (hb : (μ.filter (fun ζ => Q1.eval ζ = 0 ∧ Q0.eval ζ = W.eval ζ)).card = b)
    (hab : b < a) :
    (univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + Polynomial.C γ * Q1 - W).eval ζ = 0)).card)).card
      ≤ μ.card / (a - b) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact line_ball_single_codeword_card_mul_le Q0 Q1 W μ hb hab

/-- **Deep-band specialization (`Q₁ = Xᵏ`, `0 ∉ μ`).** For the deep-band single-pencil
direction `Q₁ = Xᵏ` (`k ≥ 1`, so `Xᵏ` never vanishes on the zero-excluding domain `μ`), the
constant-slot count `b = 0`, so the per-codeword line-ball incidence is the clean envelope
`#bad ≤ |μ| / a` — linear in `n`, independent of `|F|`.  This is the `O(n)` line-ball
incidence the deep-band δ\* attack needs, proven by the degree-1 / disjoint-fibre mechanism
(no `±` coset rigidity). -/
theorem deep_band_line_ball_card_le
    [Fintype F] [DecidableEq F]
    (Q0 W : F[X]) (μ : Finset F) (k a : ℕ) (_hk : 1 ≤ k) (ha : 1 ≤ a) (hμ0 : (0 : F) ∉ μ) :
    (univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + Polynomial.C γ * X ^ k - W).eval ζ = 0)).card)).card
      ≤ μ.card / a := by
  classical
  have hb : (μ.filter (fun ζ => (X ^ k : F[X]).eval ζ = 0 ∧ Q0.eval ζ = W.eval ζ)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ζ hζ
    rintro ⟨hev, -⟩
    rw [eval_pow, eval_X] at hev
    exact pow_ne_zero k (fun h => hμ0 (h ▸ hζ)) hev
  have h := line_ball_single_codeword_card_le Q0 (X ^ k) W μ hb (Nat.succ_le_iff.mp ha)
  simpa using h

end ProximityGap.Frontier.LineBallEnvelope

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]` only) -/
#print axioms ProximityGap.Frontier.LineBallEnvelope.coordPoly_natDegree_le
#print axioms ProximityGap.Frontier.LineBallEnvelope.coordPoly_eval
#print axioms ProximityGap.Frontier.LineBallEnvelope.line_ball_single_codeword_card_mul_le
#print axioms ProximityGap.Frontier.LineBallEnvelope.line_ball_single_codeword_card_le
#print axioms ProximityGap.Frontier.LineBallEnvelope.deep_band_line_ball_card_le
