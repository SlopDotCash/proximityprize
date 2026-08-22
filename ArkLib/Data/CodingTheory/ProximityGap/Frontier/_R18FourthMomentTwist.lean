/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16LegendreCosetFace
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17QuadrupleWeilRung

/-!
# LANE WEILFORM (#466 round 18): FourthMomentTwistBound reduced to ONE named per-tuple Weil input

Round 17 (`_R17QuadrupleWeilRung.lean`) consumed `∑_t |T_χ(t)|⁴ ≤ 6n²p` as "textbook Weil".
This file determines EXACTLY what Weil-type statement that is, and proves the reduction
axiom-clean: the fourth-moment bound follows from a **per-nondegenerate-quadruple** complete
character-sum bound `‖∑_s χ(s−x₁)χ(s−x₂)·conj(χ(s−y₁))conj(χ(s−y₂))‖ ≤ 3√p`, with the
degenerate quadruples handled UNCONDITIONALLY (trivial `≤ p` per tuple, count `≤ 3n²`).

## (a) The exact Weil statement needed

Expanding `∑_s |T_χ(s)|⁴` over quadruples `(x₁,x₂,y₁,y₂) ∈ G⁴` gives per quadruple the
complete sum `S(x,y) = ∑_s χ((s−x₁)(s−x₂))·conj(χ((s−y₁)(s−y₂)))`.  For `χ` of order `d`
this is `∑_s χ(f(s))` with `f = (s−x₁)(s−x₂)(s−y₁)^{d−1}(s−y₂)^{d−1}`; Weil gives
`|S| ≤ (m−1)√p`, `m ≤ 4` the distinct-root count of the d-th-power-free kernel, PROVIDED
`f` is not a perfect d-th power.  For `d = 2` (quadratic χ, the deg=2 face) the degeneracy
is exactly "all root multiplicities of `(s−x₁)(s−x₂)(s−y₁)(s−y₂)` even", i.e.

  `IsDegenerate ⟺ {x₁,x₂} = {y₁,y₂} (as multisets) ∨ (x₁ = x₂ ∧ y₁ = y₂)`,

the three-clause predicate below.  Probe (`probe_r18_fourthmoment_twist.py`, n = 8/16,
p = 41…786433, FULL per-tuple check at 9 cells incl. p = 4129 ≥ n⁴):
* classification EXACT: degenerate tuples give `S = p−1` (all four equal) or `p−2` (else);
  every nondegenerate tuple has `|S| ≤ 1.95√p < 3√p` (constant 3 never tight — the generic
  tuple is the 4-distinct-root genus-1 case, Hasse `≈ 2√p`);
* degenerate total `= n(p−1) + 3n(n−1)(p−2)` exactly at every cell;
* `∑_s |T|⁴/(n²p) ∈ [2.5, 3.0]` for `p ≥ n⁴` — the constant 6 has ≈2× room.

## (b) Mathlib audit (verified by grep, 2026-07-07)

`grep -rn "Weil" .lake/packages/mathlib/Mathlib/NumberTheory/` → nothing.  Mathlib has
`quadraticChar_sum_zero`, Gauss sums, Dirichlet orthogonality — but NO complete character
sum of a polynomial of degree ≥ 2 (not even `∑_x χ(x²+bx+c)`) and no Hasse–Weil bound in
any form (nothing in `FieldTheory/Finite` or `AlgebraicGeometry`).  Campaign belief
CONFIRMED.  The quadratic-polynomial case IS in-tree
(`_R17TchiMomentIdentities.sum_mulChar_mul_conj_shift` = `∑_a χ(a²+ab) = −1` in disguise);
the quartic case is genus 1 = Hasse for elliptic curves, absent from Mathlib.

## (c) The elementary-average escape: REFUTED

The hoped-for wall-free discharge — `∑_s|T_χ|⁴` exactly expressible in the PROVEN
Problem-A energy `E₂(μ_n)` for quadratic χ — is numerically REFUTED:
`(∑|T|⁴ − degenerate)/E₂(μ_n)` takes values `−325.0, −37.0, −32.5, −19.6, +1.8, +3.1,
+12.9, +79.0, +223.6` across the probe cells (sign-varying, unbounded) — no exact relation
of any fixed shape.  The additive-Fourier route turns `∑_s|T|⁴` into a χ-TWISTED additive
energy of the η-weights (`(1/p)∑_{c₁+c₃=c₂+c₄} χ(c₁c₂c₃c₄)·ηηηη`), which is NOT `E₂(μ_n)`;
dropping the twist by triangle inequality loses the cancellation.  The Weil input is
genuinely load-bearing.

## PROVEN here (axiom-clean)

* `IsDegenerate` + `card_filter_degenerate_le`: at most `3n²` degenerate quadruples.
* `norm_quadTerm_le_card`: trivial `≤ p` per quadruple; `quadTerm_pair_diag`: the
  pairing-diagonal value is EXACTLY `p − 2` — the degenerate layer genuinely carries mass
  `≈ 3n²p`, so the entire slack of the constant 6 sits in the Weil constant 3.
* `QuarticWeilInput` (the NAMED open input) and the reduction
  `fourthMoment_le_of_quarticWeilInput`:
  `QuarticWeilInput χ G → |G|⁴ ≤ p → ∑_s ‖T_χ(s)‖⁴ ≤ 6·|G|²·p`,
  plus the deleted-offset corollary `fourthMomentAway_le_of_quarticWeilInput` (the form
  `_R17QuadrupleWeilRung` consumes, `D = {0} ∪ μ_n`).

No closure claimed: `QuarticWeilInput` is Hasse for genus ≤ 1 — true mathematics, absent
from Mathlib, now the SINGLE named formalization gap of the r=2 Weil lane.
Issue #466, round 18, WEILFORM lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R18FourthMomentTwist

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Unit-circle ingredients (self-contained; the R17 import chain is deliberately avoided) -/

/-- Values of a multiplicative character into ℂ at nonzero arguments lie on the unit
circle. -/
theorem mulChar_mul_conj (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * conj' (χ a) = 1 := by
  have hpow : χ a ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  have hcard : Fintype.card F - 1 ≠ 0 := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hnorm : ‖χ a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hcard
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]

/-- `‖χ u‖ ≤ 1` everywhere (`= 0` at nonunits, `= 1` at units). -/
theorem norm_mulChar_le_one (χ : MulChar F ℂ) (u : F) : ‖χ u‖ ≤ 1 := by
  by_cases hu : u = 0
  · rw [hu, χ.map_nonunit (by simp)]; simp
  · have hpow : χ u ^ (Fintype.card F - 1) = 1 := by
      rw [← map_pow, FiniteField.pow_card_sub_one_eq_one u hu, map_one]
    have hcard : Fintype.card F - 1 ≠ 0 := by
      have h2 : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    exact le_of_eq (Complex.norm_eq_one_of_pow_eq_one hpow hcard)

/-! ## The quadruple layer -/

/-- The complete character sum of one quadruple `z = ((x₁,x₂),(y₁,y₂))`:
`S(z) = ∑_s χ(s−x₁)·χ(s−x₂)·conj(χ(s−y₁))·conj(χ(s−y₂))`.  For `χ` of order `d` this is
`∑_s χ(f(s))`, `f = (s−x₁)(s−x₂)(s−y₁)^{d−1}(s−y₂)^{d−1}`. -/
noncomputable def quadTerm (χ : MulChar F ℂ) (z : (F × F) × (F × F)) : ℂ :=
  ∑ s : F, (χ (s - z.1.1) * χ (s - z.1.2))
    * (conj' (χ (s - z.2.1)) * conj' (χ (s - z.2.2)))

/-- **The exact d=2 Weil-degeneracy predicate**: `(s−x₁)(s−x₂)(s−y₁)(s−y₂)` is a perfect
square iff all root multiplicities are even iff (multiset `{x₁,x₂} = {y₁,y₂}`) or
(`x₁ = x₂ ∧ y₁ = y₂`): `y = x` as pairs, or `y = swap x`, or both pairs diagonal. -/
def IsDegenerate (z : (F × F) × (F × F)) : Prop :=
  (z.1.1 = z.2.1 ∧ z.1.2 = z.2.2) ∨ (z.1.1 = z.2.2 ∧ z.1.2 = z.2.1)
    ∨ (z.1.1 = z.1.2 ∧ z.2.1 = z.2.2)

instance moduleInstance_R18FourthMomentTwist_1 : DecidablePred (IsDegenerate (F := F)) := fun z => by
  unfold IsDegenerate; infer_instance

/-- **THE NAMED OPEN INPUT (Weil/Hasse for genus ≤ 1; absent from Mathlib, docstring (b))**:
every NONdegenerate quadruple has complete sum `≤ 3√p`.  Probe max observed: `1.95√p`. -/
def QuarticWeilInput (χ : MulChar F ℂ) (G : Finset F) : Prop :=
  ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z →
    ‖quadTerm χ z‖ ≤ 3 * Real.sqrt (Fintype.card F)

/-- Trivial bound: every quadruple sum has norm at most `p`. -/
theorem norm_quadTerm_le_card (χ : MulChar F ℂ) (z : (F × F) × (F × F)) :
    ‖quadTerm χ z‖ ≤ (Fintype.card F : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ s : F, ‖(χ (s - z.1.1) * χ (s - z.1.2))
      * (conj' (χ (s - z.2.1)) * conj' (χ (s - z.2.2)))‖ ≤ 1 := by
    intro s
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have h12 : ‖χ (s - z.1.1)‖ * ‖χ (s - z.1.2)‖ ≤ 1 :=
      mul_le_one₀ (norm_mulChar_le_one χ _) (norm_nonneg _) (norm_mulChar_le_one χ _)
    have h34 : ‖χ (s - z.2.1)‖ * ‖χ (s - z.2.2)‖ ≤ 1 :=
      mul_le_one₀ (norm_mulChar_le_one χ _) (norm_nonneg _) (norm_mulChar_le_one χ _)
    exact mul_le_one₀ h12 (by positivity) h34
  calc ∑ s : F, ‖(χ (s - z.1.1) * χ (s - z.1.2))
        * (conj' (χ (s - z.2.1)) * conj' (χ (s - z.2.2)))‖
      ≤ ∑ _s : F, (1 : ℝ) := Finset.sum_le_sum fun s _ => h1 s
    _ = (Fintype.card F : ℝ) := by simp

/-- **Exact pairing-diagonal value**: for `x₁ ≠ x₂` the degenerate quadruple
`((x₁,x₂),(x₁,x₂))` has `quadTerm = p − 2` EXACTLY — the degenerate layer genuinely carries
its full trivial mass (the `≤ p` bound is tight up to `O(1)`). -/
theorem quadTerm_pair_diag (χ : MulChar F ℂ) {x₁ x₂ : F} (h : x₁ ≠ x₂) :
    quadTerm χ ((x₁, x₂), (x₁, x₂)) = (Fintype.card F : ℂ) - 2 := by
  classical
  have hpt : ∀ s : F, (χ (s - x₁) * χ (s - x₂)) * (conj' (χ (s - x₁)) * conj' (χ (s - x₂)))
      = if s ∈ ({x₁, x₂} : Finset F) then 0 else 1 := by
    intro s
    by_cases hs : s ∈ ({x₁, x₂} : Finset F)
    · rw [if_pos hs]
      rcases Finset.mem_insert.mp hs with hs1 | hs2
      · rw [hs1, sub_self, χ.map_nonunit (show ¬ IsUnit (0 : F) by simp)]; simp
      · rw [Finset.mem_singleton.mp hs2, sub_self,
          χ.map_nonunit (show ¬ IsUnit (0 : F) by simp)]
        simp
    · rw [if_neg hs]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      push_neg at hs
      have h1 : s - x₁ ≠ 0 := sub_ne_zero.mpr hs.1
      have h2 : s - x₂ ≠ 0 := sub_ne_zero.mpr hs.2
      calc (χ (s - x₁) * χ (s - x₂)) * (conj' (χ (s - x₁)) * conj' (χ (s - x₂)))
          = (χ (s - x₁) * conj' (χ (s - x₁))) * (χ (s - x₂) * conj' (χ (s - x₂))) := by ring
        _ = 1 := by rw [mulChar_mul_conj χ h1, mulChar_mul_conj χ h2, one_mul]
  have hcardpair : ({x₁, x₂} : Finset F).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
  have h2le : 2 ≤ Fintype.card F := by
    haveI : Nontrivial F := ⟨⟨x₁, x₂, h⟩⟩
    exact Fintype.one_lt_card
  unfold quadTerm
  rw [Finset.sum_congr rfl fun s _ => hpt s, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, smul_zero, zero_add, nsmul_eq_mul, mul_one]
  have hcount : (Finset.univ.filter (fun s => s ∉ ({x₁, x₂} : Finset F))).card
      = Fintype.card F - 2 := by
    have hfilter : Finset.univ.filter (fun s => s ∈ ({x₁, x₂} : Finset F))
        = ({x₁, x₂} : Finset F) := by
      ext s; simp
    have hsum :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset F)) (p := fun s => s ∈ ({x₁, x₂} : Finset F))
    rw [hfilter, hcardpair, Finset.card_univ] at hsum
    omega
  rw [hcount, Nat.cast_sub h2le]
  norm_num

/-! ## The exact expansion of the fourth moment into the quadruple layer -/

/-- Pointwise: `‖T_χ(s)‖⁴` (cast to ℂ) equals `T² · conj(T²)`. -/
theorem norm_pow_four_eq (χ : MulChar F ℂ) (G : Finset F) (s : F) :
    ((‖shiftedCharSum χ G s‖ ^ 4 : ℝ) : ℂ)
      = (shiftedCharSum χ G s) ^ 2 * conj' ((shiftedCharSum χ G s) ^ 2) := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, norm_pow]
  ring

/-- **Exact expansion**: the fourth moment equals the sum of the quadruple complete sums.
This is the interchange `∑_s ∑_{quadruples} = ∑_{quadruples} ∑_s`, exact, no analysis. -/
theorem fourthMoment_expand (χ : MulChar F ℂ) (G : Finset F) :
    ((∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 : ℝ) : ℂ)
      = ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), quadTerm χ z := by
  classical
  push_cast
  have hsq : ∀ s : F, (shiftedCharSum χ G s) ^ 2
      = ∑ a ∈ G ×ˢ G, χ (s - a.1) * χ (s - a.2) := by
    intro s
    rw [Finset.sum_product, pow_two]
    unfold shiftedCharSum
    rw [Finset.sum_mul_sum]
  have hconj : ∀ s : F, conj' ((shiftedCharSum χ G s) ^ 2)
      = ∑ b ∈ G ×ˢ G, conj' (χ (s - b.1)) * conj' (χ (s - b.2)) := by
    intro s
    rw [hsq s, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [map_mul]
  have hpt : ∀ s : F, ((‖shiftedCharSum χ G s‖ ^ 4 : ℝ) : ℂ)
      = ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G),
          (χ (s - z.1.1) * χ (s - z.1.2))
            * (conj' (χ (s - z.2.1)) * conj' (χ (s - z.2.2))) := by
    intro s
    rw [norm_pow_four_eq χ G s, hconj s, hsq s, Finset.sum_mul_sum, ← Finset.sum_product']
  calc (∑ s : F, (‖shiftedCharSum χ G s‖ ^ 4 : ℂ))
      = ∑ s : F, ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G),
          (χ (s - z.1.1) * χ (s - z.1.2))
            * (conj' (χ (s - z.2.1)) * conj' (χ (s - z.2.2))) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        have := hpt s
        push_cast at this
        exact this
    _ = ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), quadTerm χ z := Finset.sum_comm

/-! ## The degenerate count -/

/-- The degenerate quadruples are covered by three explicit images of `G × G`. -/
theorem filter_degenerate_subset (G : Finset F) :
    ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter IsDegenerate
      ⊆ ((G ×ˢ G).image (fun a => (a, a)))
        ∪ ((G ×ˢ G).image (fun a => (a, (a.2, a.1))))
        ∪ ((G ×ˢ G).image (fun a => ((a.1, a.1), (a.2, a.2)))) := by
  intro z hz
  obtain ⟨hzQ, hdeg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzQ
  obtain ⟨h11, h12⟩ := Finset.mem_product.mp hz1
  obtain ⟨h21, h22⟩ := Finset.mem_product.mp hz2
  rcases hdeg with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    refine Finset.mem_image.mpr ⟨z.1, hz1, ?_⟩
    exact Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨ha, hb⟩⟩
  · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    refine Finset.mem_image.mpr ⟨z.1, hz1, ?_⟩
    exact Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨hb, ha⟩⟩
  · refine Finset.mem_union_right _ ?_
    refine Finset.mem_image.mpr ⟨(z.1.1, z.2.1), Finset.mem_product.mpr ⟨h11, h21⟩, ?_⟩
    exact Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨rfl, ha⟩, Prod.ext_iff.mpr ⟨rfl, hb⟩⟩

/-- At most `3n²` degenerate quadruples. -/
theorem card_filter_degenerate_le (G : Finset F) :
    (((G ×ˢ G) ×ˢ (G ×ˢ G)).filter IsDegenerate).card ≤ 3 * G.card ^ 2 := by
  refine le_trans (Finset.card_le_card (filter_degenerate_subset G)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h3 : ((G ×ˢ G).image (fun a : F × F => ((a.1, a.1), (a.2, a.2)))).card
      ≤ G.card ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_product]; ring_nf; omega
  have h12 : (((G ×ˢ G).image (fun a : F × F => (a, a)))
      ∪ ((G ×ˢ G).image (fun a : F × F => (a, (a.2, a.1))))).card ≤ 2 * G.card ^ 2 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have ha : ((G ×ˢ G).image (fun a : F × F => (a, a))).card ≤ G.card ^ 2 := by
      refine le_trans (Finset.card_image_le) ?_
      rw [Finset.card_product]; ring_nf; omega
    have hb : ((G ×ˢ G).image (fun a : F × F => (a, (a.2, a.1)))).card ≤ G.card ^ 2 := by
      refine le_trans (Finset.card_image_le) ?_
      rw [Finset.card_product]; ring_nf; omega
    omega
  omega

/-! ## The main reduction -/

/-- **THE ROUND-18 REDUCTION**: the FourthMomentTwistBound
`∑_s ‖T_χ(s)‖⁴ ≤ 6·|G|²·p` holds for `p ≥ |G|⁴` GIVEN the named per-tuple Weil input.
Split: degenerate tuples (≤ `3n²` of them) at the trivial `≤ p`; nondegenerate tuples
(≤ `n⁴`) at Weil `3√p`, and `3n⁴√p ≤ 3n²p` exactly when `n⁴ ≤ p`. -/
theorem fourthMoment_le_of_quarticWeilInput (χ : MulChar F ℂ) (G : Finset F)
    (hW : QuarticWeilInput χ G)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  classical
  set Q : Finset ((F × F) × (F × F)) := (G ×ˢ G) ×ˢ (G ×ˢ G) with hQ
  set p : ℝ := (Fintype.card F : ℝ) with hpdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hp0 : 0 ≤ p := by positivity
  have hn0 : 0 ≤ n := by positivity
  -- Step 1: the moment is the norm of its own complexification
  have hnn : 0 ≤ ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hstep1 : ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      = ‖((∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  -- Step 2: expansion + triangle inequality
  have hstep2 : ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 ≤ ∑ z ∈ Q, ‖quadTerm χ z‖ := by
    rw [hstep1, fourthMoment_expand χ G]
    exact norm_sum_le _ _
  -- Step 3: split degenerate / nondegenerate
  have hsplit : ∑ z ∈ Q, ‖quadTerm χ z‖
      = ∑ z ∈ Q.filter IsDegenerate, ‖quadTerm χ z‖
        + ∑ z ∈ Q.filter (fun z => ¬ IsDegenerate z), ‖quadTerm χ z‖ :=
    (Finset.sum_filter_add_sum_filter_not Q IsDegenerate _).symm
  -- degenerate: each ≤ p, count ≤ 3n²
  have hdeg : ∑ z ∈ Q.filter IsDegenerate, ‖quadTerm χ z‖ ≤ 3 * n ^ 2 * p := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ p
      (fun z _ => norm_quadTerm_le_card χ z)) ?_
    rw [nsmul_eq_mul]
    have hcount : ((Q.filter IsDegenerate).card : ℝ) ≤ 3 * n ^ 2 := by
      have := card_filter_degenerate_le G
      rw [hndef]
      exact_mod_cast this
    nlinarith [hcount, hp0]
  -- nondegenerate: each ≤ 3√p (the Weil input), count ≤ n⁴
  have hnondeg : ∑ z ∈ Q.filter (fun z => ¬ IsDegenerate z), ‖quadTerm χ z‖
      ≤ n ^ 4 * (3 * Real.sqrt p) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (3 * Real.sqrt p)
      (fun z hz => ?_)) ?_
    · obtain ⟨hzQ, hzn⟩ := Finset.mem_filter.mp hz
      exact hW z hzQ hzn
    · rw [nsmul_eq_mul]
      have hcQ : (Q.card : ℝ) = n ^ 4 := by
        rw [hQ, Finset.card_product, Finset.card_product, hndef]
        push_cast; ring
      have hcle : ((Q.filter (fun z => ¬ IsDegenerate z)).card : ℝ) ≤ n ^ 4 := by
        rw [← hcQ]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hsq0 : 0 ≤ 3 * Real.sqrt p := by positivity
      nlinarith [hcle, hsq0]
  -- Step 4: arithmetic — 3n²p + 3n⁴√p ≤ 6n²p when n⁴ ≤ p
  have hn2sq : n ^ 2 ≤ Real.sqrt p := by
    have h1 : Real.sqrt (n ^ 4) ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
    have hn20 : 0 ≤ n ^ 2 := sq_nonneg n
    rwa [show n ^ 4 = (n ^ 2) ^ 2 by ring, Real.sqrt_sq hn20] at h1
  have hsqmul : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  have hsqnn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have harith : n ^ 4 * (3 * Real.sqrt p) ≤ 3 * n ^ 2 * p := by
    have hn20 : 0 ≤ n ^ 2 := sq_nonneg n
    have hmain : n ^ 2 * Real.sqrt p ≤ p := by
      have := mul_le_mul_of_nonneg_right hn2sq hsqnn
      nlinarith [this, hsqmul]
    nlinarith [mul_le_mul_of_nonneg_left hmain hn20]
  calc ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      ≤ ∑ z ∈ Q, ‖quadTerm χ z‖ := hstep2
    _ = _ + _ := hsplit
    _ ≤ 3 * n ^ 2 * p + n ^ 4 * (3 * Real.sqrt p) := add_le_add hdeg hnondeg
    _ ≤ 3 * n ^ 2 * p + 3 * n ^ 2 * p := by linarith [harith]
    _ = 6 * n ^ 2 * p := by ring

/-- Deleted-offset corollary — the exact shape `_R17QuadrupleWeilRung` consumes
(`D = {0} ∪ μ_n`): deleting offsets only decreases the (termwise-nonnegative) moment. -/
theorem fourthMomentAway_le_of_quarticWeilInput (χ : MulChar F ℂ) (G D : Finset F)
    (hW : QuarticWeilInput χ G)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s ∈ Finset.univ \ D, ‖shiftedCharSum χ G s‖ ^ 4
      ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  refine le_trans ?_ (fourthMoment_le_of_quarticWeilInput χ G hW hp)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
    (fun s _ _ => by positivity)

/-- Adapter into the round-17 r=2 interface: the per-tuple quartic Weil input for every character
in `X` implies `FourthMomentTwistBound` with constant `6`. -/
theorem fourthMomentTwistBound_of_quarticWeilInput
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (hW : ∀ χ ∈ X, QuarticWeilInput χ G)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X 6 := by
  intro χ hχ
  calc ∑ t : F, ‖ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum χ G t‖ ^ 4
      = ∑ t : F, ‖shiftedCharSum χ G t‖ ^ 4 := by
        exact Finset.sum_congr rfl fun t _ => by
          rw [ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_twistedThinSum_eq_shiftedCharSum]
    _ ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) :=
        fourthMoment_le_of_quarticWeilInput χ G (hW χ hχ) hp

end ArkLib.ProximityGap.Frontier.R18FourthMomentTwist

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.mulChar_mul_conj
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.norm_mulChar_le_one
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.norm_quadTerm_le_card
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.quadTerm_pair_diag
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.norm_pow_four_eq
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMoment_expand
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.filter_degenerate_subset
#print axioms ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.card_filter_degenerate_le
#print axioms
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMoment_le_of_quarticWeilInput
#print axioms
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentAway_le_of_quarticWeilInput
#print axioms
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
