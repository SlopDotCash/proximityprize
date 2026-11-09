/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-!
# The rational-function level-set degree bound (δ* ratio-census attack, research-map §4 vector 1)

The `docs/kb/deltastar-research-map.md` ranks the **ratio-census identity** as the #1 never-tried
handle on the open δ* core's line–ball-incidence face (face iv): reduce the incidence of a far
direction with the syndrome ball to the *multiplicity profile of the ratio sequence* of two GRS
syndromes, then bound that profile by the fact that **a generalized-Reed–Solomon syndrome ratio is
a rational function on the smooth domain, so its level sets are root sets and multiplicities are
degree-bounded**. This file lands that algebraic core, axiom-clean and self-contained.

* `ratio_value_mult_le` — for a ratio `R/ℓ` on an injective domain, a fixed value `c` is attained
  at ≤ `max (deg R) (deg ℓ)` domain points (the level set `{x : R(x)/ℓ(x) = c}` injects into the
  roots of the nonzero polynomial `R − c·ℓ`). Hypothesis `R ≠ C c * ℓ` excludes the constant ratio.
* `grs_line_incidence_le` — the attack-facing form: the number of domain points where a combined
  syndrome `s₀ + γ·s₁` vanishes (off the poles of `s₁`) is ≤ `max (deg s₀) (deg s₁)`.

**Honest scope.** This is the *elementary algebraic lever* the ratio-census attack needs — the
degree-bounded level-set fact the general list-decoding wall lacks because it ignores the domain's
GRS structure. It is a boundary brick toward the open core, NOT a closure: the hard residual is the
*census* (`WindowRationalLinear`, `WBPencilLinearBudget.lean`) — bounding the *total* bad-scalar
count across all directions to `≤ n` in the production regime, which this per-direction bound feeds
but does not settle.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ProximityGap.RatioLevelSet

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

open Classical in
/-- **The rational-function level-set degree bound** (research-map §4 vector 1, the algebraic
core). For a ratio `R/ℓ` evaluated on an injective domain, a fixed value `c` is attained at at
most `max (deg R) (deg ℓ)` domain points: those points are roots of `R − c·ℓ`, a nonzero
polynomial of that degree. The hypothesis `R ≠ C c * ℓ` excludes the degenerate constant ratio
(level set = whole domain). This is "incidence ≤ deg-bound on how often a fixed rational function
repeats a value on a (subgroup) orbit" — the GRS syndrome ratio multiplicity bound. -/
theorem ratio_value_mult_le (dom : ι ↪ F) (R ℓ : F[X]) (c : F)
    (hne : R ≠ Polynomial.C c * ℓ) :
    (Finset.univ.filter (fun i => ℓ.eval (dom i) ≠ 0 ∧
        R.eval (dom i) = c * ℓ.eval (dom i))).card
      ≤ max R.natDegree ℓ.natDegree := by
  classical
  set P : F[X] := R - Polynomial.C c * ℓ with hPdef
  have hP0 : P ≠ 0 := sub_ne_zero.mpr hne
  -- every filtered `i` makes `dom i` a root of `P`
  have hroot : ∀ i ∈ Finset.univ.filter (fun i => ℓ.eval (dom i) ≠ 0 ∧
      R.eval (dom i) = c * ℓ.eval (dom i)), P.eval (dom i) = 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hPdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hi.2,
      sub_self]
  -- inject the filtered set into `P.roots.toFinset` via `dom`
  have hcard : (Finset.univ.filter (fun i => ℓ.eval (dom i) ≠ 0 ∧
      R.eval (dom i) = c * ℓ.eval (dom i))).card ≤ P.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun i => dom i)
    · intro i hi
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      exact hroot i hi
    · intro a _ b _ hab; exact dom.injective hab
  calc (Finset.univ.filter (fun i => ℓ.eval (dom i) ≠ 0 ∧
          R.eval (dom i) = c * ℓ.eval (dom i))).card
      ≤ P.roots.toFinset.card := hcard
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ max R.natDegree ℓ.natDegree := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        exact max_le_max (le_refl _) (Polynomial.natDegree_C_mul_le c ℓ)

open Classical in
/-- **GRS line–ball incidence at one direction, degree-bounded** (research-map §4 vector 1).
For two GRS syndromes given by polynomials `s₀, s₁`, the number of domain points where the
combined syndrome `s₀ + γ·s₁` vanishes (off the poles of `s₁`) is at most `max (deg s₀) (deg s₁)`
— because vanishing of `s₀ + γ·s₁` at `dom i` is the level set `s₀/s₁ = −γ`. The hypothesis
`s₀ ≠ C (−γ) * s₁` excludes the degenerate whole-domain-vanishing direction. This is the exact
"incidence ≤ deg-bound on how often the ratio repeats a value on the orbit" handle the ratio-census
attack needs, made concrete and axiom-clean. -/
theorem grs_line_incidence_le (dom : ι ↪ F) (s₀ s₁ : F[X]) (γ : F)
    (hne : s₀ ≠ Polynomial.C (-γ) * s₁) :
    (Finset.univ.filter (fun i => s₁.eval (dom i) ≠ 0 ∧
        s₀.eval (dom i) + γ * s₁.eval (dom i) = 0)).card
      ≤ max s₀.natDegree s₁.natDegree := by
  have h := ratio_value_mult_le dom s₀ s₁ (-γ) hne
  refine le_trans (le_of_eq ?_) h
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [neg_mul, add_eq_zero_iff_eq_neg]

end ProximityGap.RatioLevelSet

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.RatioLevelSet.ratio_value_mult_le
#print axioms ProximityGap.RatioLevelSet.grs_line_incidence_le
