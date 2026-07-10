/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Rate-quarter common-factor ownership amplifier

This file formalizes the abstract algebra and arithmetic of the
common-factor/hole/triple trade that extends the smooth rate-quarter
counterconstruction beyond maximal private thickening.

Start with the `mu_16` cell at `m=3r+1`: three proper pair cells of size
`3m`, three singleton cells of size `7r+2`, one hole, and no all-three core.
For an integer `d`:

* choose `d` singleton coordinates from line zero and `d` from line one;
* multiply all three line factors by their degree-`2d` locator `G`, turning
  those `2d` coordinates into an all-three core;
* remove `d` singleton coordinates from line two, turning them into holes.

The new Venn cells are

```text
holes             = d+1,
triple core        = 2d,
proper pair cells  = 3m each,
singleton cells    = 7r+2-d each.
```

Every core grows by `d`, while the one-fresh ownership budget remains
exactly `n+2`.  If the old factors have degree at most `3m`, the amplified
line and its fresh witness have degree at most `3m+2d+1`; hence the rate-
quarter degree bound survives whenever `2d+1<m`.

At a hole, write the common locator value as `ell` and an old line-factor
value as `t`.  Against received pair `(alpha*x,beta)`, the isolated label is

```text
gamma(t) = x * (ell*t-alpha)/(beta-ell*t).
```

The file proves the pointwise agreement equation and proves that this
Möbius map is injective on distinct `t` values when `x`, `ell`, and
`beta-alpha` are nonzero and the denominators are nonzero.  Global avoidance
of the smooth domain and of labels chosen at earlier holes is a separate
finite-field choice condition; it is not silently assumed by the local
identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Polynomial

namespace ArkLib.ProximityGap.Frontier.RateQuarterCommonFactorOwnershipAmplifier

variable {F : Type} [Field F]

/-! ## Exact Venn-cell and degree arithmetic -/

/-- Universe size with the natural availability hypothesis made explicit. -/
theorem amplified_cell_universe_size_of_d_le
    {m r d : Nat} (hm : m = 3 * r + 1) (hd : d ≤ 7 * r + 2) :
    (d + 1) + 2 * d + 3 * (3 * m) + 3 * (7 * r + 2 - d) = 16 * m := by
  omega

/-- Every amplified core has the old maximally thickened size plus `d`. -/
theorem amplified_core_size
    {m r d : Nat} (hm : m = 3 * r + 1) (hd : d ≤ 7 * r + 2) :
    (7 * r + 2 - d) + 2 * (3 * m) + 2 * d = 8 * m + r + d := by
  omega

/-- The nondead-owned coordinates plus three labels per hole always give
exactly two labels more than the universe. -/
theorem amplified_ownership_budget
    {m r d : Nat} (hm : m = 3 * r + 1) (hd : d ≤ 7 * r + 2) :
    3 * (7 * r + 2 - d) + 3 * (3 * m) + 3 * (d + 1) = 16 * m + 2 := by
  omega

/-- The factor, intercept, and one-fresh witness degree ledger stays below
`k=4m` exactly under `2d+1<m`. -/
theorem amplified_degree_budget
    {m d : Nat} (hdegree : 2 * d + 1 < m) :
    3 * m + 2 * d < 4 * m ∧
      3 * m + 2 * d + 1 < 4 * m := by
  omega

/-- The saturated choice `2d+2=m` is both degree-admissible and far inside
the singleton-cell availability bound as soon as `r` is positive. -/
theorem saturated_d_degree_and_cell_available
    {m r d : Nat} (hm : m = 3 * r + 1) (hr : 0 < r)
    (hd : 2 * d + 2 = m) :
    d ≤ 7 * r + 2 ∧ 2 * d + 1 < m := by
  omega

/-- At the saturated amplifier endpoint `2d+2=m`, the agreement threshold
`t=8m+r+d+1` obeys `6t=53m-2`. -/
theorem saturated_threshold_identity
    {m r d : Nat} (hm : m = 3 * r + 1) (hd : 2 * d + 2 = m) :
    6 * (8 * m + r + d + 1) = 53 * m - 2 := by
  omega

/-- At the same endpoint, the error count `16m-t` obeys
`6(16m-t)=43m+2`, i.e. relative radius
`43/96 + 1/(3n)` for `n=16m`. -/
theorem saturated_error_identity
    {m r d : Nat} (hm : m = 3 * r + 1) (hd : 2 * d + 2 = m) :
    6 * (16 * m - (8 * m + r + d + 1)) = 43 * m + 2 := by
  omega

/-- **Architecture-local optimality.**  Within this `d`-step amplifier, the
degree condition `2d+1<m` forces the agreement threshold no larger than the
saturated value `(53m-2)/6`.  This is not a global lower bound: it only proves
that further improvement requires changing the base proper-pair locator or
the primitive-direction architecture. -/
theorem amplified_threshold_le_saturated_of_degree
    {m r d : Nat} (hm : m = 3 * r + 1) (hdegree : 2 * d + 1 < m) :
    6 * (8 * m + r + d + 1) ≤ 53 * m - 2 := by
  omega

/-! ## Polynomial common-factor amplifier -/

/-- Multiply an old scalar line factor by the new common locator. -/
noncomputable def amplifiedFactor (G f : F[X]) : F[X] := G * f

/-- Polynomial-pair line with primitive direction `(X,1)`. -/
noncomputable def amplifiedLine (G f : F[X]) : F[X] × F[X] :=
  (X * amplifiedFactor G f, amplifiedFactor G f)

/-- The fresh-coordinate witness on source factor `f` at coordinate `x`. -/
noncomputable def amplifiedFreshWitness (G f : F[X]) (x : F) : F[X] :=
  amplifiedFactor G f * (X - C x)

/-- A root of the common locator makes every amplified polynomial line equal
to the zero pair at that coordinate. -/
theorem amplifiedLine_eval_eq_zero_of_common_root
    (G f : F[X]) {x : F} (hG : G.eval x = 0) :
    (amplifiedLine G f).1.eval x = 0 ∧
      (amplifiedLine G f).2.eval x = 0 := by
  simp [amplifiedLine, amplifiedFactor, hG]

/-- Away from the common locator, amplification preserves equality of old
line-factor values exactly; it creates no accidental pair roots. -/
theorem amplifiedLine_eval_eq_iff_factor_eval_eq
    (G f g : F[X]) {x : F} (hG : G.eval x ≠ 0) :
    ((amplifiedLine G f).1.eval x = (amplifiedLine G g).1.eval x ∧
      (amplifiedLine G f).2.eval x = (amplifiedLine G g).2.eval x) ↔
      f.eval x = g.eval x := by
  constructor
  · intro h
    simp only [amplifiedLine, amplifiedFactor, eval_mul] at h
    exact mul_left_cancel₀ hG h.2
  · intro h
    simp only [amplifiedLine, amplifiedFactor, eval_mul]
    rw [h]
    exact ⟨rfl, rfl⟩

/-- The coordinate label `gamma=-x` turns the amplified affine line into the
fresh witness polynomial. -/
theorem amplifiedFreshWitness_eq_affineLine
    (G f : F[X]) (x : F) :
    amplifiedFreshWitness G f x =
      (amplifiedLine G f).1 + C (-x) * (amplifiedLine G f).2 := by
  simp only [amplifiedFreshWitness, amplifiedLine, amplifiedFactor, C_neg]
  ring

/-- The fresh witness vanishes at its added coordinate. -/
theorem amplifiedFreshWitness_eval_self
    (G f : F[X]) (x : F) :
    (amplifiedFreshWitness G f x).eval x = 0 := by
  simp [amplifiedFreshWitness]

/-- Exact polynomial degree budget for the amplified factor, line
components, and one-fresh witness. -/
theorem amplified_polynomial_natDegree_bounds
    (G f : F[X]) {m d : Nat}
    (hGdeg : G.natDegree ≤ 2 * d)
    (hfdeg : f.natDegree ≤ 3 * m) :
    (amplifiedFactor G f).natDegree ≤ 3 * m + 2 * d ∧
      (amplifiedLine G f).1.natDegree ≤ 3 * m + 2 * d + 1 ∧
      (amplifiedLine G f).2.natDegree ≤ 3 * m + 2 * d ∧
      ∀ x : F,
        (amplifiedFreshWitness G f x).natDegree ≤ 3 * m + 2 * d + 1 := by
  have hfactor : (amplifiedFactor G f).natDegree ≤ 3 * m + 2 * d := by
    calc
      (amplifiedFactor G f).natDegree ≤ G.natDegree + f.natDegree :=
        natDegree_mul_le
      _ ≤ 2 * d + 3 * m := Nat.add_le_add hGdeg hfdeg
      _ = 3 * m + 2 * d := by omega
  have hintercept : (amplifiedLine G f).1.natDegree ≤
      3 * m + 2 * d + 1 := by
    calc
      (amplifiedLine G f).1.natDegree ≤
          X.natDegree + (amplifiedFactor G f).natDegree := by
        simpa only [amplifiedLine] using
          (natDegree_mul_le : (X * amplifiedFactor G f).natDegree ≤
            X.natDegree + (amplifiedFactor G f).natDegree)
      _ ≤ 3 * m + 2 * d + 1 := by
        rw [natDegree_X]
        omega
  have hslope : (amplifiedLine G f).2.natDegree ≤ 3 * m + 2 * d := by
    simpa only [amplifiedLine] using hfactor
  refine ⟨hfactor, hintercept, hslope, ?_⟩
  intro x
  have hlinear : (X - C x : F[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  calc
    (amplifiedFreshWitness G f x).natDegree ≤
        (amplifiedFactor G f).natDegree + (X - C x : F[X]).natDegree := by
      simpa only [amplifiedFreshWitness] using
        (natDegree_mul_le :
          (amplifiedFactor G f * (X - C x)).natDegree ≤
            (amplifiedFactor G f).natDegree + (X - C x).natDegree)
    _ ≤ (3 * m + 2 * d) + 1 := Nat.add_le_add hfactor hlinear
    _ = 3 * m + 2 * d + 1 := rfl

/-! ## Scaled-hole Möbius labels -/

/-- Isolated scalar attached to an old factor value `t` after common-locator
scaling by `ell` at a hole coordinate `x`. -/
noncomputable def scaledHoleGamma
    (x ell alpha beta t : F) : F :=
  x * ((ell * t - alpha) / (beta - ell * t))

/-- The scaled-hole label satisfies the exact affine agreement equation. -/
theorem scaledHoleGamma_agreement
    (x ell alpha beta t : F) (hden : beta - ell * t ≠ 0) :
    alpha * x + scaledHoleGamma x ell alpha beta t * beta =
      (ell * t) * (x + scaledHoleGamma x ell alpha beta t) := by
  simp only [scaledHoleGamma]
  field_simp [hden]
  ring

/-- **Scaled-row cancellation.**  If the received row at a hole is scaled by
the common-locator value, `alpha=ell*alpha0` and `beta=ell*beta0`, then the
common factor cancels from the isolated label.  The resulting label is the
old fibrewise coset formula and is independent of `ell`. -/
theorem scaledHoleGamma_scaled_rows
    (x ell alpha₀ beta₀ t : F) (hell : ell ≠ 0) :
    scaledHoleGamma x ell (ell * alpha₀) (ell * beta₀) t =
      x * ((t - alpha₀) / (beta₀ - t)) := by
  by_cases hden₀ : beta₀ - t = 0
  · have hbeta : beta₀ = t := sub_eq_zero.mp hden₀
    simp [scaledHoleGamma, hbeta]
  · have hden : ell * beta₀ - ell * t ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero hell hden₀
    simp only [scaledHoleGamma]
    field_simp [hden₀, hden, hell]

/-- Agreement equation after scaled-row cancellation. -/
theorem scaledHoleGamma_scaled_rows_agreement
    (x ell alpha₀ beta₀ t : F) (hell : ell ≠ 0)
    (hden₀ : beta₀ - t ≠ 0) :
    (ell * alpha₀) * x +
        scaledHoleGamma x ell (ell * alpha₀) (ell * beta₀) t *
          (ell * beta₀) =
      (ell * t) *
        (x + scaledHoleGamma x ell (ell * alpha₀) (ell * beta₀) t) := by
  apply scaledHoleGamma_agreement
  rw [← mul_sub]
  exact mul_ne_zero hell hden₀

/-- A nonzero scaled-hole denominator also certifies that the received pair
`(alpha*x,beta)` is not the decoded line pair `(x*(ell*t),ell*t)`.  Hence the
isolated witness is genuinely nonjoint at its added coordinate. -/
theorem scaledHole_received_pair_ne_line
    (x ell alpha beta t : F) (hden : beta - ell * t ≠ 0) :
    (alpha * x, beta) ≠ (x * (ell * t), ell * t) := by
  intro heq
  have hbeta : beta = ell * t := congrArg Prod.snd heq
  exact hden (sub_eq_zero.mpr hbeta)

/-- The scaled received pair is genuinely off the decoded line whenever the
unscaled denominator is nonzero. -/
theorem scaledHole_scaled_received_pair_ne_line
    (x ell alpha₀ beta₀ t : F) (hell : ell ≠ 0)
    (hden₀ : beta₀ - t ≠ 0) :
    ((ell * alpha₀) * x, ell * beta₀) ≠
      (x * (ell * t), ell * t) := by
  apply scaledHole_received_pair_ne_line
  rw [← mul_sub]
  exact mul_ne_zero hell hden₀

/-- Equality of two scaled-hole labels forces equality of the underlying old
factor values.  This is the exact Möbius-label invariance used to obtain three
distinct isolated labels at every hole. -/
theorem eq_of_scaledHoleGamma_eq
    {x ell alpha beta t₁ t₂ : F}
    (hx : x ≠ 0) (hell : ell ≠ 0) (hba : beta ≠ alpha)
    (hden₁ : beta - ell * t₁ ≠ 0)
    (hden₂ : beta - ell * t₂ ≠ 0)
    (heq : scaledHoleGamma x ell alpha beta t₁ =
      scaledHoleGamma x ell alpha beta t₂) :
    t₁ = t₂ := by
  have hratio :
      (ell * t₁ - alpha) / (beta - ell * t₁) =
        (ell * t₂ - alpha) / (beta - ell * t₂) := by
    exact mul_left_cancel₀ hx heq
  field_simp [hden₁, hden₂] at hratio
  have hprod : (beta - alpha) * ell * (t₁ - t₂) = 0 := by
    linear_combination hratio
  have hba' : beta - alpha ≠ 0 := sub_ne_zero.mpr hba
  have ht : t₁ - t₂ = 0 := by
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact (mul_ne_zero hba' hell hzero).elim
    · exact hzero
  exact sub_eq_zero.mp ht

/-- Function-level injectivity on any set of old factor values whose
denominators are nonzero. -/
theorem scaledHoleGamma_injective_on
    {x ell alpha beta : F}
    (hx : x ≠ 0) (hell : ell ≠ 0) (hba : beta ≠ alpha)
    (T : Set F) (hden : ∀ t ∈ T, beta - ell * t ≠ 0) :
    Set.InjOn (scaledHoleGamma x ell alpha beta) T := by
  intro t₁ ht₁ t₂ ht₂ heq
  exact eq_of_scaledHoleGamma_eq hx hell hba
    (hden t₁ ht₁) (hden t₂ ht₂) heq

/-! ## Finite-field avoidance for one hole -/

section FiniteFieldAvoidance

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- A proper finite subset of a finite type misses some element. -/
theorem exists_not_mem_of_card_lt
    (S : Finset F) (hcard : S.card < Fintype.card F) :
    ∃ x : F, x ∉ S := by
  classical
  by_contra hnot
  push Not at hnot
  have hsub : (Finset.univ : Finset F) ⊆ S := by
    intro x _hx
    exact hnot x
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ] at hle
  omega

/-- For a fixed denominator parameter `beta`, this is the unique `alpha`
that sends the scaled old value `ell*t` to a prescribed label `delta`. -/
noncomputable def forbiddenAlpha
    (x ell beta t delta : F) : F :=
  ell * t - delta * (beta - ell * t) / x

omit [Fintype F] [DecidableEq F] in
/-- Exact inversion of the label equation in the `alpha` variable. -/
theorem alpha_eq_forbiddenAlpha_of_gamma_eq
    {x ell alpha beta t delta : F}
    (hx : x ≠ 0) (hden : beta - ell * t ≠ 0)
    (hgamma : scaledHoleGamma x ell alpha beta t = delta) :
    alpha = forbiddenAlpha x ell beta t delta := by
  simp only [scaledHoleGamma, forbiddenAlpha] at hgamma ⊢
  field_simp [hx, hden] at hgamma ⊢
  linear_combination -hgamma

omit [DecidableEq F] in
/-- **One-hole finite-field avoidance.**  Let three old factor values be
distinct, let the hole coordinate and common-locator value be nonzero, and
let `B` be any forbidden scalar set.  If the field has more than three
elements and more than `3*|B|+1` elements, one can choose a received pair
`(alpha*x,beta)` whose three Möbius labels have nonzero denominators, are
pairwise distinct, and all avoid `B`.

The proof is the exact greedy count used by the general amplifier.  First
choose `beta` outside the three scaled factor values.  For fixed `beta`, each
forbidden target label excludes exactly one `alpha` for each of the three
lines; `alpha=beta` excludes one more value. -/
theorem exists_scaledHole_parameters_avoiding
    (x ell : F) (t : Fin 3 → F) (B : Finset F)
    (hx : x ≠ 0) (hell : ell ≠ 0)
    (ht : Function.Injective t)
    (hfieldThree : 3 < Fintype.card F)
    (hfieldAvoid : 3 * B.card + 1 < Fintype.card F) :
    ∃ alpha beta : F,
      (∀ i, beta - ell * t i ≠ 0) ∧
      beta ≠ alpha ∧
      (∀ i, scaledHoleGamma x ell alpha beta (t i) ∉ B) ∧
      Function.Injective
        (fun i ↦ scaledHoleGamma x ell alpha beta (t i)) := by
  classical
  let values : Finset F :=
    (Finset.univ : Finset (Fin 3)).image fun i ↦ ell * t i
  have hvaluesCard : values.card ≤ 3 := by
    calc
      values.card ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_image_le
      _ = 3 := by simp
  obtain ⟨beta, hbeta⟩ := exists_not_mem_of_card_lt values
    (hvaluesCard.trans_lt hfieldThree)
  have hden : ∀ i, beta - ell * t i ≠ 0 := by
    intro i hzero
    apply hbeta
    simp only [values, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (sub_eq_zero.mp hzero).symm⟩
  let alphaTargets : Finset F :=
    ((Finset.univ : Finset (Fin 3)).product B).image fun z ↦
      forbiddenAlpha x ell beta (t z.1) z.2
  let badAlpha : Finset F := insert beta alphaTargets
  have htargetsCard : alphaTargets.card ≤ 3 * B.card := by
    calc
      alphaTargets.card ≤
          ((Finset.univ : Finset (Fin 3)).product B).card :=
        Finset.card_image_le
      _ = 3 * B.card := by simp
  have hbadCard : badAlpha.card ≤ 3 * B.card + 1 := by
    exact (Finset.card_insert_le beta alphaTargets).trans
      (Nat.add_le_add_right htargetsCard 1)
  obtain ⟨alpha, halpha⟩ := exists_not_mem_of_card_lt badAlpha
    (hbadCard.trans_lt hfieldAvoid)
  have hbetaAlpha : beta ≠ alpha := by
    intro heq
    apply halpha
    simpa only [badAlpha, heq] using
      (Finset.mem_insert_self beta alphaTargets)
  have havoid : ∀ i, scaledHoleGamma x ell alpha beta (t i) ∉ B := by
    intro i hmem
    apply halpha
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(i, scaledHoleGamma x ell alpha beta (t i)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ i, hmem⟩
    · dsimp only
      exact (alpha_eq_forbiddenAlpha_of_gamma_eq
        (x := x) (ell := ell) (alpha := alpha) (beta := beta)
        (t := t i) (delta := scaledHoleGamma x ell alpha beta (t i))
        hx (hden i) rfl).symm
  refine ⟨alpha, beta, hden, hbetaAlpha, havoid, ?_⟩
  intro i j hij
  exact ht (eq_of_scaledHoleGamma_eq hx hell hbetaAlpha
    (hden i) (hden j) hij)

end FiniteFieldAvoidance

end ArkLib.ProximityGap.Frontier.RateQuarterCommonFactorOwnershipAmplifier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterCommonFactorOwnershipAmplifier
#print axioms amplified_cell_universe_size_of_d_le
#print axioms amplified_core_size
#print axioms amplified_ownership_budget
#print axioms amplified_degree_budget
#print axioms saturated_d_degree_and_cell_available
#print axioms saturated_threshold_identity
#print axioms saturated_error_identity
#print axioms amplified_threshold_le_saturated_of_degree
#print axioms amplifiedLine_eval_eq_zero_of_common_root
#print axioms amplifiedLine_eval_eq_iff_factor_eval_eq
#print axioms amplifiedFreshWitness_eq_affineLine
#print axioms amplified_polynomial_natDegree_bounds
#print axioms scaledHoleGamma_agreement
#print axioms scaledHoleGamma_scaled_rows
#print axioms scaledHoleGamma_scaled_rows_agreement
#print axioms scaledHole_received_pair_ne_line
#print axioms scaledHole_scaled_received_pair_ne_line
#print axioms eq_of_scaledHoleGamma_eq
#print axioms scaledHoleGamma_injective_on
#print axioms exists_not_mem_of_card_lt
#print axioms alpha_eq_forbiddenAlpha_of_gamma_eq
#print axioms exists_scaledHole_parameters_avoiding
