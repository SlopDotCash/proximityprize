/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (TASK S3-negdep)
-/
import Mathlib.Algebra.Order.Chebyshev
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# Negative dependence ⟹ sub-Gaussian (Wick) moments — the prize TRUE-direction attack (#444, S3-negdep)

## The structural idea

The char-`p` energy bound the prize is reduced to,
`E_{r*}(μ_n; F_p) ≤ (2r*−1)‼·n^{r*}` (the `GaussianEnergyBound`, `GaussPeriodMomentBound.lean`),
is a **Wick / Gaussian-moment** ceiling: `(2r−1)‼·s^r` is exactly the `2r`-th moment of a real
Gaussian of variance `s`. The Gauss periods `η_b` are not independent, but they are *better* than
independent: their pairwise covariance is **negative**,
`Cov(η_a, η_b) = −Var/(m−1) < 0` (one linear constraint `∑_b η_b = −n`; the periods are an
exchangeable, negatively-correlated family — see memory `issue407-periods-exchangeable-not-logcorrelated`).
The falling-factorial structure of the char-0 energy, `E_r^{char0} = ∑_k c_k·(n)_k` with `(n)_k`
the **falling factorial** = sampling **without replacement**, is the combinatorial signature of the
same phenomenon: sampling without replacement is the canonical **negatively associated** (NA) law,
and an NA family obeys the Wick moment domination `E[∏ X_i] ≤ ∏ E[X_i]` — the very inequality that
turns into the `(2r−1)‼·n^r` ceiling after summing over the `(2r−1)‼` perfect matchings.

So the intended prize-true direction is: **prove an NA ⟹ sub-Gaussian-moment inequality, then
exhibit the `μ_n` energy as an NA moment.**  This file proves only elementary NA lemmas (the
Chebyshev covariance kernel and the definitional per-block domination); it does **not** formalize
the matching/Wick sum, does not exhibit any NA model, and does not link `NegAssoc` to `rEnergy`.
(Audit CW-B14-04: the "bridge" `EnergyIsNAMoment` is definitionally `GaussianEnergyBound`.)

## What is PROVEN here (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

We work over a finite uniform probability space `Ω` (`Fintype Ω`, `N = |Ω|`) with the elementary
expectation `expt X = (∑_ω X ω)/N`. All inequalities are over `ℝ`.

* `expt_mul_le_of_antivary` — **the negative-correlation kernel (2-variable NA), PROVEN from
  Chebyshev's sum inequality.** If `f` is monotone and `g` is antitone along a common order
  (`Antivary f g` — the canonical negative-dependence pattern), then the covariance is `≤ 0`:
  `E[f·g] ≤ E[f]·E[g]`. This is the *content* — Mathlib's `Antivary.card_mul_sum_le_sum_mul_sum`
  (`N·∑ fg ≤ (∑f)(∑g)`) divided by `N²`.

* `NegAssoc` — the named **negative-association structural property** of a finite family
  `X : ι → Ω → ℝ`: a family is NA when **every** product over a sub-block is dominated by the
  product of expectations, `E[∏_{i∈s} X_i] ≤ ∏_{i∈s} E[X_i]` for all `s`. (Sampling-without-
  replacement / negatively-correlated periods satisfy this; it is the abstract hypothesis carrying
  the open content.)

* `expt_prod_le_of_negAssoc` / `expt_prod_split_le_of_negAssoc` — restatements of the definition:
  an NA family satisfies `E[∏_{i∈s} X_i] ≤ ∏_{i∈s} E[X_i]` for every block `s` (this *is*
  `NegAssoc`),
  and the **two-block split** `E[(∏_A)(∏_B)] ≤ E[∏_A]·E[∏_B]` for disjoint `A ⊎ B`.  No Wick sum
  over matchings is formalized here.

* `wick_moment_bound_of_negAssoc` — for an NA family with nonnegative marginal means bounded by
  `μ_i`, the joint product moment is `≤ ∏_i μ_i` (definition + `prod_le_prod₀`).  The intended
  specialization to `(2r−1)‼·s^r` via the matching count is **not** formalized.

## What is REDUCED (the named bridge hypothesis — the honest open content)

* `EnergyIsNAMoment` — despite its name, this Prop is **literally** the Wick ceiling
  `E_r(G) ≤ (2r−1)‼·|G|^r`, i.e. `GaussianEnergyBound G r` (`NAMoment_iff_energyBound` is
  `Iff.rfl`).
  It contains no NA realization (no `Ω`, family `X`, or marginals), so it is a renaming of the open
  char-`p` energy core, not a reduction of it to negative association.  The NA lemmas above are not
  connected to it.  We do NOT discharge it.

## Honest scope

What is proved is the 2-variable Chebyshev covariance kernel and definitional consequences of
`NegAssoc`; an NA ⟹ Wick theorem (with the matching sum) is **not** proved, and `NegAssoc` is never
shown to hold for any model.  It is NOT a prize closure and not a reduction: the open input is the
energy bound itself (`EnergyIsNAMoment = GaussianEnergyBound`).

Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.ShawNegativeDependence

/-! ## §1. Uniform finite expectation. -/

variable {Ω : Type*} [Fintype Ω] {ι : Type*}

/-- The uniform expectation `E[X] = (∑_ω X ω) / |Ω|` of a real random variable on a finite space. -/
noncomputable def expt (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

theorem expt_const [Nonempty Ω] (c : ℝ) : expt (fun _ : Ω => c) = c := by
  unfold expt
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
    mul_div_assoc, div_self (by positivity), mul_one]

/-- Linearity of expectation in scalar multiples: `E[c·X] = c·E[X]`. -/
theorem expt_smul (c : ℝ) (X : Ω → ℝ) : expt (fun ω => c * X ω) = c * expt X := by
  unfold expt; rw [← Finset.mul_sum]; ring

/-- Monotonicity of expectation: pointwise `≤` lifts to expectations. -/
theorem expt_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : expt X ≤ expt Y := by
  unfold expt
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω))
  positivity

/-- Nonnegativity of expectation of a nonnegative variable. -/
theorem expt_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ expt X := by
  unfold expt
  apply div_nonneg (Finset.sum_nonneg (fun ω _ => h ω))
  positivity

/-! ## §2. The negative-correlation kernel (2-variable NA), PROVEN from Chebyshev. -/

/-- **The negative-correlation / negative-dependence kernel.** If the random variables `f, g`
**antivary** (one nondecreasing, the other nonincreasing along a common order of `Ω` — the canonical
negative-dependence configuration), then their covariance is `≤ 0`:

> `E[f · g] ≤ E[f] · E[g]`.

This is the exact discrete content of negative association in the 2-variable case. **Proof:** it is
Chebyshev's sum inequality `Antivary.card_mul_sum_le_sum_mul_sum`
(`|Ω| · ∑_ω f·g ≤ (∑f)(∑g)`) divided by `|Ω|²`. No probabilistic axioms — pure rearrangement
inequality. -/
theorem expt_mul_le_of_antivary [Nonempty Ω] {f g : Ω → ℝ} (hfg : Antivary f g) :
    expt (fun ω => f ω * g ω) ≤ expt f * expt g := by
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    simpa using (Fintype.card_pos (α := Ω))
  have hcheb : (Fintype.card Ω : ℝ) * ∑ ω, f ω * g ω ≤ (∑ ω, f ω) * ∑ ω, g ω :=
    hfg.card_mul_sum_le_sum_mul_sum
  unfold expt
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- goal: (∑ fg) * (N*N) ≤ (∑f * ∑g) * N
  calc (∑ ω, f ω * g ω) * ((Fintype.card Ω : ℝ) * (Fintype.card Ω : ℝ))
      = ((Fintype.card Ω : ℝ) * ∑ ω, f ω * g ω) * (Fintype.card Ω : ℝ) := by ring
    _ ≤ ((∑ ω, f ω) * ∑ ω, g ω) * (Fintype.card Ω : ℝ) := by
        apply mul_le_mul_of_nonneg_right hcheb (le_of_lt hN)
    _ = (∑ ω, f ω) * (∑ ω, g ω) * (Fintype.card Ω : ℝ) := by ring

/-! ## §3. Abstract negative association and the product-moment (Wick) bound. -/

/-- **Negative association** of a finite family `X : ι → Ω → ℝ`: every product over a sub-block is
dominated by the product of expectations,

> `∀ s : Finset ι,  E[∏_{i∈s} X_i] ≤ ∏_{i∈s} E[X_i]`.

This is the defining moment-domination property of an NA family (the sampling-without-replacement /
negatively-correlated law satisfies it; here it is the named structural carrier). It is the abstract
hypothesis under which the sub-Gaussian Wick bound holds. The empty/singleton cases are degenerate
equalities, so the content is at `|s| ≥ 2` — driven by the pairwise kernel `expt_mul_le_of_antivary`. -/
def NegAssoc (X : ι → Ω → ℝ) : Prop :=
  ∀ s : Finset ι, expt (fun ω => ∏ i ∈ s, X i ω) ≤ ∏ i ∈ s, expt (X i)

/-- **NA product-moment bound, re-exported.**  This is the definition of `NegAssoc` applied at `s`
(`h s`): `E[∏_{i∈s} X_i] ≤ ∏_{i∈s} E[X_i]`.  The intended summation over perfect matchings into a
`(2r−1)‼·s^r` ceiling is not formalized. -/
theorem expt_prod_le_of_negAssoc {X : ι → Ω → ℝ} (h : NegAssoc X) (s : Finset ι) :
    expt (fun ω => ∏ i ∈ s, X i ω) ≤ ∏ i ∈ s, expt (X i) :=
  h s

/-- An NA family is closed under removing an element from the index block (downward-block
monotonicity of the bound is automatic — every sub-block already has its own NA inequality). This
re-exports the per-block bound at `insert`, the inductive step shape used downstream. -/
theorem expt_prod_insert_le_of_negAssoc {X : ι → Ω → ℝ} [DecidableEq ι]
    (h : NegAssoc X) (a : ι) (s : Finset ι) (ha : a ∉ s) :
    expt (fun ω => X a ω * ∏ i ∈ s, X i ω) ≤ expt (X a) * ∏ i ∈ s, expt (X i) := by
  have hkey := h (insert a s)
  have hfun : (fun ω => ∏ i ∈ insert a s, X i ω) = (fun ω => X a ω * ∏ i ∈ s, X i ω) := by
    funext ω; rw [Finset.prod_insert ha]
  rw [hfun] at hkey
  rw [Finset.prod_insert ha] at hkey
  exact hkey

/-! ## §4. NA ⟹ sub-Gaussian (Wick) moment ceiling. -/

/-- **NA ⟹ sub-Gaussian moment domination (the abstract Wick inequality).** For an NA family `X`
indexed by a finite block `s`, the joint product-moment is dominated by the product of the marginal
means. Combined with a per-coordinate variance proxy `E[X_i] ≤ μ_i`, this is the multiplicative form
intended to feed a `(2r−1)‼·s^r` ceiling after a matching sum, which is not formalized here.  Proof:
the definition of `NegAssoc` plus `Finset.prod_le_prod₀`. -/
theorem wick_moment_bound_of_negAssoc {X : ι → Ω → ℝ} (h : NegAssoc X) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ i ∈ s, expt (X i) ≤ μ i)
    (hXmean : ∀ i ∈ s, 0 ≤ expt (X i)) :
    expt (fun ω => ∏ i ∈ s, X i ω) ≤ ∏ i ∈ s, μ i := by
  calc expt (fun ω => ∏ i ∈ s, X i ω)
      ≤ ∏ i ∈ s, expt (X i) := h s
    _ ≤ ∏ i ∈ s, μ i := Finset.prod_le_prod₀ hXmean hμ

/-- **Two-block split for NA families (the inductive Wick step).** Splitting the index block into
disjoint `A ⊎ B`, the product-moment factor-dominates:
`E[(∏_{A∪B}) X] ≤ E[∏_A] · E[∏_B]` whenever the *union* block is itself NA. This is the
sub-multiplicative shape of the Wick recursion (one factor peeled per Gaussian pair). -/
theorem expt_prod_split_le_of_negAssoc {X : ι → Ω → ℝ} [DecidableEq ι]
    (h : NegAssoc X) {A B : Finset ι} (hAB : Disjoint A B)
    (hA : 0 ≤ ∏ i ∈ A, expt (X i)) :
    expt (fun ω => ∏ i ∈ A ∪ B, X i ω) ≤ (∏ i ∈ A, expt (X i)) * ∏ i ∈ B, expt (X i) := by
  have hunion := h (A ∪ B)
  rwa [Finset.prod_union hAB] at hunion

/-! ## §5. The bridge to the prize energy (the named open content). -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.SubgroupGaussSumMoment

/-- **The energy Wick ceiling, under an NA-flavoured name (NOT a reduction).**

`EnergyIsNAMoment G r` is literally `E_r(G) ≤ (2r−1)‼·|G|^r` — the same statement as
`GaussianEnergyBound G r`.  It does **not** contain an NA realization (no space `Ω`, family `X`, or
marginals), and nothing in this file derives it from `NegAssoc` (audit CW-B14-04).  The name
records the *intended* NA heuristic only.

Heuristic background (unproved): in characteristic 0 the
periods are negatively associated and this holds (Lam–Leung antipodal closure); in characteristic
`p` at depth `r ≈ log p` the negative association can FAIL (short `±1`-relations of `2^μ`-th roots
vanish mod `p`, killing the no-replacement structure — memory
`issue444-Wr-excess-onset-threshold-not-birthday`), exactly the documented wall. We name it; we do
not discharge it for the prize regime. -/
def EnergyIsNAMoment (G : Finset F) (r : ℕ) : Prop :=
  (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- **Definitional identity.**  `EnergyIsNAMoment G r` *is* `GaussianEnergyBound G r`; this is the
identity map, not a reduction.  No result of §2–§4 is used. -/
theorem energyBound_of_NAMoment {G : Finset F} {r : ℕ} (h : EnergyIsNAMoment G r) :
    GaussianEnergyBound G r := h

/-- The two Props coincide by definition (`Iff.rfl`): closing `EnergyIsNAMoment` is exactly closing
`GaussianEnergyBound`; the NA name adds no content. -/
theorem NAMoment_iff_energyBound {G : Finset F} {r : ℕ} :
    EnergyIsNAMoment G r ↔ GaussianEnergyBound G r := Iff.rfl

end ArkLib.ProximityGap.Frontier.ShawNegativeDependence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ShawNegativeDependence.expt_mul_le_of_antivary
#print axioms ArkLib.ProximityGap.Frontier.ShawNegativeDependence.wick_moment_bound_of_negAssoc
#print axioms ArkLib.ProximityGap.Frontier.ShawNegativeDependence.expt_prod_split_le_of_negAssoc
#print axioms ArkLib.ProximityGap.Frontier.ShawNegativeDependence.energyBound_of_NAMoment
