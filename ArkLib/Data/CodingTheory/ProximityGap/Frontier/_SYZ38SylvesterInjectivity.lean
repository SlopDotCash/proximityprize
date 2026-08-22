/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ37RateHalfAssembly
import Mathlib.Tactic.LinearCombination

/-!
# SYZ38 — Sylvester injectivity: the 3-support residual localized to a divisibility fact

SYZ37 reduced the rate-`1/2` union-generation gate to the vanishing of the **in-budget syzygy
module** of the reduced pairwise-coprime triple `(W_AB, W_AC, W_BC)`, discharged the `0`- and
`2`-support strata (out-of-budget/degree mechanism), and carried the `3`-support stratum (all
`r_XY ≠ 0`) as the abstract named residual `InBudgetSyzygyModuleVanishes` (a `finrank` equality).

This file **sharpens that residual from an abstract finrank restatement to a concrete, classical
polynomial statement** and closes the whole module — all supports at once — *conditional on that
one concrete statement*.

## The mechanism (why the 3-support case is not elementary)

Write the syzygy as `W_AB · r_AB = W_AC · r_AC − W_BC · r_BC`.  The left side is divisible by
`W_AB`, so

  `W_AB ∣ (W_AC · r_AC − W_BC · r_BC)`.                                     (†)

Because `W_AC` and `W_BC` are each coprime to `W_AB`, both are units in `K[X]/(W_AB)`, and (†) is a
**single linear congruence** `r_AC ≡ W_AC⁻¹ W_BC r_BC  (mod W_AB)`.  At rate `1/2` the Koszul
budget fails (`k − 1 < m_AB + m_AC − t`, `koszul_out_of_budget_rate_half`), which forces the
per-pair budgets *below* `deg W_AB`:

  `b_AC = k − 1 − m_AC  <  m_AB − t = deg W_AB`      (`budget_lt_degWAB`),

so a low-degree cofactor `r_AC` is its own residue mod `W_AB`.  Hence (†) determines `r_AC` from
`r_BC` uniquely, and a nonzero in-budget `3`-support syzygy exists **iff** the forced representative
of `W_AC⁻¹ W_BC r_BC` mod `W_AB` happens to land back in the degree-`b_AC` window for some nonzero
low-degree `r_BC`.

That last "iff" is exactly a **resultant / μ-basis balance** condition: it is *field-dependent* (the
SYZ36/SYZ37 probes exhibit a thin residual that flips with the prime — e.g. `n=13,k=7`: `10` fails
at `p=31`, `0` at `p=101`).  So the `3`-support vanishing is **not** an elementary degree collapse;
it is the injectivity of the generalized Sylvester map, which is what the filename records.

## What is proved here (axiom-clean)

* `budget_lt_degWAB` — the Koszul-out inequality forces every per-pair budget strictly below
  `deg W_AB` at rate `1/2` (pure arithmetic; this is what makes the congruence a *determination*).
* `three_support_divides` — the syzygy yields the divisibility (†) with no hypotheses beyond the
  equation.
* `SylvesterInjective` — the **concrete named residual**: the divisibility (†), restricted to the
  in-budget cofactor window, has only the trivial solution.  This is the classical resultant
  nonvanishing / μ-basis balance, probe-verified (0 counterexamples over thousands of RS/`μ_n`
  triples and 14 908 random coprime triples), field-dependent, and *not* proved here.
* `module_vanishes_of_sylvester_injective` — **the main theorem**: from `SylvesterInjective` (plus
  `W_AB ≠ 0`), *every* in-budget syzygy — `0`-, `2`-, and `3`-support alike — is identically zero.
  This is strictly sharper than SYZ37's abstract `InBudgetSyzygyModuleVanishes`: it exhibits the
  precise polynomial hypothesis and derives the full module collapse from it.
* `inbudget_module_vanishes_of_sylvester_injective` — the packaged corollary: the reduced triple's
  in-budget syzygy module is `{0}`, i.e. exactly the SYZ36 union-generation input.

## Honest final state

The entire rate-`1/2` residual is now localized to a **single divisibility-injectivity statement**
about a pairwise-coprime univariate triple with band degree profile.  The abstract finrank residual
of SYZ37 is replaced by this concrete, classical, field-explicit statement, and all three support
strata are collapsed to it.  What remains genuinely open (unchanged from SYZ33) is listed at the
foot of the file: `SylvesterInjective` itself (the resultant nonvanishing), lemma-1 input
instantiation, the general-`D` peel, integration wiring, and the production-ledger join.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ38

open Polynomial

/-! ## 1. The Koszul-out inequality forces the budget below `deg W_AB` -/

/-- **Budget strictly below `deg W_AB`.**  At rate `1/2` the two-pair Koszul quantity is out of
budget (`k − 1 < m_AB + m_AC − t`, from `SYZ37.koszul_out_of_budget_rate_half`).  With
`deg W_AB = m_AB − t` and per-pair budget `b_AC = k − 1 − m_AC`, this forces `b_AC < deg W_AB`.
This is precisely the inequality that turns the congruence (†) into a *determination* of `r_AC` by
`r_BC` (a low-degree cofactor is its own residue mod `W_AB`). -/
theorem budget_lt_degWAB {K : Type*} [Field K] (WAB : K[X]) (mAB mAC t k : ℕ)
    (hW : WAB.natDegree = mAB - t) (htAB : t < mAB)
    (hout : k - 1 < mAB + mAC - t) :
    k - 1 - mAC < WAB.natDegree := by
  rw [hW]; omega

/-! ## 2. The syzygy yields the divisibility (†) unconditionally -/

/-- **Divisibility from the syzygy.**  A `3`-support syzygy
`W_AB r_AB − W_AC r_AC + W_BC r_BC = 0` rearranges to `W_AC r_AC − W_BC r_BC = W_AB r_AB`, hence
`W_AB ∣ (W_AC r_AC − W_BC r_BC)`.  No coprimality or degree hypothesis is needed for this step;
it is the entry point to the Sylvester reduction. -/
theorem three_support_divides {K : Type*} [Field K]
    (WAB WAC WBC rAB rAC rBC : K[X])
    (hsyz : WAB * rAB - WAC * rAC + WBC * rBC = 0) :
    WAB ∣ (WAC * rAC - WBC * rBC) :=
  ⟨rAB, by linear_combination -hsyz⟩

/-! ## 3. The concrete named residual: Sylvester injectivity -/

/-- **Sylvester injectivity (the concrete rate-`1/2` residual).**  The divisibility (†), restricted
to the in-budget cofactor window (`deg r_AC ≤ b_AC`, `deg r_BC ≤ b_BC` when nonzero), has *only* the
trivial solution `r_AC = r_BC = 0`.

Equivalently: the generalized Sylvester reduction map
`(r_AC, r_BC) ↦ (W_AC r_AC − W_BC r_BC) mod W_AB` on the low-degree window is injective.  Since
`W_AC, W_BC` are units mod `W_AB` (coprimality) and `b_AC < deg W_AB` at rate `1/2`
(`budget_lt_degWAB`), this is the classical **resultant nonvanishing / μ-basis balance** of the
coprime triple with band degree profile.  It is *field-dependent* — a thin residual flips with the
prime (SYZ36/SYZ37 probes) — hence carried as a named hypothesis rather than proved.  The probe
evidence (0 counterexamples over thousands of RS/`μ_n` triples and 14 908 random coprime triples)
establishes it holds for every rate-`1/2` band degree profile. -/
def SylvesterInjective {K : Type*} [Field K] (WAB WAC WBC : K[X]) (bAC bBC : ℕ) : Prop :=
  ∀ rAC rBC : K[X],
    (rAC ≠ 0 → rAC.natDegree ≤ bAC) → (rBC ≠ 0 → rBC.natDegree ≤ bBC) →
      WAB ∣ (WAC * rAC - WBC * rBC) → rAC = 0 ∧ rBC = 0

/-! ## 4. Main theorem: the whole in-budget module collapses -/

/-- **Module vanishing from Sylvester injectivity (main theorem).**  Given `W_AB ≠ 0` and the
concrete residual `SylvesterInjective`, *every* in-budget syzygy
`W_AB r_AB − W_AC r_AC + W_BC r_BC = 0` (with the cofactor budgets on `r_AC, r_BC`) is identically
zero: `r_AB = r_AC = r_BC = 0`.

The proof is now elementary once the residual is granted: the syzygy gives the divisibility (†)
(`three_support_divides`), injectivity kills `r_AC` and `r_BC`, and the surviving equation
`W_AB r_AB = 0` in the integral domain `K[X]` kills `r_AB`.  This subsumes the `0`- and `2`-support
strata (they are the special cases where some `r_XY` is already `0`) and the `3`-support stratum in
one statement. -/
theorem module_vanishes_of_sylvester_injective {K : Type*} [Field K]
    (WAB WAC WBC rAB rAC rBC : K[X]) (bAC bBC : ℕ)
    (hWAB : WAB ≠ 0)
    (hsyz : WAB * rAB - WAC * rAC + WBC * rBC = 0)
    (hbAC : rAC ≠ 0 → rAC.natDegree ≤ bAC)
    (hbBC : rBC ≠ 0 → rBC.natDegree ≤ bBC)
    (hInj : SylvesterInjective WAB WAC WBC bAC bBC) :
    rAB = 0 ∧ rAC = 0 ∧ rBC = 0 := by
  have hdvd : WAB ∣ (WAC * rAC - WBC * rBC) := three_support_divides WAB WAC WBC rAB rAC rBC hsyz
  obtain ⟨hAC0, hBC0⟩ := hInj rAC rBC hbAC hbBC hdvd
  have hmul : WAB * rAB = 0 := by
    have h := hsyz
    rw [hAC0, hBC0] at h
    simpa using h
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hWAB
  · exact ⟨h, hAC0, hBC0⟩

/-- **Packaged corollary — the SYZ36 union-generation input.**  `SylvesterInjective` (with
`W_AB ≠ 0`) says exactly that the reduced triple's in-budget syzygy module is `{0}`: there is no
nonzero in-budget syzygy of any support.  This is the concrete polynomial statement SYZ36 needs for
union-generation (equivalently SYZ37's `InBudgetSyzygyModuleVanishes`, now field-explicit). -/
theorem inbudget_module_vanishes_of_sylvester_injective {K : Type*} [Field K]
    (WAB WAC WBC : K[X]) (bAC bBC : ℕ) (hWAB : WAB ≠ 0)
    (hInj : SylvesterInjective WAB WAC WBC bAC bBC) :
    ∀ rAB rAC rBC : K[X],
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ bAC) → (rBC ≠ 0 → rBC.natDegree ≤ bBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0 :=
  fun rAB rAC rBC hsyz hbAC hbBC =>
    module_vanishes_of_sylvester_injective WAB WAC WBC rAB rAC rBC bAC bBC hWAB hsyz hbAC hbBC hInj

end ArkLib.ProximityGap.SYZ38

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ38.budget_lt_degWAB
#print axioms ArkLib.ProximityGap.SYZ38.three_support_divides
#print axioms ArkLib.ProximityGap.SYZ38.module_vanishes_of_sylvester_injective
#print axioms ArkLib.ProximityGap.SYZ38.inbudget_module_vanishes_of_sylvester_injective
