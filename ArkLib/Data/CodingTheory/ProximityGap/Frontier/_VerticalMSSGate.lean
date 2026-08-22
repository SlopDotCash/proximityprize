/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# `_VerticalMSSGate` — "average the spectrum over primes" cannot beat the bad mean (#466)

## The proposal being gated

Essay §2.4 (`docs/kb/deltastar-466-essay-novel-mathematics-2026-07-01.md`): a
Marcus–Spielman–Srivastava-style attack on the ∃-form of the prize — treat the Paley adjacency
operators `{A_p}` over primes `p ≡ 1 (mod n)` as a family, hope for an interlacing structure, and
bound `min_p M(n,p)` by data of the *expected* spectrum. The essay derives two independent kills:

1. **No interlacing mechanism.** MSS interlacing comes from rank-one/signing convexity; the prime
   index carries no such structure. (Named here as the absent hypothesis
   `InterlacingFamilyOverPrimes` — nobody may consume it silently.)
2. **The mean is bad — and that kills even the best-case guarantee.** Any route of shape
   "compute family-averaged even moments, conclude a bound on the best prime" is governed by
   `min ≤ average`: the guaranteed bound on the best prime is `(avg_p Σ_b η_b(p)^{2r})^{1/(2r)}`,
   and the landed first-moment fact (`E_p[W_r] ≈ n^{2r−4}/(2r)! ≫ Wick` — *the average prime is
   bad*, in-tree via the first-moment-averaging closure) forces that guarantee ABOVE the prize
   target. This file proves the skeleton: the averaged-moment ∃-guarantee is exactly the average
   (no better), so a bad mean makes the route vacuous — as pure order arithmetic, so that no
   future "average the characteristic polynomial / spectrum over p" lane re-opens it without
   first breaking the mean-domination hypothesis.

**What survives (recorded honestly):** a *sieved* family (excluding per-`r` bad primes) is not
covered by this gate; the essay traces that route into the conjugate-count no-go at depth
`r ≈ log p` (super-polynomial resultant heights) — that reduction lives in prose/essay, not here.
-/

namespace ArkLib.ProximityGap.VerticalMSS

open Finset

/-- The absent MSS input, named so it can never be silently consumed: an interlacing-family
structure on the vertical prime family delivering the usual "some member beats the expected
root" conclusion. No mechanism is known to supply it; stated abstractly over an index type. -/
def InterlacingFamilyOverPrimes {ι : Type*} (best expectedRoot : ι → ℝ) : Prop :=
  ∀ i, best i ≤ expectedRoot i

/-- **The min ≤ average kill, moment form.** For a nonempty finite family of nonnegative
per-prime moment aggregates `S p` (think `S p = Σ_{b≠0} η_b(p)^{2r}`), some prime achieves at
most the average — and this is ALL an averaged-moment argument can guarantee. -/
theorem exists_le_average {P : Type*} (s : Finset P) (hs : s.Nonempty) (S : P → ℝ) :
    ∃ p ∈ s, S p ≤ (∑ q ∈ s, S q) / s.card := by
  by_contra h
  push Not at h
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsum : (∑ _q ∈ s, (∑ q ∈ s, S q) / s.card) < ∑ q ∈ s, S q := by
    refine Finset.sum_lt_sum_of_nonempty hs ?_
    intro q hq
    exact h q hq
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hcard)] at hsum
  exact lt_irrefl _ hsum

/-- **The gate.** If the family-averaged moment already exceeds the target's `2r`-th power
(`the mean is bad`), then the averaged-moment guarantee `∃ p, S p ≤ avg` cannot certify any
prime below the target: the bound it delivers is `≥ target^{2r}`. Pure order arithmetic —
the route's best case is the average, and the average is above target. -/
theorem averaged_moment_route_vacuous_of_bad_mean {P : Type*} (s : Finset P)
    (S : P → ℝ) (target : ℝ)
    (hbad : target ≤ (∑ q ∈ s, S q) / s.card) :
    ¬ ((∑ q ∈ s, S q) / s.card < target) := not_lt.mpr hbad

/-- Composition: even GRANTING the (mechanism-free) interlacing hypothesis with the expected
root as the guarantee, a bad expected root gives a vacuous conclusion for the target. -/
theorem verticalMSS_vacuous_of_bad_expected {ι : Type*} (best expectedRoot : ι → ℝ)
    (target : ℝ) (_hMSS : InterlacingFamilyOverPrimes best expectedRoot)
    (i : ι) (hbad : target ≤ expectedRoot i) :
    ¬ (expectedRoot i < target) := not_lt.mpr hbad

#print axioms ArkLib.ProximityGap.VerticalMSS.exists_le_average
#print axioms ArkLib.ProximityGap.VerticalMSS.averaged_moment_route_vacuous_of_bad_mean
#print axioms ArkLib.ProximityGap.VerticalMSS.verticalMSS_vacuous_of_bad_expected

end ArkLib.ProximityGap.VerticalMSS
