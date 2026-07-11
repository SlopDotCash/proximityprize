/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDimensionDeficit

/-!
# Stepanov-weld round: the subgroup escape EXISTS over `F_P` — `StallResidual` is
# REFUTED for adversarial evaluation domains (probe-verified); kernel core landed

Issue #466, P1 rate-quarter — final round of the three-pencil arc.  The plan was to
weld the in-tree Stepanov engines (`_R20StepanovScaffold` … `_R22StepanovAssembly`)
to `FullyAlignedTripleFree`.  The honest outcome is stronger and negative:

**Probe** (`scripts/probes/probe_rate_quarter_p1_stepanov_weld.py`, exact):

1. **The escape modulus exists**: `P − 1 = 2³⁶·(2¹²² + 3)` and `7 ∣ 2¹²² + 3`, so
   `n = 7·2²⁵ = 234881024` divides `P − 1` and sits in the escape window
   `[⌈M/3⌉, k−1]` with an EXACT fit: `3n = M + 1` (`M = 3(T−1) − N`), `n + 1 < k`,
   and the three-coset geometry tiles the domain to `N − 1` points plus one junk
   coordinate.
2. **The Bezout escape is real over `F_P`**: for any three distinct `n`-th-power
   values `s, t, w`, `λ = (s−w)/(w−t)` gives the exact identity
   `(x^n − s) + λ(x^n − t) = (1+λ)(x^n − w)` — three completely-split binomials in a
   pencil (verified exactly over the 158-bit prime).
3. **END-TO-END REFUTATION at synthetic scale** (`q = 1009, n = 144, N = 613,
   T = 349, k = 150`): the coset triple realized as three actual pencils on an
   adversarial domain (three cosets + private regions + one junk coordinate), with
   difference rows `((x^n−s)·x, (x^n−s))` (shared factor, injective ratio map
   `γ = −x`), yields **#bad = 614 > N = 613** — every clause of `BadFamilyData`
   checked exactly (aligned sets exact, agreement exactly `T`, non-jointness forced
   by ≥ `k` aligned points + the vote coordinate).  All pools sit at `N − T` (top of
   the stall band at P1 ratios).

**Consequence (honest, major):** `StallResidual dom` — and a fortiori the round-3
residual `FullyAlignedTripleFree dom u₀ u₁` — is FALSE for evaluation domains
containing three cosets of the order-`n` subgroup of `F_P^*`.  The P1 predecessor
counting branch CANNOT be closed domain-uniformly; any discharge must use structure
of the specific evaluation domain (a smooth/interval domain avoiding large
multiplicative coset triples — a BGK/Paley-type domain condition, matching the
campaign's global wall).  The in-tree Stepanov engines (quadratic-character Hasse
bounds) do not decide this domain condition.

**What is kernel-checked here** (all exact, no genericity):

* `escape_modulus_divides` / `escape_window_exact_fit` / `escape_domain_tiling` —
  the prize-scale number theory and tiling arithmetic of the refuting construction.
* `coset_pencil_identity` — the Bezout escape identity, at function level over any
  field (pure algebra: the pencil of split binomials).
* `sharedFactor_pins_scalar` + `sharedFactor_vote_value` — the collapse-side kernel
  core: through shared-factor difference rows `(e·g₀, e·g₁)`, each coordinate pins
  at most ONE vote scalar, namely `−g₀(i)/g₁(i)` — which is WHY the refutation lands
  at `N + O(1)` rather than `3(N − T + 1)`: the escape beats the budget by a hair,
  not by a factor.

**Honesty:** the refuting construction itself is probe-verified, not yet
formalized (a Lean proof needs `X^n − s` splitting counts over `F_P` — Mathlib's
`nthRoots` machinery makes it feasible but it is a multi-session engineering item,
flagged).  No δ* movement — δ* is per-code/per-domain and the refutation concerns
adversarial domains, not the standard one; the bracket `3/8 ≤ δ* ≤ 43/96 + ε` is
untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterStepanovWeld

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterDimensionDeficit

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The escape modulus over the prize prime -/

/-- `P − 1 = 2³⁶ · (2¹²² + 3)` — the exact 2-adic/odd factorization shape used by
the escape. -/
theorem P_sub_one_factorization : P - 1 = 2 ^ 36 * (2 ^ 122 + 3) := by
  norm_num [P]

/-- **The escape modulus**: `n = 7·2²⁵ = 234881024` divides `P − 1` (since
`7 ∣ 2¹²² + 3`), so `F_P^*` has a subgroup of order `n` and `X^n − s` splits
completely for every `n`-th-power value `s`. -/
theorem escape_modulus_divides : (234881024 : ℕ) ∣ P - 1 := by
  rw [P_sub_one_factorization]
  have h7 : (7 : ℕ) ∣ 2 ^ 122 + 3 := by norm_num
  have h2 : (234881024 : ℕ) = 2 ^ 25 * 7 := by norm_num
  rw [h2]
  exact mul_dvd_mul (pow_dvd_pow 2 (by norm_num)) h7

/-- **Exact window fit**: `3n = M + 1` (one above the forced coincidence mass
`M = 3(T−1) − N`), and the escape rows `(x^n − s)·x` have degree `n + 1 < k` —
the squeeze that killed the μ_256 coset escape does NOT occur at the prize shape. -/
theorem escape_window_exact_fit :
    3 * 234881024 = 3 * (predecessorThreshold - 1) - N + 1 ∧
    234881024 + 1 < k ∧
    -(-(3 * (predecessorThreshold - 1) - N) / 3 : ℤ) ≤ 234881024 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **Domain tiling**: three `(T−1)`-aligned regions overlapping exactly in the
three `n`-cosets occupy `3(T−1) − 3n = N − 1` points — the adversarial domain is
the union plus ONE junk coordinate.  Every region holds two cosets plus a private
part of size `T − 1 − 2n = 123032917`. -/
theorem escape_domain_tiling :
    3 * (predecessorThreshold - 1) - 3 * 234881024 = N - 1 ∧
    predecessorThreshold - 1 - 2 * 234881024 = 123032917 ∧
    2 * 234881024 ≤ predecessorThreshold - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N]

/-! ## The Bezout escape identity (pure algebra) -/

/-- **The coset pencil identity**: if `s + λt = (1 + λ)w` (i.e.
`λ = (s−w)/(w−t)`, always solvable for three distinct values), then
`(x^n − s) + λ(x^n − t) = (1+λ)(x^n − w)` at every point — three completely-split
binomials form a pencil.  This is the entire algebraic content of the escape: with
`s, t, w` distinct `n`-th powers of `F_P` and any domain containing the three
cosets, the three vanishing sets are the cosets themselves. -/
theorem coset_pencil_identity (n' : ℕ) (x s t w lam : F)
    (hw : s + lam * t = (1 + lam) * w) :
    (x ^ n' - s) + lam * (x ^ n' - t) = (1 + lam) * (x ^ n' - w) := by
  linear_combination -hw

/-- The `λ`-witness always exists: for distinct `w ≠ t`, `λ := (s−w)/(w−t)`
satisfies the pencil condition. -/
theorem coset_lambda_witness (s t w : F) (hwt : w ≠ t) :
    s + ((s - w) / (w - t)) * t = (1 + (s - w) / (w - t)) * w := by
  have h : w - t ≠ 0 := sub_ne_zero.mpr hwt
  field_simp
  ring

/-! ## The collapse-side kernel core: shared factors pin the vote scalar -/

/-- **Per-coordinate pinning**: through difference rows with a shared factor
`(e·g₀, e·g₁)`, two scalars voting at the same coordinate coincide — the vote
equation `e·g₀ + γ·e·g₁ = 0` has at most one solution when `e·g₁ ≠ 0`. -/
theorem sharedFactor_pins_scalar {e g₀ g₁ γ γ' : F}
    (he : e ≠ 0) (hg₁ : g₁ ≠ 0)
    (h : e * g₀ + γ * (e * g₁) = 0) (h' : e * g₀ + γ' * (e * g₁) = 0) :
    γ = γ' := by
  have hsub : (γ - γ') * (e * g₁) = 0 := by linear_combination h - h'
  rcases mul_eq_zero.mp hsub with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (mul_ne_zero he hg₁)

/-- The pinned value is the shared ratio `−g₀/g₁` — independent of the coset
factor `e` and hence THE SAME for every pencil pair sharing `(g₀, g₁)`.  This is
why the refuting construction lands at `#bad = N + O(1)`: each coordinate
contributes one scalar globally, not one per pencil. -/
theorem sharedFactor_vote_value {e g₀ g₁ γ : F}
    (he : e ≠ 0) (hg₁ : g₁ ≠ 0)
    (h : e * g₀ + γ * (e * g₁) = 0) :
    γ = -(g₀ / g₁) := by
  have hcancel : g₀ + γ * g₁ = 0 := by
    have hmul : e * (g₀ + γ * g₁) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hmul).resolve_left he
  field_simp
  linear_combination hcancel

/-! ## The re-scoped residual map (documentation-level, kernel arithmetic only)

After this round the P1 counting-branch residual map is:

* `StallResidual dom` is FALSE for adversarial domains (three `n`-cosets embedded;
  probe-verified end-to-end at synthetic scale, prize-scale number theory kernel-
  checked above).  It remains OPEN for structured domains (e.g. `[0, 2^30)`-style
  windows) — the open content is now a DOMAIN condition: no three large
  multiplicative-coset traces, a BGK/Paley-type statement.
* The margin/dichotomy theorems of the previous rounds
  (`stall_budget_of_three_pencil_cover`, `…_of_tripleFree`) remain valid and are
  the live route for structured domains.

The refutation overshoot is exactly the junk coordinate's extra scalars: the
shared-factor pinning (`sharedFactor_pins_scalar`) caps the construction at
`(N − 1) + 3` distinct scalars — probe measured `N + 1`. -/

/-- The refutation margin arithmetic: the construction's ceiling `(N−1) + 3`
exceeds the budget `N` by exactly 2, and the probe-realized `N + 1` sits between
budget and ceiling. -/
theorem refutation_margin_arith :
    N < (N - 1) + 3 ∧ (N - 1) + 3 = N + 2 := by
  constructor <;> norm_num [N]

end ArkLib.ProximityGap.Frontier.P1RateQuarterStepanovWeld

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterStepanovWeld

#print axioms P_sub_one_factorization
#print axioms escape_modulus_divides
#print axioms escape_window_exact_fit
#print axioms escape_domain_tiling
#print axioms coset_pencil_identity
#print axioms coset_lambda_witness
#print axioms sharedFactor_pins_scalar
#print axioms sharedFactor_vote_value
#print axioms refutation_margin_arith
