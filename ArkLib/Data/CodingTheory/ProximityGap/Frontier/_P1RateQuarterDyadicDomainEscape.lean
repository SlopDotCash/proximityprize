/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDimensionDeficit

/-!
# Dyadic-domain escape: the 2-adic obstruction — the subgroup refutation does NOT
# transport to the literal prize domain `μ_{2^30}`

Issue #466, P1 rate-quarter — the decisive domain round following
`_P1RateQuarterStepanovWeld.lean` (which REFUTED `StallResidual` on adversarial
domains via `n = 7·2²⁵`-coset triples).  The literal prize instance evaluates on
`μ_{2^30} ⊂ F_P^*`: every element has 2-power order
(`dyadic_element_order`, kernel), subgroups are exactly the `μ_{2^j}`, so
coset-shaped root sets have 2-power sizes.

**Probe** (`scripts/probes/probe_rate_quarter_p1_dyadic_domain_escape.py`, exact):

1. **The 2-adic window obstruction**: a binomial escape needs subgroup order `n`
   with coverage `3n ≥ M = 3(T−1) − N = 704643071` and row degree `n ≤ k − 1`,
   i.e. `n ∈ [234881024, 268435455]` — and this window lies STRICTLY between
   `2²⁷ = 134217728` and `2²⁸ = 268435456`: it contains **no 2-power** (kernel:
   `dyadic_window_empty`, `no_dyadic_binomial_escape`).  Scale-invariant: the
   window sits inside `(k/2, k)` and `k` is the 2-power (μ_256 analogue
   `[56, 63] ⊂ (32, 64)` verified).
2. **Two-level variants are blocked by triple-point counting**: shared extra
   roots of `(x^m − s)·α` are TRIPLE points, raising the coverage demand to
   `|T_α| ≥ (M − 3m)/2 = 150994944` against a degree budget of
   `k − 1 − m = 134217727` — deficit `2²⁴ + 1` (kernel: `two_level_blocked`).
   Coset-union variants reduce by the substitution `y = x^{2^j}` to the same
   problem one level down (self-similar).
3. **Exhaustive-ish dyadic census** at `μ_256 ⊂ F_65537` (domain = the literal
   256th roots of unity): exact Bezout solution dimension **0** across every
   dyadic-structured geometry (subgroup-coset truncations, coset unions,
   two-level shared sets, random domain subsets, arcs); the stall census on the
   dyadic domain never exceeded the two-pencil capacity `2(N−T+1) = 230 < 256`.

**Consequence (the decisive answer):** the Stepanov-weld refutation CANNOT be
transported to `μ_{2^30}` — `StallResidual` on the literal dyadic domain is
UNREFUTED, every known escape class is blocked there by kernel-checked
arithmetic, and the escape-free margin machinery
(`stall_budget_of_three_pencil_cover(_of_tripleFree)`,
`stall_budget_of_four_pencil_cover`) is the live route: for the dyadic domain the
`FullyAlignedTripleFree` residual is exactly "no Bezout escape on `μ_{2^30}`",
whose only known constructors are now all excluded.

**Honesty:** this does NOT prove `FullyAlignedTripleFree` for `μ_{2^30}` — escapes
outside the binomial/two-level/coset-union classes are not classified (the toy
fiber-coincidence escapes exist in general position at `Σ = 2k`; the dyadic
question is whether rank-drop `≥ M − 2k + 1 = 167772160` is achievable inside
`μ_{2^30}` — open, probe-supported negative).  `StallResidual(μ_{2^30})` remains
OPEN, not proven.  No δ* movement; the bracket `3/8 ≤ δ* ≤ 43/96 + ε` is
untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterDyadicDomainEscape

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterDimensionDeficit

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The domain's multiplicative substructure is purely dyadic -/

/-- Every element of `μ_{2^30}` has 2-power order: `x^(2^30) = 1` forces
`orderOf x = 2^i` for some `i ≤ 30`.  In particular every subgroup-coset root-set
construction on the dyadic domain uses a subgroup of 2-power order. -/
theorem dyadic_element_order {x : F} (hx : x ^ (2 ^ 30 : ℕ) = 1) :
    ∃ i ≤ 30, orderOf x = 2 ^ i := by
  have hdvd : orderOf x ∣ 2 ^ 30 := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨i, hi, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨i, hi, heq⟩

/-! ## The 2-adic window obstruction -/

/-- **The escape window contains no power of two**: `[234881024, 268435455]` lies
strictly between `2²⁷` and `2²⁸`. -/
theorem dyadic_window_empty (j : ℕ) :
    ¬ (234881024 ≤ 2 ^ j ∧ 2 ^ j ≤ 268435455) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_ge 27 j with hj | hj
  swap
  · have hle : (2 : ℕ) ^ j ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) hj
    norm_num at hle
    omega
  · have hge : (2 : ℕ) ^ 28 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    norm_num at hge
    omega

/-- The escape window in the P1 constants: coverage `3n ≥ 3(T−1) − N` forces
`n ≥ 234881024` and the row-degree budget forces `n ≤ k − 1 = 268435455`. -/
theorem escape_window_constants :
    3 * (predecessorThreshold - 1) - N = 704643071 ∧
    (704643071 + 2) / 3 = 234881024 ∧ k - 1 = 268435455 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **No dyadic binomial escape**: no divisor of `2^30` (= subgroup order of
`μ_{2^30}`) satisfies both the coverage floor `3(T−1) − N ≤ 3n` and the degree
budget `n ≤ k − 1`.  The Stepanov-weld refutation (which used `n = 7·2²⁵`) cannot
be transported to the literal dyadic prize domain. -/
theorem no_dyadic_binomial_escape (n : ℕ) (hdvd : n ∣ 2 ^ 30) :
    ¬ (3 * (predecessorThreshold - 1) - N ≤ 3 * n ∧ n ≤ k - 1) := by
  rintro ⟨h1, h2⟩
  obtain ⟨j, _hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  exact dyadic_window_empty j (by omega)

/-! ## The two-level construction is blocked -/

/-- **Two-level dyadic constructions are blocked by triple-point counting**: with
subgroup level `m = 2²⁷` (the largest admissible power below the window) and shared
extra roots `T_α` (which are TRIPLE points, raising the coverage demand to
`3m + 2|T_α| ≥ M`), the demand `|T_α| ≥ 150994944` exceeds the entire remaining
degree budget `k − 1 − 2²⁷ = 134217727` — deficit `2²⁴ + 1 = 16777217`. -/
theorem two_level_blocked :
    2 * (k - 1 - 2 ^ 27) + 3 * 2 ^ 27 <
      3 * (predecessorThreshold - 1) - N ∧
    (3 * (predecessorThreshold - 1) - N - 3 * 2 ^ 27 + 1) / 2 -
      (k - 1 - 2 ^ 27) = 16777217 := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- The obstruction is scale-invariant: at the μ_256 ratios the window `[56, 63]`
sits strictly between `2⁵ = 32` and `2⁶ = 64 = k` (probe section A), and the
two-level demand `36` exceeds the budget `31` (probe section B). -/
theorem mu256_dyadic_obstruction :
    (3 * (142 - 1) - 256 + 2) / 3 = 56 ∧ 32 < 56 ∧ 63 < 64 ∧
    (3 * (142 - 1) - 256 - 3 * 32 + 1) / 2 = 36 ∧ 64 - 1 - 32 = 31 ∧ 31 < 36 := by
  norm_num

/-! ## The restored route (documentation)

With every known escape class excluded on `μ_{2^30}`:

* `FullyAlignedTripleFree dom u₀ u₁` for dyadic `dom` is UNREFUTED and all its
  known potential counterexample constructors are kernel-blocked above;
* the conditional compositions remain the live route verbatim (they are
  domain-generic): `stall_budget_of_three_pencil_cover_of_tripleFree`
  (`_P1RateQuarterDimensionDeficit`) and the margin/four-pencil budgets
  (`_P1RateQuarterPencilHarvestCap`);
* the remaining open content for the literal prize domain: (a) escapes outside
  the classified constructions (rank-drop `≥ 167772160` inside `μ_{2^30}` —
  probe-supported negative, unproven), (b) margin growth for `≥ 5` pencils,
  (c) cover-by-few-pencils. -/

/-- The rank-drop any unclassified dyadic escape must achieve:
`M − 2k + 1 = 167772161` — the same forced-coincidence constant as the
fully-aligned overlap floor. -/
theorem unclassified_escape_rank_drop :
    3 * (predecessorThreshold - 1) - N - 2 * k + 1 = 167772160 ∧
    3 * (predecessorThreshold - 1) - N - 2 * (k - 1) = 167772161 := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- **Sparse-uncertainty scale no-go.**  The first genuinely higher dyadic
sparse extremizer (`s=2`, four terms) already has `3N/4 = 805306368` roots,
whereas an unclassified Bezout escape needs only `167772160` ranks of defect.
Thus any argument that treats one relation polynomial solely through a generic
dyadic sparse-root upper bound has over `637` million coordinates of slack and
cannot exclude the required rank drop.  A successful proof must use the coupled
identity among all three Bezout polynomials, not single-polynomial uncertainty. -/
theorem dyadic_sparse_floor_far_exceeds_escape_rank_drop :
    3 * (N / 4) = 805306368 ∧
      3 * (predecessorThreshold - 1) - N - 2 * k + 1 = 167772160 ∧
      167772160 + 637534208 = 3 * (N / 4) := by
  constructor
  · norm_num [N]
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterDyadicDomainEscape

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterDyadicDomainEscape

#print axioms dyadic_element_order
#print axioms dyadic_window_empty
#print axioms escape_window_constants
#print axioms no_dyadic_binomial_escape
#print axioms two_level_blocked
#print axioms mu256_dyadic_obstruction
#print axioms unclassified_escape_rank_drop
#print axioms dyadic_sparse_floor_far_exceeds_escape_rank_drop
