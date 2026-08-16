/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# SP-4 (Lewko nonlinear-Roth via one-variable Weil): VACUOUS for `μ_n` at `β = 4` (#444)

## The technique under test (paper 2604.27501, Lewko)

Lewko proves an improved **nonlinear Roth** theorem: for a subset `A ⊆ F` of a finite field `F`,

  `|A| ≥ C · |F|^{5/6}  ⟹  A contains a nontrivial config (x, x+y, x+y²)`,

with the engine being **one-variable Weil estimates** on the config-count error term. The natural
test for the prize is: the same one-variable-Weil machinery counts the **cubic wraparound** char-sum
`N := #{(a,b,c) ∈ μ_n³ : a + b − c = 1 in F_p} = Σ_{t≠0} η_t² conj(η_t) e_p(−t)/p + n³/p`, which is
the **shallow additive-energy residual** `E_+(μ_n)` that `AddEnergyGcdDegreeBound` reduces to a
resultant count. Does Lewko's density theorem bound this residual?

## The exact threshold (proven below, axiom-clean)

The decisive input is purely the **applicability condition** `|A| ≥ |F|^{5/6}`. For `A = μ_n` the
order-`n` subgroup of `F_p^*` with `p = n^β` (`β` = thinness, prize is `β = 4`):

  `|μ_n| = n = p^{1/β}`,   Lewko floor `|F|^{5/6} = (n^β)^{5/6} = n^{5β/6}`.

Applicability `n ≥ n^{5β/6}` holds **iff** the exponents satisfy `1 ≥ 5β/6`, i.e.

  **`β ≤ 6/5 = 1.2`   (`β_crit = 6/5`).**

So Lewko's nonlinear-Roth / one-variable-Weil engine is non-vacuous for `μ_n` only in the *thick*
regime `β ≤ 1.2`. At the **prize thinness `β = 4`** the floor exponent is `5·4/6 = 10/3` and

  `|μ_n| = n^1   <   n^{10/3} = |F|^{5/6}`   (short by `n^{10/3 − 1} = n^{7/3} = n^{2.333…}`),

so the hypothesis `|μ_n| ≥ |F|^{5/6}` is **FALSE** — the theorem applies to nothing. This places
Lewko firmly in the **sum-product / incidence cluster that stalls at `θ = 1/4`** (`β = 4`): the
density floor `5β/6` it requires is far above the subgroup density the prize works at.

## Integer-exponent encoding (to keep the build axiom-clean)

We avoid real `rpow` for the headline vacuity by clearing the `5/6` denominator: the floor condition
`n ≥ n^{5β/6}` is, after raising to the 6th power, `n⁶ ≥ n^{5β}`. With `p = n^β` this is

  `LewkoFloorMet n p :  (μ_card)⁶ ≥ p⁵`   (i.e. `n⁶ ≥ p⁵`, the 6th-power-cleared `|A| ≥ |F|^{5/6}`).

At `β = 4` (`p = n⁴`): `p⁵ = n^{20}` and `μ⁶ = n⁶`, so `n⁶ < n^{20}` strictly for `n ≥ 2` — the
floor is never met. We prove this in clean ℕ-arithmetic (`lewko_vacuous_beta4`), and the rational
threshold `β = 6/5` separately over ℝ (`lewko_threshold_exponent`).

## What this gives for `μ_n` at `β = 4` — the EXACT exponent

The one-variable-Weil route, when it *does* fire, bounds the per-frequency sum by `√p` (the lossy
Weil per-Gauss-sum bound), giving `M ≤ √p` per frequency, i.e. exponent `α = 1` in `M ≤ n^{1−δ'}`
reads `δ' = 0` — the **census α = 1 STALL**. At `β = 4` it does not even fire (hypothesis false),
so it yields nothing beyond the trivial bound. **It does NOT improve on the stall.**

## Honest tag — VACUITY brick (expected outcome for the sum-product cluster)

This is the precise vacuity/threshold result, not a closure. Lewko's nonlinear-Roth is a genuine
new theorem, but its `|F|^{5/6}` density floor is `n^{7/3}` above `μ_n` at the prize thinness; it
joins the sum-product/incidence techniques that go vacuous at `θ = 1/4`. The genuinely-fresh lever
(Kurihara's discriminant-power formula on the resultant count) is a separate, possibly-non-vacuous
tool and is NOT what this file tests.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.

## References
- [Lewko26] Lewko. *Improved nonlinear Roth* (one-variable Weil), arXiv 2604.27501. The `|F|^{5/6}`
  density floor and the one-variable-Weil config-count engine.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement.* #444.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth

/-! ## Part 0 — the applicability predicate (6th-power-cleared `|A| ≥ |F|^{5/6}`) -/

/-- **Lewko's applicability floor, 6th-power-cleared.** The nonlinear-Roth hypothesis
`|A| ≥ |F|^{5/6}` becomes, after raising both sides to the 6th power, `|A|⁶ ≥ |F|⁵`. Here
`μcard = |A| = |μ_n| = n` and `p = |F|`. This is the *exact* applicability condition (the constant
`C` only shifts it by a multiplicative factor, irrelevant to the exponent comparison). -/
def LewkoFloorMet (μcard p : ℕ) : Prop := p ^ 5 ≤ μcard ^ 6

/-- At the prize regime `μcard = n`, `p = n⁴` (`β = 4`): the floor is `(n⁴)⁵ = n^{20} ≤ n⁶`,
i.e. `n^{20} ≤ n^6`. -/
def LewkoFloorMet_beta4 (n : ℕ) : Prop := LewkoFloorMet n (n ^ 4)

/-! ## Part 1 — THE VACUITY at `β = 4` (clean ℕ-arithmetic) -/

/-- **Key arithmetic: `(n⁴)⁵ = n^{20}`.** -/
theorem p5_eq_pow20 (n : ℕ) : (n ^ 4) ^ 5 = n ^ 20 := by
  rw [← pow_mul]

/-- **THE VACUITY (strict).** At `β = 4` and any `n ≥ 2`, Lewko's floor `(n⁴)⁵ = n^{20}` strictly
exceeds `|μ_n|⁶ = n⁶`: `n⁶ < n^{20}`. So `LewkoFloorMet n (n⁴)` is FALSE — the nonlinear-Roth
hypothesis `|μ_n| ≥ |F|^{5/6}` cannot hold for the order-`n` subgroup at the prize thinness. -/
theorem mu6_lt_p5_beta4 (n : ℕ) (hn : 2 ≤ n) : n ^ 6 < (n ^ 4) ^ 5 := by
  rw [p5_eq_pow20]
  exact Nat.pow_lt_pow_right hn (by omega)

/-- **Lewko's floor is NOT met by `μ_n` at `β = 4`** (`n ≥ 2`): `¬ LewkoFloorMet n (n⁴)`. The
theorem's density hypothesis is false for the prize subgroup, so it applies to nothing. -/
theorem not_lewkoFloorMet_beta4 (n : ℕ) (hn : 2 ≤ n) : ¬ LewkoFloorMet_beta4 n := by
  unfold LewkoFloorMet_beta4 LewkoFloorMet
  -- target: ¬ (n⁴)⁵ ≤ n⁶, i.e. n⁶ < (n⁴)⁵
  exact Nat.not_le.mpr (mu6_lt_p5_beta4 n hn)

/-- **Concrete vacuity at a prize-representative point** `n = 64`: `64⁶ < (64⁴)⁵`. Derived from the
general theorem (no `decide` on `64^20`). -/
theorem vacuity_concrete_n64 : ¬ LewkoFloorMet_beta4 64 :=
  not_lewkoFloorMet_beta4 64 (by norm_num)

/-- **The strict deficit exponent is `7/3` in `n` (= `14` in the 6th-powered form).** The 6th-power
floor `n^{20}` exceeds `μ⁶ = n⁶` by the factor `n^{14}` (and `14/6 = 7/3` un-powered). We record the
factor explicitly: `n^{20} = n^{14} · n⁶`, so the gap is a genuine `n^{14}` in the cleared form. -/
theorem deficit_factor_beta4 (n : ℕ) : (n ^ 4) ^ 5 = n ^ 14 * n ^ 6 := by
  rw [p5_eq_pow20, ← pow_add]

/-! ## Part 2 — the EXACT rational threshold `β_crit = 6/5` (over ℝ) -/

/-- **The exact threshold.** Treat the floor in exponent form: `|μ_n| = n^1` meets Lewko's floor
`|F|^{5/6} = n^{5β/6}` iff `1 ≥ 5β/6`. We prove the clean rational pin: for `n > 1` the real
inequality `(n : ℝ)^(1 : ℝ) ≥ (n^β)^((5:ℝ)/6)` (the un-cleared `|μ_n| ≥ |F|^{5/6}`) holds **iff**
`β ≤ 6/5`. This is the boundary `β_crit = 6/5 = 1.2` separating thick (Lewko fires) from thin
(vacuous); the prize `β = 4 > 6/5` is on the vacuous side. -/
theorem lewko_threshold_exponent (n : ℝ) (β : ℝ) (hn : 1 < n) :
    (n : ℝ) ^ (1 : ℝ) ≤ (n ^ β) ^ ((5 : ℝ) / 6) ↔ (6 : ℝ) / 5 ≤ β := by
  have hn0 : (0 : ℝ) ≤ n := le_of_lt (lt_trans one_pos hn)
  -- RHS = (n^β)^{5/6} = n^{β · 5/6};  LHS = n^1.  With base > 1, n^a ≤ n^b ↔ a ≤ b.
  rw [← Real.rpow_mul hn0, Real.rpow_le_rpow_left_iff hn]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Prize side: `β = 4` is on the vacuous side of the threshold.** Since `4 > 6/5`, the
applicability inequality `n^1 ≤ (n^4)^{5/6}` holds (floor is ABOVE `μ_n`), i.e. `μ_n` is below the
floor — confirming `not_lewkoFloorMet_beta4` over ℝ. (The direction flips from "fires" to
"vacuous": `μ_n ≤ floor` means the hypothesis `μ_n ≥ floor` fails.) -/
theorem lewko_floor_above_mu_beta4 (n : ℝ) (hn : 1 < n) :
    (n : ℝ) ^ (1 : ℝ) ≤ (n ^ (4 : ℝ)) ^ ((5 : ℝ) / 6) := by
  rw [lewko_threshold_exponent n 4 hn]; norm_num

/-! ## Part 3 — the consumer reading: Lewko cannot bound the cubic wraparound residual at `β = 4` -/

/-- **`LewkoBoundsCubicResidual`** — the (named, NOT proven) statement that the Lewko/one-variable-
Weil route delivers a usable bound on the cubic wraparound residual: it requires the applicability
floor `LewkoFloorMet μcard p`. We model the route as: *if* Lewko gives a residual bound, *then* its
floor was met. This is the honest direction — Lewko's conclusion is gated on its density hypothesis. -/
def LewkoRouteFires (μcard p : ℕ) : Prop := LewkoFloorMet μcard p

/-- **Consumer vacuity (PROVEN).** At `β = 4`, `n ≥ 2`, the Lewko route does NOT fire on `μ_n`:
`¬ LewkoRouteFires n (n⁴)`. Hence whatever cubic-wraparound bound Lewko's nonlinear-Roth machinery
would deliver, it is unavailable for the prize subgroup — the technique is vacuous at `θ = 1/4`. -/
theorem lewko_route_does_not_fire_beta4 (n : ℕ) (hn : 2 ≤ n) :
    ¬ LewkoRouteFires n (n ^ 4) := by
  unfold LewkoRouteFires
  exact not_lewkoFloorMet_beta4 n hn

/-- **No improvement over the census `α = 1` stall.** The Lewko route, even charitably granted its
best per-frequency output `M ≤ √p` (the lossy one-variable-Weil per-Gauss-sum bound) *when it
fires*, yields exponent `α = 1` (`δ' = 0`). We record the stall as: there is NO `n, β = 4` at which
Lewko both fires AND `μ_n` is in the prize-thin regime — the two requirements are disjoint. -/
theorem lewko_no_stall_improvement (n : ℕ) (hn : 2 ≤ n) :
    ¬ (LewkoRouteFires n (n ^ 4) ∧ True) := by
  rintro ⟨hfire, _⟩
  exact lewko_route_does_not_fire_beta4 n hn hfire

/-- **Threshold dichotomy, ℕ form.** For `n ≥ 2`: Lewko's floor is met at `β = 4` iff `n^{20} ≤ n⁶`,
which never holds. The dichotomy `β ≤ 6/5 ⟺ fires` (Part 2) places `β = 4` strictly on the vacuous
side; this ℕ statement is the machine-checked instance at the prize. -/
theorem lewko_dichotomy_beta4 (n : ℕ) (hn : 2 ≤ n) :
    LewkoFloorMet_beta4 n ↔ False := by
  constructor
  · intro h; exact not_lewkoFloorMet_beta4 n hn h
  · intro h; exact absurd h not_false

end ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth

/-! ## Axiom audit — every PROVEN theorem must show only `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.p5_eq_pow20
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.mu6_lt_p5_beta4
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.not_lewkoFloorMet_beta4
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.vacuity_concrete_n64
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.deficit_factor_beta4
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.lewko_threshold_exponent
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.lewko_floor_above_mu_beta4
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.lewko_route_does_not_fire_beta4
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.lewko_no_stall_improvement
#print axioms ArkLib.ProximityGap.Frontier.SP4LewkoWeilRoth.lewko_dichotomy_beta4
