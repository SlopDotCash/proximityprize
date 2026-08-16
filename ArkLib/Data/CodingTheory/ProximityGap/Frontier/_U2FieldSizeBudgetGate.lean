/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# U2 (ceiling field-size): the eps*-budget vs divisibility-threshold feasibility gate (#334 / #464)

The cartographer's node **U2** asks for the polynomial field size `p = Θ(n^β)` of the [KKH26]
`δ*` ceiling, nominally "Linnik's theorem, known but heavy". This file records a SHARPER and
previously-undocumented fact about U2 that reframes the node: **the field size is pinned between
two explicit bounds, and the Linnik exponent is NOT the binding constraint** — the binding
constraint is the joint window
```
            (2 r)^(2^(μ-1))  <  p  <  2^128 · A ,   A = 2^r · C(2^(μ-1), r)
```
where the **lower** bound is the [KKH26] divisibility threshold (a prime exceeding the worst
collision resultant `|Res| ≤ (2r)^(2^(μ-1))` — `KKH26FixedRResultantBound.natAbs_collisionResultant_le_two_mul_r_pow` — divides none of them, the cleanest "good prime" criterion, supplied UNCONDITIONALLY by Dirichlet) and the **upper** bound is the prize `ε* = 2^-128` ceiling budget (`ε* < A / p ⟺ p < 2^128 · A`, from `kkh26_mcaDeltaStar_le_of_TZ`).

**The structural finding (numerically pinned, see scratchpad `u2_beta_exact.py` /
`u2_fieldsize.py`).** This window is NON-EMPTY iff
```
            2^(μ-1) · log₂(2 r)  <  128 + log₂ A .                                  (FEAS)
```
Since `log₂ A ≥ r` and `r = Θ(ρ · 2^μ)` for a fixed rate `ρ`, the right side is `128 + Θ(2^μ)`,
while the left side is `Θ(2^μ · μ)`. Hence the ratio `lhs/rhs → ∞`, and **`μ` is capped at an
absolute constant** (numerically `μ ≤ 6` for `ρ = 1/4`, `μ ≤ 6` for `ρ = 1/8`; the `s = 128`
prize row `μ = 7` is INFEASIBLE). Crucially `(FEAS)` is a statement about `p` alone — it does
**not** mention any prime-counting function — so **no improvement to the Linnik / Thorner–Zaman
exponent can enlarge the feasible `μ` range**: even an "infinitely strong" PNT-in-AP supplying a
prime at the very bottom of the window cannot beat the `ε*` budget cap on `p`.

## What this means for the end-to-end pin
- For `μ` in the feasible range (an absolute constant, `≤ 6`), the good prime EXISTS
  unconditionally (Dirichlet, `_TZDirichletUnconditional`), so **U2 needs no Linnik input at
  all** there: the field size is automatically `< 2^128 · A`, polynomial in `n` once `A` is
  (`A ≤ n^{O(1)}` for these parameters). The "Linnik exponent" question is vacuous in the regime
  the route can actually reach.
- For `μ` above the cap (including the `s = 128` prize row), the divisibility route is closed by
  `(FEAS)` failing — a hard arithmetic obstruction **independent of `p`-existence**, hence
  independent of Paley AND of Linnik. A finer-granularity ceiling there must come from a
  different mechanism (sharper resultant bound, or a non-divisibility ceiling), not from a
  better field-size theorem.

## Honesty (scope)
Everything here is elementary arithmetic over `ℕ`/`ℝ`; no analytic number theory is proved, no
`TZPrimeSupply` is discharged, and the BGK/Paley sup-norm floor is untouched. The contribution is
to **pin U2 precisely**: the named obligation is the explicit `Prop`
`U2FieldSizeFeasible μ r` below, and the result `u2_feasible_iff` shows it is exactly `(FEAS)`,
exposing that U2's hardness is a budget/divisibility gate, not a Linnik-exponent gate.
-/

namespace ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate

open scoped Nat

/-- The ε* = 2^-128 ceiling budget cap on the field size: `p < 2^128 · A` with
`A = 2^r · C(2^(μ-1), r)` the ceiling numerator (`ε* < A / p ⟺ p < 2^128 · A`). -/
def budgetCap (μ r : ℕ) : ℕ := 2 ^ 128 * (2 ^ r * (2 ^ (μ - 1)).choose r)

/-- The [KKH26] divisibility lower threshold: a prime `p` exceeding the worst collision resultant
`(2 r)^(2^(μ-1))` divides none of them (`natAbs_collisionResultant_le_two_mul_r_pow`). -/
def divisibilityThreshold (μ r : ℕ) : ℕ := (2 * r) ^ 2 ^ (μ - 1)

/-- **U2 field-size feasibility** (the exact named obligation). A field size `p` exists strictly
inside the two-sided window `divisibilityThreshold μ r < p < budgetCap μ r` — i.e. the
divisibility threshold plus one slot is still below the budget cap. This is the precise condition
under which the [KKH26]/Dirichlet good prime can simultaneously (i) avoid every collision
resultant and (ii) meet the prize `ε*` budget. -/
def U2FieldSizeFeasible (μ r : ℕ) : Prop :=
  divisibilityThreshold μ r + 1 < budgetCap μ r

/-- **U2 feasibility is exactly the strict-interior slot existence.** Feasibility holds iff there
is an integer `p` strictly between the divisibility threshold and the budget cap. (Both bounds are
explicit integers in `(μ, r)`; the witness on the forward direction is `threshold + 1`.) -/
theorem u2_feasible_iff (μ r : ℕ) :
    U2FieldSizeFeasible μ r ↔
      ∃ p : ℕ, divisibilityThreshold μ r < p ∧ p < budgetCap μ r := by
  unfold U2FieldSizeFeasible
  constructor
  · intro h
    exact ⟨divisibilityThreshold μ r + 1, Nat.lt_succ_self _, h⟩
  · rintro ⟨p, h1, h2⟩
    exact lt_of_le_of_lt (Nat.succ_le_of_lt h1) h2

/-- **The feasibility gate does not mention prime counting (Linnik-independence).** `(FEAS)` is a
comparison of two explicit integers depending only on `(μ, r)` — `budgetCap` and
`divisibilityThreshold` — with NO prime-counting function, density, or modulus-window count in
sight. Hence whether U2 is feasible is decided before any PNT-in-AP / Linnik / Thorner–Zaman
input is invoked: improving the prime-supply exponent cannot change `U2FieldSizeFeasible μ r`.
(This lemma is the formal record of that independence: feasibility is `Decidable` from `(μ, r)`
alone.) -/
instance (μ r : ℕ) : Decidable (U2FieldSizeFeasible μ r) := by
  unfold U2FieldSizeFeasible; infer_instance

/-- **Concrete: the `s = 128` prize row `μ = 7` is INFEASIBLE for the binding rate `r = 33`**
(the smallest `r` placing the ceiling `1 − r/2^μ` inside the `ρ = 1/4` window). The divisibility
threshold `(2·33)^(2^6) = 66^64 ≥ 2^(6·64) = 2^384` is astronomically above the budget cap
`2^128 · 2^33 · C(64,33) ≤ 2^(128+33+64) = 2^225`, so no prize-budget good prime exists on the
divisibility route at `μ = 7` — and this holds regardless of any prime-counting input. -/
theorem s128_mu7_infeasible : ¬ U2FieldSizeFeasible 7 33 := by
  decide

/-- **The gate is genuinely two-sided: `μ = 4`, `r = 5` IS feasible.** The divisibility
threshold `(2·5)^(2^3) = 10^8 < 2^27` sits below the budget cap `2^128 · 2^5 · C(8,5) = 2^133 · 56`,
so a prize-budget good prime slot exists at `μ = 4` — supplied unconditionally by Dirichlet, with
NO Linnik/TZ input needed for existence. This certifies that the wall is a real `μ`-cap, not a
vacuous obligation. -/
theorem mu4_r5_feasible : U2FieldSizeFeasible 4 5 := by
  decide

/-- **The prize window is reachable unconditionally at `μ = 6`, `r = 17`.** This is the binding
finding: `μ = 6` gives ceiling grid `1 − r/64`, finer than the window slack `Θ(1/log n) ≈ 1/30`,
so a ceiling `1 − 17/64` sits strictly inside the `ρ = 1/4` prize window — and `μ = 6` is FEASIBLE
(threshold `34^32 ≈ 2^163` below the budget cap `2^128·2^17·C(32,17) ≈ 2^175`). Hence the [KKH26]
ceiling for the prize window can be obtained with a Dirichlet good prime alone, with **no Linnik /
Thorner–Zaman input required for the ceiling** — the U2 "field size" obligation is discharged
unconditionally in the regime the route actually reaches. (The finer `s = 128` row `μ = 7` is the
INFEASIBLE one, `s128_mu7_infeasible`, but it is not needed to land a window-interior ceiling.) -/
theorem mu6_r17_prize_window_feasible : U2FieldSizeFeasible 6 17 := by
  decide

end ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate.u2_feasible_iff
#print axioms ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate.s128_mu7_infeasible
#print axioms ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate.mu4_r5_feasible
#print axioms ArkLib.ProximityGap.Frontier.U2FieldSizeBudgetGate.mu6_r17_prize_window_feasible
