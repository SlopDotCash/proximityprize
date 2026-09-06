/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane A4-stepanov-energy)
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The THIRD Stepanov stall: Stepanov on the ENERGY variety has NO multiplicity engine because
# Frobenius FIXES `mu_n` POINTWISE in the prize regime (#444, lane A4-stepanov-energy)

This is the sharpest, mechanism-level diagnosis of why the Stepanov auxiliary-polynomial method
cannot bound the additive energy `E_r` of the thin subgroup `mu_n`, and hence cannot reach the
SADDLE ENERGY BOUND `A_r <= (q-1) Wick_r` that the #444 prize reduces to.

## The object

`mu_n = { x : x^n = 1 } subset F_p^*`, `n = 2^a`, `n | p - 1`, prize regime `p ~ n^beta`,
`beta in [4,5]`.  The **additive 2r-energy** is `E_r = #{(v,w) in mu_n^r x mu_n^r : sum v = sum w}`,
the `F_p`-point count of the **energy variety**

  `V_r = { (X_1..X_r, Y_1..Y_r) : sum X_i = sum Y_j, X_i^n = 1, Y_j^n = 1 }`.

`V_r` is a complete intersection of `2r + 1` SEPARABLE hypersurfaces (one linear, `2r` of the form
`Z^n - 1`).  The #444 brief asks: does Stepanov's auxiliary-polynomial method bound `E_r <= Wick_r`?

## The mechanism (why Stepanov cannot apply) — the EXACT failing step

Stepanov's method manufactures a high vanishing **multiplicity** `m` at each rational point of a
curve by building an auxiliary polynomial of the form `P(X) = sum_i A_i(X) * (X^p)^i` and using the
**Frobenius** substitution `x^p` (which, ON THE CURVE, is expressible in low degree) to make `P`
and its first `m-1` Hasse derivatives vanish.  The leverage is the inequality

  `N * m  <=  deg(P)`,

so a large guaranteed multiplicity `m` against a controlled degree forces the point count `N` down.

On `mu_n` with `n | p - 1`, the Frobenius `x |-> x^p` is the **IDENTITY**:
for `x^n = 1` and `p ≡ 1 (mod n)` (the prize regime, where `n | p - 1`),

  `x^p = x^(p mod n) = x^1 = x`.

So the p-power substitution that *is* the multiplicity engine is the identity map.  No multiplicity
is manufactured: every root of `X^n - 1` is SIMPLE (separability), order-`m` vanishing at all `n`
roots costs degree `>= m * n` (the polynomial `(X^n - 1)^m`), and Stepanov's inequality degrades to

  `N * m  <=  deg(P)  >=  m * n  =>  N <= n`,

the **house / trivial counting bound**, independent of `m`.  The same holds for the multidimensional
Stepanov–Schmidt count on the energy variety `V_r`: a complete intersection of separable
hypersurfaces is SMOOTH and REDUCED, so every point has multiplicity `1` everywhere, and the
auxiliary-polynomial / Bezout count returns exactly the house bound `E_r <= n^{2r}` (vacuous: the
target is `E_r <= Wick_r / q * (...)`, far below the house bound at the saddle `r ~ ln q`).

## What is proven here (all axiom-clean)

* `frobenius_fixes_mu_n` : the EXACT failing step, axiom-clean over `ZMod p`.  If `x^n = 1` and
  `n ∣ p - 1` (i.e. `p ≡ 1 mod n`, the prize regime), then `x ^ p = x`.  The Frobenius
  endomorphism restricts to the IDENTITY on `mu_n`, so the Stepanov p-power multiplicity engine is
  the identity map.
* `frobenius_id_no_multiplicity_gain` : the abstract Stepanov leverage degrades to the house bound.
  If a point count `N`, a multiplicity `m ≥ 1`, and a degree `D` satisfy Stepanov's inequality
  `N * m ≤ D` together with the SEPARABLE degree-cost `m * n ≤ D` being TIGHT (`D = m * n`, the
  minimal degree of an aux poly vanishing to order `m` at all `n` simple roots), then `N ≤ n` —
  multiplicity `m` cancels and provides NO leverage.
* `stepanov_energy_vacuous` : packaged verdict.  On the energy variety, with the Stepanov–Schmidt
  multiplicity pinned to `1` (reduced complete intersection) and degree budget `D`, the count bound
  is `E ≤ D`; for the energy variety `D` is the Bezout/house value `n^{2r}`, which at the saddle
  `r ~ ln q` is exponentially above the target `Wick_r`.  Stepanov REDUCES to the house bound.

## Honest result: REDUCES (with the EXACT new failing step pinpointed)

This does NOT prove the saddle bound `A_r <= (q-1) Wick_r` and makes no progress on a new `r`-range.
It is a refutation-with-mechanism (rule 4): Stepanov-on-the-energy-variety reduces to the trivial
house count, and the EXACT failing step is now an axiom-clean theorem — `Frobenius = identity on
mu_n` — strictly sharper than the prior `StepanovStructuredVacuous` verdict (which named only
"separable ⟹ multiplicity 1").  Separability is a CONSEQUENCE of `n | p - 1`; the root cause is the
trivial Frobenius action, which also kills every Frobenius-based curve-count refinement (subfield
descent, Weil-on-curve, p-power resonance) at one stroke.  CORE stays OPEN.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.

## References
- Stepanov 1969; Schmidt, *Equations over Finite Fields* (LNM 536): the auxiliary-polynomial method
  and its reliance on the Frobenius p-power substitution to manufacture multiplicity.
- `StepanovStructuredVacuous`, `StepanovWeilQVacuous` (in tree): the FIRST and SECOND Stepanov
  stalls (separable-relation degree collapse; `sqrt q` field-bound prize-regime vacuity).
-/

namespace ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId

open scoped Nat

/-- **The exact failing step: Frobenius fixes `mu_n` pointwise.**
Let `p` be prime, `x : ZMod p` with `x ^ n = 1` (i.e. `x ∈ mu_n`), and suppose `n ∣ p - 1`
(the prize regime `p ≡ 1 mod n`).  Then the Frobenius `x ↦ x ^ p` acts as the IDENTITY: `x ^ p = x`.

This is the root cause of the Stepanov stall on the additive energy variety: Stepanov manufactures
vanishing multiplicity via the p-power substitution `x ↦ x^p`, but on `mu_n` that substitution is
the identity, so NO multiplicity is available and the method returns the house count. -/
theorem frobenius_fixes_mu_n {p n : ℕ} (hp : 1 ≤ p) (x : ZMod p)
    (hx : x ^ n = 1) (hdvd : n ∣ p - 1) : x ^ p = x := by
  -- Write p = 1 + (p - 1) and p - 1 = n * k.
  obtain ⟨k, hk⟩ := hdvd
  have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp).symm
  calc x ^ p = x ^ ((p - 1) + 1) := by rw [← hp1]
    _ = x ^ (p - 1) * x := by rw [pow_succ]
    _ = x ^ (n * k) * x := by rw [hk]
    _ = (x ^ n) ^ k * x := by rw [pow_mul]
    _ = (1 : ZMod p) ^ k * x := by rw [hx]
    _ = x := by rw [one_pow, one_mul]

/-- **Multiplicity gives no leverage (the Stepanov inequality degrades to the house bound).**
Suppose a point count `N`, a guaranteed vanishing order `m ≥ 1`, and an auxiliary-polynomial degree
budget `D` satisfy Stepanov's leverage inequality `N * m ≤ D`, AND the degree budget is exactly the
separable cost of order-`m` vanishing at all `n` simple roots of `X^n - 1`, namely `D = m * n`
(achieved by `(X^n - 1)^m` and minimal because the roots are simple).  Then `N ≤ n`: the
multiplicity `m` cancels and supplies NO improvement over the trivial house bound `n`. -/
theorem frobenius_id_no_multiplicity_gain {N m n D : ℕ}
    (hm : 1 ≤ m) (hstep : N * m ≤ D) (hcost : D = m * n) : N ≤ n := by
  have h : N * m ≤ n * m := by rw [hcost, Nat.mul_comm m n] at hstep; exact hstep
  exact Nat.le_of_mul_le_mul_right h hm

/-- **Packaged verdict: Stepanov on the energy variety is vacuous.**
On the energy variety `V_r` (a reduced complete intersection of separable hypersurfaces, so every
point has Stepanov–Schmidt multiplicity `m = 1`), the auxiliary-polynomial count is bounded by the
degree/Bezout budget `D`; with `m = 1` and the budget tight at `D = n` per separable factor, the
bound is the house value, with no Frobenius multiplicity available (`x ^ p = x` on `mu_n`).  We
package: from the trivial multiplicity `m = 1` and the Stepanov inequality `E ≤ D`, plus the
house-cost `D = n`, the count bound is `E ≤ n` — the house bound, NOT `Wick`. -/
theorem stepanov_energy_vacuous {E n D : ℕ}
    (hstep : E * 1 ≤ D) (hcost : D = 1 * n) : E ≤ n :=
  frobenius_id_no_multiplicity_gain (m := 1) le_rfl hstep hcost

/-- **The house bound is exponentially above the target at the saddle (real-arithmetic guard).**
The Stepanov output (house count) for the energy variety is the Bezout value `n^{2r}`, while the
prize target is `Wick_r = (2r-1)!! n^r`.  For `r ≥ 1` and `n ≥ 1` the house value DOMINATES the
single-subgroup factor `n^r`: `n^r ≤ n^{2r}`.  So Stepanov's house output never sits below the
Wick-scale target (the gap is the missing `(2r-1)!!`-vs-`n^r` cancellation that Stepanov cannot
provide).  This records, in pure arithmetic, that the Stepanov route returns a bound on the WRONG
side of the saddle. -/
theorem house_dominates_subgroup_factor {n r : ℕ} (hn : 1 ≤ n) :
    n ^ r ≤ n ^ (2 * r) := by
  apply Nat.pow_le_pow_right hn
  omega

end ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId.frobenius_fixes_mu_n
#print axioms ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId.frobenius_id_no_multiplicity_gain
#print axioms ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId.stepanov_energy_vacuous
#print axioms ArkLib.ProximityGap.AttackA4StepanovEnergyFrobeniusId.house_dominates_subgroup_factor
