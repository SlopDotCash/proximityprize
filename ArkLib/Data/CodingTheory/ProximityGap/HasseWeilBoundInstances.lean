/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Concrete, computationally-proven instances of the Weil bound on curves (Issue #232 context)

The open core of #232 reduces (see `MomentCollisionWeilConditional`, `StepanovFrobeniusReduction`,
`StepanovNonVanishing`) to the **Weil bound for curves over `𝔽_q`** — equivalently the Hasse–Weil
point count `|#C(𝔽_q) − (q+1)| ≤ 2g·√q` for smooth projective curves. Two different statements
must be kept apart:
* the **classical Hasse–Weil theorem** (all `q`, all smooth projective curves; Weil 1948) is a
  known theorem of mathematics, but it is NOT formalised in Lean / mathlib (it is RH-for-curves);
* the **stronger incomplete / subgroup-restricted character-sum bound** in the deep-interior
  (thin-subgroup) regime that #232 actually needs is a different, stronger statement, and that is
  the part which is open research.
This file does the part that **is** unconditionally provable here: it *proves*, by finite
computation, that the relevant numeric inequalities **hold for concrete curves over concrete
fields**.

For the elliptic curve `y² = x³ + x + 1` (nonsingular over each field below), the projective count is
`#E = affineCount + 1`, so Hasse `|#E − (p+1)| ≤ 2√p` is exactly `(affineCount − p)² ≤ 4p` — the
genus-1 Weil bound. Each instance is closed by the kernel `decide` (axiom-clean: no `native_decide`,
no `sorryAx`).

## Honest scope
These are *verified concrete instances* of the Weil bound on curves — genuine non-conditional proofs
of the bound for specific `(curve, field)` pairs. They do **not** prove the general bound and do
**not** close #232's asymptotic open core (the subgroup character-sum bound for growing `q`);
`advancesOpenCore = false`. They certify the target inequality is true where it can be checked, and
exercise the reduction's endpoint on real data.
-/

open Finset

namespace ArkLib.CodingTheory.HasseWeilInstances

/-- The number of affine `𝔽_p`-points `(x, y)` on `y² = f x`. -/
def affineCount (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) : ℕ :=
  (Finset.univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = f xy.1)).card

/-- A cubic, used as the right-hand side of the elliptic curves below. -/
def cubic (p : ℕ) (x : ZMod p) : ZMod p := x ^ 3 + x + 1

/-! ### The genus-1 Weil (Hasse) bound `(affineCount − p)² ≤ 4p`, proven per field. -/

/-- Weil/Hasse bound for `y² = x³ + x + 1` over `𝔽₅`. -/
theorem hasse_F5 : ((affineCount 5 (cubic 5) : ℤ) - 5) ^ 2 ≤ 4 * 5 := by decide

/-- Weil/Hasse bound for `y² = x³ + x + 1` over `𝔽₇`. -/
theorem hasse_F7 : ((affineCount 7 (cubic 7) : ℤ) - 7) ^ 2 ≤ 4 * 7 := by decide

/-- Weil/Hasse bound for `y² = x³ + x + 1` over `𝔽₁₁`. -/
theorem hasse_F11 : ((affineCount 11 (cubic 11) : ℤ) - 11) ^ 2 ≤ 4 * 11 := by decide

/-- Weil/Hasse bound for `y² = x³ + x + 1` over `𝔽₁₃`. -/
theorem hasse_F13 : ((affineCount 13 (cubic 13) : ℤ) - 13) ^ 2 ≤ 4 * 13 := by decide

/-- Weil/Hasse bound for `y² = x³ + x + 1` over `𝔽₁₇`. -/
theorem hasse_F17 : ((affineCount 17 (cubic 17) : ℤ) - 17) ^ 2 ≤ 4 * 17 := by decide

/-! ### The quintic `y² = x⁵ + x + 1`: the `2g·√q` scaling with `g = 2`, `deg f = 5`.

When `f = x⁵ + x + 1` is squarefree over `𝔽_p`, `y² = f(x)` is a smooth genus-2 hyperelliptic curve
with one point at infinity (odd degree), so `#C = affineCount + 1` and the Weil bound
`|#C − (p+1)| ≤ 2·2·√p` reads `(affineCount − p)² ≤ 16p`.

**This hypothesis FAILS over `𝔽₇`.**  There `X⁵ + X + 1 = (X − 4)²·(X³ + X² + 6X + 4)`: both `f(4)`
and `f'(4) = 5·4⁴ + 1` vanish (`quintic_F7_singular`), so `(4, 0)` is a singular point, the curve is
not a smooth genus-2 curve (its normalization has smaller genus), and `affineCount + 1` is not a
smooth genus-2 projective count.  `weil_genus2_F7` is therefore only a true numeric inequality for
this singular affine curve, not an instance of the genus-2 Hasse–Weil theorem.  Over `𝔽₁₁`,
`gcd(f, f') = 1` in `𝔽₁₁[X]` (checked by a polynomial-gcd computation, not formalised here), so the
curve is smooth there and `weil_genus2_F11` is a genuine genus-2 instance. -/

/-- The quintic `x⁵ + x + 1` (right-hand side of `y² = x⁵ + x + 1`; genus 2 only where it is
squarefree, e.g. over `𝔽₁₁` but NOT over `𝔽₇`). -/
def quintic (p : ℕ) (x : ZMod p) : ZMod p := x ^ 5 + x + 1

/-- Over `𝔽₇` the quintic has a repeated root at `x = 4`: `f(4) = 0` and `f'(4) = 5·4⁴ + 1 = 0`,
so `y² = x⁵ + x + 1` is singular at `(4, 0)`. -/
theorem quintic_F7_singular : quintic 7 4 = 0 ∧ (5 * 4 ^ 4 + 1 : ZMod 7) = 0 := by decide

/-- Numeric inequality `(affineCount − p)² ≤ 16p` over `𝔽₇` for the SINGULAR affine curve
`y² = x⁵ + x + 1` (see `quintic_F7_singular`).  True, but not a smooth genus-2 Hasse–Weil
instance. -/
theorem weil_genus2_F7 : ((affineCount 7 (quintic 7) : ℤ) - 7) ^ 2 ≤ 16 * 7 := by decide

/-- Genus-2 Weil bound over `𝔽₁₁` (where `x⁵ + x + 1` is squarefree). -/
theorem weil_genus2_F11 : ((affineCount 11 (quintic 11) : ℤ) - 11) ^ 2 ≤ 16 * 11 := by decide

/-! ### The multiplicative Weil **character-sum** bound `(∑ₓ χ(f x))² ≤ (deg f − 1)²·p`.

This is the exact object #232's open core concerns: the Weil bound on a *character sum*
`|∑ₓ χ(f x)| ≤ (deg f − 1)√p`. Here `χ` is the quadratic character `χ(a) = a^((p−1)/2) ∈ {0, ±1}`
(written computably as `qc`), so the bound is the integer inequality `(∑ₓ χ(f x))² ≤ (deg f − 1)²·p`,
closed by `decide`. (The open #232 input is the *subgroup-restricted, deep-interior* analogue for
growing `q`; these are the complete-sum, fixed-`q` instances — true and proven, not the asymptotic
prize.) -/

/-- The computable quadratic character `χ : 𝔽_p → ℤ`, `χ(a) = a^((p−1)/2) ∈ {0, ±1}`. -/
def qc (p : ℕ) [NeZero p] (a : ZMod p) : ℤ :=
  if a = 0 then 0 else if a ^ ((p - 1) / 2) = 1 then 1 else -1

/-- The complete quadratic character sum `∑ₓ χ(f x)`. -/
def charSum (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) : ℤ := ∑ x : ZMod p, qc p (f x)

/-- Weil character-sum bound, cubic (`deg = 3`) over `𝔽₇`: `(∑ₓ χ(f x))² ≤ 2²·7`. -/
theorem weilchar_cubic_F7 : (charSum 7 (cubic 7)) ^ 2 ≤ 2 ^ 2 * 7 := by decide

/-- Weil character-sum bound, cubic over `𝔽₁₁`. -/
theorem weilchar_cubic_F11 : (charSum 11 (cubic 11)) ^ 2 ≤ 2 ^ 2 * 11 := by decide

/-- Weil character-sum bound, cubic over `𝔽₁₃`. -/
theorem weilchar_cubic_F13 : (charSum 13 (cubic 13)) ^ 2 ≤ 2 ^ 2 * 13 := by decide

/-- Weil character-sum bound, quintic (`deg = 5`) over `𝔽₇`: `(∑ₓ χ(f x))² ≤ 4²·7`. -/
theorem weilchar_quintic_F7 : (charSum 7 (quintic 7)) ^ 2 ≤ 4 ^ 2 * 7 := by decide

/-- Weil character-sum bound, quintic over `𝔽₁₁`. -/
theorem weilchar_quintic_F11 : (charSum 11 (quintic 11)) ^ 2 ≤ 4 ^ 2 * 11 := by decide

end ArkLib.CodingTheory.HasseWeilInstances

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.CodingTheory.HasseWeilInstances
#print axioms hasse_F5
#print axioms hasse_F7
#print axioms hasse_F11
#print axioms hasse_F13
#print axioms hasse_F17
#print axioms quintic_F7_singular
#print axioms weil_genus2_F7
#print axioms weil_genus2_F11
#print axioms weilchar_cubic_F7
#print axioms weilchar_cubic_F11
#print axioms weilchar_cubic_F13
#print axioms weilchar_quintic_F7
#print axioms weilchar_quintic_F11
end AxiomAudit
