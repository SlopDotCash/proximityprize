/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Concrete, computationally-proven instances of the Weil bound on curves (Issue #232 context)

The open core of #232 reduces (see `MomentCollisionWeilConditional`, `StepanovFrobeniusReduction`,
`StepanovNonVanishing`) to the **Weil bound for curves over `𝔽_q`** — equivalently the Hasse–Weil
point count `|#C(𝔽_q) − (q+1)| ≤ 2g·√q`. The *general* (asymptotic, all-`q`) statement is genuinely
open in Lean (it is RH-for-curves, which mathlib lacks, and for the deep-interior subgroup regime it
is unsolved research). This file does the part that **is** unconditionally provable: it *proves*, by
finite computation, that the Weil/Hasse bound **holds for concrete curves over concrete fields**.

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

/-! ### A genus-2 example: the general `2g·√q` Weil scaling (`g = 2`, `deg f = 5`).

For `y² = x⁵ + x + 1` (odd degree ⟹ one point at infinity, `#C = affineCount + 1`), the genus is
`g = 2`, so the Weil bound is `|#C − (p+1)| ≤ 2·2·√p`, i.e. `(affineCount − p)² ≤ 16p`. -/

/-- The quintic for the genus-2 hyperelliptic curve `y² = x⁵ + x + 1`. -/
def quintic (p : ℕ) (x : ZMod p) : ZMod p := x ^ 5 + x + 1

/-- Genus-2 Weil bound `(affineCount − p)² ≤ 16p` over `𝔽₇`. -/
theorem weil_genus2_F7 : ((affineCount 7 (quintic 7) : ℤ) - 7) ^ 2 ≤ 16 * 7 := by decide

/-- Genus-2 Weil bound over `𝔽₁₁`. -/
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
#print axioms weil_genus2_F7
#print axioms weil_genus2_F11
#print axioms weilchar_cubic_F7
#print axioms weilchar_cubic_F11
#print axioms weilchar_cubic_F13
#print axioms weilchar_quintic_F7
#print axioms weilchar_quintic_F11
end AxiomAudit
