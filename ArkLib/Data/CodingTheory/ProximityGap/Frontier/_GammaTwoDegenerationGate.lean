/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `_GammaTwoDegenerationGate` — chaining degenerates to the union bound on flat-covariance
# families (#466, essay §2.1 gate)

## The claim being gated

Talagrand `γ₂`-chaining is the canonical "L∞ from increments" tool, and on an index set of
`m` points with genuinely varied increment structure it can beat the union bound. The essay
(`docs/kb/deltastar-466-essay-novel-mathematics-2026-07-01.md` §2.1) claims chaining is NOT a
route around the #466 wall because the Gauss-period family is **exchangeable with flat
covariance**: `Var η_b = v` for all `b` and `Cov (η_a, η_b) = −v/(m−1)` for all `a ≠ b`
(the measured/derived structure; the exact off-diagonal value is forced by `Σ_b η_b = −1 ≈ 0`
mass balance). Under flat covariance the increment second moment

  `E |η_a − η_b|² = 2·v·m/(m−1)`

is the SAME for every pair `a ≠ b` — so any metric built from second-order data is a multiple
of the **discrete metric**, all chaining nets are trivial, and `γ₂`-chaining collapses to the
union bound over the `m` points, whose input is exactly the per-period sub-Gaussian tail =
form (A) of the open core. This file proves the increment-flatness identity abstractly
(pure algebra — no probability measure needed: we work with an abstract second-moment form),
which is the load-bearing step; the chaining-collapse reading is recorded in the docstring.

**What this does NOT say:** a metric built from *higher-order* or *positivity* data (essay
§2.2) is not covered — that door is deliberately left open.

## The abstract setting

`R` a commutative ring; `ip : ι → ι → R` an abstract "second-moment pairing" (think
`ip a b = E[η_a·η_b]`). Hypotheses: `ip` symmetric, `ip b b = v` constant on the diagonal,
`ip a b = w` constant off the diagonal. Conclusion: the increment quadratic form
`incr a b := ip a a + ip b b − 2 · ip a b` equals the constant `2·(v − w)` for every
off-diagonal pair — pair-independent, i.e. the "metric" is discrete. Specializing
`w = −v/(m−1)` gives the Gauss-period value `2·v·m/(m−1)`.
-/

namespace ArkLib.ProximityGap.GammaTwoDegeneration

variable {ι : Type*} {R : Type*} [CommRing R]

/-- The increment second moment associated to an abstract pairing. -/
def incr (ip : ι → ι → R) (a b : ι) : R := ip a a + ip b b - 2 * ip a b

/-- **Flat covariance ⟹ discrete increment metric.** If the pairing has constant diagonal `v`
and constant off-diagonal `w`, every off-diagonal increment equals the constant `2·(v − w)` —
no pair of frequencies is closer than any other, so second-order chaining nets are trivial. -/
theorem incr_const_of_flat (ip : ι → ι → R) (v w : R)
    (hdiag : ∀ a, ip a a = v) (hoff : ∀ a b, a ≠ b → ip a b = w) :
    ∀ a b, a ≠ b → incr ip a b = 2 * (v - w) := by
  intro a b hab
  unfold incr
  rw [hdiag a, hdiag b, hoff a b hab]
  ring

/-- The exchangeable Gauss-period specialization: with diagonal `v` and the mass-balance
off-diagonal `w = −v/(m−1)` (over a field, `m ≠ 1`), the constant increment is
`2·v·m/(m−1)`. -/
theorem incr_const_gaussPeriod {F : Type*} [Field F] (ip : ι → ι → F) (v : F) (m : F)
    (hm : m - 1 ≠ 0)
    (hdiag : ∀ a, ip a a = v) (hoff : ∀ a b, a ≠ b → ip a b = -v / (m - 1)) :
    ∀ a b, a ≠ b → incr ip a b = 2 * v * m / (m - 1) := by
  intro a b hab
  rw [incr_const_of_flat ip v (-v / (m - 1)) hdiag hoff a b hab]
  field_simp
  ring

/-- **The degeneration reading, as a Prop-level corollary.** If a "metric candidate" `d` is any
function of the increment (i.e. factors through `incr`), then on a flat family it is constant
off the diagonal: there are no non-trivial chaining scales. -/
theorem metric_from_incr_is_discrete {γ : Type*} (ip : ι → ι → R) (v w : R)
    (hdiag : ∀ a, ip a a = v) (hoff : ∀ a b, a ≠ b → ip a b = w)
    (d : ι → ι → γ) (f : R → γ) (hd : ∀ a b, d a b = f (incr ip a b)) :
    ∀ a b a' b', a ≠ b → a' ≠ b' → d a b = d a' b' := by
  intro a b a' b' hab hab'
  rw [hd a b, hd a' b',
    incr_const_of_flat ip v w hdiag hoff a b hab,
    incr_const_of_flat ip v w hdiag hoff a' b' hab']

#print axioms ArkLib.ProximityGap.GammaTwoDegeneration.incr_const_of_flat
#print axioms ArkLib.ProximityGap.GammaTwoDegeneration.incr_const_gaussPeriod
#print axioms ArkLib.ProximityGap.GammaTwoDegeneration.metric_from_incr_is_discrete

end ArkLib.ProximityGap.GammaTwoDegeneration
