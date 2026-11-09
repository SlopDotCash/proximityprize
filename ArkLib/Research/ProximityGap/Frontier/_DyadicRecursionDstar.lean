/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Research.ProximityGap.Frontier.SymmetricTowerBracket
import Mathlib.Tactic.NormNum

/-!
# #444 CONCRETE RUNG [dyadic-recursion-Dstar] — fixed-slice growth of a binding count (the
# two-variable recursion is NOT refuted here)

**Target.** The proposed dyadic halving recursion for the binding distinct-γ far-line count
`D*_n(m)` (`m = s − k` the stack-excess; the conjecture `m* = log₂ n + O(1)` for the window
location):

  `D*_{2n}(m) = D*_n(m−1)`     (each doubling of `n` shifts the binding excess by one).

**Verdict (corrected per audit R-307): NOT refuted by this file.** The recursion is
TWO-VARIABLE: it compares `D*` at `(2n, m)` with `D*` at `(n, m−1)`. The numerics below evaluate a
one-variable polynomial `bindingDeepCount n` on the *same described deep band* (`r = 3`, `a = 4`)
for `n = 16` and `n = 32`. That would contradict the recursion only after proving that the band at
`2n` has excess argument `m` and the compared band at `n` has argument `m − 1`; no `m` variable, band
identification, or such bridge appears here. A shifted recursion can grow at every fixed `m`:
`D(n, m) = n·2^{−m}` satisfies `D(2n, m) = D(n, m−1)` yet doubles at fixed `m`
(`shifted_recursion_can_grow_at_fixed_slice`). So fixed-slice growth alone is not a countermodel.
The earlier header's "REFUTED for the binding count" verdict is withdrawn; what is proved is only
the arithmetic inequality `bindingDeepCount 32 ≠ bindingDeepCount 16`, which refutes the
*fixed-slice value-preservation* statement `bindingDeepCount (2n) = bindingDeepCount n`, a
different (one-variable) claim.

Two facts, both machine-checked (as arithmetic / generic transport):

1. **The exact dyadic halving DOES hold — but only for the SYMMETRIC / even sub-family.**
   For an *even* codeword `g = glue e 0` (so `g(x) = e(x²)`) against an *even* word `w`, the
   squaring map `σ : μ_{2n} → μ_n` (2-to-1, fibers `{±d}`) gives the EXACT transport
   `agreement_{level 0}(glue e 0, w) = 2 · agreement_{level 1}(e, W)` — the dyadic doubling — by
   `SymmetricTowerBracket.symmetric_agreement_transport` (proven, axiom-clean, char-free). This is
   the genuine `n ↦ 2n` halving the recursion hopes for. We re-export it here as the symmetric
   instance of the rung. The transport is a generic agreement identity for arbitrary even words; the
   claim that this family is empty at the window radii (`SymmetricTowerBracket` §2 base case) and
   carries none of the binding mass needs the actual bad/far-word predicates and is not re-proved
   here.

2. **A fixed-slice binding count grows under doubling.**
   Probe `probe_dyadic_recursion_dstar.py` (BabyBear `p = 15·2²⁷+1`, `p² ≫ C(n,a)`)
   measures the binding far line `(x^{n/2}, x^{n/2−1})` at the `r=3` deep band (`a = 4`):

     `n =  8 : #bad = 8 + 1 =   9`
     `n = 16 : #bad = 96 + 1 =  97`
     `n = 32 : #bad = 896 + 1 = 897`

   These match the CONJ.md closed form `bindingDeepCount n = n·C(n/4,2) + 1` (whose derivation needs
   the no-extra-collision range of `PairSumRigidityModP`; it is not field-independent without that
   guard, cf. audit R-084/T115). This file does NOT compute actual far-line sets: it defines the
   polynomial and checks its values. The polynomial has CUBIC leading term `n³/32`. The machine-
   checked inequality `bindingDeepCount 32 = 897 ≠ 97 = bindingDeepCount 16` refutes only
   fixed-slice value preservation, not the shifted two-variable recursion (see the verdict above).

**Honest scope.** The dyadic shift `m ↦ m−1` is a real property of the *symmetric* squaring tower
(fact 1, exactly proven). For the binding count, this file neither proves nor refutes
`D*_{2n}(m) = D*_n(m−1)`: deciding it requires a genuine two-variable count `D*_n(m)`, the exact
identification of which deep band at `n` corresponds to excess `m − 1` and which band at `2n` to `m`,
and actual count witnesses at both. The fiber identity `agreement = 2|B| + s(S)`
(`_S2NonSymTower.lean`) explains why the symmetric transport's factor-2 weighting does not apply
verbatim to singleton-bearing lines, but that is a heuristic for why the recursion might fail, not a
proof that it does. Status of the rung: OPEN (fixed-slice growth recorded).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.DyadicRecursionDstar

open Polynomial Finset

/-! ## §1  The dyadic halving that DOES hold — the symmetric stratum (re-exported, proven). -/

section SymmetricHalving

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- **The exact dyadic halving on the symmetric stratum.** For an even codeword `g = glue e 0`
and an even word `w`, the level-0 agreement over the `±`-paired domain `μ_n = ⋃_{z} {y z, −y z}`
(`D₁ = μ_{n/2}`) is exactly twice the level-1 agreement of the half-degree part `e` with the
induced word `W(z) := w (y z)` on `D₁`:

  `agreement_{level 0}(glue e 0, w) = 2 · agreement_{level 1}(e, W)`.

This is the `n ↦ 2n` dyadic doubling the recursion hopes for, proven char-free in
`SymmetricTowerBracket.symmetric_agreement_transport`. It is the SYMMETRIC face of the
[dyadic-recursion-Dstar] rung. It is a statement about arbitrary even words; the assertion that the
symmetric family is empty at the window radii (`SymmetricTowerBracket` §2 base case) needs the
actual bad/far-word predicates and is not part of this theorem. -/
theorem symmetric_dyadic_halving
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (e : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => (DescentKernel.glue e 0).eval x = w x)).card
      = 2 * (D₁.filter (fun z => e.eval z = w (y z))).card :=
  SymmetricTowerBracket.symmetric_agreement_transport w hy hyne hweven e

end SymmetricHalving

/-! ## §2  The binding (non-symmetric) deep-band count: CONJ.md closed form at one fixed slice. -/

/-- The **binding deep-band far-line count** at the `r = 3` deep band (`a = 4`), for the binding
far line `(x^{n/2}, x^{n/2−1})` on the proper subgroup `μ_n` (`n = 2^μ`):

  `bindingDeepCount n = n · C(n/4, 2) + 1`.

This is the CONJ.md closed form (`#bad(n, r=3) = n·C(n/4,2)+1`, derived from the order-2
parity split → antipodal pair-product `x_a x_b + x_c x_d = 0` → `γ = −e₁(S)`, injectivity by
`A4 PairSumRigidityModP`, which needs its no-extra-collision range). Here it is only a *definition*
of the polynomial; no far-line set is computed in Lean. It reproduces the BabyBear probe values
`9 (n=8), 97 (n=16), 897 (n=32), 7681 (n=64)` (`probe_dyadic_recursion_dstar.py`). Leading term
`n³/32` (cubic). -/
def bindingDeepCount (n : ℕ) : ℕ := n * Nat.choose (n / 4) 2 + 1

/-- Calibration: the closed form matches the probe at `n = 8, 16, 32, 64` (anti-fabrication). -/
theorem bindingDeepCount_values :
    bindingDeepCount 8 = 9 ∧ bindingDeepCount 16 = 97 ∧
    bindingDeepCount 32 = 897 ∧ bindingDeepCount 64 = 7681 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold bindingDeepCount; decide)

/-- **The fixed-slice polynomial grows under doubling.** `bindingDeepCount` strictly increases from
`n` to `2n` in the tested range. This is growth at one fixed deep band; it is compatible with a
shifted two-variable recursion (see `shifted_recursion_can_grow_at_fixed_slice`). -/
theorem bindingDeepCount_strictMono_at :
    bindingDeepCount 8 < bindingDeepCount 16 ∧
    bindingDeepCount 16 < bindingDeepCount 32 ∧
    bindingDeepCount 32 < bindingDeepCount 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold bindingDeepCount; decide)

/-- **Fixed-slice inequality `bindingDeepCount 32 ≠ bindingDeepCount 16`.**

`bindingDeepCount 32 = 897 ≠ 97 = bindingDeepCount 16`, by `decide`. This refutes only the
*fixed-slice value preservation* `bindingDeepCount (2n) = bindingDeepCount n` (one variable, same deep
band at both sizes). It does NOT refute the two-variable recursion `D*_{2n}(m) = D*_n(m−1)`, which
compares DIFFERENT excess arguments; that would need the band-to-excess identification described in
the module header (audit R-307). -/
theorem bindingDeepCount_32_ne_16 :
    bindingDeepCount 32 ≠ bindingDeepCount 16 := by
  unfold bindingDeepCount; decide

/-- Legacy name of `bindingDeepCount_32_ne_16`. Despite the name, it does NOT refute the shifted
recursion `D*_{2n}(m) = D*_n(m−1)`; it is only a fixed-slice inequality (audit R-307). -/
@[deprecated bindingDeepCount_32_ne_16 (since := "2026-10-28")]
theorem dyadic_recursion_REFUTED :
    bindingDeepCount 32 ≠ bindingDeepCount 16 :=
  bindingDeepCount_32_ne_16

/-- Fixed-slice growth factor: doubling `n` multiplies `bindingDeepCount` by more than `8` (here
`9.25` at `n = 16 → 32`). Again a statement about one fixed band, not about the shifted recursion. -/
theorem dyadic_recursion_growth_ge :
    8 * bindingDeepCount 16 < bindingDeepCount 32 := by
  unfold bindingDeepCount; decide

/-- **Fixed-slice growth is compatible with the shifted recursion** (audit R-307). The two-variable
function `D(n, m) = n · 2^{−m}` satisfies `D(2n, m) = D(n, m − 1)` for all `n, m`, yet at the fixed
slice `m = 0` it doubles: `D(32, 0) ≠ D(16, 0)`. Hence growth of a count at a fixed band, by itself,
is not a countermodel to `D*_{2n}(m) = D*_n(m−1)`. -/
theorem shifted_recursion_can_grow_at_fixed_slice :
    ∃ D : ℕ → ℤ → ℚ, (∀ n m, D (2 * n) m = D n (m - 1)) ∧ D 32 0 ≠ D 16 0 := by
  refine ⟨fun n m => (n : ℚ) / (2 : ℚ) ^ m, ?_, ?_⟩
  · intro n m
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    show ((2 * n : ℕ) : ℚ) / (2 : ℚ) ^ m = (n : ℚ) / (2 : ℚ) ^ (m - 1)
    rw [zpow_sub_one₀ h2]
    push_cast
    field_simp
  · norm_num

end ArkLib.ProximityGap.DyadicRecursionDstar

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.DyadicRecursionDstar
#print axioms symmetric_dyadic_halving
#print axioms bindingDeepCount_values
#print axioms bindingDeepCount_strictMono_at
#print axioms bindingDeepCount_32_ne_16
#print axioms dyadic_recursion_growth_ge
#print axioms shifted_recursion_can_grow_at_fixed_slice
end AxiomAudit
