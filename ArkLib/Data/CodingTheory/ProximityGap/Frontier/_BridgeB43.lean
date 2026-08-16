/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Bridge B43 — base cases of the `#bad` graded count over `ZMod 4` (target E6, #444)

**Spec.** Define the `fhat` graded count in Lean over `ZMod 4` (`n = 4`) and prove the two base
cases `#bad_4(1,1)` and `#bad_4(1,2)` explicitly by `decide` / `Finset.card`.

## Context — the EXACT FFT-graded recursion E6

E6 (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) asserts the 2-adic
self-similarity of the graded obstruction count:

  `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`  and  `#bad_{2n}(k, odd) = 0`.

Here `#bad_n(k, m)` counts the *distinct nonzero* graded frequency vectors `fhat A` arising from
`(k+m)`-subsets `A ⊆ ZMod n` (with the lower graded pieces zero in the full E6 setup). This file
provides a concrete, *computable* base-case model at the smallest tower level `n = 4`.

## The concrete model (computable, decidable)

For `n = 4`, `μ_4 = {1, i, -1, -i}` and the additive character is `ω^(a·b)` with `ω = i = exp(2πi/4)`.
The graded frequency vector of a subset `A ⊆ ZMod 4` is the integer-pair-valued

  `fhat A b := ∑_{a ∈ A} (cos, sin)` of angle `2π·(a*b)/4`,

i.e. `ω^{a·b} ∈ {(1,0), (0,1), (-1,0), (0,-1)}` for `a·b ≡ 0,1,2,3 (mod 4)`. We realize this with the
exact lattice value `gaussUnit : ZMod 4 → ℤ × ℤ` (the four 4th-roots of unity on the `ℤ[i]`
lattice), so `fhat A : ZMod 4 → ℤ × ℤ` is exactly computable and `DecidableEq`, and the
`#bad` count is an honest `Finset.card` of the image of `fhat` over `(k+m)`-subsets, minus the zero
vector.

## What this file proves (LANDED, axiom-clean)

* `gaussUnit` / `fhat` — the concrete computable graded-frequency model over `ZMod 4`;
* `numBad` — the `#bad_4(k,m)` count as a `Finset.card`;
* `numBad_4_1_1` — `#bad_4(1,1) = 6`  (`decide`): all `C(4,2)=6` two-subsets give distinct
  nonzero graded vectors;
* `numBad_4_1_2` — `#bad_4(1,2) = 4`  (`decide`): all `C(4,3)=4` three-subsets give distinct
  nonzero graded vectors.

These pin the two base cases the E6 recursion is anchored at; the recursion step itself (even fold +
odd vanishing, the latter landed in `_BridgeB35`/`_Bridge05`) is a separate brick.

Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB43

/-- The four 4th-roots of unity `ω^j = i^j` realized exactly on the Gaussian-integer lattice
`ℤ × ℤ ≅ ℤ[i]`: `ω^0 = (1,0)`, `ω^1 = (0,1)`, `ω^2 = (-1,0)`, `ω^3 = (0,-1)`. The argument is an
exponent in `ZMod 4`. This is the exact additive character `a ↦ i^a` on `ZMod 4`, fully computable
and with decidable equality (so image-cardinalities are `decide`-able). -/
def gaussUnit : ZMod 4 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

/-- **Graded frequency vector (`fhat`).** For a subset `A ⊆ ZMod 4`, its graded frequency at
frequency `b` is the Gauss period `∑_{a ∈ A} ω^{a·b} = ∑_{a ∈ A} gaussUnit (a*b)`, valued in the
exact lattice `ℤ × ℤ`. `fhat A : ZMod 4 → ℤ × ℤ` is the full frequency vector. -/
def fhat (A : Finset (ZMod 4)) : ZMod 4 → ℤ × ℤ :=
  fun b => ∑ a ∈ A, gaussUnit (a * b)

/-- The family of `(k+m)`-element subsets of `ZMod 4` whose graded frequency `fhat` is used to form
the `#bad` count. `powersetCard (k+m) univ` enumerates all `(k+m)`-subsets. -/
def subsets (k m : ℕ) : Finset (Finset (ZMod 4)) :=
  (Finset.univ : Finset (ZMod 4)).powersetCard (k + m)

/-- **The `#bad_4(k,m)` count.** The number of *distinct nonzero* graded frequency vectors `fhat A`
over all `(k+m)`-subsets `A ⊆ ZMod 4`. We take the image of `fhat` over the `(k+m)`-subsets, then
remove the zero vector (the all-`(0,0)` frequency), and count. This is an honest `Finset.card`. -/
def numBad (k m : ℕ) : ℕ :=
  (((subsets k m).image fhat).erase (fun _ => (0, 0))).card

/-- **Base case `#bad_4(1,1) = 6`.** Over the `2`-subsets of `ZMod 4` (`k+m = 2`), there are exactly
`6 = C(4,2)` distinct nonzero graded frequency vectors. Proved by `decide` (finite, exact). -/
theorem numBad_4_1_1 : numBad 1 1 = 6 := by decide

/-- **Base case `#bad_4(1,2) = 4`.** Over the `3`-subsets of `ZMod 4` (`k+m = 3`), there are exactly
`4 = C(4,3)` distinct nonzero graded frequency vectors. Proved by `decide`. -/
theorem numBad_4_1_2 : numBad 1 2 = 4 := by decide

/-- Cross-check: the all-frequency model is genuinely nontrivial — the `2`-subset image (before
erasing the zero vector) has more than one element, so `numBad` is not measuring an empty/degenerate
object. -/
theorem image_1_1_nontrivial : 1 < ((subsets 1 1).image fhat).card := by decide

end ArkLib.ProximityGap.BridgeB43

/-! ## Axiom audit (expected: no axioms, or `propext, Classical.choice, Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.BridgeB43.numBad_4_1_1
#print axioms ArkLib.ProximityGap.BridgeB43.numBad_4_1_2
#print axioms ArkLib.ProximityGap.BridgeB43.image_1_1_nontrivial
