/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #444 — the pair-pinned scalar for the `r = 2` line, and the antipodal `γ = 0` fibre.

## Context: the supply-strip → prize-window collapse residual

`SinglePencilQIndependence.mca_badscalar_packing` proves the `q`-independent packing bound
`#bad · C(a, k+1) ≤ C(|μ|, k+1)` for the single-poly pencil `Q₀ + γ·Xᵏ`.  Its `mca_badscalar_sharp`
docstring flags the *honest residual* between this **supply-strip** count `C(n, k+1)/C(a, k+1)` and
the **prize budget** `2^r·C(2^{μ-1}, r)` as the claim that *"the pinning `(k+1)`-subsets are
coset-structured, not arbitrary"* — i.e. that the witness subsets pinning the bad scalars are forced
into the KKH26 fibre/coset shape, collapsing the supply-strip count to the prize budget.

**That coset-rigidity residual is REFUTED at the demand level** (probe
`scripts/probes/probe_pinning_subset_coset_rigidity.py`, exact mod-`p`, PROPER `μ_n`, prize primes
`p ≡ 1 (mod n)`, `p ≫ n³`, never `n = q-1`, with a thick control): on the `r = 2` worst-case line
`Q₀ = X²`, `Q₁ = X` (`k = 1`, constant codewords) over the smooth `2`-power domain `μ_n` (`n = 2^μ`),
the pinning pairs observed by the probe are **generic**, NOT coset-structured: in the probed
instances the pinned-scalar map `{x,y} ↦ γ` was close to injective, and the only high-multiplicity
collision observed was the single scalar `γ = 0`, realised by EXACTLY the `n/2` *antipodal* pairs
`{x, −x}` (and `−x = x·g^{n/2}` is the order-2 / `2`-power-coset shift).  That is a probe
observation, **not a theorem**: uniqueness of the pair pinning a nonzero scalar `γ = −(x+y)` is the
statement that `μ_n` has no nontrivial additive coincidence `x + y = x' + y'` (a Sidon-type
condition), and it is not proved here and fails in general even above `p > n³`.  Exact
counterexample: `p = 32993` (prime), `n = 32`, `g = 4612` has `g^32 = 1`, `g^16 = −1`, and
`p > 32³ = 32768`; the distinct elements `4604, 28385, 4608, 28381` of `μ_32` satisfy
`4604 + 28385 = 4608 + 28381 = −4 (mod p)`, so the two non-antipodal pairs both pin `γ = 4`.  So
the supply-strip count is attained up to the antipodal collision *and whatever additive
coincidences the particular `(p, n)` has*; either way coset rigidity does NOT collapse it to the
prize budget.

## What this file proves (the rigorous kernel of that finding)

For the `r = 2` line `X² + γ·X` and codeword class = constants (degree `< 1`):

* `pairPinnedScalar_eq` — the pinned scalar of a pair `{x, y}` (`x ≠ y`) is exactly `γ = −(x + y)`:
  the constant interpolant agrees on the pair iff `x² + γx = y² + γy`, i.e. `(x − y)(x + y + γ) = 0`.

* `pairPinned_zero_iff_antipodal` — that scalar is `0` iff `y = −x`: the `γ = 0` fibre is *exactly*
  the antipodal pairs.

* `antipodal_mem_nthRoots` — over `μ_n` (`n = 2^μ`, even), `−x ∈ μ_n` whenever `x ∈ μ_n`, so the
  antipodal partner stays in the domain: the `γ = 0` fibre is the `n/2`-element antipodal pairing,
  the coset-structured collision (other, non-coset collisions of nonzero scalars can occur; see
  the counterexample above).

All `sorry`-free, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

**Honest scope (rule 3, rule 6).** This is NOT a CORE closure and NOT thinness-essential: the pinned
scalar formula `−(x+y)` and the antipodal `γ = 0` fibre hold over ANY field, thick or thin (the probe
confirms the same genericity on thick `n = 6, 12`).  It *refutes the coset-rigidity supply→prize
mechanism* by exhibiting the coset-structured collision (a single scalar saving `n/2 − 1` of the
`Θ(C(n,2))` count) and identifying every pinned scalar as `−(x+y)`.  It does **not** prove the map
injective outside the antipodal fibre: that needs the additional Sidon-type hypothesis above, which
fails at `p = 32993`, `n = 32` (this witness extends the known Sidon-failure family above the
commonly cited `p > n³` regime; it is not a prize refutation).  The
supply-strip→prize-window collapse must come from elsewhere (the W4 sub-exponential cancellation),
NOT from the pinning subsets being coset-structured.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026 (#444).
-/

set_option linter.style.longLine false


open Polynomial

namespace ArkLib.ProximityGap.PairPinnedScalarAntipodal

variable {F : Type*} [Field F]

/-- **The pair-pinned scalar identity.**  For distinct `x, y` the `r = 2` line value
`x² + γ·x` equals `y² + γ·y` (the constant-codeword agreement condition on the pair `{x, y}`) iff
`γ = −(x + y)`.  Mechanism: `(x² + γx) − (y² + γy) = (x − y)(x + y + γ)`, and `x ≠ y` cancels the
first factor. -/
theorem pairPinnedScalar_eq {x y γ : F} (hxy : x ≠ y) :
    x ^ 2 + γ * x = y ^ 2 + γ * y ↔ γ = -(x + y) := by
  have hfac : (x ^ 2 + γ * x) - (y ^ 2 + γ * y) = (x - y) * (x + y + γ) := by ring
  constructor
  · intro h
    have hzero : (x - y) * (x + y + γ) = 0 := by rw [← hfac, h, sub_self]
    have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hsum : x + y + γ = 0 := by
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 hxy0
      · exact h2
    -- `x + y + γ = 0` ⟹ `γ = -(x + y)`
    linear_combination hsum
  · intro h
    rw [h]; ring

/-- **The `γ = 0` fibre is the antipodal pairs.**  The pinned scalar `−(x + y)` of a distinct pair
`{x, y}` vanishes iff `y = -x`: the `γ = 0` fibre of the `r = 2` line is exactly the antipodal
pairing.  (This says nothing about fibres of nonzero scalars, which can also contain several
pairs; see the module docstring.) -/
theorem pairPinned_zero_iff_antipodal {x y : F} (hxy : x ≠ y) :
    (x ^ 2 + (0 : F) * x = y ^ 2 + (0 : F) * y) ↔ y = -x := by
  rw [pairPinnedScalar_eq hxy]
  constructor
  · intro h
    -- `0 = -(x + y)` ⟹ `x + y = 0` ⟹ `y = -x`
    have : x + y = 0 := by linear_combination h
    linear_combination this
  · intro h
    -- `y = -x` ⟹ `0 = -(x + y)`
    linear_combination h

/-- **The antipodal partner stays in the domain `μ_n` for even `n` (`n = 2^μ`).**  If `x^n = 1` and
`n` is even then `(-x)^n = 1`, so `-x ∈ μ_n`; the `γ = 0` antipodal fibre `{x, -x}` lives inside the
`2`-power domain (and `-x = x · g^{n/2}` is the order-2 coset shift). -/
theorem antipodal_mem_nthRoots {n : ℕ} (hn : Even n) {x : F} (hx : x ^ n = 1) :
    (-x) ^ n = 1 := by
  rw [hn.neg_pow, hx]

end ArkLib.ProximityGap.PairPinnedScalarAntipodal

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PairPinnedScalarAntipodal.pairPinnedScalar_eq
#print axioms ArkLib.ProximityGap.PairPinnedScalarAntipodal.pairPinned_zero_iff_antipodal
#print axioms ArkLib.ProximityGap.PairPinnedScalarAntipodal.antipodal_mem_nthRoots
