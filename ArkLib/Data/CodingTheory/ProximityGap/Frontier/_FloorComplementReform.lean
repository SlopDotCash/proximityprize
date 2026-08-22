/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# The floor-bad complement reformulation (#466, lane FS1)

**A pattern's floor-bad realizability is a condition on the COMPLEMENT polynomial.**

The floor-bad scanner (`scripts/probes/floor_scan_exact.c`) tests, for an adjacent-7th-type
pattern `A ⊆ ℤ/n` (`|A| = 5n/8`) with points `ω^j` (`ω` a primitive `n`-th root of unity in
`𝔽_p`, `p ≡ 1 mod n`), whether the remainder `r = X^{3n/4} mod P_A` (`P_A = ∏_{j∈A}(X-ω^j)`)
has all coefficients `r_k = 0` for `k ∈ [n/2+1, |A|-1]`, i.e. whether `deg r ≤ n/2`.

Let `B = ℤ/n \ A` be the complement (`|B| = 3n/8`) and `Q_B = ∏_{j∈B}(X-ω^j)`, so that
`P_A · Q_B = X^n - 1`.  The **reformulation** (this file's mechanism lemma) is:

  `A` realizable at `p`  ↔  `deg r ≤ n/2`  ↔  `[X^i] Q_B = 0` for all `i ∈ [n/8+1, n/4-1]`.

This turns a test on the degree-`5n/8` remainder into a test on `n/8 - 1` middle coefficients of
the degree-`3n/8` COMPLEMENT polynomial `Q_B`, and factors `Q_B = U · W` along the class
structure — the handle that makes `floor-bad(64)` decidable by a meet-in-the-middle search
(`scripts/probes/probe_466_floorbad64_decide.py`), replacing the `2.2·10^{15}`-pattern scan.

## What is proved here (axiom-clean, general in the ring `R` and the exponents)

The algebraic **core** of the reformulation, valid over any commutative ring, for any `P`
and any `Q` with `P · Q = X^N - 1`:

* `floorReform_dvd`  :  `(X^N - 1) ∣ (X^D * Q - (X^D %ₘ P) * Q)`
* `floorReform_congr`  :  `(X^N - 1) ∣ ((X^D %ₘ P) * Q - X^D * Q)`
    — i.e. the remainder `r = X^D %ₘ P` satisfies `r · Q ≡ X^D · Q  (mod X^N - 1)`.

This is the pivot of the whole reformulation.  Over a field the remainder `r` has degree `< 5n/8`,
so `r · Q_B` has degree `< n`, hence `r · Q_B` **is** the reduction `(X^{3n/4} · Q_B) %ₘ (X^n - 1)`.
The floor-bad test `deg r ≤ n/2` is therefore equivalent (via `deg(r·Q_B) = deg r + 3n/8`, `Q_B`
monic) to `deg(r·Q_B) ≤ 7n/8`, i.e. to the vanishing of the coefficients of `(X^{3n/4}·Q_B) mod
(X^n-1)` at degrees `(7n/8, n)`; the elementary reduction `X^{3n/4+i} ≡ X^{(3n/4+i) mod n}` shows
those coefficients are exactly `[X^i] Q_B` for `i ∈ [n/8+1, n/4-1]`.  This last degree/coefficient
bookkeeping (an unfolding of the divisibility proved here) is verified computationally in the
probe rather than in Lean: exact at `n=16` (all `2304·4` patterns), sampled at `n=32,64`
(`0` mismatches vs the scanner's rank test).

**What this enabled** (probe `probe_466_floorbad64_decide.py`, out `_out_466_floorbad64_decide.txt`).
The factorization `Q_B = U · W` along the class structure makes the vanishing of the `7` middle
coefficients a *bilinear* condition, decided by a translation-symmetry-reduced meet-in-the-middle
(complete over the whole `2.2·10^{15}`-pattern family up to the exact `ℤ/16` translation symmetry).
Result: **`193 = p_min(64)` is NOT floor-bad at `n=64`** — no realizable adjacent-7th-type pattern
exists — which **REFUTES the uniform floor-successor conjecture** `floor-bad(n) = {p_min(n)}`
(true at `n=16,32`; false at `n=64`).

**Honesty.**  This file proves the *general polynomial mechanism* of the reformulation
(axiom-clean).  The concrete equivalence with the scanner's rank test, the numeric window, and the
`floor-bad(64)` membership DECISION are the probe's (exact at `n=16`; sampled at `n=32,64` with `0`
mismatches; complete MITM for the decision), **not** Lean objects.  Nothing here asserts a value of
`floor-bad(64)` as a Lean theorem.
-/

namespace ArkLib.ProximityGap.Frontier.FloorComplementReform

open Polynomial

variable {R : Type*} [CommRing R]

/-- **Core mechanism.** For monic `P` and any `Q` with `P * Q = X^N - 1`, the floor remainder
`r = X^D %ₘ P` satisfies `r * Q ≡ X^D * Q  (mod X^N - 1)`.  Equivalently `X^N - 1` divides the
difference.  This is the identity that moves the floor-bad test from `P_A` to the complement
`Q_B`: `r * Q_B` is the reduction of `X^{3n/4} Q_B` modulo `X^n - 1`, whose relevant coefficients
are the middle coefficients of `Q_B`. -/
theorem floorReform_dvd (P Q : R[X]) (D N : ℕ)
    (hPQ : P * Q = X ^ N - 1) :
    (X ^ N - 1) ∣ (X ^ D * Q - (X ^ D %ₘ P) * Q) := by
  refine ⟨X ^ D /ₘ P, ?_⟩
  -- `X^D %ₘ P + P * (X^D /ₘ P) = X^D`, unconditionally
  have h := modByMonic_add_div (X ^ D) P
  rw [← hPQ]     -- rewrite `X^N - 1` on the RHS as `P * Q`
  linear_combination (-Q) * h

/-- The congruence form: `r * Q ≡ X^D * Q` modulo `X^N - 1`, `r = X^D %ₘ P`. -/
theorem floorReform_congr (P Q : R[X]) (D N : ℕ)
    (hPQ : P * Q = X ^ N - 1) :
    (X ^ N - 1) ∣ ((X ^ D %ₘ P) * Q - X ^ D * Q) := by
  have h := floorReform_dvd P Q D N hPQ
  rw [show (X ^ D %ₘ P) * Q - X ^ D * Q = -(X ^ D * Q - (X ^ D %ₘ P) * Q) by ring]
  exact (dvd_neg).mpr h

end ArkLib.ProximityGap.Frontier.FloorComplementReform

#print axioms ArkLib.ProximityGap.Frontier.FloorComplementReform.floorReform_dvd
#print axioms ArkLib.ProximityGap.Frontier.FloorComplementReform.floorReform_congr
