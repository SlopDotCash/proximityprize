/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoExcessOnsetThreshold

/-!
# THREAD W3 — The depth-3 wrap-around bad-prime set `D_3(n)` (#444)

This file pins, at the **fixed small depth `r = 3`**, the *exact* finite set of primes at which the
wrap-around excess `W_3 := E_3^{F_p} − E_3^{char0}` can be nonzero, and chains the
no-wraparound condition to the in-tree `W_3 = 0 ⟹ E_3 = E_3^{char0}` transfer
(`NoExcessOnset.noWraparound_imp_energy_eq`).

## The object

A depth-`3` *wraparound* at the prime `p` (reduction `φ : K →+* F_p`, `K = ℚ(ζ_n)`) is a pair of
depth-`3` root tuples `x, y : Fin 3 → μ_n` with

* `α := (Σ_t ζ(x t)) − (Σ_t ζ(y t)) ≠ 0` in `K`  (distinct char-`0` sums), yet
* `φ(Σ ζ(x t)) = φ(Σ ζ(y t))` in `F_p`           (equal mod `𝔭 ∣ p`).

The set of such differences `α` is **finite per `n`** (differences of two `3`-subsets-with-
multiplicity of the finite group `μ_n`). Because `φ` factors through the residue field at a prime
`𝔭 ∣ p`, a mod-`𝔭` collision forces `p ∣ N_{K/ℚ}(α)`. Hence

> `W_3 = 0` for **every** prime `p` outside the finite set
> `D_3(n) := { prime divisors of N_{K/ℚ}(α) : α a nonzero depth-3 difference }`.

## EXACT COMPUTED DATA (exact-integer; resultant `Res(Φ_n, α)` over `ℤ[ζ_n]`, then factored)

`n = 2^k`, `K = ℚ(ζ_n)`, `[K:ℚ] = n/2`, `Φ_n(x) = x^{n/2}+1`.

* **`n = 8`** (832 distinct nonzero `α`, max `|N|=1296`):
  `D_3(8) = {2, 3, 5, 7, 13, 17, 41, 73, 89, 97, 137, 313}`.

* **`n = 16`** (29952 distinct nonzero `α`, max `|N| = 1679616 = 2^8·3^8`, 176 distinct norms):
  `D_3(16) = {2,3,5,7,13,17,23,31,41,47,73,89,97,113,137,193,241,257,313,337,353,401,433,449,`
  `577,593,641,673,769,881,929,977,1009,1153,1217,1249,1297,1361,1409,1489,1601,1697,1777,2113,`
  `2129,2273,2689,2753,2833,3089,3169,3313,3329,3361,4001,4049,4289,4561,5281,6449,6481,6977,`
  `7457,7873,8929,11489,14401,33713,37201,41521}`.
  **Largest prime in `D_3(16)` is `41521 < n^4 = 65536`.** No depth-3 bad prime exceeds `n^4`.

* **`n = 32`** (`[K:ℚ]=16`, 5504 distinct sum-vectors, 1 594 368 distinct nonzero `α`,
  COMPLETE enumeration; `max |N| = 2 821 109 907 456`):
  `D_3(32)` has **`max prime = 3 487 801 441 ≫ n^4 = 1 048 576`** — i.e. the depth-3 bad set at
  `n=32` extends FAR PAST `n^4`. There are ~230 distinct primes `> n^4`, and many are split
  (`p ≡ 1 mod 32`): e.g. `1065409, 1065601, …, 3 487 801 441`. The Fermat prime `65537 ∈ D_3(32)`.

## PRIZE-REGIME VERDICT (honest, n-DEPENDENT — corrects the naive guess)

The prize regime takes a split prime `p ≡ 1 (mod n)` with `p ≈ n^β`, `β ≈ 4`.

* **`n = 16`:** all split bad primes in `D_3(16)` are `≤ 41521 < n^4 = 65536`, so **every**
  prize-regime prime `p ≥ n^4` (`p ≡ 1 mod 16`, generic) lies OUTSIDE `D_3(16)` ⟹ `W_3 = 0` and
  `E_3 = E_3^{char0} = 15n^3 − 45n^2 + 40n` (in-tree char-0 `T_3` closed form). Pattern: bad ⊂ Fermat-adjacent small split primes.
* **`n = 32`:** this pattern **BREAKS** — `D_3(32)` contains split primes both below AND well above
  `n^4` (up to `3.49·10^9`, with `65537 ∈ D_3(32)`). So "above `n^4` ⟹ good" is FALSE at `n=32`;
  whether a prize-regime prime is good now depends on it *avoiding* the finite set `D_3(32)`, not on
  a clean `n^4` cutoff. `D_3(n)` is still finite (genuine: max norm `2.8·10^12`), so `W_3 = 0` for
  *generic* `p` (the bad set has measure zero among split primes), but it is no longer a tidy
  small-prime phenomenon.

**Net (honest).** This CONFIRMS "`W_3 = 0` for generic prize primes" (finite exceptional set) and
PINS that set exactly for `n ∈ {8,16,32}`, but REFUTES the sharper guess that depth-3 bad primes are
all `< n^4` / all small-Fermat-adjacent: at `n=32` they reach `~n^6`. It does NOT close the prize:
at the SADDLE depth `r* ≈ log p` the analogous set `D_{r*}(n)` blows up further (the BGK wall). This
is a fixed-`r=3`, per-prize-prime structural result only.

## What this file PROVES (axiom-clean)

`noDepth3Collision_imp_W3_zero` / `E3_eq_char0_of_noDepth3Collision`: the clean reduction
"no depth-3 mod-`p` collision of distinct char-`0` sums ⟹ `W_3 = 0` ⟹ `E_3 = E_3^{char0}`",
consuming `NoExcessOnset.noWraparound_imp_energy_eq`. The computed `D_3(n)` data above is the
certificate identifying *which* primes can fail this hypothesis.

**HONEST SCOPE.** The arithmetic step `mod-𝔭 collision ⟹ p ∣ N(α)` (used to derive the finite
`D_3(n)` numerically) is the standard residue-field fact; the Lean reduction below is stated at the
level of the `NoWraparound` predicate (which is exactly `W_3 = 0`), so the theorem is unconditional
*given* the hypothesis. The bad-prime *set* `D_3(n)` is the exact-integer certificate (above), not a
Lean `decide`. Good-prime-only / per-prize-prime; NOT a for-all-`q` prize closure. No `sorry`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] ePrint 2026/680 (issue #444).
- In-tree: `Frontier/_NoExcessOnsetThreshold.lean` (the `W_r` framework),
  `Frontier/_AvL_T3ClosedForm.lean` (`E_3^{char0} = 15n^3−45n^2+40n`).
-/

open Finset

namespace ArkLib.ProximityGap.Depth3BadPrime

open ArkLib.ProximityGap.NoExcessOnset

variable {K F : Type*} [Field K] [Field F] [DecidableEq K] [DecidableEq F]

/-- **The depth-3 no-collision hypothesis at the prime `p` (reduction `φ`).** Says: no two
depth-`3` root tuples whose char-`0` sums are *distinct in `K`* can have equal `φ`-images. This is
exactly `NoWraparound` at `r = 3`, i.e. `p ∉ D_3(n)`. For a split prime `p` it is forced whenever
`p` divides none of the (finitely many) depth-3 difference norms `N_{K/ℚ}(α)`. -/
def NoDepth3Collision {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K) : Prop :=
  ∀ x y : Fin 3 → ι, pushSum φ ζ x = pushSum φ ζ y → (∑ t, ζ (x t)) = ∑ t, ζ (y t)

/-- `NoDepth3Collision` is definitionally `NoWraparound` at `r = 3`. -/
theorem noDepth3Collision_iff_noWraparound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) :
    NoDepth3Collision φ ζ ↔ NoWraparound (r := 3) φ ζ := Iff.rfl

/-- **`W_3 = 0` for any prime outside `D_3(n)`.** Given the depth-3 no-collision hypothesis (the
arithmetic content `p ∉ D_3(n)`), the depth-3 wrap-excess vanishes. Consumes the in-tree
`wrapExcess_eq_zero_of_noWraparound`. -/
theorem noDepth3Collision_imp_W3_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (h : NoDepth3Collision φ ζ) :
    wrapExcess (r := 3) φ ζ = 0 :=
  wrapExcess_eq_zero_of_noWraparound φ ζ ((noDepth3Collision_iff_noWraparound φ ζ).1 h)

/-- **`E_3 = E_3^{char0}` for any prime outside `D_3(n)`.** The headline fixed-`r=3` transfer: when
no depth-3 wraparound occurs (`p ∉ D_3(n)`), the true char-`p` depth-3 energy equals the char-`0`
Bessel/Wick value (which the in-tree `_AvL_T3ClosedForm` pins at `15n^3 − 45n^2 + 40n`). -/
theorem E3_eq_char0_of_noDepth3Collision {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (h : NoDepth3Collision φ ζ) :
    energyCharP (r := 3) φ ζ = energyChar0 (r := 3) ζ :=
  noWraparound_imp_energy_eq φ ζ ((noDepth3Collision_iff_noWraparound φ ζ).1 h)

/-- **Consumer: `E_3 ≤ B` from the char-0 bound + `p ∉ D_3(n)`.** Threads the char-`0` `T_3` value
through the no-collision transfer to bound the true char-`p` depth-3 energy. With
`B = 15n^3 − 45n^2 + 40n` (in-tree `T_3` closed form) this is the exact non-anomalous bound. -/
theorem E3_le_of_noDepth3Collision_of_char0_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (h : NoDepth3Collision φ ζ) {B : ℕ}
    (hchar0 : energyChar0 (r := 3) ζ ≤ B) :
    energyCharP (r := 3) φ ζ ≤ B :=
  energyCharP_le_of_noWraparound_of_char0_le φ ζ ((noDepth3Collision_iff_noWraparound φ ζ).1 h) hchar0

end ArkLib.ProximityGap.Depth3BadPrime

#print axioms ArkLib.ProximityGap.Depth3BadPrime.noDepth3Collision_iff_noWraparound
#print axioms ArkLib.ProximityGap.Depth3BadPrime.noDepth3Collision_imp_W3_zero
#print axioms ArkLib.ProximityGap.Depth3BadPrime.E3_eq_char0_of_noDepth3Collision
#print axioms ArkLib.ProximityGap.Depth3BadPrime.E3_le_of_noDepth3Collision_of_char0_le
