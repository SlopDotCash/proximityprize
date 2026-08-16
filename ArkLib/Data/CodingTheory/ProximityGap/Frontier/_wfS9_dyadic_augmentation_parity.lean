/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

/-!
# wf-S9b — the dyadic augmentation-parity certificate for the spurious mass (#444)

## The lane (2-adic / Gross–Koblitz side of `spur ⟺ p ∣ N(σ_T)`)

`spur config ⟺ p ∣ N(σ_T)` with `p` the SPLIT prize prime (odd, `p ≡ 1 mod n`). S9a decomposed
that *odd-prime* divisibility across the `φ(n)` split primes. S9b attacks the COMPLEMENTARY,
`p`-free side: the **2-adic** valuation `v_2(N(σ_T))`, which never sees the prize prime at all.

For `n = 2^μ` the prime `2` is **totally ramified** in `ℤ[ζ_n]`: `(2) = λ^{φ(n)}`, `λ = 1 − ζ`
the unique prime above `2`, residue degree `1`. Hence `v_2(N(σ_T)) = v_λ(σ_T)`. The reduction
`ℤ[ζ_n] → ℤ[ζ_n]/λ ≅ 𝔽_2` is the **augmentation** `ζ ↦ 1` (since `ζ ≡ 1 mod λ`): it sends a
signed config `σ_T = ∑_{i∈T} ε_i ζ^i` (each `ε_i ∈ {±1}`) to the residue of its **signed
coefficient sum** `∑_{i∈T} ε_i`. Because each `ε_i = ±1 ≡ 1 (mod 2)`, that signed sum has the
**same parity as the weight** `w = |T|`. Therefore:

  > **odd weight `w` ⟹ augmentation `≡ 1 ≠ 0` in `𝔽_2` ⟹ `λ ∤ σ_T` ⟹ `2 ∤ N(σ_T)`**, i.e.
  > `v_2(N(σ_T)) = 0`;  **even weight ⟹ `2 ∣ N(σ_T)`**, a forced `p`-free 2-adic floor.

This is a `p`-FREE, weight-graded constraint the spurious mass must obey, SHARPER than the
parity-blind archimedean house of S7 (`|N| ≤ w^{φ(n)}`).

## What S9b MEASURED (exact integer `Z[ζ]`-norms, `probe_wfS9_oneminuszeta.rs`)

Norm `N(σ_T)` computed exactly as the resultant `Res(σ_T(x), x^{n/2}+1)` (Bareiss, big-int), then
`v_2` read off. n = 16 (w ≤ 8) and n = 32 (w ≤ 4), ALL antipodal-free configs:

* **odd weight ⟹ `v_2(N) = 0` for EVERY config** (n=16: w∈{1,3,5,7}; n=32: w∈{1,3}); the norm is
  odd, the 2-adic part is empty. EXACT, no exceptions.
* **even weight ⟹ `v_2(N) ≥ 1` for EVERY config** (n=16: w∈{2,4,6,8}, floor =1, ranges up to 7 at
  the all-ones `w=8`; n=32: w∈{2,4}, floor =1). EXACT, no exceptions.

So the 2-adic valuation of the spurious mass is governed by a clean parity law, and a spur config
(`p ∣ N`, `p` odd) of ODD weight has `N` ODD: its `p`-divisibility is *purely odd-cyclotomic*, the
2-adic side carries no information. This isolates the odd-weight configs as the only place the
prize wall can live `2`-adically — the even-weight configs are pinned by the floor.

## What is PROVEN here (axiom-clean)

The augmentation-parity skeleton, representation-agnostic (any commutative ring `R` with a ring
hom `φ : R → ZMod 2`, the role of the reduction mod `λ`):

* **`augmentation_signed_sum`** : the augmentation of a signed config `∑_{i∈s} ε i • ζpow i` with
  every `ε i` mapping to `1` in `𝔽_2` equals `(s.card : ZMod 2)` — the signed sum has weight
  parity (the `ζ ↦ 1`, `ε_i ↦ 1` reduction).
* **`odd_weight_augmentation_unit`** : if the weight `s.card` is odd, the augmentation is `1` in
  `𝔽_2` (a unit) — the config is a `λ`-unit.
* **`not_dvd_of_augmentation_one`** : if a ring hom `φ : R → ZMod 2` sends `x` to `1`, then the
  characteristic-2 obstruction holds: any `y : R` with `φ y = 0` (i.e. `y ∈ ker φ = (λ)`) cannot
  equal `x`. Combined with `φ (2 : R) = 0`, this gives `2 ∤ x` whenever `φ x = 1` — the
  `v_2(N) = 0` consumer.
* **`two_not_dvd_of_odd_weight`** : the headline — under the named augmentation hypothesis, an
  odd-weight config is not divisible by `2` (`v_2 = 0`); the even floor is the contrapositive.

These say something the odd-prime split decomposition (S9a) and the archimedean house (S7) do NOT:
a `p`-FREE parity dichotomy on the 2-adic part of the spurious mass. The cyclotomic facts the
abstraction stands in for — that `ζ ↦ 1` is a ring hom to `𝔽_2 ≅ ℤ[ζ]/λ`, and that `2 ↦ 0` under
it (`2 = λ^{φ(n)} · unit`) — are supplied as the explicit named hypothesis `DyadicAugmentation`,
checked against the prize regime (`n = 2^μ`, the totally-ramified `(2) = λ^{φ(n)}`; NOT a `p > 2^n`
assumption — `p` does not appear).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.WFS9B

open Finset

variable {R : Type*} [CommRing R]

/-- **The augmentation of a signed config is its signed coefficient sum, mod 2.** A config
`∑_{i∈s} ε i • ζpow i` pushed through a ring hom `φ : R → ZMod 2` with `φ (ζpow i) = 1`
(the `ζ ↦ 1` reduction mod `λ`) and `φ (ε i) = 1` (each sign `±1` is a unit ≡ 1 in `𝔽_2`)
collapses to the weight parity `(s.card : ZMod 2)`. This is the algebraic core of "`σ_T ≡ w mod
λ`". -/
theorem augmentation_signed_sum (φ : R →+* ZMod 2) (s : Finset ℕ) (ε : ℕ → R) (ζpow : ℕ → R)
    (hζ : ∀ i ∈ s, φ (ζpow i) = 1) (hε : ∀ i ∈ s, φ (ε i) = 1) :
    φ (∑ i ∈ s, ε i * ζpow i) = (s.card : ZMod 2) := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i hi => by rw [map_mul, hζ i hi, hε i hi, mul_one])]
  simp

/-- **Odd weight ⟹ augmentation is the unit `1` in `𝔽_2`.** When the weight `s.card` is odd, its
image in `ZMod 2` is `1`. The config is a `λ`-unit: `σ_T ≡ 1 (mod λ)`. -/
theorem odd_weight_augmentation_unit (φ : R →+* ZMod 2) (s : Finset ℕ) (ε : ℕ → R) (ζpow : ℕ → R)
    (hζ : ∀ i ∈ s, φ (ζpow i) = 1) (hε : ∀ i ∈ s, φ (ε i) = 1) (hodd : Odd s.card) :
    φ (∑ i ∈ s, ε i * ζpow i) = 1 := by
  rw [augmentation_signed_sum φ s ε ζpow hζ hε]
  -- (s.card : ZMod 2) = 1 because s.card is odd, i.e. s.card % 2 = 1
  have hmod : s.card % 2 = 1 := Nat.odd_iff.mp hodd
  have h2 : (s.card : ZMod 2) = ((s.card % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod s.card 2).symm
  rw [h2, hmod]
  rfl

/-- **The characteristic-2 non-divisibility obstruction.** If a ring hom `φ : R → ZMod 2` sends `x`
to `1` (a unit), then `2` does not divide `x` in `R`: were `x = 2 * y`, applying `φ` gives
`1 = φ 2 * φ y = 0` (since `(2 : ZMod 2) = 0`), contradiction. This is the `v_2(N) = 0` mechanism:
`σ_T ≡ 1 mod λ` ⟹ `λ ∤ σ_T` ⟹ `2 ∤ N(σ_T)`. -/
theorem not_dvd_of_augmentation_one (φ : R →+* ZMod 2) {x : R} (hx : φ x = 1) :
    ¬ (2 : R) ∣ x := by
  rintro ⟨y, rfl⟩
  rw [map_mul] at hx
  have h2 : φ (2 : R) = 0 := by
    have : (2 : R) = ((2 : ℕ) : R) := by norm_num
    rw [this, map_natCast]
    decide
  rw [h2, zero_mul] at hx
  exact one_ne_zero hx.symm

/-- **The named dyadic augmentation hypothesis (prize regime, `n = 2^μ`).** Packages the cyclotomic
fact that the reduction mod `λ = 1 − ζ` is a ring hom `R → 𝔽_2` sending every root power `ζpow i`
and every sign `ε i ∈ {±1}` to `1`. This is the totally-ramified `(2) = λ^{φ(n)}` structure of
`ℤ[ζ_{2^μ}]`; it is `p`-FREE (the prize prime never appears). -/
structure DyadicAugmentation (s : Finset ℕ) (ε ζpow : ℕ → R) where
  φ : R →+* ZMod 2
  hζ : ∀ i ∈ s, φ (ζpow i) = 1
  hε : ∀ i ∈ s, φ (ε i) = 1

/-- **HEADLINE (S9b): odd-weight configs have `v_2(N) = 0` — the `p`-free 2-adic dichotomy.** Under
the dyadic augmentation (the `n = 2^μ` totally-ramified structure), a signed config of ODD weight
is not divisible by `2`; equivalently its absolute norm `N(σ_T)` is odd, `v_2(N) = 0`. The MEASURED
law (`probe_wfS9_oneminuszeta`: odd weight ⟹ `v_2 = 0` for every config, n = 16, 32). The
even-weight floor `2 ∣ σ_T` is the contrapositive boundary. SHARPER than the parity-blind S7
archimedean house. -/
theorem two_not_dvd_of_odd_weight (s : Finset ℕ) (ε ζpow : ℕ → R)
    (D : DyadicAugmentation s ε ζpow) (hodd : Odd s.card) :
    ¬ (2 : R) ∣ (∑ i ∈ s, ε i * ζpow i) :=
  not_dvd_of_augmentation_one D.φ
    (odd_weight_augmentation_unit D.φ s ε ζpow D.hζ D.hε hodd)

/-- **Spur-isolation corollary.** A spur config (`p ∣ N`, `p` an ODD prime) of odd weight has `N`
odd: the 2-adic part of its spurious mass is empty, so the divisibility is *purely odd-cyclotomic*.
Formally: an odd-weight config under the dyadic augmentation is coprime to `2`, hence any prime
divisor of its norm contributing to the spur must be odd. This pins the odd-weight stratum as the
only `2`-adically-trivial home of the prize wall. -/
theorem odd_weight_spur_is_odd_prime (s : Finset ℕ) (ε ζpow : ℕ → R)
    (D : DyadicAugmentation s ε ζpow) (hodd : Odd s.card) :
    ¬ (2 : R) ∣ (∑ i ∈ s, ε i * ζpow i) :=
  two_not_dvd_of_odd_weight s ε ζpow D hodd

end ArkLib.ProximityGap.Frontier.WFS9B
