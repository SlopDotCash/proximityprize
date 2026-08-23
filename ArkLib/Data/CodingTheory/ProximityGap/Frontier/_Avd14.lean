/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# The wraparound count `W_r` carries NO `p`-divisibility (#444, avenue d14 — REFUTED-FALSE)

## The proposed claim (d1-4), refuted here

> *The δ-ring / Frobenius congruence forces `v_p(W_r) ≥ 1` (i.e. `W_r` is a structural multiple
> of `p`), pinning `W_r ≤ n^{2r}/p` as a divisibility, not merely an inequality.*

This file lands a **machine countermodel** (plain `decide`, no `native_decide`) showing the claim
is **false**: there are explicit `(n, p, r)` for which the wraparound count `W_r` is a **nonzero
residue mod `p`** — `v_p(W_r) = 0`. The δ-ring/Frobenius-lift congruence imposes **no** constraint
on `W_r`; it is a raw integer coincidence count whose value mod `p` is generic.

## The object

For the order-`n` multiplicative subgroup `μ_n ⊆ 𝔽_p^×` (here `n = 4`, `p = 13`, `μ_4 ⊆ 𝔽_13`),
the `r`-fold **char-`p` additive energy** is
`E_r^{𝔽_p} = #{(x,y) ∈ μ_n^r × μ_n^r : Σ x_i ≡ Σ y_j  (mod p)}
          = Σ_{c ∈ 𝔽_p} (#{x ∈ μ_n^r : Σ x_i ≡ c})²`,
and the **char-0 (Bessel/Lam–Leung) shadow** `E_r^{ℂ}` is the same count over `ℂ` (no wraparound).
The **wraparound count** is `W_r := E_r^{𝔽_p} − E_r^{ℂ} ≥ 0`, a nonnegative integer counting the
*extra* coincidences created by reduction mod `p`.

## The witness (exact `𝔽_p` computation, this session)

`μ_4 ⊆ 𝔽_13 = {1, 5, 8, 12}` (the 4th roots of unity, `{1, 5, −5, −1}`). At depth `r = 3`:

| quantity | value |
|---|---|
| `E_3^{𝔽_13}` (counted here from the explicit subgroup, `decide`) | `424` |
| `E_3^{ℂ}` (char-0 shadow, exact-verified constant) | `400` |
| `W_3 = 424 − 400` | `24` |
| `W_3 mod 13` | `11` ≠ 0 |

So `13 ∤ 24`: `v_13(W_3) = 0`, contradicting `v_p(W_r) ≥ 1`. The char-`p` energy `E_3^{𝔽_13} = 424`
is **not assumed** — it is computed in Lean as `Σ_c (fiber count c)²` over the genuine subgroup
`{1,5,8,12} ⊆ ZMod 13` via `decide`.

**Replication across more `(n,p,r)` (`python3`, exact, this session):** in **42/42** nonzero-`W_r`
cases tested (`n = 8`, `r ∈ {3,4,5}`, primes `17 … 449`) `v_p(W_r) = 0` — `W_r mod p` is a generic
nonzero residue every time (e.g. `(p,r,W,W%p)` `= (17,3,10440,2), (41,3,3120,4), (17,4,797664,7),
(73,3,480,42)`). The only `p | W_r` cases are the trivial `W_r = 0` ones (no information). The claim
has **no support whatsoever**.

## What this file proves (axiom-clean: `{propext, Classical.choice, Quot.sound}`)

- `charPEnergy3_eq` : `E_3^{𝔽_13}(μ_4) = 424` (the genuine subgroup count, `decide`).
- `wraparound3_eq` : `W_3 = 424 − 400 = 24`.
- `wraparound3_ne_zero` : `W_3 ≠ 0` (the wraparound is *real* — this is not the trivial `W = 0`
  case where divisibility is vacuous).
- **`pDivisibility_REFUTED`** : `¬ (13 ∣ W_3)` — the headline refutation: `p ∤ W_r` with `W_r ≠ 0`,
  so `v_p(W_r) = 0`, killing the δ-ring/Frobenius `v_p(W_r) ≥ 1` claim.
- `pValuation_zero` : packaged as `W_3 % 13 = 11 ≠ 0`.

Issue #444.
-/

namespace ProximityGap.Frontier.Avd14

/-- `μ_4 ⊆ 𝔽_13`: the order-4 multiplicative subgroup (4th roots of unity), `{1, 5, 8, 12}`
(`= {1, 5, −5, −1}`), represented as residues in `[0,13)` for cheap `ℕ`-arithmetic `decide`.
Generator `8 = 2^3` (`2` is a primitive root of `13`). -/
def mu4 : List ℕ := [1, 5, 8, 12]

/-- All `r`-fold sums `Σ x_i  (mod 13)` over `x ∈ μ_4^r`, as a flat list of residues in `[0,13)`.
Reductions are taken mod `13` at every step so values stay small and `decide` reduces cheaply. -/
def sumsOf : ℕ → List ℕ
  | 0 => [0]
  | (k + 1) => (sumsOf k).flatMap (fun s => mu4.map (fun x => (s + x) % 13))

/-- The char-`p` additive energy `E_r^{𝔽_13}(μ_4) = Σ_{c} (#{x ∈ μ_4^r : Σ x_i ≡ c})²`, computed
as the sum over the residue range `[0,13)` of the squared fiber counts of `sumsOf r`. -/
def charPEnergy (r : ℕ) : ℕ :=
  (List.range 13).foldr
    (fun c acc => acc + ((sumsOf r).filter (fun s => s == c)).length ^ 2) 0

/-- The char-0 (Bessel/Lam–Leung) additive-energy shadow at `n = 4`, depth `r = 3`:
`E_3^{ℂ}(μ_4) = 400` (exact-verified constant, the no-wraparound count). -/
def charZeroEnergy3 : ℕ := 400

/-- The wraparound count `W_3 := E_3^{𝔽_13} − E_3^{ℂ}` (nonneg integer coincidence count). -/
def W3 : ℤ := (charPEnergy 3 : ℤ) - (charZeroEnergy3 : ℤ)

/-! ## The genuine char-`p` energy count (computed, not assumed) -/

/-- The char-`p` additive energy of `μ_4 ⊆ 𝔽_13` at depth `r = 3` equals `424`, computed directly
from the explicit subgroup `{1,5,8,12}` by counting equal-sum `3`-tuples (`decide`). -/
theorem charPEnergy3_eq : charPEnergy 3 = 424 := by decide

/-! ## The wraparound is real and is NOT divisible by `p` -/

/-- `W_3 = 424 − 400 = 24`. -/
theorem wraparound3_eq : W3 = 24 := by
  unfold W3 charZeroEnergy3
  rw [charPEnergy3_eq]; norm_num

/-- The wraparound is genuinely nonzero (`W_3 = 24 ≠ 0`): this is **not** the trivial `W = 0` case
in which `p ∣ W` holds vacuously. -/
theorem wraparound3_ne_zero : W3 ≠ 0 := by
  rw [wraparound3_eq]; norm_num

/-- **The refutation.** `13 ∤ W_3` (since `W_3 = 24` and `13 ∤ 24`). Together with
`wraparound3_ne_zero`, this gives `v_13(W_3) = 0`, contradicting the proposed δ-ring/Frobenius
congruence claim `v_p(W_r) ≥ 1`. The wraparound count carries **no** `p`-divisibility. -/
theorem pDivisibility_REFUTED : ¬ ((13 : ℤ) ∣ W3) := by
  rw [wraparound3_eq]; decide

/-- Packaged valuation statement: `W_3 mod 13 = 11 ≠ 0`, i.e. `v_13(W_3) = 0`. -/
theorem pValuation_zero : W3 % 13 = 11 := by
  rw [wraparound3_eq]; decide

/-- The combined countermodel record: a nonzero wraparound that is a generic nonzero residue mod
`p`. There is a depth `r` and an explicit `(n, p) = (4, 13)` with `W_r ≠ 0` yet `p ∤ W_r`. -/
theorem charP_wraparound_not_pDivisible : W3 ≠ 0 ∧ ¬ ((13 : ℤ) ∣ W3) :=
  ⟨wraparound3_ne_zero, pDivisibility_REFUTED⟩

end ProximityGap.Frontier.Avd14

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.Avd14.charPEnergy3_eq
#print axioms ProximityGap.Frontier.Avd14.wraparound3_eq
#print axioms ProximityGap.Frontier.Avd14.wraparound3_ne_zero
#print axioms ProximityGap.Frontier.Avd14.pDivisibility_REFUTED
#print axioms ProximityGap.Frontier.Avd14.pValuation_zero
#print axioms ProximityGap.Frontier.Avd14.charP_wraparound_not_pDivisible
