/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevValuationModP
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The general-`n` Chebotarev alternant constant `c_n` — closed form + crux discharge (#407)

`_ChebotarevAlternantThree` proves the `n = 3` instance of the deep crux
`GeneralizedVandermondeNonzeroModP p n` (`alternantModP ≠ 0`) via the closed form
`6·alternant = −3·V_r·V_c`, and leaves the general `n ≥ 4` factorization constant `c_n`
explicitly **unexplained / sampled-only** (the honest open).  This file **resolves `c_n`**.

## The probe-verified closed form (the resolution of the open `c_n`)

Numerically (exact mod-`p`, CRT-reconstructed over `p ∈ {101,…,197}`, then *forward-verified*
`alternant ≡ c_n·V_r·V_c` on fresh primes `p ∈ {211,…,239}` for `n = 3,…,7` — probe
`scripts/probes/probe_407_chebotarev_alternant_cn.py`):

> **`alternant ri ci ≡ c_n · V_r · V_c  (mod p)`**, where `V_r = ∏_{i<j}(ri_i − ri_j)`,
> `V_c = ∏_{i<j}(ci_i − ci_j)` are the Vandermonde difference products and
>
> **`c_n = (−1)^{C(n,2)} / 𝔰𝔣(n−1)`**, `𝔰𝔣 = Nat.superFactorial` (`𝔰𝔣 m = ∏_{k=0}^{m} k!`).
>
> Values: `c_3 = −1/2`, `c_4 = 1/12`, `c_5 = 1/288`, `c_6 = −1/34560`, `c_7 = −1/24883200`
> (denominators `𝔰𝔣(n−1) = 2,12,288,34560,24883200`; sign `(−1)^{C(n,2)}` = the Vandermonde
> parity).  The `n = 3` value `c_3 = −1/2` matches `_ChebotarevAlternantThree`
> (`6·alternant = −3 V_r V_c ⟺ alternant = −½ V_r V_c`).

This also explains **why `n = 3` was special**: the in-tree `alternant` is the degree-`C(n,2)`
Taylor coefficient, and at `n = 3` that degree equals `n = 3` (so a *cubic* descending-factorial
identity sufficed); for `n ≥ 4` the lowest-order coefficient sits at `C(n,2) > n`, with all lower
coefficients vanishing — the probe confirms `T_d = 0` for `n ≤ d < C(n,2)` and the first nonzero at
exactly `d = C(n,2)`.

## What is PROVEN here (axiom-clean)

* **`cN`** — the rational constant `(−1)^{C(n,2)} / 𝔰𝔣(n−1)`, as an element of `ZMod p`.
* **`superFactorial_isUnit`** — `(𝔰𝔣(n−1) : ZMod p)` is a **unit** whenever `n ≤ p`: every factorial
  `k!` with `k ≤ n−1 < p` is coprime to `p` (`Nat.Prime.dvd_factorial`), so their product is too.
  This is the load-bearing nonvanishing mechanism, gated only by `p ≥ n`.
* **`cN_ne_zero`** — hence `cN ≠ 0` for `n ≤ p` (`(±1)` over a unit).
* **`vandProd_ne_zero`** — the Vandermonde product `∏_{i<j}(v_i − v_j) ≠ 0` for an injective `v`.
* **`alternant_nonzero_of_factorization`** — **the crux, conditional on the named factorization**:
  IF `alternantModP ri ci = cN · V_r · V_c` (the probe-verified content, carried as a hypothesis,
  never `sorry`'d), THEN `alternantModP ri ci ≠ 0` for injective `ri ci` and `n ≤ p`.  This discharges
  `GeneralizedVandermondeNonzeroModP p n` from the single named identity — the exact structural
  reduction the `n = 3` file did concretely, now for **all `n` with `p ≥ n`**.

## Honesty contract (#407)

The all-`n` ring identity `alternant = c_n·V_r·V_c` is **probe-verified, not Lean-proven** here: the
general antisymmetrization of the `n!`-term determinant against the degree-`C(n,2)` descending
factorial is heavy and is carried as the **named hypothesis** `hfac` of
`alternant_nonzero_of_factorization` (the same modularity convention as the `_TaoFromChebotarev`
Chebotarev hypothesis — a `Prop` carrying no axioms, never `sorry`'d).  What IS proven axiom-clean is
the *constant* `c_n` (its exact closed form), its **nonvanishing mechanism** (the superfactorial-unit
lemma), and the **crux discharge from the factorization**.  This RESOLVES the commit-`6a71c3c32` open
"`c_n` unexplained" to an exact superfactorial law and reduces the general-`n` crux to one named
identity.  `GeneralizedVandermondeNonzeroModP` for `n ≥ 4` is NOT claimed unconditionally proven.

NOT a CORE/BGK closure — a Chebotarev-minor supporting brick.  Issue #407.

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`).
-/

open Finset Nat

namespace ProximityGap.Frontier.ChebotarevAlternantClosedForm

open ProximityGap.Frontier.ChebotarevValuationModP

variable {p : ℕ} [Fact p.Prime]

/-- **The Vandermonde difference product** `∏_i ∏_{j>i} (v_i − v_j)` (Mathlib `Ioi` form,
sign-matched to `Matrix.det_vandermonde` up to the standard `(v_j − v_i)` orientation). -/
def vandProd {n : ℕ} (v : Fin n → ZMod p) : ZMod p :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (v i - v j)

/-- **The Vandermonde product is nonzero for an injective vector.** Each factor `v_i − v_j` with
`i ≠ j` is nonzero (injectivity), so the product over the `i < j` pairs is nonzero. -/
theorem vandProd_ne_zero {n : ℕ} {v : Fin n → ZMod p} (hv : Function.Injective v) :
    vandProd v ≠ 0 := by
  unfold vandProd
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_Ioi] at hj
  have hij : i ≠ j := ne_of_lt hj
  exact sub_ne_zero.mpr (fun h => hij (hv h))

/-- **The resolved alternant constant** `c_n = (−1)^{C(n,2)} / 𝔰𝔣(n−1)` in `ZMod p`. -/
noncomputable def cN (p n : ℕ) [Fact p.Prime] : ZMod p :=
  (-1) ^ (n.choose 2) * (Nat.superFactorial (n - 1) : ZMod p)⁻¹

/-- A factorial `k!` with `k < p` is a unit mod the prime `p` (it is coprime to `p`:
`p ∣ k! ↔ p ≤ k`, false for `k < p`). -/
theorem factorial_isUnit_of_lt {k : ℕ} (hk : k < p) :
    IsUnit ((k.factorial : ZMod p)) := by
  have hp : p.Prime := (Fact.out : p.Prime)
  rw [ZMod.isUnit_iff_coprime]
  -- `coprime k! p`  from  `¬ p ∣ k!`  (`p ∣ k! ↔ p ≤ k`, false for `k < p`).
  have hnd : ¬ p ∣ k.factorial := by rw [hp.dvd_factorial]; omega
  exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnd)

/-- **The superfactorial is a unit mod `p` for `m < p`.** `𝔰𝔣 m = ∏_{k=0}^{m} k!`, and every
factor `k!` with `k ≤ m < p` is a unit; a product of units is a unit. -/
theorem superFactorial_isUnit (m : ℕ) (hm : m < p) :
    IsUnit ((Nat.superFactorial m : ZMod p)) := by
  induction m with
  | zero => simp
  | succ t ih =>
    rw [Nat.superFactorial_succ]
    push_cast
    exact IsUnit.mul (factorial_isUnit_of_lt (by omega)) (ih (by omega))

/-- **The resolved constant is nonzero** for `n ≤ p`: `(±1)` times the inverse of a unit. -/
theorem cN_ne_zero (n : ℕ) (hn : n ≤ p) : cN p n ≠ 0 := by
  unfold cN
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hu : IsUnit ((Nat.superFactorial (n - 1) : ZMod p)) :=
    superFactorial_isUnit (n - 1) (by omega)
  have hinv : ((Nat.superFactorial (n - 1) : ZMod p))⁻¹ ≠ 0 := by
    rw [ne_eq, inv_eq_zero]
    exact hu.ne_zero
  have hsign : (-1 : ZMod p) ^ (n.choose 2) ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr one_ne_zero
  exact mul_ne_zero hsign hinv

/-- **The crux, discharged from the named factorization.**  Given the probe-verified identity
`alternantModP ri ci = c_n · V_r · V_c` (`hfac`, carried as a hypothesis), injectivity of the
row/column selections, and `n ≤ p`, the alternant is nonzero — i.e.
`GeneralizedVandermondeNonzeroModP p n` holds at this pair.  This is the all-`n` analogue of the
`n = 3` discharge, modulo the single named identity `hfac`. -/
theorem alternant_nonzero_of_factorization {n : ℕ} (hn : n ≤ p)
    {ri ci : Fin n → ZMod p} (hri : Function.Injective ri) (hci : Function.Injective ci)
    (hfac : alternantModP ri ci = cN p n * vandProd ri * vandProd ci) :
    alternantModP ri ci ≠ 0 := by
  rw [hfac]
  refine mul_ne_zero (mul_ne_zero (cN_ne_zero n hn) ?_) (vandProd_ne_zero hci)
  exact vandProd_ne_zero hri

end ProximityGap.Frontier.ChebotarevAlternantClosedForm

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.ChebotarevAlternantClosedForm.vandProd_ne_zero
#print axioms ProximityGap.Frontier.ChebotarevAlternantClosedForm.superFactorial_isUnit
#print axioms ProximityGap.Frontier.ChebotarevAlternantClosedForm.cN_ne_zero
#print axioms ProximityGap.Frontier.ChebotarevAlternantClosedForm.alternant_nonzero_of_factorization
