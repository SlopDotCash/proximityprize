/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.NumberField.Basic
import ArkLib.Data.CodingTheory.ProximityGap.HeightGateNormBound

/-!
# Fp-vanishing → norm-divisibility bridge (#407)

The height gate `gate_2power_antipodal` (in `HeightGateNormBound.lean`) consumes the hypothesis
`(p : ℤ) ∣ Algebra.norm ℤ (∑_{i∈S} ζ^i)` — divisibility of the INTEGER norm by the rational
prime `p`.  The actual proximity-gap object, however, is vanishing **in `F_p` itself**:
`μ_n ⊂ F_p` (`n ∣ p-1`), `ω ∈ F_p` a primitive `n`-th root, and "spurious vanishing" is
`∑_{i∈S} ω^i = 0` in `F_p`.

This file supplies the missing BRIDGE, and wires it to the gate.

## Mechanism (the clean self-divides-norm route)

The ring hom `r : 𝓞_K → F_p` sending `ζ ↦ ω` exists because `p` splits completely in
`ℚ(ζ_n)` when `n ∣ p-1` (concretely: a prime `𝔭 ∣ p` with residue field `F_p`).  Given any such
hom `r` with `r ζ = ω`:

* `Sg := ∑_{i∈S} ζ^i ∈ 𝓞_K`  maps to `r Sg = ∑_{i∈S} ω^i = 0`.
* `Sg` divides its own integer norm inside `𝓞_K`:
  `Sg ∣ algebraMap ℤ 𝓞_K (Algebra.norm ℤ Sg)`  (`Algebra.dvd_algebraMap_intNorm_self`
  + `Algebra.intNorm_eq_norm`).  So `algebraMap ℤ 𝓞_K N = Sg · w`.
* Apply `r`: `r (algebraMap ℤ 𝓞_K N) = r Sg · r w = 0`.
* `r ∘ algebraMap ℤ 𝓞_K = Int.cast` (the unique ring hom `ℤ → ZMod p`), so `(N : ZMod p) = 0`.
* `ZMod.intCast_zmod_eq_zero_iff_dvd` turns this into `(p : ℤ) ∣ N`.  ∎

The construction of `r` from the splitting (picking `𝔭 ∣ p`) is the one heavy step; per the
project's modularity convention it is kept as the EXPLICIT hypothesis `(r) (hr : r ζ = ω)`.
Everything else (and the whole gate downstream) is proved unconditionally from it.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField

namespace ArkLib.ProximityGap.FpBridge

variable {K : Type*} [Field K] [NumberField K]

/-! ## The self-divides-norm fact for `𝓞_K`

`x : 𝓞_K` divides the image in `𝓞_K` of its own rational-integer norm `Algebra.norm ℤ x`. -/

/-- For `x : 𝓞_K`, `x` divides `algebraMap ℤ (𝓞 K) (Algebra.norm ℤ x)`.

This is `Algebra.dvd_algebraMap_intNorm_self` over the integrally-closed finite-free domain
extension `ℤ → 𝓞_K`, with `Algebra.intNorm ℤ (𝓞 K) = Algebra.norm ℤ` (`Algebra.intNorm_eq_norm`,
which holds because `𝓞_K` is `Module.Free`/`Module.Finite` over `ℤ`). -/
theorem self_dvd_algebraMap_norm (x : 𝓞 K) :
    x ∣ algebraMap ℤ (𝓞 K) (Algebra.norm ℤ x) := by
  have h := Algebra.dvd_algebraMap_intNorm_self (A := ℤ) (B := 𝓞 K) x
  rwa [Algebra.intNorm_eq_norm] at h

/-! ## The bridge (conditional on the reduction hom) -/

/-- **`Fp_vanish_imp_dvd_norm` (conditional form).**

Given a ring hom `r : 𝓞_K → ZMod p` (the reduction at a prime above `p`, `ζ ↦ ω`), if the
root-sum `∑_{i∈S} ω^i` vanishes in `ZMod p`, then `(p : ℤ)` divides the integer norm
`Algebra.norm ℤ (∑_{i∈S} ζ^i)`.

The hypothesis `hvanish` is exactly the `F_p`-vanishing of the proximity-gap object, transported
along `r` (`r (∑ ζ^i) = ∑ (r ζ)^i = ∑ ω^i`).  We state it directly in terms of `r` so the lemma
is independent of how `ω` is named. -/
theorem Fp_vanish_imp_dvd_norm {p : ℕ} (r : 𝓞 K →+* ZMod p) {S : Finset ℕ} {ζ : 𝓞 K}
    (hvanish : r (∑ i ∈ S, ζ ^ i) = 0) :
    (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, ζ ^ i) := by
  classical
  set Sg : 𝓞 K := ∑ i ∈ S, ζ ^ i with hSg
  set N : ℤ := Algebra.norm ℤ Sg with hN
  -- `Sg ∣ algebraMap ℤ 𝓞_K N`.
  obtain ⟨w, hw⟩ := self_dvd_algebraMap_norm (K := K) Sg
  -- Apply `r`: `r (algebraMap ℤ 𝓞_K N) = r Sg · r w = 0`.
  have hr0 : r (algebraMap ℤ (𝓞 K) N) = 0 := by
    rw [hw, map_mul, hvanish, zero_mul]
  -- `r ∘ algebraMap ℤ 𝓞_K = (Int.cast : ℤ → ZMod p)`: `algebraMap ℤ 𝓞_K N = (N : 𝓞_K)`,
  -- and `r (N : 𝓞_K) = (N : ZMod p)` by `map_intCast`.
  have hcomp : r (algebraMap ℤ (𝓞 K) N) = ((N : ZMod p)) := by
    rw [algebraMap_int_eq, eq_intCast, map_intCast]
  -- `(N : ZMod p) = 0`.
  have hNzero : (N : ZMod p) = 0 := by rw [← hcomp]; exact hr0
  -- divisibility.
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hNzero

/-- **`Fp_vanish_imp_dvd_norm` (named-`ω` form).**

The same bridge, phrased with `ω : ZMod p`, `r ζ = ω`, and the literal `F_p`-vanishing
`∑_{i∈S} ω^i = 0` of the proximity-gap object.  We transport `∑ ω^i = 0` to `r (∑ ζ^i) = 0`
via `r ζ = ω` (`map_sum` + `map_pow`) and invoke the conditional form. -/
theorem Fp_vanish_imp_dvd_norm' {p : ℕ} (r : 𝓞 K →+* ZMod p) {S : Finset ℕ} {ζ : 𝓞 K}
    {ω : ZMod p} (hr : r ζ = ω) (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, ζ ^ i) := by
  apply Fp_vanish_imp_dvd_norm r
  rw [map_sum]
  rw [← hvanish]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_pow, hr])

/-! ## End-to-end: `F_p`-vanishing ⟹ antipodal (the height gate, wired through the bridge) -/

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`spurious_Fp_vanish_imp_antipodal` (general number-field form).**

Let `ζ : 𝓞_K` have `(ζ : K)` a primitive `2^a`-th root of unity (`a ≥ 1`), `S ⊆ {0,…,2^a-1}`,
`r : 𝓞_K → ZMod p` a ring hom with `r ζ = ω`, and the height bound `p > (#S)^{[K:ℚ]}`.  If the
root-sum vanishes in `F_p` (`∑_{i∈S} ω^i = 0`), then `S` is **antipodal**
(`ExponentAntipodal a S`).

This chains the bridge `Fp_vanish_imp_dvd_norm'` (`F_p`-vanish ⟹ `p ∣ N(Σ)`) with the LANDED
height gate `gate_2power_antipodal` (`p ∣ N(Σ)` ∧ `p > height` ⟹ antipodal).  At small `n` it
says: EVERY actual spurious-in-`F_p` vanishing subset is antipodal = `NoSpuriousVanishing`
end-to-end, conditional only on the reduction hom `r`. -/
theorem spurious_Fp_vanish_imp_antipodal {a : ℕ} (ha : 1 ≤ a) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ((ζ : K)) (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} (r : 𝓞 K →+* ZMod p) {ω : ZMod p} (hr : r ζ = ω)
    (hp : (S.card : ℝ) ^ Module.finrank ℚ K < p)
    (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    ExponentAntipodal a S := by
  have hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, ζ ^ i) :=
    Fp_vanish_imp_dvd_norm' r hr hvanish
  exact ArkLib.ProximityGap.GateNorm.gate_2power_antipodal ha hζ hS hp hdvd

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`spurious_Fp_vanish_imp_antipodal` (prize-scale form, `n = 2^a`).**

The same end-to-end statement packaged with the prize-scale height hypothesis
`p > n^{n/2}` (`n = 2^a`, so `n/2 = 2^{a-1} = φ(2^a) = [K:ℚ]`), where `K` is a number field of
the cyclotomic dimension `finrank ℚ K = 2^{a-1}` (e.g. `K = CyclotomicField (2^a) ℚ`).

Concretely: for `n = 2^a`, prize-scale `p > n^{n/2}`, `ζ : 𝓞_K` with `(ζ:K)` a primitive `n`-th
root, `ω = r ζ` a primitive `n`-th root in `F_p`, `S ⊆ range n` with `∑_{i∈S} ω^i = 0` in `F_p`,
the subset `S` is antipodal.  This is `NoSpuriousVanishing` END-TO-END at small `n`: at this
height every actual `F_p`-spurious vanishing subset is a disjoint union of negation pairs.

The height hypothesis is delivered from `p > n^{n/2}` via `S.card ≤ n` and
`(S.card)^{2^{a-1}} ≤ n^{2^{a-1}} = n^{n/2} < p`, then `finrank ℚ K = 2^{a-1}` rewrites the gate
exponent.  (`hfin` holds for the cyclotomic field by `IsCyclotomicExtension.finrank` +
`Nat.totient_prime_pow`.) -/
theorem spurious_Fp_vanish_imp_antipodal_prize {a : ℕ} (ha : 1 ≤ a)
    (hfin : Module.finrank ℚ K = 2 ^ (a - 1)) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ((ζ : K)) (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} (r : 𝓞 K →+* ZMod p) {ω : ZMod p} (hr : r ζ = ω)
    (hp : ((2 ^ a : ℕ) : ℝ) ^ (2 ^ (a - 1)) < p)
    (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    ExponentAntipodal a S := by
  -- `S.card ≤ 2^a` from `S ⊆ range (2^a)`.
  have hcard : S.card ≤ 2 ^ a := by
    calc S.card ≤ (Finset.range (2 ^ a)).card := Finset.card_le_card hS
      _ = 2 ^ a := Finset.card_range _
  -- The gate's height hypothesis `(S.card)^{finrank ℚ K} < p`.
  have hp' : (S.card : ℝ) ^ Module.finrank ℚ K < p := by
    rw [hfin]
    refine lt_of_le_of_lt ?_ hp
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hcard
  exact spurious_Fp_vanish_imp_antipodal ha hζ hS r hr hp' hvanish

end ArkLib.ProximityGap.FpBridge

#print axioms ArkLib.ProximityGap.FpBridge.Fp_vanish_imp_dvd_norm
#print axioms ArkLib.ProximityGap.FpBridge.Fp_vanish_imp_dvd_norm'
#print axioms ArkLib.ProximityGap.FpBridge.spurious_Fp_vanish_imp_antipodal
#print axioms ArkLib.ProximityGap.FpBridge.spurious_Fp_vanish_imp_antipodal_prize
