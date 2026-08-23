/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import ArkLib.Data.CodingTheory.ProximityGap.HeightGateAMGM
import ArkLib.Data.CodingTheory.ProximityGap.HeightGateNormBound
import ArkLib.Data.CodingTheory.ProximityGap.FpReductionHom

/-!
# amgm-gate-wire: the TIGHT AM-GM bound wired into an END-TO-END height gate (#407)

`HeightGateAMGM.lean` proves the genuinely-sharp norm bound
`abs_norm_sq_le_card_pow_half`: for `α = Σ_{i∈S} ζ^i ∈ K = ℚ(ζ_{2^a})`, conditional on the
named cyclotomic L²-mass datum (`hmass : Σ_σ ‖σα‖² = (n/2)·#S`, `hcard : #(K→ₐℂ) = n/2`),

    `|N_{ℚ}(α)|² ≤ (#S)^{n/2}`   i.e.   `|N(α)| ≤ (#S)^{n/4}`     (HALF the house exponent).

That file stopped at the bound; the gate itself (`HeightGateNormBound.gate_2power_antipodal`)
still consumed the *crude* house bound `(#S)^{n/2}` through `abs_norm_sum_rootsOfUnity_le`.  This
file **closes the (2) gap**: it wires the tight AM-GM bound into a working gate.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `gate_sum_zero_via_amgm`: given the AM-GM squared threshold `(#S)^{n/2} < p²` (= the
  HALF-exponent house) plus the L²-mass datum and `p ∣ N_ℤ(Σ ζ^i)`, the sum **vanishes in `𝓞_K`**.
  Logic: `|N|² ≤ (#S)^{n/2} < p²` ⟹ `|N| < p`; a nonzero integer divisible by `p` has `|·| ≥ p`;
  contradiction forces `N = 0`, hence `Σ = 0` (`Algebra.norm_eq_zero_iff`).  This CONSUMES the
  proven tight bound — `hmass`/`hcard` are the *same* named datum, not a fresh house hypothesis.
* `gate_closes_via_amgm`: chains to **antipodality** of the exponent set `S` (via the landed
  char-0 converse `zero_sum_imp_antipodal`).  The end-to-end height gate at the *halved* exponent.
* `gate_closes_via_amgm_quarter`: the clean consumer form taking the natural HALF-house threshold
  `(#S)^{n/4} < p` directly (for `a ≥ 2`, where `n/2 = 2·(n/4)`).
* `Fp_gate_closes_via_amgm`: the `F_p`-vanishing form, with the reduction hom CONSTRUCTED through
  `FpReductionHom.redHom` — `Σ ω^i = 0` in `F_p` ⟹ antipodal, at the halved exponent.

## Honest boundary (NOT a prize closure)

This is the rigorous wiring of the `32 → 64` AM-GM push (see `HeightGateAMGM`'s honest boundary):
the exponent `n/4` is still linear in `n`, so the gate is provably capped at `n ≤ 64–96` and CANNOT
reach the prize `n = 2^30` (`HeightGateThresholdAnalysis.gate_fails_above_128`).  Two residuals
remain explicit: the named `CyclotomicL2Mass` datum (`hmass`/`hcard`, Mathlib lacks the cyclotomic
trace API) and, fundamentally, the fact that no fixed mean-inequality exponent reaches `O(log n)`.
The prize needs the BGK/Paley character-sum lane, not this gate.  This file makes the AM-GM bound
*usable* (end-to-end gate), which it was not before.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Module

namespace ArkLib.ProximityGap.GateAMGMWire

open ArkLib.ProximityGap.GateAMGM

variable {K : Type*} [Field K] [NumberField K]

/-! ## The AM-GM gate forces the sum to vanish in `𝓞_K` -/

/-- **The AM-GM height gate (sum-vanishing form).**

Let `Sg = Σ_{i∈S} u_i ∈ 𝓞_K`.  Suppose the conjugate-L²-mass of its image `(Sg : K)` equals
`(n/2)·t` and `#(K→ₐℂ) = n/2` (the named `CyclotomicL2Mass` datum, with `t = #S` the reduced
support).  If the AM-GM squared threshold `t^{n/2} < p²` holds — this is the HALF-house exponent,
since `t^{n/2} = (t^{n/4})²` — and `(p:ℤ) ∣ N_ℤ(Sg)`, then `Sg = 0`.

Mechanism: `abs_norm_sq_le_card_pow_half` gives `|N_ℚ(Sg:K)|² ≤ t^{n/2} < p²`, so `|N_ℤ Sg| < p`
(via `Algebra.coe_norm_int`); a nonzero integer divisible by `p` has `|·| ≥ p`; contradiction
forces `N_ℤ Sg = 0`, hence `Sg = 0` (`Algebra.norm_eq_zero_iff` over the finite-free domain
`ℤ → 𝓞_K`).  This consumes the PROVEN tight bound, not a fresh house hypothesis. -/
theorem gate_sum_zero_via_amgm {Sg : 𝓞 K} {n t : ℕ} {p : ℕ}
    (hcard : Fintype.card (K →ₐ[ℚ] ℂ) = n / 2)
    (hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((Sg : K))‖ ^ 2) = ((n / 2 : ℕ) : ℝ) * t)
    (hthr : (t : ℝ) ^ (n / 2) < (p : ℝ) ^ 2)
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ Sg) :
    Sg = 0 := by
  classical
  set N : ℤ := Algebra.norm ℤ Sg with hN
  -- The integer norm equals the rational norm of the image in `K`.
  have hcoe : (N : ℚ) = Algebra.norm ℚ ((Sg : K)) := Algebra.coe_norm_int Sg
  by_contra hne
  -- `N ≠ 0` because the norm of a nonzero element is nonzero (finite-free domain extension).
  have hN0 : N ≠ 0 := by rw [hN]; exact (Algebra.norm_ne_zero_iff).mpr hne
  -- the TIGHT bound `|N_ℚ(Sg:K)|² ≤ t^{n/2}`.
  have hsqbound : ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) ^ 2 ≤ (t : ℝ) ^ (n / 2) :=
    abs_norm_sq_le_card_pow_half hcard hmass
  -- transport to `|N : ℤ|`: `(|N|:ℝ) = (|N_ℚ(Sg:K)|:ℝ)`.
  have heq : ((|N| : ℤ) : ℝ) = ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) := by
    have hQ : ((|N| : ℤ) : ℚ) = (|Algebra.norm ℚ ((Sg : K))| : ℚ) := by
      rw [Int.cast_abs, hcoe]
    have : (((|N| : ℤ) : ℚ) : ℝ) = ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) := by rw [hQ]
    simpa using this
  -- `|N|² < p²` as reals.
  have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < (p : ℝ) ^ 2 := by
    rw [heq]; exact lt_of_le_of_lt hsqbound hthr
  -- `|N| < p` from `|N|² < p²` (both nonneg).
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hNnn : (0 : ℝ) ≤ ((|N| : ℤ) : ℝ) := by positivity
  have hlt : ((|N| : ℤ) : ℝ) < (p : ℝ) := by
    nlinarith [hsq, hpnn, hNnn, sq_nonneg (((|N| : ℤ) : ℝ) - (p : ℝ)),
      sq_nonneg (((|N| : ℤ) : ℝ) + (p : ℝ))]
  -- `p ∣ N` with `N ≠ 0` ⟹ `p ≤ |N|`, contradiction with `|N| < p`.
  have hple : (p : ℤ) ≤ |N| := Int.le_of_dvd (abs_pos.mpr hN0) ((dvd_abs _ _).mpr hdvd)
  have hpleR : (p : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast hple
  exact absurd (lt_of_le_of_lt hpleR hlt) (lt_irrefl _)

/-! ## End-to-end: the AM-GM gate forces antipodality (`2^a` group) -/

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`gate_closes_via_amgm` — the AM-GM height gate ⟹ antipodality.**

Let `ζ : 𝓞_K` with `(ζ:K)` a primitive `2^a`-th root (`a ≥ 1`), `S ⊆ range (2^a)`, and the named
cyclotomic L²-mass datum for `α = Σ_{i∈S} ζ^i` (`hcard`, `hmass` with `t = #S`).  If the AM-GM
squared (HALF-house) threshold `(#S)^{2^a/2} < p²` holds and `p ∣ N_ℤ(Σ ζ^i)`, then `S` is
**antipodal** (`ExponentAntipodal a S`).

Chains `gate_sum_zero_via_amgm` (sum vanishes in `𝓞_K`) with `zero_sum_imp_antipodal` (char-0
converse Lam–Leung).  This is `gate_2power_antipodal` at the *halved* AM-GM exponent — the tight
bound made end-to-end. -/
theorem gate_closes_via_amgm {a : ℕ} (ha : 1 ≤ a) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ((ζ : K)) (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ}
    (hcard : Fintype.card (K →ₐ[ℚ] ℂ) = (2 ^ a) / 2)
    (hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((∑ i ∈ S, (ζ ^ i : 𝓞 K) : 𝓞 K) : K)‖ ^ 2)
      = (((2 ^ a) / 2 : ℕ) : ℝ) * S.card)
    (hthr : (S.card : ℝ) ^ ((2 ^ a) / 2) < (p : ℝ) ^ 2)
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, (ζ ^ i : 𝓞 K))) :
    ExponentAntipodal a S := by
  classical
  -- the AM-GM gate forces the sum to vanish in `𝓞_K`.
  have hzero : (∑ i ∈ S, (ζ ^ i : 𝓞 K)) = 0 :=
    gate_sum_zero_via_amgm hcard hmass hthr hdvd
  -- transport to `K`.
  have hzeroK : (∑ i ∈ S, ((ζ : K)) ^ i) = 0 := by
    have hcastZero : ((∑ i ∈ S, (ζ ^ i : 𝓞 K) : 𝓞 K) : K) = ((0 : 𝓞 K) : K) := by rw [hzero]
    push_cast at hcastZero
    simpa using hcastZero
  exact zero_sum_imp_antipodal ha hζ hS hzeroK

/-! ## The clean half-house consumer form (`a ≥ 2`: `n/4` exponent directly) -/

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`gate_closes_via_amgm_quarter` — the half-house threshold `(#S)^{n/4} < p` directly.**

For `a ≥ 2` (so `n = 2^a` is divisible by `4` and `n/2 = 2·(n/4)`), the squared threshold
`(#S)^{n/2} < p²` of `gate_closes_via_amgm` is exactly the square of the natural HALF-house
threshold `(#S)^{n/4} < p`.  This consumer takes that cleaner hypothesis directly.

This is the literal "AM-GM threshold `(#S)^{n/4} < p` (HALF the house exponent `n/2`)" gate:
`|N| ≤ (#S)^{n/4} < p`, so `p ∣ N_ℤ` with `|N_ℤ| < p` forces `N_ℤ = 0 ⟹ Σ = 0 ⟹` antipodal. -/
theorem gate_closes_via_amgm_quarter {a : ℕ} (ha : 2 ≤ a) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ((ζ : K)) (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ}
    (hcard : Fintype.card (K →ₐ[ℚ] ℂ) = (2 ^ a) / 2)
    (hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((∑ i ∈ S, (ζ ^ i : 𝓞 K) : 𝓞 K) : K)‖ ^ 2)
      = (((2 ^ a) / 2 : ℕ) : ℝ) * S.card)
    (hthr : (S.card : ℝ) ^ ((2 ^ a) / 4) < (p : ℝ))
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, (ζ ^ i : 𝓞 K))) :
    ExponentAntipodal a S := by
  classical
  -- `2^a / 2 = (2^a / 4) · 2` for `a ≥ 2`.
  have hdiv : (2 ^ a) / 2 = ((2 ^ a) / 4) * 2 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    have h4 : (2 : ℕ) ^ (b + 2) = 2 ^ b * 4 := by rw [pow_add]; ring
    rw [h4, Nat.mul_div_assoc _ (by norm_num : (2 : ℕ) ∣ 4),
      Nat.mul_div_assoc _ (by norm_num : (4 : ℕ) ∣ 4)]
    ring
  -- square the half-house threshold to get the squared threshold.
  have hthr2 : (S.card : ℝ) ^ ((2 ^ a) / 2) < (p : ℝ) ^ 2 := by
    rw [hdiv, pow_mul]
    have hnn : (0 : ℝ) ≤ (S.card : ℝ) ^ ((2 ^ a) / 4) := by positivity
    exact pow_lt_pow_left₀ hthr hnn (by norm_num)
  exact gate_closes_via_amgm (le_of_lt (lt_of_lt_of_le one_lt_two ha)) hζ hS hcard hmass hthr2 hdvd

/-! ## The `F_p`-vanishing form (reduction hom CONSTRUCTED) -/

variable {a : ℕ} {ζK : K}

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`Fp_gate_closes_via_amgm` — the AM-GM gate from `F_p`-vanishing (constructed reduction).**

The end-to-end AM-GM gate phrased on the actual proximity-gap object: `μ_n ⊂ F_p`, `ω` a primitive
`2^a`-th root in `F_p`, and spurious vanishing `Σ_{i∈S} ω^i = 0` in `F_p`.  The reduction hom
`𝓞_K → F_p` is CONSTRUCTED (`FpReductionHom.redHom`, via the cyclotomic root condition `hω`),
turning `Σ ω^i = 0` into `p ∣ N_ℤ(Σ ζ^i)` (`FpBridge.Fp_vanish_imp_dvd_norm'`), which the AM-GM
gate then closes at the HALVED exponent.

Conditional only on: the named L²-mass datum (`hcard`/`hmass`), the AM-GM squared threshold
`(#S)^{n/2} < p²`, and `ω` being a primitive `2^a`-th root mod `p` (the `n ∣ p-1` input). -/
theorem Fp_gate_closes_via_amgm [IsCyclotomicExtension {2 ^ a} ℚ K] [CharZero K]
    (ha : 1 ≤ a) (hζK : IsPrimitiveRoot ζK (2 ^ a))
    {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} {ω : ZMod p} (hω : Polynomial.aeval ω (Polynomial.cyclotomic (2 ^ a) ℤ) = 0)
    (hcard : Fintype.card (K →ₐ[ℚ] ℂ) = (2 ^ a) / 2)
    (hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((∑ i ∈ S, (hζK.toInteger ^ i : 𝓞 K) : 𝓞 K) : K)‖ ^ 2)
      = (((2 ^ a) / 2 : ℕ) : ℝ) * S.card)
    (hthr : (S.card : ℝ) ^ ((2 ^ a) / 2) < (p : ℝ) ^ 2)
    (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    ExponentAntipodal a S := by
  classical
  -- `ζ.toInteger : 𝓞 K` has `(ζ.toInteger : K) = ζK` a primitive `2^a`-th root.
  have hζ' : IsPrimitiveRoot ((hζK.toInteger : 𝓞 K) : K) (2 ^ a) := by
    have hco : ((hζK.toInteger : 𝓞 K) : K) = ζK := hζK.coe_toInteger
    rw [hco]; exact hζK
  -- the constructed reduction hom sends `ζ.toInteger ↦ ω`.
  have hr : (ArkLib.ProximityGap.FpReductionHom.redHom hζK hω).toRingHom (hζK.toInteger) = ω := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_ringHom_mk]
    exact ArkLib.ProximityGap.FpReductionHom.redHom_toInteger hζK hω
  -- `F_p`-vanishing ⟹ `p ∣ N_ℤ(Σ ζ^i)` via the constructed reduction.
  have hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, (hζK.toInteger ^ i : 𝓞 K)) :=
    ArkLib.ProximityGap.FpBridge.Fp_vanish_imp_dvd_norm'
      (ArkLib.ProximityGap.FpReductionHom.redHom hζK hω).toRingHom hr hvanish
  exact gate_closes_via_amgm ha hζ' hS hcard hmass hthr hdvd

end ArkLib.ProximityGap.GateAMGMWire

#print axioms ArkLib.ProximityGap.GateAMGMWire.gate_sum_zero_via_amgm
#print axioms ArkLib.ProximityGap.GateAMGMWire.gate_closes_via_amgm
#print axioms ArkLib.ProximityGap.GateAMGMWire.gate_closes_via_amgm_quarter
#print axioms ArkLib.ProximityGap.GateAMGMWire.Fp_gate_closes_via_amgm
