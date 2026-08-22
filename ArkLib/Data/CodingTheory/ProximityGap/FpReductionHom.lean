/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic
import ArkLib.Data.CodingTheory.ProximityGap.FpVanishingBridge

/-!
# fp-reduction-hom: the reduction map `𝓞_K → F_p` is CONSTRUCTED, not assumed (#407, LEVER L)

`FpVanishingBridge.lean` discharges the height gate's divisibility hypothesis
`(p : ℤ) ∣ N(∑ ζ^i)` from the actual `F_p`-vanishing `∑ ω^i = 0` — BUT only **conditional on a
ring hom** `r : 𝓞_K → ZMod p` with `r ζ = ω` (the reduction at a prime above `p`), kept there as
an explicit hypothesis ("the one heavy step").

This file **CONSTRUCTS that hom** for the prize-relevant case `K = CyclotomicField (2^a) ℚ`
(`n = 2^a`, a prime power), eliminating the hypothesis.  This is the Mathlib-gap **LEVER L** lift
that makes the height gate `gate_2power_antipodal` fully rigorous end to end: the only remaining
INPUT is the elementary fact that `ω : ZMod p` is a root of the cyclotomic polynomial mod `p`
(equivalently a primitive `2^a`-th root in `F_p`, which holds exactly when `2^a ∣ p-1`).

## Mechanism (no Dedekind/ramification machinery)

For `n = 2^a` a prime power, Mathlib gives the **integral power basis**
`hζ.integralPowerBasisOfPrimePow : PowerBasis ℤ (𝓞 K)` with generator `ζ.toInteger` and minimal
polynomial `minpoly ℤ ζ.toInteger = cyclotomic (2^a) ℤ` (`RingOfIntegers.minpoly_coe` +
`cyclotomic_eq_minpoly`).  An algebra hom out of a power-basis ring is then DETERMINED by the image
of the generator, provided that image is a root of the minimal polynomial (`PowerBasis.lift`).  So
sending `ζ.toInteger ↦ ω` extends to a ring hom `𝓞_K →ₐ[ℤ] ZMod p` **iff**
`aeval ω (cyclotomic (2^a) ℤ) = 0` — exactly "ω is a primitive `2^a`-th root mod `p`".  No choice
of prime above `p`, no residue-field identification, no Kummer–Dedekind: the splitting is encoded
entirely in the single polynomial-root condition on `ω`.

## What is PROVED (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `redHom` / `redHom_toInteger`: the constructed reduction hom and `r ζ.toInteger = ω`.
* `aeval_cyclotomic_eq_zero_of_isPrimitiveRoot`: the root condition holds for any primitive
  `2^a`-th root `ω ∈ ZMod p` (`p` odd) — the natural `n ∣ p-1` form of the input.
* `spurious_Fp_vanish_imp_antipodal_constructed`: the END-TO-END height gate with the `r`
  hypothesis REMOVED — `F_p`-spurious vanishing of a root-sum (over the constructed reduction)
  forces antipodality, conditional only on the height bound and `ω` being a primitive root mod `p`.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Polynomial IsPrimitiveRoot

namespace ArkLib.ProximityGap.FpReductionHom

variable {K : Type*} [Field K] [CharZero K] {a : ℕ} {ζ : K}

/-! ## The minimal polynomial of the integral generator is the cyclotomic polynomial -/

/-- For `K` a `2^a`-th cyclotomic extension of `ℚ` and `ζ` a primitive `2^a`-th root, the minimal
polynomial over `ℤ` of the integral power-basis generator `ζ.toInteger` is `cyclotomic (2^a) ℤ`.

`integralPowerBasisOfPrimePow.gen = ζ.toInteger` (`integralPowerBasisOfPrimePow_gen`), and
`minpoly ℤ ζ.toInteger = minpoly ℤ (ζ.toInteger : K) = minpoly ℤ ζ = cyclotomic (2^a) ℤ`
(`RingOfIntegers.minpoly_coe`, `coe_toInteger`, `cyclotomic_eq_minpoly`). -/
theorem minpoly_integralGen_eq [IsCyclotomicExtension {2 ^ a} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) :
    minpoly ℤ (hζ.integralPowerBasisOfPrimePow.gen) = cyclotomic (2 ^ a) ℤ := by
  rw [hζ.integralPowerBasisOfPrimePow_gen, ← RingOfIntegers.minpoly_coe hζ.toInteger]
  change minpoly ℤ (hζ.toInteger.1 : K) = _
  rw [hζ.coe_toInteger, cyclotomic_eq_minpoly hζ (by positivity)]

/-! ## The constructed reduction hom -/

/-- **The reduction hom `𝓞_K →ₐ[ℤ] ZMod p`, `ζ.toInteger ↦ ω`** (`n = 2^a`).

Constructed via `PowerBasis.lift` on the integral power basis of `𝓞_K`: it exists because the
image `ω` is a root of the generator's minimal polynomial `cyclotomic (2^a) ℤ` (hypothesis `hω`).
This is the splitting/reduction map of `FpVanishingBridge.lean`, now an explicit construction
rather than a hypothesis. -/
noncomputable def redHom {p : ℕ} [IsCyclotomicExtension {2 ^ a} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) {ω : ZMod p}
    (hω : aeval ω (cyclotomic (2 ^ a) ℤ) = 0) :
    𝓞 K →ₐ[ℤ] ZMod p :=
  hζ.integralPowerBasisOfPrimePow.lift ω (by rw [minpoly_integralGen_eq hζ]; exact hω)

/-- The constructed reduction hom sends `ζ.toInteger ↦ ω` (`PowerBasis.lift_gen`). -/
@[simp]
theorem redHom_toInteger {p : ℕ} [IsCyclotomicExtension {2 ^ a} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) {ω : ZMod p}
    (hω : aeval ω (cyclotomic (2 ^ a) ℤ) = 0) :
    redHom hζ hω hζ.toInteger = ω := by
  unfold redHom
  rw [← hζ.integralPowerBasisOfPrimePow_gen]
  exact PowerBasis.lift_gen _ _ _

/-! ## The root condition from a primitive root in `F_p` (the natural `n ∣ p-1` input) -/

/-- **The cyclotomic-root condition holds for any primitive `2^a`-th root in `F_p`** (`p` odd).

If `ω : ZMod p` is a primitive `2^a`-th root of unity (equivalently `2^a ∣ p-1` provides such an
`ω`), then `aeval ω (cyclotomic (2^a) ℤ) = 0` — exactly the hypothesis `redHom` consumes.  This is
`isRoot_cyclotomic_iff` over `ZMod p` (which needs `NeZero ((2^a : ℕ) : ZMod p)`, i.e. `p ∤ 2^a`,
supplied by oddness of `p`), pulled back along `map_cyclotomic_int : map (Int.cast) (cyclotomic n ℤ) = cyclotomic n (ZMod p)`. -/
theorem aeval_cyclotomic_eq_zero_of_isPrimitiveRoot {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ a)) :
    aeval ω (cyclotomic (2 ^ a) ℤ) = 0 := by
  -- `aeval ω (cyclotomic (2^a) ℤ) = eval ω (map Int.cast (cyclotomic (2^a) ℤ)) = eval ω (cyclotomic (2^a) (ZMod p))`.
  have hmap : (aeval ω) (cyclotomic (2 ^ a) ℤ) = eval ω (cyclotomic (2 ^ a) (ZMod p)) := by
    rw [aeval_def, eval₂_eq_eval_map]
    congr 1
    rw [← map_cyclotomic_int (2 ^ a) (ZMod p)]
    simp only [algebraMap_int_eq]
  rw [hmap]
  -- `p ∤ 2^a` (p odd prime): so `(2^a : ZMod p) ≠ 0`, giving `NeZero`.
  haveI : NeZero ((2 ^ a : ℕ) : ZMod p) := by
    refine ⟨?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow hdvd))
  -- `ω` root of `cyclotomic (2^a) (ZMod p)` ⟺ primitive root.
  rw [← IsRoot.def, isRoot_cyclotomic_iff]
  exact hω

/-! ## End-to-end: the height gate with the reduction hom CONSTRUCTED (no `r` hypothesis) -/

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`spurious_Fp_vanish_imp_antipodal_constructed` — LEVER L closed (small/mid `n`).**

The end-to-end height gate of `FpVanishingBridge.lean`, with the reduction-hom hypothesis
**eliminated**.  For `K` a `2^a`-th cyclotomic extension of `ℚ` (`a ≥ 1`), `ζ` a primitive
`2^a`-th root, `ω : ZMod p` a root of `cyclotomic (2^a) ℤ` (= a primitive `2^a`-th root in `F_p`,
i.e. `2^a ∣ p-1`), and the height bound `p > (#S)^{[K:ℚ]}`: if the root-sum vanishes in `F_p`
(`∑_{i∈S} ω^i = 0`), then the exponent set `S` is antipodal.

The reduction hom is the CONSTRUCTED `redHom hζ' hω` (`hζ'` the primitivity of `ζ.toInteger`),
fed into `FpBridge.spurious_Fp_vanish_imp_antipodal`.  No prime-above-`p` is chosen by hand; the
splitting datum is exactly the polynomial-root condition `hω` on `ω`. -/
theorem spurious_Fp_vanish_imp_antipodal_constructed [NumberField K]
    [IsCyclotomicExtension {2 ^ a} ℚ K] (ha : 1 ≤ a)
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} {ω : ZMod p} (hω : aeval ω (cyclotomic (2 ^ a) ℤ) = 0)
    (hp : (S.card : ℝ) ^ Module.finrank ℚ K < p)
    (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    ExponentAntipodal a S := by
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  -- `ζ.toInteger : 𝓞 K` has `(ζ.toInteger : K) = ζ` a primitive `2^a`-th root.
  have hζ' : IsPrimitiveRoot ((hζ.toInteger : 𝓞 K) : K) (2 ^ a) := by
    have : ((hζ.toInteger : 𝓞 K) : K) = ζ := hζ.coe_toInteger
    rw [this]; exact hζ
  -- the constructed reduction hom, with `r ζ.toInteger = ω`.
  exact ArkLib.ProximityGap.FpBridge.spurious_Fp_vanish_imp_antipodal ha hζ' hS
    (redHom hζ hω).toRingHom (by rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_ringHom_mk]; exact redHom_toInteger hζ hω) hp hvanish

open ArkLib.ProximityGap.RouVanishingCount in
/-- **`spurious_Fp_vanish_imp_antipodal_of_primitiveRoot` — the `n ∣ p-1` packaging.**

`spurious_Fp_vanish_imp_antipodal_constructed` with the cyclotomic-root input replaced by the
NATURAL hypothesis that `ω : ZMod p` is a **primitive `2^a`-th root of unity** (`p` an odd prime;
such an `ω` exists exactly when `2^a ∣ p-1`).  The root condition is supplied by
`aeval_cyclotomic_eq_zero_of_isPrimitiveRoot`.  This is the cleanest consumer form: NO reduction
hom and NO polynomial condition — just "a primitive `2^a`-th root mod `p`, a height bound, and an
`F_p`-vanishing root-sum ⟹ antipodal exponent set". -/
theorem spurious_Fp_vanish_imp_antipodal_of_primitiveRoot [NumberField K]
    [IsCyclotomicExtension {2 ^ a} ℚ K] (ha : 1 ≤ a)
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ a))
    (hp : (S.card : ℝ) ^ Module.finrank ℚ K < p)
    (hvanish : ∑ i ∈ S, ω ^ i = 0) :
    ExponentAntipodal a S :=
  spurious_Fp_vanish_imp_antipodal_constructed ha hζ hS
    (aeval_cyclotomic_eq_zero_of_isPrimitiveRoot hodd hω) hp hvanish

end ArkLib.ProximityGap.FpReductionHom

#print axioms ArkLib.ProximityGap.FpReductionHom.minpoly_integralGen_eq
#print axioms ArkLib.ProximityGap.FpReductionHom.redHom_toInteger
#print axioms ArkLib.ProximityGap.FpReductionHom.aeval_cyclotomic_eq_zero_of_isPrimitiveRoot
#print axioms ArkLib.ProximityGap.FpReductionHom.spurious_Fp_vanish_imp_antipodal_constructed
#print axioms ArkLib.ProximityGap.FpReductionHom.spurious_Fp_vanish_imp_antipodal_of_primitiveRoot
