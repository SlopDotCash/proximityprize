/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidon
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# LIFTING `μ_n` SIDON FROM ℂ TO `F_p` VIA THE CYCLOTOMIC RESULTANT (#389)

The small-subgroup δ* pin needs: for `n = 2^m`, prime `p ≡ 1 (mod n)` with `p > 2^n`, the
subgroup `μ_n ⊂ F_p` is Sidon (`r(c) ≤ 2`).  The bridge from the ℂ-Sidon fact
(`unitCircle_sidon`) to the finite field is the **cyclotomic resultant**:

* a parallelogram `ω^i + ω^j = ω^k + ω^l` (`{i,j}≠{k,l}`) at a primitive `n`-th root `ω ∈ F_p`
  forces `Res(Φ_n, X^i+X^j−X^k−X^l) ≡ 0 (mod p)`, i.e. `p ∣ Res`;
* `Res` is a **nonzero** integer — nonzero because the four-term polynomial does not vanish at a
  primitive `n`-th root over ℂ (this is `unitCircle_sidon`);
* `|Res| ≤ 4^{φ(n)} = 2^n`.

Hence `p > 2^n` is impossible, so no such parallelogram exists.  This file builds the chain.  The
first brick, `fourTerm_ne_zero_of_pair_ne`, is the ℂ input (the corollary of `unitCircle_sidon`
that the four-term value is nonzero), which gives the nonzero resultant.  Issue #389.
-/

open Polynomial Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- For `n`-th roots of unity, `(ζ^i)^n = 1`. -/
private theorem pow_pow_eq_one {n : ℕ} {ζ : ℂ} (hζ : ζ ^ n = 1) (i : ℕ) : (ζ ^ i) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

/-- **The ℂ four-term value is nonzero** (corollary of `unitCircle_sidon`).  If the powers do not
form a matched pair and the partial sum `ζ^i + ζ^j ≠ 0`, then `ζ^i + ζ^j − ζ^k − ζ^l ≠ 0`.  This is
exactly the statement that the four-term polynomial does not vanish at the root of unity `ζ` — the
nonvanishing that makes the cyclotomic resultant nonzero. -/
theorem fourTerm_ne_zero_of_pair_ne {n : ℕ} (hn : n ≠ 0) {ζ : ℂ} (hζ : ζ ^ n = 1)
    {i j k l : ℕ} (hsum : ζ ^ i + ζ ^ j ≠ 0)
    (hpair : ¬ ((ζ ^ i = ζ ^ k ∧ ζ ^ j = ζ ^ l) ∨ (ζ ^ i = ζ ^ l ∧ ζ ^ j = ζ ^ k))) :
    ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0 := by
  intro h
  have heq : ζ ^ i + ζ ^ j = ζ ^ k + ζ ^ l := by linear_combination h
  exact hpair (unitCircle_sidon hn (pow_pow_eq_one hζ i) (pow_pow_eq_one hζ j)
    (pow_pow_eq_one hζ k) (pow_pow_eq_one hζ l) heq hsum)

/-- **Resultant divisibility.**  If a field `K` has a primitive `n`-th root `ω` (with `n` a unit)
at which the integer polynomial `f` vanishes mod the structure map, then the integer
`resultant (cyclotomic n ℤ) f` maps to `0` in `K`.  Specialized to `K = ZMod p` this gives
`p ∣ resultant`. -/
theorem resultant_map_eq_zero_of_primitiveRoot {K : Type*} [Field K] {n : ℕ} [NeZero (n : K)]
    {ω : K} (hω : IsPrimitiveRoot ω n) (f : ℤ[X])
    (hfdeg : (f.map (Int.castRingHom K)).natDegree = f.natDegree)
    (hf : (f.map (Int.castRingHom K)).eval ω = 0) :
    (algebraMap ℤ K) (resultant (cyclotomic n ℤ) f) = 0 := by
  -- `ω` is a root of `cyclotomic n K = (cyclotomic n ℤ).map`
  have hcyc : (cyclotomic n K).IsRoot ω := (isRoot_cyclotomic_iff).mpr hω
  rw [← map_cyclotomic n (Int.castRingHom K)] at hcyc
  -- both `cyclotomic n ℤ |>.map` and `f.map` vanish at `ω`, so they are not coprime
  have hncop : ¬ IsCoprime ((cyclotomic n ℤ).map (Int.castRingHom K)) (f.map (Int.castRingHom K)) := by
    intro hcop
    have hmap := hcop.map (evalRingHom ω)  -- evaluate the Bezout identity at ω
    rw [IsRoot.def] at hcyc
    simp only [coe_evalRingHom, hcyc, hf] at hmap
    exact not_isUnit_zero (isCoprime_zero_left.mp hmap)
  -- so the resultant over `K` is zero
  have hz : resultant ((cyclotomic n ℤ).map (Int.castRingHom K)) (f.map (Int.castRingHom K)) = 0 := by
    rw [resultant_eq_zero_iff]
    refine ⟨Or.inl ?_, hncop⟩
    rw [map_cyclotomic]; exact cyclotomic_ne_zero n K
  -- align the degree arguments: cyclotomic is monic (degree preserved), and `hfdeg` for `f`
  have hcd : ((cyclotomic n ℤ).map (Int.castRingHom K)).natDegree = (cyclotomic n ℤ).natDegree := by
    rw [map_cyclotomic, natDegree_cyclotomic, natDegree_cyclotomic]
  rw [resultant, hcd, hfdeg, ← resultant, resultant_map_map] at hz
  simpa using hz

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.fourTerm_ne_zero_of_pair_ne
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.resultant_map_eq_zero_of_primitiveRoot
