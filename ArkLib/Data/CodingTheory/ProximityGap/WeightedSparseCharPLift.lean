/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeightedSparseResultant
import ArkLib.Data.CodingTheory.ProximityGap.CyclotomicSidonLift

/-!
# THE CHAR-`p` WEIGHTED-SPARSE PRIME LIFT — the general mirror of `prime_le_of_genuineSixTerm` (#444)

`WeightedSparseResultant.weightedSparse_resultant_sq_le` proved the **complex** resultant bound
`|Res(Φ_n, f)|² ≤ (2·W)^{φ(n)}` for the weighted sparse polynomial `f = ∑ᵢ mᵢ·X^{eᵢ}` with
`W = ∑ᵢ mᵢ²` (subsuming the `±1` six-term `W = 6 ⟹ 12^{φ(n)}` *and* the repeated-value /
multiplicity relations). Its char-`p` prime lift — the general mirror of
`SixTermResultantImproved.prime_le_of_genuineSixTerm` — was **never** stated. This file supplies it:

> **`prime_le_of_genuineWeightedSparse`.** A **genuine** (non-char-0-vanishing, distinct-power)
> weighted relation `∑ᵢ mᵢ·ω^{eᵢ} = 0` over `F_p` (`ω` a primitive `2^m`-th root) forces
> `p² ≤ (2·W)^{φ(n)}`, i.e. `p ≤ (2W)^{n/4}`.

**Why this matters (the honest `RepThree` threshold).** The doc-comment of
`prime_le_of_genuineSixTerm` claimed that `p > 12^{n/4}` already forces `RepThree(μ_n)`. That is
**over-stated** (already flagged in `WeightedSparseResultant`): a weight-`[5,1]` degenerate
zero-sum sextuple `5·ζ⁰ + ζ⁵ ≡ 0` (`W = 26`) is a *genuine* `RepThree`-failure that lives **above**
`12^{n/4}` — e.g. `RepThree(μ_8)` fails at `p = 313 > 144 = 12^{8/4}` via `5 + ζ⁵ ≡ 0 (mod 313)`.
The `12`-bound governs only the **simple-sign / distinct** six-term. The *true* `RepThree` threshold
is the **weighted** one `(2·Wmax(6))^{n/4} = 52^{n/4}` (`Wmax(6) = 26`), and the lever that produces
it is exactly the weighted prime lift formalized here — the simple six-term is the `W = 6` instance.

EXTEND-proven off `weightedSparse_resultant_sq_le` + `resultant_map_eq_zero_of_primitiveRoot`
(char-`p` divisibility) + `resultant_cast_eq_prod_gen` (the complex product, for `R ≠ 0`). No `sorry`,
no `axiom`; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`). Probe: the threshold is a
valid sufficient ceiling — `RepThree(μ_8)` holds at every tested `p == 1 (mod 8)` above `52² = 2704`,
and the only sub-threshold failure found is the `[5,1]` worst-weight `p = 313`. Issue #444.
-/

open Complex Finset Polynomial
open ArkLib.ProximityGap.WeightedSparseResultant

namespace ArkLib.ProximityGap.WeightedSparseCharP

variable {n : ℕ}

/-- **`weightedSparse` evaluated over a field `K`.** For `f = ∑ᵢ mᵢ·X^{eᵢ}` mapped to `K` and any
`ζ : K`, `(f.map (Int.castRingHom K)).eval ζ = ∑ᵢ (mᵢ : K)·ζ^{eᵢ}`. The field-side companion of
`weightedSparse_eq_lincomb` (used to feed the genuine relation into the resultant). -/
theorem eval_weightedSparse_castMap {K : Type*} [Field K] (ζ : K) {k : ℕ}
    (m : Fin k → ℤ) (e : Fin k → ℕ) :
    ((weightedSparse m e).map (Int.castRingHom K)).eval ζ
      = ∑ i : Fin k, ((m i : K)) * ζ ^ (e i) := by
  rw [weightedSparse, Polynomial.map_sum, eval_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    eval_mul, eval_C, eval_pow, eval_X]
  simp

/-- **THE CHAR-`p` WEIGHTED-SPARSE PRIME LIFT.** For `n = 2^m` (`m ≥ 1`), a primitive `n`-th root
`ω ∈ ZMod p`, a **genuine** weighted relation `∑ᵢ mᵢ·ω^{eᵢ} = 0` over `F_p` (`hpara`) whose `ω`-powers
are pairwise distinct (`hdist`, over a fixed complex primitive root `ωc`) and which does **not** vanish
at any complex primitive `n`-th root (`hne`, i.e. it is not a char-0 / antipodally-paired relation),
together with the degree-preservation `hfdeg` and the weight bound `hW : ∑ᵢ mᵢ² ≤ W`, forces
`p² ≤ (2·W)^{φ(n)} = (2W)^{n/2}`, i.e. `p ≤ (2W)^{n/4}`. The general mirror of
`prime_le_of_genuineSixTerm` (its `W = 6` instance); the lever governing the **true** weighted
`RepThree` threshold `(2·Wmax)^{n/4}` that the simple `12^{n/4}` bound does not reach. -/
theorem prime_le_of_genuineWeightedSparse {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] {ω : ZMod p} (hωp : IsPrimitiveRoot ω (2 ^ m))
    {k : ℕ} (mc : Fin k → ℤ) (e : Fin k → ℕ)
    (hfdeg : ((weightedSparse mc e).map (Int.castRingHom (ZMod p))).natDegree
        = (weightedSparse mc e).natDegree)
    (hpara : ∑ i : Fin k, ((mc i : ZMod p)) * ω ^ (e i) = 0)
    {ωc : ℂ} (hωc : IsPrimitiveRoot ωc (2 ^ m))
    (hdist : Function.Injective (weightedVals ωc e))
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ m) → ∑ i : Fin k, ((mc i : ℂ)) * ζ ^ (e i) ≠ 0)
    {W : ℕ} (hW : ∑ i : Fin k, (mc i) ^ 2 ≤ (W : ℤ)) :
    p ^ 2 ≤ (2 * W) ^ (2 ^ m).totient := by
  set N := 2 ^ m with hN_def
  have hN0 : N ≠ 0 := by positivity
  haveI : NeZero (N : ℂ) := ⟨Nat.cast_ne_zero.mpr hN0⟩
  set R := resultant (cyclotomic N ℤ) (weightedSparse mc e) with hR
  -- `p ∣ R` from the genuine relation mod p
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine ArkLib.ProximityGap.AdditiveEnergyRepBound.resultant_map_eq_zero_of_primitiveRoot
      hωp (weightedSparse mc e) hfdeg ?_
    rw [eval_weightedSparse_castMap]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  -- `R ≠ 0`: resultant is the product over complex primitive roots, each factor nonzero by `hne`
  have hR0 : R ≠ 0 := by
    intro h0
    have hcast0 : (algebraMap ℤ ℂ) R = 0 := by rw [h0]; simp
    have hprod : (((cyclotomic N ℂ).roots).map
        (fun ζ => eval ζ ((weightedSparse mc e).map (algebraMap ℤ ℂ)))).prod = 0 := by
      rw [← ArkLib.ProximityGap.ManyTermResultant.resultant_cast_eq_prod_gen
        (weightedSparse mc e)]
      exact hcast0
    rw [Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hprod
    have hxprim : IsPrimitiveRoot x N := by
      rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
        mem_primitiveRoots (Nat.pos_of_ne_zero hN0)] at hx
      exact hx
    -- the complex factor equals `∑ᵢ mᵢ·x^{eᵢ}`, nonzero by `hne`
    have hxval : eval x ((weightedSparse mc e).map (algebraMap ℤ ℂ))
        = ∑ i : Fin k, ((mc i : ℂ)) * x ^ (e i) := by
      have := eval_weightedSparse_castMap (K := ℂ) x mc e
      rwa [show (Int.castRingHom ℂ) = (algebraMap ℤ ℂ) from rfl] at this
    rw [hxval] at hx0
    exact hne x hxprim hx0
  -- `p ≤ |R|`, and `|R|² = (R.natAbs)² ≤ (2W)^{φ(n)}`
  have hdvdabs : (p : ℤ) ∣ |R| := by rw [Int.abs_eq_natAbs]; exact Int.dvd_natAbs.mpr hpdvd
  have hle : (p : ℤ) ≤ |R| := Int.le_of_dvd (abs_pos.mpr hR0) hdvdabs
  have hpnat : p ≤ R.natAbs := by
    have : (p : ℤ) ≤ (R.natAbs : ℤ) := by rwa [Int.abs_eq_natAbs] at hle
    exact_mod_cast this
  have hsq : p ^ 2 ≤ R.natAbs ^ 2 := Nat.pow_le_pow_left hpnat 2
  have hbound : R.natAbs ^ 2 ≤ (2 * W) ^ N.totient :=
    weightedSparse_resultant_sq_le hm mc e hωc hdist hW
  exact le_trans hsq hbound

/-- **The simple six-term is the `W = 6` instance.** For the `±1` six-term coefficient vector
`![1,1,1,−1,−1,−1]`, the weight `∑ᵢ mᵢ² = 6`, so `prime_le_of_genuineWeightedSparse` recovers the
`12^{φ(n)}` bound of `prime_le_of_genuineSixTerm` — confirming the simple six-term is the minimal-weight
special case and the weighted lift strictly generalizes it. -/
theorem sixSign_weight_eq_six :
    (∑ i : Fin 6, (((![1, 1, 1, -1, -1, -1] : Fin 6 → ℤ)) i) ^ 2) = 6 := by
  decide

end ArkLib.ProximityGap.WeightedSparseCharP

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WeightedSparseCharP.eval_weightedSparse_castMap
#print axioms ArkLib.ProximityGap.WeightedSparseCharP.prime_le_of_genuineWeightedSparse
#print axioms ArkLib.ProximityGap.WeightedSparseCharP.sixSign_weight_eq_six
