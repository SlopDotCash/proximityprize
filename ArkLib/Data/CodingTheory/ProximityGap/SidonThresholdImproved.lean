/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonResultantImproved
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated

/-!
# THE IMPROVED NO-PARALLELOGRAM THRESHOLD — `p² ≤ 8^{φ(n)}` (#389)

Deploying `SidonResultantImproved.abs_resultant_fourTerm_sq_le` (`|Res|² ≤ 8^{φ(n)}`) through the
parallelogram machinery of `SidonLiftDevacuated`: a distinct-exponent parallelogram mod `p` forces
`p² ≤ 8^{φ(n)}`, i.e. `p ≤ 2^{3n/4}`.  Contrapositive: `p > 2^{3n/4}` forbids the parallelogram —
sharpening `prime_le_of_parallelogram'` (`p ≤ 2^n`).  Issue #389.
-/

open Complex Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The improved no-parallelogram threshold.**  For `n = 2^m`, a prime `p > 2` with a primitive
`n`-th root `ω ∈ ZMod p`, a complex primitive root `ζ` with pairwise-distinct powers, and a
parallelogram nontrivial over ℂ at every primitive root, `p² ≤ 8^{φ(n)}` — i.e. `p ≤ 2^{3n/4}`.
Contrapositive: `p > 2^{3n/4}` forbids the (distinct-exponent) parallelogram.  Sharpens
`prime_le_of_parallelogram'` (`p ≤ 2^n`) using the Parseval/AM-GM resultant bound. -/
theorem prime_sq_le_of_parallelogram {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 2 < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ m)) {i j k l : ℕ}
    (hpara : ω ^ i + ω ^ j - ω ^ k - ω ^ l = 0)
    (hne : ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 ^ m) → ξ ^ i + ξ ^ j - ξ ^ k - ξ ^ l ≠ 0)
    (hdist : Function.Injective (![ζ ^ i, ζ ^ j, ζ ^ k, ζ ^ l] : Fin 4 → ℂ)) :
    p ^ 2 ≤ 8 ^ (2 ^ m).totient := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  set R := resultant (cyclotomic n ℤ) (fourTerm i j k l) with hR
  -- fourTerm ≠ 0 (nonzero at a complex primitive root)
  have hne0 : fourTerm i j k l ≠ 0 := by
    intro h0
    refine hne _ (Complex.isPrimitiveRoot_exp n hn0) ?_
    have he := eval_fourTerm_map (Int.castRingHom ℂ)
      (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) i j k l
    rw [h0] at he; simp only [Polynomial.map_zero, eval_zero] at he; exact he.symm
  -- p ∣ R
  have hfdeg : ((fourTerm i j k l).map (Int.castRingHom (ZMod p))).natDegree
      = (fourTerm i j k l).natDegree := fourTerm_natDegree_map hp i j k l hne0
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine resultant_map_eq_zero_of_primitiveRoot hω (fourTerm i j k l) hfdeg ?_
    rw [eval_fourTerm_map]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  -- R ≠ 0, so p ≤ R.natAbs
  have hR0 : R ≠ 0 := resultant_fourTerm_ne_zero' hn0 hne
  have hdvdN : p ∣ R.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hpdvd
  have hple : p ≤ R.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hR0) hdvdN
  -- the improved bound: R.natAbs² ≤ 8^{φ(n)}
  have hsq : R.natAbs ^ 2 ≤ 8 ^ n.totient := abs_resultant_fourTerm_sq_le hm hζ hdist
  calc p ^ 2 ≤ R.natAbs ^ 2 := Nat.pow_le_pow_left hple 2
    _ ≤ 8 ^ n.totient := hsq

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prime_sq_le_of_parallelogram
