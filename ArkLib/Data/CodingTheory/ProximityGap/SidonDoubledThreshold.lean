/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonDoubledBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated

/-!
# THE DOUBLED-CASE NO-PARALLELOGRAM THRESHOLD — `p² ≤ 12^{φ(n)}` (#389)

Deploying `SidonDoubledBound.abs_resultant_doubled_sq_le` (`|Res|² ≤ 12^{φ(n)}` for the doubled
four-term `2X^i − X^k − X^l`) through the parallelogram machinery: a doubled parallelogram
`2ω^i = ω^k + ω^l` mod `p` forces `p² ≤ 12^{φ(n)}`, i.e. `p ≤ 12^{n/4}`.  Together with the
all-distinct threshold `prime_sq_le_of_parallelogram` (`p² ≤ 8^{φ(n)}`), the worst genuine
coincidence is the doubled one, so `p > 12^{n/4}` forbids every genuine nontrivial coincidence —
the full improved Sidon threshold.  Issue #389.
-/

open Complex Finset Polynomial
namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The doubled-case no-parallelogram threshold** (`S = 6`).  A doubled parallelogram
`2ω^i = ω^k + ω^l` mod `p` (with distinct complex `ζ`-powers and ℂ-nonvanishing) forces
`p² ≤ 12^{φ(n)}` — i.e. `p ≤ 12^{n/4}`.  Contrapositive: `p > 12^{n/4}` forbids it. -/
theorem prime_sq_le_doubled {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 2 < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ m)) {i k l : ℕ}
    (hpara : ω ^ i + ω ^ i - ω ^ k - ω ^ l = 0)
    (hne : ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 ^ m) → ξ ^ i + ξ ^ i - ξ ^ k - ξ ^ l ≠ 0)
    (hdist : Function.Injective (![ζ ^ i, ζ ^ k, ζ ^ l] : Fin 3 → ℂ)) :
    p ^ 2 ≤ 12 ^ (2 ^ m).totient := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  set R := resultant (cyclotomic n ℤ) (fourTerm i i k l) with hR
  have hne0 : fourTerm i i k l ≠ 0 := by
    intro h0
    refine hne _ (Complex.isPrimitiveRoot_exp n hn0) ?_
    have he := eval_fourTerm_map (Int.castRingHom ℂ)
      (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) i i k l
    rw [h0] at he; simp only [Polynomial.map_zero, eval_zero] at he; exact he.symm
  have hfdeg : ((fourTerm i i k l).map (Int.castRingHom (ZMod p))).natDegree
      = (fourTerm i i k l).natDegree := fourTerm_natDegree_map hp i i k l hne0
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine resultant_map_eq_zero_of_primitiveRoot hω (fourTerm i i k l) hfdeg ?_
    rw [eval_fourTerm_map]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  have hR0 : R ≠ 0 := resultant_fourTerm_ne_zero' hn0 hne
  have hdvdN : p ∣ R.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hpdvd
  have hple : p ≤ R.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hR0) hdvdN
  have hsq : R.natAbs ^ 2 ≤ 12 ^ n.totient := abs_resultant_doubled_sq_le hm hζ hdist
  calc p ^ 2 ≤ R.natAbs ^ 2 := Nat.pow_le_pow_left hple 2
    _ ≤ 12 ^ n.totient := hsq

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prime_sq_le_doubled
