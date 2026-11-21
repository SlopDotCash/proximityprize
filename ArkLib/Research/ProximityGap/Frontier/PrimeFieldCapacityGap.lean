/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity
import ArkLib.Research.ProximityGap.MCAEndpointUpper

/-!
# Finite security budgets for prime-field Reed–Solomon domains

Every evaluation embedding bounds the length by the characteristic in a prime field.
Consequently the capacity theorem applies uniformly to prescribed evaluation domains.
Its explicit field-size condition gives a sufficient security test at fixed slack.
-/

namespace ProximityGap.PrimeFieldCapacityGap

open CoreDefinitions ReedSolomon

variable {p n k : ℕ} [Fact p.Prime]

/-- At a fixed positive gap from capacity, the DKT exceptional-set estimates apply to
every prime-field evaluation embedding for all message dimensions up to its length. -/
theorem prime_capacity_bounds [SampleableType (ZMod p)] {gap : ℝ} (hg : 0 < gap)
    (hn : capacityLineLength gap ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (dom : Fin n ↪ ZMod p) :
    let E := capacityLineConstant gap * (n : ℝ) ^ (capacityLineDerivativeOrder gap + 1)
    mcaError (AffineLineGenerator (ZMod p)) (code dom k) (capacityRadius gap n k)
        ≤ ENNReal.ofReal (E / p) ∧
      ∀ s : ℕ, mcaError (AffineSpaceGenerator (ZMod p) s) (code dom k) (capacityRadius gap n k)
        ≤ ENNReal.ofReal (E / ((p : ℝ) - 1)) := by
  have hnp : n ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hchar : k - 1 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; omega
  simpa using (capacity_lineAgreement hg).mcaError_le hn hk (Or.inr hchar) dom

/-- A sufficient 128-bit line-MCA test, including every radius below the given
capacity radius. The field-size hypothesis can be checked before choosing the domain. -/
theorem prime_line_security128 [SampleableType (ZMod p)] {gap r : ℝ} (hg : 0 < gap)
    (hn : capacityLineLength gap ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hr : r ≤ capacityRadius gap n k)
    (hsize : (2 : ℝ)^128 *
      (capacityLineConstant gap * (n : ℝ) ^ (capacityLineDerivativeOrder gap + 1)) ≤ p)
    (dom : Fin n ↪ ZMod p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom k) r ≤ ENNReal.ofReal (1 / (2 : ℝ)^128) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (mcaError_mono _ _ hr).trans ((prime_capacity_bounds hg hn hk hkn dom).1.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hp (by positivity : (0 : ℝ) < 2^128)).mpr
  simpa [mul_comm] using hsize

/-- A line-MCA bound at every positive block length. The short-length term counts
subsets on which a scalar can be pinned, and the long-length term uses DKT. -/
theorem prime_capacity_all_lengths [SampleableType (ZMod p)] {gap : ℝ} (hg : 0 < gap)
    (hk : 0 < k) (hkn : k ≤ n) (dom : Fin n ↪ ZMod p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom k) (capacityRadius gap n k) ≤
      ENNReal.ofReal ((if capacityLineLength gap ≤ n then
        capacityLineConstant gap * (n : ℝ) ^ (capacityLineDerivativeOrder gap + 1)
        else (2 : ℝ)^n) / p) := by
  split_ifs with hn
  · exact (prime_capacity_bounds hg hn hk hkn dom).1
  · haveI : NeZero n := ⟨by omega⟩
    have hr : capacityRadius gap n k ≤ (1 : ℝ) := by
      unfold capacityRadius
      have hd : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
      linarith
    have h := epsMCA_le_two_pow_card_div (code dom k) (1 : NNReal)
    rw [epsMCA_eq_mcaError] at h
    refine (mcaError_mono _ _ hr).trans ?_
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos),
      ENNReal.ofReal_pow (by norm_num)]
    simpa using h

end ProximityGap.PrimeFieldCapacityGap

#print axioms ProximityGap.PrimeFieldCapacityGap.prime_capacity_bounds
#print axioms ProximityGap.PrimeFieldCapacityGap.prime_line_security128

#print axioms ProximityGap.PrimeFieldCapacityGap.prime_capacity_all_lengths
