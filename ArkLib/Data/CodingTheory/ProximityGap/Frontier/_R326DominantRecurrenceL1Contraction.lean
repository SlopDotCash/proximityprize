/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R324KernelRelationLengthStratification

/-!
# LANE B2 (#466 round 326): dominant recurrence contracts `L1` preimages

R325 bounds short preimages of a dominant recurrence by a coordinate box.  In the prize
regime that loses exponentially in the ambient dimension `m`.  The useful geometry is instead
the dimension-free `L1` contraction

```text
(|a|-b) * ‖g‖₁ <= ‖v‖₁
```

whenever `v = a*g + residual` and the residual has total `L1` mass at most `b*‖g‖₁`.
For a dominant binomial, the residual is a signed coordinate permutation times `b`, so the
hypothesis is exact.  Combined with R322/R324, generator-count growth `m^k` is offset by the
endpoint weight `m^(r-k)` rather than becoming a box count of the form `K^m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope

/-- Integer `L1` mass of a vector. -/
def intL1 {m : ℕ} (v : Fin m → ℤ) : ℤ :=
  ∑ i : Fin m, |v i|

theorem intL1_nonneg {m : ℕ} (v : Fin m → ℤ) : 0 ≤ intL1 v := by
  unfold intL1
  positivity

/-- **Dominant-recurrence `L1` contraction.** -/
theorem dominant_l1_contraction
    {m : ℕ} (a b : ℤ) (g v : Fin m → ℤ)
    (hb : 0 ≤ b) (hab : b ≤ |a|)
    (hresidual : intL1 (fun i => v i - a * g i) ≤ b * intL1 g) :
    (|a| - b) * intL1 g ≤ intL1 v := by
  have hpoint : ∀ i : Fin m,
      |a| * |g i| ≤ |v i| + |v i - a * g i| := by
    intro i
    calc
      |a| * |g i| = |a * g i| := (abs_mul a (g i)).symm
      _ = |v i + (-(v i - a * g i))| := by ring_nf
      _ ≤ |v i| + |(-(v i - a * g i))| := abs_add_le _ _
      _ = |v i| + |v i - a * g i| := by rw [abs_neg]
  have hsum : |a| * intL1 g ≤ intL1 v + intL1 (fun i => v i - a * g i) := by
    unfold intL1
    rw [Finset.mul_sum]
    calc
      (∑ i : Fin m, |a| * |g i|)
          ≤ ∑ i : Fin m, (|v i| + |v i - a * g i|) :=
            Finset.sum_le_sum fun i _ => hpoint i
      _ = (∑ i : Fin m, |v i|) + ∑ i : Fin m, |v i - a * g i| :=
        Finset.sum_add_distrib
  have hg0 := intL1_nonneg g
  have hgap : 0 ≤ |a| - b := sub_nonneg.mpr hab
  nlinarith

/-- Binomial/permutation specialization: a residual `c_i*g(σ i)` with constant absolute
coefficient `b` preserves total `L1` mass when `σ` is a permutation. -/
theorem dominant_permutation_l1_contraction
    {m : ℕ} (a b : ℤ) (hb : 0 ≤ b) (hab : b ≤ |a|)
    (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ b)
    (σ : Equiv.Perm (Fin m)) (g v : Fin m → ℤ)
    (hv : ∀ i, v i - a * g i = c i * g (σ i)) :
    (|a| - b) * intL1 g ≤ intL1 v := by
  apply dominant_l1_contraction a b g v hb hab
  unfold intL1
  calc
    (∑ i : Fin m, |v i - a * g i|)
        = ∑ i : Fin m, |c i * g (σ i)| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hv i]
    _ ≤ ∑ i : Fin m, b * |g (σ i)| := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    _ = b * ∑ i : Fin m, |g (σ i)| := by rw [Finset.mul_sum]
    _ = b * ∑ i : Fin m, |g i| := by
          congr 1
          exact Fintype.sum_equiv σ _ _ fun i => rfl

/-- Natural-valued `L1` mass. -/
def natL1 {m : ℕ} (v : Fin m → ℤ) : ℕ :=
  ∑ i : Fin m, (v i).natAbs

theorem intL1_eq_natL1_cast {m : ℕ} (v : Fin m → ℤ) :
    intL1 v = (natL1 v : ℤ) := by
  unfold intL1 natL1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (Int.natCast_natAbs (v i)).symm

/-- **Exponent cancellation.** If endpoint length contracts generator length by a factor
at least two, then cancellation depth plus generator `L1` mass is at most the walk depth. -/
theorem cancellationDepth_add_natL1_le
    {m r s : ℕ} {d g : Fin m → ℤ}
    (hdepth : r + r = 2 * s + endpointL1 d)
    (hcontract : 2 * natL1 g ≤ endpointL1 d) :
    s + natL1 g ≤ r := by
  omega

/-- The corresponding powers of the ambient dimension cancel at `m^r`. -/
theorem pow_cancellation
    (m r s k : ℕ) (hm : 0 < m) (hsk : s + k ≤ r) :
    m ^ s * m ^ k ≤ m ^ r := by
  rw [← pow_add]
  exact pow_le_pow_right' (Nat.succ_le_iff.mpr hm) hsk

end ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction.dominant_l1_contraction
#print axioms
  ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction.dominant_permutation_l1_contraction
#print axioms
  ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction.cancellationDepth_add_natL1_le
#print axioms
  ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction.pow_cancellation
