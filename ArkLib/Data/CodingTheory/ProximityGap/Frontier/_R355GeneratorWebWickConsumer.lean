/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R326DominantRecurrenceL1Contraction

/-!
# R355: a normalized generator-web census gives a Wick-scale collision bound

R324 retains cancellation depth but drops the factorial denominator in R322's endpoint
envelope.  This file keeps the denominator and shows exactly what a multi-generator recurrence
web must prove.  If the depth-`s` relation stratum obeys

```text
(r-s)! * #relations(s) <= 3^(r-s) * m^(r-s),
```

then binomial recombination gives

```text
r! * shadowCollisionMass <= 4^r * (2r)! * m^r.
```

Since `(2r-1)!! = (2r)!/(2^r r!)`, this is an `8^r`-times-Wick envelope.  This is a
shallow-rung consumer: beyond the DC crossover the raw collision mass contains the unavoidable
uniform `1/|F|` floor, so the normalized census is not expected to hold.  A deep-wall argument
must center that floor before applying an analogous recurrence-web decomposition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer

open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification

/-- The exact normalized relation-count target for a multi-generator recurrence web. -/
def GeneratorWebCensus
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) : Prop :=
  ∀ s ∈ Finset.range r,
    (r - s).factorial * (relationCancellationStratum g m r s).card ≤
      3 ^ (r - s) * m ^ (r - s)

/-- Factorial recombination without division.  The auxiliary cardinal `B` cancels rather
than being counted twice. -/
theorem factorial_recombine {r s A B X Y : ℕ} (hsr : s ≤ r)
    (hA : s.factorial * A ≤ B * X) (hB : (r - s).factorial * B ≤ Y) :
    r.factorial * A ≤ r.choose s * X * Y := by
  have hAX : (r - s).factorial * (s.factorial * A) ≤ Y * X := by
    calc
      (r - s).factorial * (s.factorial * A) ≤
          (r - s).factorial * (B * X) := Nat.mul_le_mul_left _ hA
      _ = ((r - s).factorial * B) * X := by ring
      _ ≤ Y * X := Nat.mul_le_mul_right _ hB
  calc
    r.factorial * A =
        r.choose s * ((r - s).factorial * (s.factorial * A)) := by
      rw [← Nat.choose_mul_factorial_mul_factorial hsr]
      ring
    _ ≤ r.choose s * (Y * X) := Nat.mul_le_mul_left _ hAX
    _ = r.choose s * X * Y := by ring

/-- R322's endpoint envelope with only the cancellation factorial retained. -/
theorem shadowRelationMass_mul_factorial_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ relationCancellationStratum g m r s) :
    s.factorial * shadowRelationMass g (2 * m) m r d ≤
      (r + r).factorial * m ^ s := by
  have hdrel : d ∈ shadowKernelRelations g (2 * m) m r :=
    (Finset.mem_filter.mp hd).1
  have hdepth := decomposition_of_mem_relationCancellationStratum g m r s hd
  have h := shadowRelationMass_factorial_envelope g m r s hdrel hdepth
  have hprod : 1 ≤ ∏ j : Fin m, (d j).natAbs.factorial := by
    apply Finset.one_le_prod
    intro j _
    exact Nat.factorial_pos (d j).natAbs
  calc
    s.factorial * shadowRelationMass g (2 * m) m r d ≤
        s.factorial * shadowRelationMass g (2 * m) m r d *
          (∏ j : Fin m, (d j).natAbs.factorial) := by
      simpa using Nat.mul_le_mul_left
        (s.factorial * shadowRelationMass g (2 * m) m r d) hprod
    _ ≤ (r + r).factorial * m ^ s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The mass of one stratum retains its `s!` denominator. -/
theorem factorial_mul_stratumMass_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) :
    s.factorial *
        (∑ d ∈ relationCancellationStratum g m r s,
          shadowRelationMass g (2 * m) m r d) ≤
      (relationCancellationStratum g m r s).card *
        ((r + r).factorial * m ^ s) := by
  rw [Finset.mul_sum]
  calc
    (∑ d ∈ relationCancellationStratum g m r s,
        s.factorial * shadowRelationMass g (2 * m) m r d) ≤
      ∑ _d ∈ relationCancellationStratum g m r s,
        ((r + r).factorial * m ^ s) := by
      apply Finset.sum_le_sum
      intro d hd
      exact shadowRelationMass_mul_factorial_le g m r s hd
    _ = (relationCancellationStratum g m r s).card *
        ((r + r).factorial * m ^ s) := by simp

/-- **Generator-web Wick consumer.** A normalized low-`L1` census of every cancellation
stratum implies an `8^r`-times-Wick collision envelope, with no single-generator assumption. -/
theorem factorial_mul_shadowCollisionMass_le_of_generatorWebCensus
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hweb : GeneratorWebCensus g m r) :
    r.factorial * shadowCollisionMass g (2 * m) m r ≤
      4 ^ r * (r + r).factorial * m ^ r := by
  rw [shadowCollisionMass_eq_sum_cancellation_strata, Finset.mul_sum]
  calc
    (∑ s ∈ Finset.range r, r.factorial *
        ∑ d ∈ relationCancellationStratum g m r s,
          shadowRelationMass g (2 * m) m r d) ≤
      ∑ s ∈ Finset.range r,
        r.choose s * ((r + r).factorial * m ^ s) *
          (3 ^ (r - s) * m ^ (r - s)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsr : s ≤ r := Nat.le_of_lt (Finset.mem_range.mp hs)
      exact factorial_recombine hsr
        (factorial_mul_stratumMass_le g m r s) (hweb s hs)
    _ = (r + r).factorial * m ^ r *
        ∑ s ∈ Finset.range r, r.choose s * 3 ^ (r - s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hsr : s ≤ r := Nat.le_of_lt (Finset.mem_range.mp hs)
      have hpow : m ^ s * m ^ (r - s) = m ^ r := by
        rw [← pow_add, Nat.add_sub_of_le hsr]
      rw [← hpow]
      ring
    _ ≤ (r + r).factorial * m ^ r * 4 ^ r := by
      apply Nat.mul_le_mul_left
      calc
        (∑ s ∈ Finset.range r, r.choose s * 3 ^ (r - s)) ≤
            ∑ s ∈ Finset.range (r + 1), r.choose s * 3 ^ (r - s) := by
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ r))
        _ = 4 ^ r := by
          calc
            (∑ s ∈ Finset.range (r + 1), r.choose s * 3 ^ (r - s)) =
                ∑ s ∈ Finset.range (r + 1),
                  1 ^ s * 3 ^ (r - s) * r.choose s := by
              apply Finset.sum_congr rfl
              intro s hs
              ring
            _ = 4 ^ r := by simpa using (add_pow (1 : ℕ) 3 r).symm
    _ = 4 ^ r * (r + r).factorial * m ^ r := by ring

end ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer.factorial_recombine
#print axioms
  ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer.shadowRelationMass_mul_factorial_le
#print axioms
  ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer.factorial_mul_shadowCollisionMass_le_of_generatorWebCensus
