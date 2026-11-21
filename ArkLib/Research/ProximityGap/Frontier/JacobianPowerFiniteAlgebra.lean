/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.MonicRawPolynomialQuotient
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Data.Nat.Choose.Sum

/-! # The finite algebra cut out by Jacobian powers

The auxiliary-column codimension is controlled by one more linear polar in the
same finite algebra. Its dimension is the sum of dimensions of explicitly
specified local Artinian quotients.
-/

set_option autoImplicit false
noncomputable section

open Finset Module
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.JacobianPowerFiniteAlgebra

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S] [FiniteDimensional K S]

/-- Ideal cut out by all the degree-a products of the two Jacobian columns. -/
def mixedIdeal (u v : S) (a : ℕ) : Ideal S :=
  Ideal.span (Set.range fun j : Fin (a+1) => u^j.val * v^(a-j.val))

/-- The algebra encoding the raw multiplier quotient. -/
abbrev PowerQuotient (u v : S) (a : ℕ) := S ⧸ mixedIdeal u v a

/-- Add one polar to the raw algebra. Its dimension records only intersection
points supported on the mixed Jacobian ideal. -/
abbrev FirstPolar (c u v : S) (a : ℕ) :=
  PowerQuotient u v a ⧸ Ideal.span {Ideal.Quotient.mk (mixedIdeal u v a) (u + c*v)}

/-- The class of the polar has the expected nilpotence order. -/
theorem polar_power_zero (c u v : S) (a : ℕ) :
    (Ideal.Quotient.mk (mixedIdeal u v a) (u + c*v))^a = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, add_pow]
  apply Ideal.sum_mem
  intro j hj
  have hgen : u^j * v^(a-j) ∈ mixedIdeal u v a :=
    Ideal.subset_span ⟨⟨j, by simpa using hj⟩, rfl⟩
  convert (mixedIdeal u v a).mul_mem_left (c^(a-j) * (a.choose j : S)) hgen using 1
  rw [mul_pow]
  ring

/-- The complete quotient by the raw columns has dimension at most a times
the dimension of the first-polar quotient. -/
theorem power_quotient_finrank (c u v : S) (a : ℕ) :
    finrank K (PowerQuotient u v a) ≤ a * finrank K (FirstPolar c u v a) := by
  let Q := PowerQuotient u v a
  let r : Q := Ideal.Quotient.mk (mixedIdeal u v a) (u + c*v)
  let I : Ideal Q := Ideal.span {r}
  have hz : I^a = ⊥ := by
    rw [show I = Ideal.span {r} from rfl, Ideal.span_singleton_pow]
    rw [show r^a = 0 from polar_power_zero c u v a]
    simp
  have h := MonicRawPolynomialQuotient.local_power_colength (K := K) I r
    (Ideal.mem_span_singleton_self r) a
  rw [hz] at h
  have he := (AlgEquiv.quotientBot K Q).toLinearEquiv.finrank_eq
  rw [he] at h
  exact h

/-- The first-polar dimension is a sum of the dimensions of local quotients at
its maximal ideals. The exponent can be any nilpotence bound for the nilradical. -/
theorem finrank_eq_sum_local {R : Type*} [CommRing R] [Algebra K R] [FiniteDimensional K R]
    [IsArtinianRing R] (N : ℕ) (hn : nilradical R ^ N = ⊥) :
    letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    finrank K R = ∑ m : MaximalSpectrum R, finrank K (R ⧸ m.asIdeal^N) := by
  classical
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let e := (AlgEquiv.quotientBot R R).symm |>.trans
    ((Ideal.quotientEquivAlgOfEq R hn.symm).trans (IsArtinianRing.quotNilradicalPowEquivPi R N))
  have he := (e.restrictScalars K).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_pi_fintype] using he

/-- Direct colength bound using the local factors of the actual first
polar quotient, with a common nilpotence exponent. -/
theorem power_quotient_local_sum (c u v : S) (a : ℕ)
    [IsArtinianRing (FirstPolar c u v a)] :
    let R := FirstPolar c u v a
    letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    ∃ N : ℕ, finrank K (PowerQuotient u v a) ≤
      a * ∑ m : MaximalSpectrum R, finrank K (R ⧸ m.asIdeal^N) := by
  classical
  let R := FirstPolar c u v a
  obtain ⟨N, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  refine ⟨N, ?_⟩
  exact (power_quotient_finrank (K := K) c u v a).trans_eq
    (congrArg (a * ·) (finrank_eq_sum_local (K := K) N hn))

#print axioms polar_power_zero
#print axioms power_quotient_finrank
#print axioms finrank_eq_sum_local
#print axioms power_quotient_local_sum

end ArkLib.ProximityGap.Frontier.JacobianPowerFiniteAlgebra
