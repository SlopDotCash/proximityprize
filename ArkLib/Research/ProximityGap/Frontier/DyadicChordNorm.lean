/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFrobeniusNorm

/-! # Cyclotomic norms of chords on dyadic roots

The norm of a nonzero chord from one is two raised to the gcd of the
exponent and the dyadic order. This turns identities of products of
chords into precise additive conditions on their exponents.
-/
namespace ProximityGap.DyadicChordNorm
open Polynomial Algebra
variable {L : Type*} [Field L] [Algebra ℚ L] {m : ℕ}
  [IsCyclotomicExtension {2^(m+1)} ℚ L] {z : L}

/-- The rational norm of a chord to one for any integer exponent
represented by a natural number. -/
theorem chord (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) {e : ℕ}
    (nonzero : ¬2^(m+1) ∣ e) :
    Algebra.norm ℚ (z^e-1)=(2:ℚ)^(e.gcd (2^(m+1))) := by
  have e₀ : e≠0 := fun zero => nonzero (by rw [zero]; exact dvd_zero _)
  obtain ⟨s,t,odd,rfl⟩ := Nat.exists_eq_two_pow_mul_odd e₀
  have hs : s≤m := by
    by_contra! large
    exact nonzero ((pow_dvd_pow 2 large).trans (dvd_mul_right _ _))
  have prime : IsPrimitiveRoot (z^t) (2^(m+1)) := hz.pow_of_coprime t (odd.coprime_two_right.pow_right _)
  have gcd : (2^s*t).gcd (2^(m+1))=2^s := by
    have split : 2^(m+1)=2^s*2^(m+1-s) := by
      rw [← pow_add]; congr 1; omega
    rw [split,Nat.gcd_mul_left,(odd.coprime_two_right.pow_right _).gcd_eq_one,mul_one]
  rw [gcd,Nat.mul_comm,pow_mul]
  exact prime.norm_pow_sub_one_eq_prime_pow_of_ne_zero
    (cyclotomic.irreducible_rat (by positivity)) hs (by omega)

/-- A primitive dyadic root in order at least four has rational norm one. -/
theorem norm_root (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) :
    Algebra.norm ℚ z=1 := by
  apply hz.norm_eq_one _ (cyclotomic.irreducible_rat (by positivity))
  exact ne_of_gt (lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Chord norm for two exponents in increasing order. -/
theorem between (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i j : ℕ)
    (nonzero : ¬ 2^(m+1) ∣ j) :
    Algebra.norm ℚ (z^(i+j)-z^i)=(2:ℚ)^(j.gcd (2^(m+1))) := by
  rw [show z^(i+j)-z^i=z^i*(z^j-1) by rw [pow_add]; ring,
    map_mul,map_pow,norm_root hm hz,one_pow,one_mul,chord hm hz nonzero]

/-- Equal products of nonzero chords force equal sums of gcds. -/
theorem products {ι κ : Type*} [Fintype ι] [Fintype κ] (hm : 0<m)
    (hz : IsPrimitiveRoot z (2^(m+1))) (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, ¬2^(m+1) ∣ a i) (hb : ∀ j, ¬2^(m+1) ∣ b j)
    (same : ∏ i, (z^a i-1) = ∏ j, (z^b j-1)) :
    ∑ i, (a i).gcd (2^(m+1)) = ∑ j, (b j).gcd (2^(m+1)) := by
  have h := congrArg (Algebra.norm ℚ) same
  simp only [map_prod,fun i => chord hm hz (ha i),fun j => chord hm hz (hb j),
    Finset.prod_pow_eq_pow_sum] at h
  exact (pow_right_injective₀ (by norm_num : (0:ℚ)<2) (by norm_num : (2:ℚ)≠1)) h

end ProximityGap.DyadicChordNorm
#print axioms ProximityGap.DyadicChordNorm.chord
#print axioms ProximityGap.DyadicChordNorm.products
