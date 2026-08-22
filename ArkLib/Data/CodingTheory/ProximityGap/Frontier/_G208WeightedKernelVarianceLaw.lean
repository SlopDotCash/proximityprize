/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G208: exact variance law for a collision-free weighted kernel (#466)

For

`W_G(t) = #{(y,z) ∈ G² : 2y - z = t}`,

write `u = z/y`.  On nonzero multiplicative `G`-orbits the profile of `W_G` is the fiber
multiplicity of `u ↦ (2-u)^n`.  G206 and G207 show that injectivity of this map controls neither
the sign nor the normalized magnitude of the late-Newton alignments.  This file explains why
injectivity also gives no asymptotic spectral flattening on the kernel side.

Let `m = (q-1)/n` be the number of nonzero multiplicative `G`-classes and let `w` be the class
profile.  Collision-freeness means that every `w_i` is zero or one and `Σw_i=n`.  Therefore

`m Σ_i w_i² - (Σ_i w_i)² = n(m-n)`.

By Fourier Parseval on the quotient this is exactly the total nonprincipal quotient-character
energy.  In particular it grows linearly with the quotient index `m`; its average per nonprincipal
character tends to `n`, rather than to zero.  No large-prime threshold can turn collision-free
support into a Fourier-small profile.

The field-level integer variance used in G207 is consequently forced as well.  When the zero class
is absent (the nondegenerate `2 ∉ G` case), its exact expansion is

`Q_W = q² n Σ_i w_i² - q n⁴ = q n² (q-n²)`.

This reproduces G207's recorded values `Q_W=354368` at `(q,n)=(113,8)` and `11063360` at
`(449,8)`, now as instances of a general identity rather than isolated cells.

This is a structural no-go, not a prize closure.  It removes only the proposed kernel-side
large-prime flattening mechanism.  The signed joint placement of this phase-bearing profile against
`R_5,R_6` remains the open BGK covariance.  FS15-FS18 are fully respected: almost-all-prime
resultant control is fixed-depth and cannot select the production prime at logarithmic depth; the
present exact identity supplies no exceptional-prime exclusion.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G208

open Finset

/-- A quotient-class profile is collision-free when all weights are `0/1` and its total mass is
`n`.  Integer-valued weights keep the centered identities subtraction-safe. -/
def CollisionFreeClassProfile {m : ℕ} (w : Fin m → ℤ) (n : ℕ) : Prop :=
  (∀ i, w i = 0 ∨ w i = 1) ∧ ∑ i, w i = (n : ℤ)

/-- The numerator of the centered square mass of a profile on `m` classes.  Under quotient Fourier
Parseval this is the total nonprincipal character energy. -/
def centeredClassMass {m : ℕ} (w : Fin m → ℤ) : ℤ :=
  (m : ℤ) * ∑ i, (w i) ^ 2 - (∑ i, w i) ^ 2

/-- A collision-free `0/1` profile has `Σw²=Σw=n`. -/
theorem sum_sq_eq_mass {m n : ℕ} {w : Fin m → ℤ}
    (h : CollisionFreeClassProfile w n) :
    ∑ i, (w i) ^ 2 = (n : ℤ) := by
  calc
    ∑ i, (w i) ^ 2 = ∑ i, w i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases h.1 i with hi | hi <;> simp [hi]
    _ = (n : ℤ) := h.2

/-- A collision-free profile of mass `n` needs at least `n` quotient classes.  Thus weighted
kernel injectivity is possible only once the quotient itself is at least as large as the
subgroup. -/
theorem mass_le_classes {m n : ℕ} {w : Fin m → ℤ}
    (h : CollisionFreeClassProfile w n) : n ≤ m := by
  have hsum : ∑ i, w i ≤ ∑ _i : Fin m, (1 : ℤ) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases h.1 i with hi | hi <;> omega
  rw [h.2] at hsum
  simpa using hsum

/-- In a prime-field application with quotient index `m=(q-1)/n`, collision-freeness forces the
sharp threshold `n²+1 ≤ q`. -/
theorem field_size_ge_sq_add_one {m n q : ℕ} {w : Fin m → ℤ}
    (h : CollisionFreeClassProfile w n) (hq : q = n * m + 1) : n ^ 2 + 1 ≤ q := by
  have hnm := mass_le_classes h
  rw [hq]
  nlinarith

/-- **Exact collision-free quotient variance.**  The nonprincipal quotient energy is
`n(m-n)`, so it is not suppressed by support injectivity. -/
theorem centeredClassMass_eq {m n : ℕ} {w : Fin m → ℤ}
    (h : CollisionFreeClassProfile w n) :
    centeredClassMass w = (n : ℤ) * ((m : ℤ) - (n : ℤ)) := by
  rw [centeredClassMass, sum_sq_eq_mass h, h.2]
  ring

/-- The exact profile energy grows by `n*d` when the quotient index grows by `d`.  This is the
threshold-robust obstruction: collision-free support does not become spectrally flatter at larger
primes. -/
theorem collisionFree_energy_growth (m n d : ℕ) :
    (n : ℤ) * (((m + d : ℕ) : ℤ) - (n : ℤ)) =
      (n : ℤ) * ((m : ℤ) - (n : ℤ)) + (n : ℤ) * (d : ℤ) := by
  push_cast
  ring

/-- The field-scaled variance numerator used by G207, expressed from the quotient class profile. -/
def fieldScaledVariance (q n sumSq : ℤ) : ℤ :=
  q ^ 2 * n * sumSq - q * n ^ 4

/-- **Exact field-level variance law.**  Collision-freeness forces
`Q_W = q n²(q-n²)`. -/
theorem fieldScaledVariance_eq {m n : ℕ} {w : Fin m → ℤ}
    (h : CollisionFreeClassProfile w n) (q : ℤ) :
    fieldScaledVariance q n (∑ i, (w i) ^ 2) = q * (n : ℤ) ^ 2 * (q - (n : ℤ) ^ 2) := by
  rw [fieldScaledVariance, sum_sq_eq_mass h]
  ring

/-- G207's injective `(q,n)=(113,8)` variance is an instance of the general law. -/
theorem q113_n8_variance :
    (113 : ℤ) * (8 : ℤ) ^ 2 * (113 - (8 : ℤ) ^ 2) = 354368 := by
  norm_num

/-- G207's injective `(q,n)=(449,8)` variance is an instance of the general law. -/
theorem q449_n8_variance :
    (449 : ℤ) * (8 : ℤ) ^ 2 * (449 - (8 : ℤ) ^ 2) = 11063360 := by
  norm_num

#print axioms sum_sq_eq_mass
#print axioms mass_le_classes
#print axioms field_size_ge_sq_add_one
#print axioms centeredClassMass_eq
#print axioms collisionFree_energy_growth
#print axioms fieldScaledVariance_eq
#print axioms q113_n8_variance
#print axioms q449_n8_variance

end ArkLib.ProximityGap.Frontier.G208
