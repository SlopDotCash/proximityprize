/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Research.ProximityGap.Frontier._DoorIVMixedConjugateMomentCollapse
import ArkLib.Research.ProximityGap.Frontier._DoorIVOddSignedMomentCauchy

/-!
# Door-(iv) Lane-1 CAPSTONE: even split-collapse and odd Cauchy bound for real moments (#444)

This module CONSOLIDATES the three proven Lane-1 facts about conjugate splits into a single citable
statement (even-degree split-collapse plus an odd-degree magnitude inequality; see the scope note
below). For the negation-closed thin subgroup `μ_n`, every
`η_b` is REAL, and the campaign proved:

* `_DoorIVEvenMomentPhaseVacuity` / `_DoorIVMixedConjugateMomentCollapse`: every mixed-conjugate
  correlator `Σ_c η_c^a · conj(η_c)^b` of fixed total degree `a+b` is split-INDEPENDENT, and an EVEN
  total degree `2r` collapses EXACTLY onto the modulus (energy) moment `E_r = Σ_c ‖η_c‖^{2r}` (the
  refuted door-(i)/BGK object).
* `_DoorIVOddSignedMomentCauchy`: an ODD total degree `D` collapses onto the real SIGNED moment
  `A_D = Σ_c (η_c)^D`, whose magnitude is Cauchy-dominated by the energy face,
  `|A_D|² ≤ card · Σ_c (η_c)^{2D}`.

So on the real axis the conjugate split never matters: every correlator `Σ η^a · conj(η)^b`
equals the signed moment `Σ η^{a+b}`; at EVEN total degree this is exactly the modulus/energy
moment, and at ODD total degree its *magnitude* is bounded above by an even/energy moment.

Scope (audit correction R-101): this is a one-sided magnitude bound, not an equivalence or a
recovery theorem, and it does NOT say that odd signed moments carry no information. A nonzero
real value has phase `0` **or** `π`, and that sign survives in odd moments: the real vectors
`(1, 1)` and `(1, −1)` have identical moduli and identical even power sums, but every odd power
sum is `2` versus `0`. An earlier version of this header claimed "no phase-carrying correlator
anywhere in the moment hierarchy" and "phase identically zero on the real axis"; both are false
and are withdrawn. Excluding the use of the signed odd correlators of the actual periods would need
a separate theorem about the actual fixed-period constraints, which is not proved here.

This is a STRUCTURAL consolidation capstone (composition of proven facts), NOT a CORE / cancellation /
completion / anti-concentration / capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVMomentHierarchyEnergyDominated

open Finset
open scoped ComplexConjugate

/-- **Even-total correlator = energy moment (capstone form).** For a finite real-valued field, any
mixed-conjugate correlator of EVEN total degree `2r` equals the modulus/energy moment of that order,
regardless of the conjugate split `(a, b)` with `a + b = 2r`. -/
theorem evenTotal_mixedCorrelator_eq_energy
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a b r : ℕ) (hab : a + b = 2 * r) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b
      = ∑ c ∈ s, ((‖η c‖ : ℝ) : ℂ) ^ (2 * r) :=
  DoorIVMixedConjugateMomentCollapse.mixedMoment_eq_modulusMoment s η hreal a b r hab

/-- **Odd-total correlator collapses to the real signed moment.** For a finite real-valued field, any
mixed-conjugate correlator of total degree `D` (any parity) equals the unmodulated signed moment
`Σ_c (η_c)^D`: the conjugate split is irrelevant on the real axis. -/
theorem mixedCorrelator_eq_signedMoment
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a b : ℕ) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b = ∑ c ∈ s, (η c) ^ (a + b) := by
  apply Finset.sum_congr rfl
  intro c hc
  exact DoorIVMixedConjugateMomentCollapse.mixed_pow_eq_total_pow (η c) (hreal c hc) a b

/-- **CAPSTONE: the entire mixed-conjugate moment hierarchy is energy-dominated at BOTH parities.**
For a finite real-valued field `η : β → ℝ` (the real period field of the negation-closed `μ_n`):

* EVEN total degree `2r`: the real mixed-conjugate correlator equals the modulus/energy moment
  `Σ_c (η_c)^{2r}` exactly, for every split `(a, b)` with `a + b = 2r`;
* ODD (or any) total degree `D`: the real signed correlator `Σ_c (η_c)^D` has its square bounded by
  `card · Σ_c (η_c)^{2D}` (Cauchy-Schwarz energy domination).

Hence even-degree correlators collapse onto energy moments, and odd-degree signed correlators are
*bounded in magnitude* by an even moment. The odd signed moments themselves still carry sign
information that the even moments do not determine (e.g. `(1, 1)` vs `(1, −1)`), so this is not a
statement that the hierarchy is phase-free or that signed odd correlators are useless. Constraint
capstone — NO CORE / cancellation / completion / anti-concentration / capacity claim. CORE remains
OPEN. -/
theorem momentHierarchy_energy_dominated
    {β : Type*} (s : Finset β) (η : β → ℝ) :
    (∀ a b r : ℕ, a + b = 2 * r →
        ∑ c ∈ s, (η c) ^ a * (η c) ^ b = ∑ c ∈ s, (η c) ^ (2 * r))
      ∧ (∀ D : ℕ,
        (∑ c ∈ s, (η c) ^ D) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, (η c) ^ (2 * D)) := by
  refine ⟨?_, ?_⟩
  · intro a b r hab
    apply Finset.sum_congr rfl
    intro c _
    rw [← pow_add, hab]
  · intro D
    exact DoorIVOddSignedMomentCauchy.sq_signedMoment_le_card_mul_evenMoment s η D

end ArkLib.ProximityGap.Frontier.DoorIVMomentHierarchyEnergyDominated
