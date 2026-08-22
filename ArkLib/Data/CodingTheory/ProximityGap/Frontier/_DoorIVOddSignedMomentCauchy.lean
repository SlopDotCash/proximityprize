/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# Door-(iv) Lane-1: the ODD signed moment routes back to the energy face (#444)

`_DoorIVEvenMomentPhaseVacuity` proved the *even* unmodulated moment `Σ_b η_b^{2r}` collapses onto
the modulus (energy) moment `Σ_b ‖η_b‖^{2r}` for the negation-closed thin subgroup `μ_n` (each `η_b`
is REAL). `_DoorIVMixedConjugateMomentCollapse` then proved the WHOLE mixed-conjugate lattice
`Σ_c η_c^a · conj(η_c)^b` is split-independent at every total degree: an **even** total degree lands on
the energy moment `E_r`, while an **odd** total degree `D` lands on the real SIGNED moment

    A_D := Σ_b (η_b)^D   (real, sign-sensitive).

The signed moment `A_D` is the LAST named "different object" the collapse leaves standing: it is real
and sign-sensitive, unlike the even (modulus/energy) moments, so a priori it could carry the missing
door-(iv) arithmetic. This module forecloses it: `A_D` is CONTROLLED by the energy face via
Cauchy-Schwarz, so it is NOT an independent lever.

## Mechanism

For a real-valued period field `η : β → ℝ` (the real part of the negation-closed `η_b`, see the
companion `field_real_of_negation_closed`), the signed `D`-moment `A_D = Σ_b (η_b)^D` obeys the sharp
Cauchy-Schwarz / power-mean bound

    (Σ_b (η_b)^D)^2  ≤  card(s) · Σ_b ((η_b)^D)^2  =  card(s) · Σ_b (η_b)^{2D},

i.e. `|A_D|^2 ≤ card(s) · E`, where `E = Σ_b (η_b)^{2D}` is exactly the (refuted) even/energy moment of
order `2D`. So the real sign-sensitive signed moment is dominated by `√card` times the dead modulus
moment: any attempt to extract a square-root cancellation from `A_D` must already control `E`, the
energy object proven non-proving (door (i)/BGK). The odd endpoint of the mixed-conjugate ladder carries
no new door-(iv) content.

This is a STRUCTURAL constraint lemma (kernel-checked Cauchy-Schwarz), NOT a CORE / cancellation /
completion / anti-concentration / capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVOddSignedMomentCauchy

open Finset

/-- **Signed moment ≤ √card · energy (Cauchy-Schwarz).** For a finite real-valued period field
`η : β → ℝ` and any degree `D`, the square of the signed `D`-moment `Σ_b (η_b)^D` is bounded by
`card(s)` times the sum of squares of the `D`-th powers — which is exactly the even/energy moment
`Σ_b (η_b)^{2D}`. The real sign-sensitive object is dominated by the refuted modulus moment. -/
theorem sq_signedMoment_le_card_mul_energy
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) :
    (∑ b ∈ s, (η b) ^ D) ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ((η b) ^ D) ^ 2 := by
  -- `(Σ f)^2 ≤ card · Σ f^2` is `sq_sum_le_card_mul_sum_sq`.
  simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun b => (η b) ^ D)

/-- **Energy form.** The bound restated with the energy moment `Σ_b (η_b)^{2D}` on the right, making
explicit that the controlling object is the order-`2D` even/modulus moment. -/
theorem sq_signedMoment_le_card_mul_evenMoment
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) :
    (∑ b ∈ s, (η b) ^ D) ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D) := by
  have h := sq_signedMoment_le_card_mul_energy s η D
  have hrw : (∑ b ∈ s, ((η b) ^ D) ^ 2) = ∑ b ∈ s, (η b) ^ (2 * D) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [← pow_mul]
    ring_nf
  rwa [hrw] at h

/-- **|A_D| ≤ √(card · energy).** Absolute-value form: the magnitude of the signed `D`-moment is at most
the square root of `card(s)` times the energy moment of order `2D`. The signed odd moment cannot exceed
the `√card`-scaled energy face. -/
theorem abs_signedMoment_le_sqrt_card_mul_evenMoment
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) :
    |∑ b ∈ s, (η b) ^ D| ≤ Real.sqrt ((s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D)) := by
  have h := sq_signedMoment_le_card_mul_evenMoment s η D
  -- `|x| = √(x^2) ≤ √(bound)`.
  have hx : |∑ b ∈ s, (η b) ^ D| = Real.sqrt ((∑ b ∈ s, (η b) ^ D) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [hx]
  exact Real.sqrt_le_sqrt h

/-- **Consumer no-go (energy budget controls the signed moment).** If the energy moment is bounded by
a budget `E₀ ≥ 0` and `card(s) · E₀ < T²` for some `T ≥ 0`, then the signed `D`-moment cannot reach
`T` in magnitude. Thus the odd signed moment carries no cancellation independent of the energy face:
a prize-scale signed-moment certificate already forces a matching energy expenditure. -/
theorem not_abs_signedMoment_ge_of_energy_budget
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) {E₀ T : ℝ}
    (hE : ∑ b ∈ s, (η b) ^ (2 * D) ≤ E₀) (hT : 0 ≤ T)
    (hbudget : (s.card : ℝ) * E₀ < T ^ 2) :
    |∑ b ∈ s, (η b) ^ D| < T := by
  have hsq := sq_signedMoment_le_card_mul_evenMoment s η D
  -- chain: |A|^2 ≤ card·energy ≤ card·E₀ < T^2, so |A| < T.
  have hmono : (s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D) ≤ (s.card : ℝ) * E₀ := by
    apply mul_le_mul_of_nonneg_left hE
    exact Nat.cast_nonneg _
  have hlt : (∑ b ∈ s, (η b) ^ D) ^ 2 < T ^ 2 := lt_of_le_of_lt (le_trans hsq hmono) hbudget
  -- `x^2 < T^2` with `T ≥ 0` gives `|x| < T`.
  have habs : |∑ b ∈ s, (η b) ^ D| ^ 2 < T ^ 2 := by
    rwa [sq_abs]
  nlinarith [abs_nonneg (∑ b ∈ s, (η b) ^ D), hlt, habs, hT]

/-- **Energy floor forced by a signed-moment spike.** Contrapositive: if the signed `D`-moment reaches
magnitude `T`, then the energy moment is at least `T² / card(s)`. Even a single large odd signed moment
has already paid the energy cost; isolating it is not free arithmetic information. -/
theorem evenMoment_ge_of_abs_signedMoment_ge
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) {T : ℝ}
    (hcard : 0 < (s.card : ℝ)) (hTnonneg : 0 ≤ T)
    (hspike : T ≤ |∑ b ∈ s, (η b) ^ D|) :
    T ^ 2 / (s.card : ℝ) ≤ ∑ b ∈ s, (η b) ^ (2 * D) := by
  have hsq := sq_signedMoment_le_card_mul_evenMoment s η D
  -- `T^2 ≤ |A|^2 = A^2 ≤ card·energy`, divide by card.
  have hT2 : T ^ 2 ≤ (∑ b ∈ s, (η b) ^ D) ^ 2 := by
    nlinarith [hspike, hTnonneg, sq_abs (∑ b ∈ s, (η b) ^ D), abs_nonneg (∑ b ∈ s, (η b) ^ D)]
  have hchain : T ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D) := le_trans hT2 hsq
  rw [div_le_iff₀ hcard]
  linarith [hchain]

end ArkLib.ProximityGap.Frontier.DoorIVOddSignedMomentCauchy
