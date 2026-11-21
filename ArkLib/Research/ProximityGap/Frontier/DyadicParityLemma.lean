import Mathlib.Analysis.Fourier.ZMod

/-!
# Three reflection centres force an antiperiodic function to vanish

Let `F` be a complex function on `ZMod N` with `F (y + h) = -F y`, and suppose the
symmetrised functions `i ↦ F (x + i) + F (x - i)` coincide for three distinct centres `x`.
If every frequency `k` is a unit or is annihilated by `h`, then `F = 0`.

For `N = 2 ^ (e + 1)` and `h = 2 ^ e` the frequency hypothesis always holds. This is the
Fourier step ("parity lemma") of the written argument in
`docs/research/proximity-gap/dyadic-radius-successor-list-three.md`. The cyclotomic-unit
input that produces the reflection equations from a polynomial pencil is not formalised here.
-/

open Finset ZMod

namespace ProximityGap.DyadicParity

variable {N : ℕ} [NeZero N]

/-- The transform of a translate. -/
lemma dft_shift (F : ZMod N → ℂ) (x k : ZMod N) :
    𝓕 (fun i ↦ F (x + i)) k = stdAddChar (x * k) * 𝓕 F k := by
  rw [dft_apply, dft_apply, mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun i ↦ ?_
  simp only [Equiv.coe_addLeft, smul_eq_mul]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  have h : x * k + -((x + i) * k) = -(i * k) := by ring
  rw [h]

/-- The transform of a reflected translate. -/
lemma dft_reflect (F : ZMod N → ℂ) (x k : ZMod N) :
    𝓕 (fun i ↦ F (x - i)) k = stdAddChar (-(x * k)) * 𝓕 F (-k) := by
  rw [dft_apply, dft_apply, mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun i ↦ ?_
  simp only [Equiv.subLeft_apply, smul_eq_mul]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  have h : -(x * k) + -((x - i) * -k) = -(i * k) := by ring
  rw [h]

/-- Three distinct reflection centres with a common symmetrisation force an antiperiodic
function to vanish, provided every frequency is a unit or is killed by the period. -/
theorem eq_zero_of_three_centers (h : ZMod N) (F c : ZMod N → ℂ)
    (hanti : ∀ y, F (y + h) = -F y)
    (hk : ∀ k : ZMod N, h * k = 0 ∨ IsUnit k)
    {x₁ x₂ x₃ : ZMod N} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (H₁ : ∀ i, F (x₁ + i) + F (x₁ - i) = c i)
    (H₂ : ∀ i, F (x₂ + i) + F (x₂ - i) = c i)
    (H₃ : ∀ i, F (x₃ + i) + F (x₃ - i) = c i) : F = 0 := by
  have hinj : Function.Injective (𝓕 : (ZMod N → ℂ) → (ZMod N → ℂ)) :=
    (dft (N := N) (E := ℂ)).injective
  apply hinj
  rw [map_zero]
  funext k
  rw [Pi.zero_apply]
  rcases hk k with hz | hu
  · have hs := dft_shift F h k
    have hfun : (fun i ↦ F (h + i)) = -F := by
      funext i
      rw [add_comm, hanti, Pi.neg_apply]
    rw [hfun, map_neg, Pi.neg_apply, hz, AddChar.map_zero_eq_one, one_mul] at hs
    have h2 : (2 : ℂ) * 𝓕 F k = 0 := by linear_combination -hs
    simpa using h2
  · have key : ∀ x : ZMod N, (∀ i, F (x + i) + F (x - i) = c i) →
        𝓕 F k * stdAddChar (x * k) ^ 2 + 𝓕 F (-k) = 𝓕 c k * stdAddChar (x * k) := by
      intro x H
      have hfun : (fun i ↦ F (x + i)) + (fun i ↦ F (x - i)) = c := by
        funext i
        exact H i
      have ht := congrArg (fun G ↦ 𝓕 G k) hfun
      simp only [map_add, Pi.add_apply] at ht
      rw [dft_shift, dft_reflect, AddChar.map_neg_eq_inv] at ht
      have hone : stdAddChar (x * k) * stdAddChar (-(x * k)) = (1 : ℂ) := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      have hne : stdAddChar (x * k) ≠ (0 : ℂ) := left_ne_zero_of_mul_eq_one hone
      rw [← ht]
      field_simp
    have hdist : ∀ x y : ZMod N, x ≠ y → stdAddChar (x * k) ≠ (stdAddChar (y * k) : ℂ) := by
      intro x y hxy he
      exact hxy (hu.mul_left_injective (injective_stdAddChar he))
    set A := 𝓕 F k
    set B := 𝓕 F (-k)
    set C := 𝓕 c k
    set u₁ : ℂ := stdAddChar (x₁ * k)
    set u₂ : ℂ := stdAddChar (x₂ * k)
    set u₃ : ℂ := stdAddChar (x₃ * k)
    have E₁ := key x₁ H₁
    have E₂ := key x₂ H₂
    have E₃ := key x₃ H₃
    have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr (hdist _ _ h12)
    have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr (hdist _ _ h13)
    have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr (hdist _ _ h23)
    have e12 : A * (u₁ + u₂) = C := by
      have : (u₁ - u₂) * (A * (u₁ + u₂) - C) = 0 := by linear_combination E₁ - E₂
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left d12)
    have e13 : A * (u₁ + u₃) = C := by
      have : (u₁ - u₃) * (A * (u₁ + u₃) - C) = 0 := by linear_combination E₁ - E₃
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left d13)
    have : (u₂ - u₃) * A = 0 := by linear_combination e12 - e13
    exact (mul_eq_zero.mp this).resolve_left d23

/-- On `ZMod (2 ^ (e + 1))` every frequency is a unit or is killed by `2 ^ e`. -/
lemma dyadic_frequency (e : ℕ) (k : ZMod (2 ^ (e + 1))) :
    ((2 : ZMod (2 ^ (e + 1))) ^ e) * k = 0 ∨ IsUnit k := by
  rcases Nat.even_or_odd k.val with hev | hodd
  · left
    obtain ⟨m, hm⟩ := hev
    have hkv : k = ((m + m : ℕ) : ZMod (2 ^ (e + 1))) := by
      rw [← hm, ZMod.natCast_zmod_val]
    have hz : ((2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 1))) = 0 := ZMod.natCast_self _
    rw [hkv]
    have : ((2 : ZMod (2 ^ (e + 1))) ^ e) * ((m + m : ℕ) : ZMod (2 ^ (e + 1)))
        = ((2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 1))) * (m : ZMod (2 ^ (e + 1))) := by
      push_cast
      ring
    rw [this, hz, zero_mul]
  · right
    have hcop : Nat.Coprime k.val (2 ^ (e + 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    have := (ZMod.isUnit_iff_coprime k.val (2 ^ (e + 1))).mpr hcop
    rwa [ZMod.natCast_zmod_val] at this

/-- The parity lemma on a dyadic cyclic group. -/
theorem dyadic_eq_zero_of_three_centers (e : ℕ) (F c : ZMod (2 ^ (e + 1)) → ℂ)
    (hanti : ∀ y, F (y + 2 ^ e) = -F y)
    {x₁ x₂ x₃ : ZMod (2 ^ (e + 1))} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (H₁ : ∀ i, F (x₁ + i) + F (x₁ - i) = c i)
    (H₂ : ∀ i, F (x₂ + i) + F (x₂ - i) = c i)
    (H₃ : ∀ i, F (x₃ + i) + F (x₃ - i) = c i) : F = 0 :=
  eq_zero_of_three_centers (2 ^ e) F c hanti (dyadic_frequency e) h12 h13 h23 H₁ H₂ H₃

end ProximityGap.DyadicParity

#print axioms ProximityGap.DyadicParity.eq_zero_of_three_centers
#print axioms ProximityGap.DyadicParity.dyadic_eq_zero_of_three_centers
