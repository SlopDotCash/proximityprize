/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # Four collinear heads and one transverse head at five-eighths errors

The scalar count depends on ordered deficits. Bounding the cost of the first
one, two, three and four heads permits summation by parts. -/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.EighthOutlierArithmetic

/-- The largest reciprocal sum subject to the triangle and quartet deficit
inequalities occurs at `(1,1,3,6;1)`. -/
theorem reciprocals {a b c d z : ℕ} (pos : 1 ≤ a) (ord₁ : a ≤ b) (ord₂ : b ≤ c)
    (ord₃ : c ≤ d) (posZ : 1 ≤ z) (triple : 6 ≤ a + b + c + z)
    (quad : 12 ≤ a + b + c + d + z) :
    (5 : ℚ) / a + 4 / b + 3 / c + 2 / d + 5 / z ≤ 46 / 3 := by
  have coarse (A B C D Z : ℕ) (bounds : 1 ≤ A ∧ A ≤ a ∧ 1 ≤ B ∧ B ≤ b ∧
      1 ≤ C ∧ C ≤ c ∧ 1 ≤ D ∧ D ≤ d ∧ 1 ≤ Z ∧ Z ≤ z) :
      (5 : ℚ) / a + 4 / b + 3 / c + 2 / d + 5 / z ≤ 5 / A + 4 / B + 3 / C + 2 / D + 5 / Z := by
    obtain ⟨A0,Aa,B0,Bb,C0,Cc,D0,Dd,Z0,Zz⟩ := bounds
    gcongr
  by_cases h : 2 ≤ a
  · exact (coarse 2 2 2 2 1 (by omega)).trans (by norm_num)
  by_cases h : 2 ≤ b
  · exact (coarse 1 2 2 2 1 (by omega)).trans (by norm_num)
  by_cases h : 4 ≤ z
  · exact (coarse 1 1 1 1 4 (by omega)).trans (by norm_num)
  by_cases h : z = 3
  · by_cases hc : c = 1
    · exact (coarse 1 1 1 6 3 (by omega)).trans (by norm_num)
    · exact (coarse 1 1 2 2 3 (by omega)).trans (by norm_num)
  by_cases h : z = 2
  · exact (coarse 1 1 2 2 2 (by omega)).trans (by norm_num)
  by_cases h : 5 ≤ c
  · exact (coarse 1 1 5 5 1 (by omega)).trans (by norm_num)
  by_cases h : c = 4
  · exact (coarse 1 1 4 5 1 (by omega)).trans (by norm_num)
  exact (coarse 1 1 3 6 1 (by omega)).trans (by norm_num)

/-- A bounded deficit on each of the four prefixes bounds the entire scalar
assignment. The constants allow 1,024 missing sites per large core. -/
theorem count {a b c d z x₁ x₂ x₃ x₄ x₅ : ℕ}
    (pos : 1 ≤ a) (ord₁ : a ≤ b) (ord₂ : b ≤ c) (ord₃ : c ≤ d) (posZ : 1 ≤ z)
    (triple : 6 ≤ a + b + c + z) (quad : 12 ≤ a + b + c + d + z)
    (pref₁ : a*x₁ ≤ 5*134217728 + 16384)
    (pref₂ : a*x₁+b*x₂ ≤ 9*134217728 + 16384)
    (pref₃ : a*x₁+b*x₂+c*x₃ ≤ 12*134217728 + 16384)
    (pref₄ : a*x₁+b*x₂+c*x₃+d*x₄ ≤ 14*134217728 + 16384)
    (outer : z*x₅ ≤ 5*134217728 + z) :
    x₁ + x₂ + x₃ + x₄ + x₅ ≤ 2058021547 := by
  have recip := reciprocals pos ord₁ ord₂ ord₃ posZ triple quad
  have a0 : (0 : ℚ) < a := by exact_mod_cast (by omega : 0<a)
  have b0 : (0 : ℚ) < b := by exact_mod_cast (by omega : 0<b)
  have c0 : (0 : ℚ) < c := by exact_mod_cast (by omega : 0<c)
  have d0 : (0 : ℚ) < d := by exact_mod_cast (by omega : 0<d)
  have z0 : (0 : ℚ) < z := by exact_mod_cast (by omega : 0<z)
  have w1 : 0 ≤ (1:ℚ)/a-1/b := sub_nonneg.mpr (one_div_le_one_div_of_le a0 (by exact_mod_cast ord₁))
  have w2 : 0 ≤ (1:ℚ)/b-1/c := sub_nonneg.mpr (one_div_le_one_div_of_le b0 (by exact_mod_cast ord₂))
  have w3 : 0 ≤ (1:ℚ)/c-1/d := sub_nonneg.mpr (one_div_le_one_div_of_le c0 (by exact_mod_cast ord₃))
  have err : (1:ℚ)/a ≤ 1 := (div_le_iff₀ a0).mpr (by simpa using (show (1:ℚ)≤a by exact_mod_cast pos))
  have c1 : (a:ℚ)*x₁ ≤ 5*134217728 + 16384 := by exact_mod_cast pref₁
  have c2 : (a:ℚ)*x₁+b*x₂ ≤ 9*134217728 + 16384 := by exact_mod_cast pref₂
  have c3 : (a:ℚ)*x₁+b*x₂+c*x₃ ≤ 12*134217728 + 16384 := by exact_mod_cast pref₃
  have c4 : (a:ℚ)*x₁+b*x₂+c*x₃+d*x₄ ≤ 14*134217728 + 16384 := by exact_mod_cast pref₄
  have c5 : (z:ℚ)*x₅ ≤ 5*134217728 + z := by exact_mod_cast outer
  have B : (x₁:ℚ)+x₂+x₃+x₄+x₅ ≤ (46:ℚ)/3*134217728+16385 := by
    have lhs : (x₁:ℚ)+x₂+x₃+x₄+x₅ =
        (1/a-1/b)*(a*x₁) + (1/b-1/c)*(a*x₁+b*x₂) + (1/c-1/d)*(a*x₁+b*x₂+c*x₃) +
          (1/d)*(a*x₁+b*x₂+c*x₃+d*x₄) + (1/z)*(z*x₅) := by
      push_cast
      field_simp
      <;> ring
    rw [lhs]
    have hb := add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left c1 w1) (mul_le_mul_of_nonneg_left c2 w2))
      (mul_le_mul_of_nonneg_left c3 w3)) (mul_le_mul_of_nonneg_left c4 (by positivity : 0≤(1:ℚ)/d)))
      (mul_le_mul_of_nonneg_left c5 (by positivity : 0≤(1:ℚ)/z))
    apply hb.trans
    have eq : (1/(z:ℚ))*z=1 := by field_simp
    linear_combination (norm := ring_nf) 134217728 * recip + 16384 * err + eq
    norm_num
  have h := show (x₁:ℚ)+x₂+x₃+x₄+x₅ < 2058021548 from B.trans_lt (by norm_num)
  exact Nat.le_of_lt_succ (by exact_mod_cast h)

#print axioms count
end ArkLib.ProximityGap.Frontier.EighthOutlierArithmetic
