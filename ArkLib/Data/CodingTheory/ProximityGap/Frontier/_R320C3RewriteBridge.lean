
/-! R320: algebraic bridge for the c=3 relation web. -/
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R320C3RewriteBridge

variable {F : Type*} [Semiring F]

theorem three_mul_pow_eq_pow_add
    (g : F) (h t : ℕ) (hthree : g ^ h = (3 : F)) :
    (3 : F) * g ^ t = g ^ (h + t) := by
  rw [← hthree, ← pow_add]

theorem pow_mul_three_eq_pow_add
    (g : F) (h t : ℕ) (hthree : g ^ h = (3 : F)) :
    g ^ t * (3 : F) = g ^ (t + h) := by
  rw [← hthree, ← pow_add]

theorem rewrite_orientations_eq
    (g : F) (h t : ℕ) (hthree : g ^ h = (3 : F)) :
    g ^ (h + t) = g ^ (t + h) := by
  rw [Nat.add_comm]

/-- A translated point may be replaced inside any three-term additive relation. -/
theorem triple_translate_rewrite
    (g : F) (h t u v : ℕ) (hthree : g ^ h = (3 : F)) :
    g ^ (h + t) + g ^ u + g ^ v =
      (3 : F) * g ^ t + g ^ u + g ^ v := by
  rw [three_mul_pow_eq_pow_add g h t hthree]

/-- The reverse normalization, useful when a collision is presented with a scalar `3`. -/
theorem triple_scalar_rewrite
    (g : F) (h t u v : ℕ) (hthree : g ^ h = (3 : F)) :
    (3 : F) * g ^ t + g ^ u + g ^ v =
      g ^ (h + t) + g ^ u + g ^ v := by
  rw [three_mul_pow_eq_pow_add g h t hthree]

end ArkLib.ProximityGap.Frontier.R320C3RewriteBridge

#print axioms ArkLib.ProximityGap.Frontier.R320C3RewriteBridge.three_mul_pow_eq_pow_add
#print axioms ArkLib.ProximityGap.Frontier.R320C3RewriteBridge.pow_mul_three_eq_pow_add
#print axioms ArkLib.ProximityGap.Frontier.R320C3RewriteBridge.rewrite_orientations_eq
