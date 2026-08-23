/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungTopCancel

/-!
# The pool triple relation (#371, rung): the algebraic core of pool ≤ 2

Three pairwise-distinct bad scalars of a polynomial-pair stack satisfy an
EXACT three-term relation among their witness data: eliminating `R₁` between
the pairwise subtractions of the defect identities,

  `(γ₂−γ₃)·g₁m_{S₁} + (γ₃−γ₁)·g₂m_{S₂} + (γ₁−γ₂)·g₃m_{S₃}
     + (γ₂−γ₃)·P₁ + (γ₃−γ₁)·P₂ + (γ₁−γ₂)·P₃ = 0`

with all three elimination coefficients NONZERO and summing to zero.
Consequences wired here:
* `pool_triple_relation` — the law itself (the residue-cone obstruction that
  the pool-extension probes saw as `7 conditions vs 4 parameters`);
* `pool_triple_inter_roots` — on the triple witness intersection the three
  `v`-terms die, so every shared point is a root of the degree-`<k`
  codeword combination `W = (γ₂−γ₃)P₁ + (γ₃−γ₁)P₂ + (γ₁−γ₂)P₃`;
* `pool_triple_inter_card_le` — hence `|S₁∩S₂∩S₃| ≤ k−1` whenever `W ≠ 0`.

Probe record: `probe_wb371_pool_extend.py` — all constructed pool stacks have
fiber exactly the built-in pair (sizes {2: 20}); this relation is the formal
mechanism behind that cap.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section TripleRelation

variable {dom : Fin n ↪ F} {k : ℕ} {R₀ R₁ : F[X]}

/-- **The pool triple relation**: three bad scalars' witness data satisfy an
exact zero-sum three-term combination, with elimination coefficients
`(γ₂−γ₃, γ₃−γ₁, γ₁−γ₂)` — nonzero when the scalars are pairwise distinct,
always summing to zero.  `R₀` and `R₁` are both eliminated. -/
theorem pool_triple_relation
    {γ₁ γ₂ γ₃ : F} {P₁ P₂ P₃ g₁ g₂ g₃ : F[X]} {S₁ S₂ S₃ : Finset (Fin n)}
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂)
    (hid₃ : R₀ + C γ₃ * R₁ - P₃ = g₃ * vanishingPoly dom S₃) :
    C (γ₂ - γ₃) * (g₁ * vanishingPoly dom S₁)
      + C (γ₃ - γ₁) * (g₂ * vanishingPoly dom S₂)
      + C (γ₁ - γ₂) * (g₃ * vanishingPoly dom S₃)
      + (C (γ₂ - γ₃) * P₁ + C (γ₃ - γ₁) * P₂ + C (γ₁ - γ₂) * P₃) = 0 := by
  simp only [C_sub]
  linear_combination (C γ₃ - C γ₂) * hid₁ + (C γ₁ - C γ₃) * hid₂
    + (C γ₂ - C γ₁) * hid₃

/-- On the triple witness intersection the vanishing parts die: every shared
point is a root of the degree-`<k` codeword combination
`(γ₂−γ₃)P₁ + (γ₃−γ₁)P₂ + (γ₁−γ₂)P₃`. -/
theorem pool_triple_inter_roots
    {γ₁ γ₂ γ₃ : F} {P₁ P₂ P₃ g₁ g₂ g₃ : F[X]} {S₁ S₂ S₃ : Finset (Fin n)}
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂)
    (hid₃ : R₀ + C γ₃ * R₁ - P₃ = g₃ * vanishingPoly dom S₃) :
    ∀ i ∈ S₁ ∩ S₂ ∩ S₃,
      (C (γ₂ - γ₃) * P₁ + C (γ₃ - γ₁) * P₂ + C (γ₁ - γ₂) * P₃).eval (dom i)
        = 0 := by
  intro i hi
  rw [Finset.mem_inter] at hi
  obtain ⟨hi12, hi3⟩ := hi
  rw [Finset.mem_inter] at hi12
  have hev := congrArg (Polynomial.eval (dom i))
    (pool_triple_relation hid₁ hid₂ hid₃)
  have h1 : (vanishingPoly dom S₁).eval (dom i) = 0 :=
    vanishingPoly_eval_eq_zero dom hi12.1
  have h2 : (vanishingPoly dom S₂).eval (dom i) = 0 :=
    vanishingPoly_eval_eq_zero dom hi12.2
  have h3 : (vanishingPoly dom S₃).eval (dom i) = 0 :=
    vanishingPoly_eval_eq_zero dom hi3
  simp only [eval_add, eval_mul, eval_zero, h1, h2, h3, mul_zero, zero_add,
    add_zero] at hev
  simp only [eval_add, eval_mul]
  linear_combination hev

/-- **The triple-intersection bound**: if the codeword combination is nonzero,
the three witnesses share at most `k − 1` points. -/
theorem pool_triple_inter_card_le (hk : 1 ≤ k)
    {γ₁ γ₂ γ₃ : F} {P₁ P₂ P₃ g₁ g₂ g₃ : F[X]} {S₁ S₂ S₃ : Finset (Fin n)}
    (hdP₁ : P₁.natDegree < k) (hdP₂ : P₂.natDegree < k) (hdP₃ : P₃.natDegree < k)
    (hWne : C (γ₂ - γ₃) * P₁ + C (γ₃ - γ₁) * P₂ + C (γ₁ - γ₂) * P₃ ≠ 0)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂)
    (hid₃ : R₀ + C γ₃ * R₁ - P₃ = g₃ * vanishingPoly dom S₃) :
    (S₁ ∩ S₂ ∩ S₃).card ≤ k - 1 := by
  classical
  have hroots := pool_triple_inter_roots hid₁ hid₂ hid₃
  have hdvd : vanishingPoly dom (S₁ ∩ S₂ ∩ S₃)
      ∣ C (γ₂ - γ₃) * P₁ + C (γ₃ - γ₁) * P₂ + C (γ₁ - γ₂) * P₃ := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hroots i hi
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hWne
  rw [vanishingPoly_natDegree] at hdeg
  have t1 : (C (γ₂ - γ₃) * P₁).natDegree ≤ k - 1 :=
    le_trans (natDegree_C_mul_le _ _) (by omega)
  have t2 : (C (γ₃ - γ₁) * P₂).natDegree ≤ k - 1 :=
    le_trans (natDegree_C_mul_le _ _) (by omega)
  have t3 : (C (γ₁ - γ₂) * P₃).natDegree ≤ k - 1 :=
    le_trans (natDegree_C_mul_le _ _) (by omega)
  have hWdeg : (C (γ₂ - γ₃) * P₁ + C (γ₃ - γ₁) * P₂
      + C (γ₁ - γ₂) * P₃).natDegree ≤ k - 1 :=
    le_trans (natDegree_add_le _ _)
      (max_le (le_trans (natDegree_add_le _ _) (max_le t1 t2)) t3)
  omega

end TripleRelation

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pool_triple_relation
#print axioms ProximityGap.WBPencil.pool_triple_inter_roots
#print axioms ProximityGap.WBPencil.pool_triple_inter_card_le
