/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-! # Jacobian columns on a polynomial section

A linear value factor gives an exact common divisor of both specialized partial
derivatives and of their padded polar resultant. Products of the partials and
polynomial combinations preserve the resulting order of divisibility.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.PolynomialSectionJacobian

variable {A : Type*} [CommRing A] [IsDomain A] [Differential A]

omit [IsDomain A] in
/-- The two partial derivatives on the linear section, with no division. -/
theorem section_partials (q : A) (G : A[X]) (F : A[X])
    (hF : F = (X - C q) * G) :
    (Differential.mapCoeffs F).eval q = -q′ * G.eval q ∧
      F.derivative.eval q = G.eval q := by
  subst F
  simp [Derivation.leibniz, Polynomial.derivative_mul, mul_comm]

omit [Differential A] in
/-- A fixed-size resultant still has the linear section's value factor when
the degree of the equation decreases in a specialized scalar fiber. -/
theorem eval_dvd_padded_resultant (q : A) (G T : A[X]) (m n : ℕ)
    (hm : 1 + G.natDegree ≤ m) (hn : T.natDegree ≤ n) :
    T.eval q ∣ ((X - C q) * G).resultant T m n := by
  let e := 1 + G.natDegree
  have hle : ((X - C q) * G).natDegree ≤ e := by
    exact natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_sub_C_le q) _)
  have hm' : m = e + (m - e) := by dsimp [e]; omega
  rw [hm', resultant_add_left_deg _ _ _ _ _ hle]
  apply dvd_mul_of_dvd_right
  have hf := resultant_mul_left (X - C q) G T n hn
  rw [natDegree_X_sub_C] at hf
  rw [show e = 1 + G.natDegree from rfl, hf, resultant_X_sub_C_left _ _ _ hn]
  exact dvd_mul_right ..

/-- Every simple-section residual divides the padded Jacobian polar. -/
theorem polar_resultant_dvd (q c : A) (F G : A[X]) (m n : ℕ)
    (hF : F = (X - C q) * G)
    (hm : 1 + G.natDegree ≤ m)
    (hn : (Differential.mapCoeffs F + C c * F.derivative).natDegree ≤ n) :
    G.eval q ∣ F.resultant (Differential.mapCoeffs F + C c * F.derivative) m n := by
  let T := Differential.mapCoeffs F + C c * F.derivative
  have ht : G.eval q ∣ T.eval q := by
    obtain ⟨hx, hy⟩ := section_partials q G F hF
    refine ⟨-q′ + c, ?_⟩
    simp only [T, eval_add, eval_mul, eval_C, hx, hy]
    ring
  change G.eval q ∣ F.resultant T m n
  apply ht.trans
  conv_rhs => rw [hF]
  exact eval_dvd_padded_resultant q G T m n hm hn

omit [IsDomain A] in
/-- Each degree-a product of the two Jacobian columns contributes a copies of
the same section divisor. -/
theorem mixed_column_dvd (q : A) (F G : A[X]) (hF : F = (X - C q) * G)
    (a i : ℕ) (hi : i ≤ a) :
    G.eval q ^ a ∣ ((Differential.mapCoeffs F)^i * F.derivative^(a-i)).eval q := by
  obtain ⟨hx, hy⟩ := section_partials q G F hF
  simp only [eval_mul, eval_pow, hx, hy, mul_pow]
  use (-q′)^i
  rw [show a = i + (a-i) by omega] at ⊢
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

variable {k ι : Type*} [Field k]

/-- A multiplier combination of columns, after specializing the value to a
polynomial section, vanishes if its degree is below the shared divisor. -/
theorem multiplier_sum_forced_zero (q g : k[X]) (a : ℕ)
    (S : Finset ι) (u col : ι → k[X][X]) (R : k[X][X])
    (hR : R = ∑ i ∈ S, u i * col i)
    (hcol : ∀ i ∈ S, g^a ∣ (col i).eval q)
    (hdeg : (R.eval q).natDegree < a * g.natDegree) :
    R.eval q = 0 := by
  have hd : g ^ a ∣ R.eval q := by
    rw [hR, eval_finsetSum]
    apply Finset.dvd_sum
    intro i hi
    rw [eval_mul]
    exact dvd_mul_of_dvd_right (hcol i hi) _
  by_contra hn
  exact (not_le_of_gt hdeg) (by simpa using natDegree_le_of_dvd hd hn)

variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

/-- Multiply bounded scalar-polynomial coefficients by polynomial columns.
The output still lies in the prescribed scalar degree window. -/
def boundedColumns (cols : I → T → k[X]) (u s : ℕ)
    (hcols : ∀ i t, u + (cols i t).natDegree ≤ s) :
    (I → degreeLT k (u+1)) →ₗ[k] (T → degreeLT k (s+1)) where
  toFun v t := ⟨∑ i, (v i : k[X]) * cols i t, by
    rw [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
    apply natDegree_sum_le_of_forall_le
    intro i _
    have bounded (p : k[X]) (hp : p ∈ degreeLT k (u+1)) : p.natDegree ≤ u := by
      rwa [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le] at hp
    have hi := bounded _ (v i).property
    exact natDegree_mul_le.trans ((Nat.add_le_add_right hi _).trans (hcols i t))⟩
  map_add' v w := by
    funext t
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext t
    apply Subtype.ext
    simp [Finset.smul_sum]

private theorem bounded_finrank (i : Type*) [Fintype i] (s : ℕ) :
    Module.finrank k (i → degreeLT k s) = Fintype.card i * s := by
  have h := (degreeLTEquiv k s).finrank_eq
  simp only [Module.finrank_fin_fun] at h
  simp [Module.finrank_pi_fintype, h]

/-- If the raw polynomial columns have independent allowed multipliers, a
strict surplus yields a nonzero source vector equal to their polynomial
combination. The equality holds at every specialization. -/
theorem bounded_column_intersection
    (source : I → T → k[X]) (cols : J → T → k[X]) (u s : ℕ)
    (hs : ∀ i t, s + (source i t).natDegree ≤ s)
    (hc : ∀ j t, u + (cols j t).natDegree ≤ s)
    (independent : Function.Injective (boundedColumns cols u s hc))
    (surplus : Fintype.card T * (s+1) <
      Fintype.card I * (s+1) + Fintype.card J * (u+1)) :
    ∃ (v : I → degreeLT k (s+1)) (w : J → degreeLT k (u+1)),
      v ≠ 0 ∧ ∀ t, ∑ i, (v i : k[X]) * source i t = ∑ j, (w j : k[X]) * cols j t := by
  classical
  let A := boundedColumns source s s hs
  let B := boundedColumns cols u s hc
  let L := A.coprod (-B)
  have hd : Module.finrank k (T → degreeLT k (s+1)) <
      Module.finrank k ((I → degreeLT k (s+1)) × (J → degreeLT k (u+1))) := by
    simpa only [Module.finrank_prod, bounded_finrank] using surplus
  obtain ⟨⟨v,w⟩, hker, hne⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hd)
  have heq : A v = B w := by
    change A v + (-B) w = 0 at hker
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hker)
  refine ⟨v, w, ?_, fun t => congrArg Subtype.val (congrFun heq t)⟩
  intro hv
  subst v
  have hw : w = 0 := independent (by simpa [A, B] using heq.symm)
  exact hne (by simp [hw])

#print axioms bounded_column_intersection
#print axioms section_partials
#print axioms eval_dvd_padded_resultant
#print axioms polar_resultant_dvd
#print axioms mixed_column_dvd
#print axioms multiplier_sum_forced_zero

end ArkLib.ProximityGap.Frontier.PolynomialSectionJacobian
