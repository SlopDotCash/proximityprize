/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.JacobianPowerFiniteAlgebra

/-! # The quotient seen by the degree-bounded Jacobian columns

In a monic chart the window maps onto the actual algebra cut out by the
mixed Jacobian powers. An element of the kernel has a homogeneous
presentation using exactly the residual value-degree slots.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Module Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.RawJacobianWindow

open JacobianPowerFiniteAlgebra MonicRawPolynomialQuotient

variable {A : Type*} [CommRing A]

/-- Projection of a bounded value polynomial onto the actual finite algebra. -/
def windowMap (f u v : A[X]) (a h : ℕ) :
    degreeLT A h →ₗ[A] PowerQuotient (AdjoinRoot.mk f u) (AdjoinRoot.mk f v) a :=
  ((Ideal.Quotient.mkₐ A _).toLinearMap.comp (AdjoinRoot.mkₐ f).toLinearMap).comp
    (degreeLT A h).subtype

/-- The bounded window is onto as soon as it includes the short-remainder
slots of the monic equation. -/
theorem windowMap_surjective (f u v : A[X]) (a h : ℕ) (hf : f.Monic)
    (hb : 0 < f.natDegree) (hh : f.natDegree ≤ h) :
    Function.Surjective (windowMap f u v a h) := by
  intro x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
  have hr := natDegree_modByMonic_lt p hf (by rintro rfl; simp at hb)
  have hmem : p %ₘ f ∈ degreeLT A h :=
    mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast hr.trans_le hh))
  refine ⟨⟨p %ₘ f, hmem⟩, ?_⟩
  apply congrArg (Ideal.Quotient.mk _)
  change AdjoinRoot.mk f (p %ₘ f) = AdjoinRoot.mk f p
  simpa only [AdjoinRoot.modByMonicHom_mk] using AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f p)

/-- The formal codimension of the kernel of the window projection equals the
dimension of the concrete mixed-power quotient. -/
theorem window_codimension {K : Type*} [Field K] [Algebra K A]
    (f u v : A[X]) (a h : ℕ) (hf : f.Monic) (hb : 0 < f.natDegree) (hh : f.natDegree ≤ h) :
    finrank K (degreeLT A h ⧸ LinearMap.ker ((windowMap f u v a h).restrictScalars K)) =
      finrank K (PowerQuotient (AdjoinRoot.mk f u) (AdjoinRoot.mk f v) a) :=
  (((windowMap f u v a h).restrictScalars K).quotKerEquivOfSurjective
    (windowMap_surjective f u v a h hf hb hh)).finrank_eq

/-- Every kernel element has an equality of binary homogeneous forms using
the original mixed-power columns and true bounded-degree multipliers. -/
theorem kernel_homogeneous_columns (f u v : A[X]) (a b l : ℕ)
    (hf : f.Monic) (hb : f.natDegree = b+1) (hn : b+1 ≤ l+b)
    (hg : ∀ i : Fin (a+1), (u^i.val * v^(a-i.val)).natDegree ≤ l)
    (E : degreeLT A (l+b+1)) (hE : windowMap f u v a (l+b+1) E = 0) :
    ∃ (w : A[X]) (c : Fin (a+1) → A[X]),
      w.natDegree ≤ l+b-(b+1) ∧ (∀ i, (c i).natDegree ≤ b) ∧
        (E : A[X]).homogenize (l+b) = f.homogenize (b+1) * w.homogenize (l+b-(b+1)) +
        ∑ i, (u^i.val * v^(a-i.val)).homogenize l * (c i).homogenize b := by
  let C (i : Fin (a+1)) := u^i.val * v^(a-i.val)
  have hmem : AdjoinRoot.mk f (E : A[X]) ∈
      mixedIdeal (AdjoinRoot.mk f u) (AdjoinRoot.mk f v) a := Ideal.Quotient.eq_zero_iff_mem.mp hE
  have hgen : AdjoinRoot.mk f (E : A[X]) ∈ Ideal.span (Set.range fun i => AdjoinRoot.mk f (C i)) := by
    simpa only [C, map_mul, map_pow, mixedIdeal] using hmem
  have hcap (p : A[X]) (hp : p ∈ degreeLT A (l+b+1)) : p.natDegree ≤ l+b := by
    rwa [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le] at hp
  exact homogeneous_column_presentation f _ C b l hf hb hn (hcap _ E.property) hg hgen

/-- Under the coefficient reduction modulo P, every Y-polynomial lifts with
unchanged value-degree bound and coefficient X-degrees below P's degree. -/
theorem bounded_coordinate_lift {K : Type*} [Field K] (P : K[X]) (hP : P.Monic)
    (hn : 0 < P.natDegree) (Q : (AdjoinRoot P)[X]) :
    ∃ E : K[X][X], E.map (AdjoinRoot.mk P) = Q ∧ E.natDegree ≤ Q.natDegree ∧
      ∀ j, (E.coeff j).natDegree < P.natDegree := by
  classical
  let rem := AdjoinRoot.modByMonicHom hP
  let E := ∑ j ∈ Q.support, monomial j (rem (Q.coeff j))
  have hcoeff (i : ℕ) : E.coeff i = rem (Q.coeff i) := by
    by_cases hi : i ∈ Q.support
    · simp [E, finsetSum_coeff, coeff_monomial, hi]
    · simp [E, finsetSum_coeff, coeff_monomial, hi, notMem_support_iff.mp hi]
  refine ⟨E, ?_, ?_, ?_⟩
  · ext i
    rw [coeff_map, hcoeff]
    exact AdjoinRoot.mk_leftInverse hP _
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [hcoeff, coeff_eq_zero_of_natDegree_lt hm, map_zero]
  · intro j
    rw [hcoeff]
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (Q.coeff j)
    rw [← hq]
    exact natDegree_modByMonic_lt q hP (by rintro rfl; simp at hn)

#print axioms windowMap_surjective
#print axioms window_codimension
#print axioms kernel_homogeneous_columns
#print axioms bounded_coordinate_lift

end ArkLib.ProximityGap.Frontier.RawJacobianWindow
