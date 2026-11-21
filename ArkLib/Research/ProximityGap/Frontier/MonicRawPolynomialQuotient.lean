/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Homogeneous columns in a monic chart

Over a coefficient ring with possible zero divisors, the residual binary
multipliers of degree two represent every class modulo a monic cubic. This
identifies the homogeneous-column quotient with the corresponding ideal quotient
after a chart with unit value-leading coefficient has been chosen.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.MonicRawPolynomialQuotient

variable {A ι : Type*} [CommRing A] [Nontrivial A] [Fintype ι]

omit [Nontrivial A] in
/-- In a monic chart, ideal membership admits a combination with all residual
multipliers of degree smaller than the monic equation. -/
theorem short_multipliers (f : A[X]) (hf : f.Monic) (hb : 0 < f.natDegree)
    (cols : ι → A[X]) (x : AdjoinRoot f) :
    x ∈ Ideal.span (Set.range fun i => AdjoinRoot.mk f (cols i)) ↔
      ∃ v : ι → A[X], (∀ i, (v i).natDegree < f.natDegree) ∧
        ∑ i, AdjoinRoot.mk f (cols i * v i) = x := by
  classical
  change x ∈ Submodule.span (AdjoinRoot f) (Set.range fun i => AdjoinRoot.mk f (cols i)) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, h⟩
    refine ⟨fun i => AdjoinRoot.modByMonicHom hf (c i), ?_, ?_⟩
    · intro i
      change (AdjoinRoot.modByMonicHom hf (c i)).natDegree < f.natDegree
      obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (c i)
      rw [← hp, AdjoinRoot.modByMonicHom_mk]
      exact natDegree_modByMonic_lt p hf (by rintro rfl; simp at hb)
    · have hm (q : AdjoinRoot f) : AdjoinRoot.mk f (AdjoinRoot.modByMonicHom hf q) = q :=
        AdjoinRoot.mk_leftInverse hf q
      simp only [map_mul, hm]
      simpa only [smul_eq_mul, mul_comm] using h
  · rintro ⟨c, -, h⟩
    refine ⟨fun i => AdjoinRoot.mk f (c i), ?_⟩
    simpa [mul_comm] using h

omit [Nontrivial A] in
/-- Degree-v homogeneous forms obtained from the short multipliers present
the full ideal in the monic chart, including over Artinian coefficient rings. -/
theorem homogeneous_column_presentation (f E : A[X]) (cols : ι → A[X])
    (b l : ℕ) (hf : f.Monic) (hfdeg : f.natDegree = b+1)
    (hcap : b+1 ≤ l+b) (hE : E.natDegree ≤ l+b) (hc : ∀ i, (cols i).natDegree ≤ l)
    (hmem : AdjoinRoot.mk f E ∈ Ideal.span (Set.range fun i => AdjoinRoot.mk f (cols i))) :
    ∃ (h : A[X]) (v : ι → A[X]), h.natDegree ≤ l+b-(b+1) ∧ (∀ i, (v i).natDegree ≤ b) ∧
      E.homogenize (l+b) = f.homogenize (b+1) * h.homogenize (l+b-(b+1)) +
        ∑ i, (cols i).homogenize l * (v i).homogenize b := by
  classical
  obtain ⟨v, hv, hq⟩ := (short_multipliers f hf (by omega) cols _).mp hmem
  have hv' (i : ι) : (v i).natDegree ≤ b := by have := hv i; omega
  let S := ∑ i, cols i * v i
  have hS : S.natDegree ≤ l+b :=
    natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_mul_le.trans (Nat.add_le_add (hc i) (hv' i))
  have hmod : AdjoinRoot.mk f E = AdjoinRoot.mk f S := by simpa [S] using hq.symm
  have hdvd := AdjoinRoot.mk_eq_mk.mp hmod
  let H := (E-S) /ₘ f
  have hH : H.natDegree ≤ l+b-(b+1) := by
    rw [show H = (E-S) /ₘ f from rfl, natDegree_divByMonic _ hf, hfdeg]
    exact Nat.sub_le_sub_right ((natDegree_sub_le _ _).trans (max_le hE hS)) _
  have hmul : f * H = E-S := by
    simpa [(modByMonic_eq_zero_iff_dvd hf).mpr hdvd, H] using modByMonic_add_div (E-S) f
  have hEeq : E = f * H + S := by rw [hmul]; abel
  refine ⟨H, v, hH, hv', ?_⟩
  have hsum : b+1+(l+b-(b+1)) = l+b := by omega
  have hfh := homogenize_mul f H (m := b+1) (n := l+b-(b+1)) hfdeg.le hH
  rw [hsum] at hfh
  rw [hEeq, homogenize_add, hfh]
  congr 1
  change (∑ i, cols i * v i).homogenize (l+b) = _
  rw [homogenize_finsetSum]
  exact Finset.sum_congr rfl fun i _ => homogenize_mul _ _ (hc i) (hv' i)

/-- The additional scalar-coordinate column removes exactly the kernel of the
coefficient reduction, also when the coefficients are polynomials in Y. -/
theorem coordinate_modulus_kernel {R : Type*} [CommRing R] (P : R[X]) (E : R[X][X]) :
    E.map (AdjoinRoot.mk P) = 0 ↔ C P ∣ E := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have hx := congrArg (fun q : (AdjoinRoot P)[X] => q.coeff i) h
    simpa only [coeff_map, coeff_zero, AdjoinRoot.mk_eq_zero] using hx
  · intro h
    ext i
    simpa [AdjoinRoot.mk_eq_zero] using h i

/-- One common affine value misses the roots of every fiber above the scalar
modulus. Its value in the quotient is therefore a unit. -/
theorem exists_unit_chart_value {K : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    (P : K[X]) (hP : P ≠ 0) (F : K[X][X])
    (hfib : ∀ x : K, P.eval x = 0 → F.map (evalRingHom x) ≠ 0) :
    ∃ c : K, IsUnit (AdjoinRoot.mk P (F.eval (C c))) := by
  classical
  let S := P.roots.toFinset
  let B := ∏ x ∈ S, F.map (evalRingHom x)
  have hb : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx =>
    hfib x ((mem_roots hP).mp (Multiset.mem_toFinset.mp hx))
  obtain ⟨c, hc⟩ : ∃ c : K, B.eval c ≠ 0 := by
    by_contra! hn
    exact hb (Polynomial.funext (by simpa using hn))
  have hcop : IsCoprime P (F.eval (C c)) := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K P (F.eval (C c))).mpr
    intro x
    by_cases hz : P.eval x = 0
    · right
      have hx : x ∈ S := Multiset.mem_toFinset.mpr ((mem_roots hP).mpr hz)
      have hprod : ∏ x ∈ S, (F.map (evalRingHom x)).eval c ≠ 0 := by
        simpa [B, eval_prod] using hc
      have hv := (Finset.prod_ne_zero_iff.mp hprod) x hx
      simpa [Polynomial.map_evalRingHom_eval, Polynomial.evalEval,
        aeval_def] using hv
    · left
      simpa [aeval_def] using hz
  obtain ⟨u, v, h⟩ := hcop
  refine ⟨c, isUnit_iff_exists_inv'.mpr ⟨AdjoinRoot.mk P v, ?_⟩⟩
  simpa using congrArg (AdjoinRoot.mk P) h

/-- Translating the common avoided point and then reversing the binary
coordinates makes the value-leading coefficient a unit, over the quotient
ring itself. The nominal degree is retained. -/
theorem reciprocal_chart_leading_unit (f : A[X]) (c : A) (b : ℕ)
    (hb : f.natDegree ≤ b) (hc : IsUnit (f.eval c)) :
    ((taylor c f).reflect b).natDegree = b ∧ IsUnit ((taylor c f).reflect b).leadingCoeff := by
  have ht : ((taylor c f).reflect b).coeff b = f.eval c := by
    rw [coeff_reflect, revAt_le (le_refl b), Nat.sub_self, taylor_coeff_zero]
  have hn : ((taylor c f).reflect b).natDegree ≤ b := by
    simpa only [natDegree_taylor, max_eq_left hb] using
      (natDegree_reflect_le (N := b) (p := taylor c f))
  have hn' := hn.antisymm (le_natDegree_of_ne_zero (ht ▸ hc.ne_zero))
  exact ⟨hn', by simpa only [Polynomial.leadingCoeff, hn', ht] using hc⟩

private theorem kernel_power_bound {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (a : ℕ) :
    Module.finrank K (LinearMap.ker (f^a)) ≤ a * Module.finrank K (LinearMap.ker f) := by
  induction a with
  | zero => simp [Module.End.one_eq_id]
  | succ a ih =>
    let h : LinearMap.ker (f^(a+1)) →ₗ[K] LinearMap.ker f :=
      ((f^a).comp (LinearMap.ker (f^(a+1))).subtype).codRestrict _ fun x => by
        change f ((f^a) (x : V)) = 0
        have hx := x.property
        simpa only [pow_succ', Module.End.mul_apply, LinearMap.mem_ker] using hx
    let i : LinearMap.ker h →ₗ[K] LinearMap.ker (f^a) :=
      ((LinearMap.ker (f^(a+1))).subtype.comp (LinearMap.ker h).subtype).codRestrict _ fun x => by
        exact congrArg Subtype.val x.property
    have hi : Function.Injective i := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker (f^a) => (z : V)) hxy))
    have hr := h.finrank_range_add_finrank_ker
    have h1 := (LinearMap.range h).finrank_le
    have h2 := LinearMap.finrank_le_finrank_of_injective hi
    rw [Nat.succ_mul]
    omega

/-- In each finite algebra at a polar base point the colength of an ideal
power is at most the power times the colength of any given polar it contains.
This applies also to truncated, nonreduced local algebras. -/
theorem local_power_colength {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    [FiniteDimensional K S] (I : Ideal S) (r : S) (hr : r ∈ I) (a : ℕ) :
    Module.finrank K (S ⧸ I^a) ≤ a * Module.finrank K (S ⧸ Ideal.span {r}) := by
  let L := LinearMap.mulLeft K r
  have hspan (s : S) : (Ideal.span {s} : Ideal S).restrictScalars K =
      LinearMap.range (LinearMap.mulLeft K s) := by
    ext x
    simp [Ideal.mem_span_singleton, LinearMap.mem_range, LinearMap.mulLeft_apply, dvd_def, eq_comm]
  have hcod (s : S) : Module.finrank K (S ⧸ Ideal.span {s}) =
      Module.finrank K (LinearMap.ker (LinearMap.mulLeft K s)) := by
    have he := ((Ideal.span {s} : Ideal S).restrictScalars K).finrank_quotient_add_finrank
    have h := (LinearMap.mulLeft K s).finrank_range_add_finrank_ker
    change Module.finrank K (S ⧸ Ideal.span {s}) +
      Module.finrank K ((Ideal.span {s} : Ideal S).restrictScalars K) = _ at he
    rw [hspan] at he
    omega
  have hincl : (Ideal.span {r^a} : Ideal S).restrictScalars K ≤ (I^a).restrictScalars K :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (Ideal.pow_mem_pow hr a)
  have hle := Submodule.finrank_mono hincl
  have hquot : Module.finrank K (S ⧸ I^a) ≤ Module.finrank K (S ⧸ Ideal.span {r^a}) := by
    have h1 := ((I^a).restrictScalars K).finrank_quotient_add_finrank
    have h2 := ((Ideal.span {r^a} : Ideal S).restrictScalars K).finrank_quotient_add_finrank
    change Module.finrank K (S ⧸ I^a) + _ = _ at h1
    change Module.finrank K (S ⧸ Ideal.span {r^a}) + _ = _ at h2
    omega
  apply hquot.trans
  rw [hcod, hcod, ← LinearMap.pow_mulLeft]
  exact kernel_power_bound L a

#print axioms local_power_colength
#print axioms exists_unit_chart_value
#print axioms reciprocal_chart_leading_unit
#print axioms short_multipliers
#print axioms homogeneous_column_presentation
#print axioms coordinate_modulus_kernel

end ArkLib.ProximityGap.Frontier.MonicRawPolynomialQuotient
