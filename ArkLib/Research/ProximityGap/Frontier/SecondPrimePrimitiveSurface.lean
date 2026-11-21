/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimitiveReceivedInterpolation
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import Mathlib.RingTheory.Polynomial.Content

/-! # Removing vertical factors from the actual second-prime witness surface -/

open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimePrimitiveSurface

open SecondPrimeQuarticInterpolation HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry

variable {F : Type} [Field F]

/-- The primitive value-dependent part of a surface still contains every section outside a
set of at most the scalar degree of one of its nonzero coefficients. -/
theorem primitive_surface {L : Type} [Field L] (φ : L →+* F)
    {Q : Polynomial (Polynomial F[X])} (hQ : Q ≠ 0) (G : Finset L)
    (q : L → F[X]) (H : ℕ) (hdeg : ∀ j, (Q.coeff j).natDegree ≤ H)
    (hsection : ∀ z ∈ G, Q.eval₂ (evalRingHom (C (φ z))) (q z) = 0) :
    ∃ (P : Polynomial (Polynomial F[X])) (E : Finset L), P ≠ 0 ∧ P.IsPrimitive ∧
      P ∣ Q ∧ P.natDegree = Q.natDegree ∧ E ⊆ G ∧ E.card ≤ H ∧
      ∀ z ∈ G, z ∉ E → P.eval₂ (evalRingHom (C (φ z))) (q z) = 0 := by
  classical
  let V := Q.content
  have hV : V ≠ 0 := fun hv => hQ (content_eq_zero_iff.mp hv)
  let E := G.filter fun z => V.eval (C (φ z)) = 0
  have hcount : E.card ≤ V.natDegree := by
    by_contra! h
    apply hV
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero V (f := fun z : E => C (φ (z : L)))
      (C_injective.comp (φ.injective.comp Subtype.val_injective))
    · exact fun z => (mem_filter.mp z.property).2
    · simpa using h
  have hdegV : V.natDegree ≤ H :=
    (natDegree_le_of_dvd (content_dvd_coeff Q.natDegree) (leadingCoeff_ne_zero.mpr hQ)).trans
      (hdeg Q.natDegree)
  refine ⟨Q.primPart, E, primPart_ne_zero _, isPrimitive_primPart _, primPart_dvd _,
    natDegree_primPart _, filter_subset _ _, hcount.trans hdegV, ?_⟩
  intro z hz he
  have hnot : V.eval (C (φ z)) ≠ 0 := fun hh => he (mem_filter.mpr ⟨hz, hh⟩)
  have hs := hsection z hz
  rw [eq_C_content_mul_primPart Q, eval₂_mul, eval₂_C] at hs
  exact (mul_eq_zero.mp hs).resolve_left hnot


/-- All irreducible factors of a primitive surface have positive value degree; their total
value degree equals the degree of the surface. Vanishing sections lie on one of them. -/
theorem factor_cover (P : Polynomial (Polynomial F[X])) (hP : P ≠ 0) (hp : P.IsPrimitive) :
    ∃ U : Multiset (Polynomial (Polynomial F[X])),
      (∀ f ∈ U, Irreducible f ∧ 0 < f.natDegree ∧ f ∣ P) ∧
      (U.map natDegree).sum = P.natDegree ∧ U.card ≤ P.natDegree ∧
      ∀ (z : F) (w : F[X]), P.eval₂ (evalRingHom (C z)) w = 0 →
        ∃ f ∈ U, f.eval₂ (evalRingHom (C z)) w = 0 := by
  classical
  obtain ⟨U, hirr, hprod⟩ := WfDvdMonoid.exists_factors P hP
  have hpos (f) (hf : f ∈ U) : 0 < f.natDegree := by
    by_contra! hn
    obtain hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn)
    have hdiv := (Multiset.dvd_prod hf).trans hprod.dvd
    have hunit := isPrimitive_iff_isUnit_of_C_dvd.mp hp (f.coeff 0) (hc ▸ hdiv)
    exact (hirr f hf).not_isUnit (hc ▸ isUnit_C.mpr hunit)
  have hdegrees : (U.map natDegree).sum = P.natDegree := by
    rw [← natDegree_multiset_prod U (fun hz => (hirr 0 hz).ne_zero rfl)]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hprod)
  refine ⟨U, fun f hf => ⟨hirr f hf, hpos f hf, (Multiset.dvd_prod hf).trans hprod.dvd⟩,
    hdegrees, ?_, ?_⟩
  · have h := Multiset.card_nsmul_le_sum (s := U.map natDegree) (a := 1) (by
      intro n hn
      obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp hn
      exact hpos f hf)
    simpa [hdegrees] using h
  · intro z w hw
    let E := eval₂RingHom (evalRingHom (C z)) w
    have h := (Associated.map E hprod).eq_zero_iff.mpr hw
    rw [map_multiset_prod] at h
    exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)

variable {ι : Type} [Fintype ι] [DecidableEq F]

/-- Every literal bad label lies on the same primitive polynomial of value degree at most four. -/
theorem all_actual_witnesses {K : Type} [Field K] (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u) :
    ∃ P : Polynomial (Polynomial K[X]), P ≠ 0 ∧ P.IsPrimitive ∧
      P.natDegree ≤ 4 ∧
      (∃ Q, Q ≠ 0 ∧ P ∣ Q ∧ ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      ∀ z ∈ fam.G, P.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
  classical
  let dom' := dom.trans (⟨φ,φ.injective⟩ : F ↪ K)
  let u₀ (i : ι) := φ (u 0 i)
  let u₁ (i : ι) := φ (u 1 i)
  obtain ⟨c,hc,hline,_⟩ := secondPrime_predecessor_quartic dom' u₀ u₁ hn
  let Q := surface c
  have hQ : Q≠0 := surface_ne_zero hc
  have hy : Q.natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  refine ⟨Q.primPart,primPart_ne_zero _,isPrimitive_primPart _,(natDegree_primPart _).le.trans hy,
    ⟨Q,hQ,primPart_dvd _,fun _ _ _ hh => surface_support c hh⟩,?_⟩
  intro z hz
  apply PrimitiveReceivedInterpolation.raw_primitive_section dom' u₀ u₁ hc (by decide) hline (φ z)
    ((fam.q z).map φ) (natDegree_map_le.trans (by have := fam.degree_lt z hz; omega))
    (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht.trans (fam.threshold_le z hz))
  intro i hi
  change ((fam.q z).map φ).eval (φ (dom i)) = _
  rw [eval_map_apply]
  simpa only [u₀,u₁,map_add,map_mul] using congrArg φ (mem_filter.mp hi).2

/-- In a literal MCA witness family, only 34 labels can be lost on removing every factor
depending solely on the scalar and coordinate. All other actual bad witnesses lie on the
same primitive polynomial of value degree at most four. -/
theorem actual_witnesses {K : Type} [Field K] (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u) :
    ∃ (P : Polynomial (Polynomial K[X])) (E : Finset F), P ≠ 0 ∧ P.IsPrimitive ∧
      P.natDegree ≤ 4 ∧ E ⊆ fam.G ∧ E.card ≤ 34 ∧
      (∃ Q, Q ≠ 0 ∧ P ∣ Q ∧ ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      ∀ z ∈ fam.G, z ∉ E → P.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
  obtain ⟨P,hP,hprim,hdeg,hQ,hh⟩ := all_actual_witnesses φ dom δ u hn ht fam
  exact ⟨P,∅,hP,hprim,hdeg,empty_subset _,by simp,hQ,fun z hz _ => hh z hz⟩

/-- The selected bad labels that survive scalar exceptions are covered by at most four
irreducible components, all with positive value degree and total value-degree budget four. -/
theorem actual_components {K : Type} [Field K] (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u) :
    ∃ (Q : Polynomial (Polynomial K[X])) (U : Multiset (Polynomial (Polynomial K[X])))
      (E : Finset F),
      Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      (∀ f ∈ U, Irreducible f ∧ 0 < f.natDegree ∧ f ∣ Q) ∧ (U.map natDegree).sum ≤ 4 ∧
      U.card ≤ 4 ∧ E ⊆ fam.G ∧ E.card ≤ 34 ∧ ∀ z ∈ fam.G, z ∉ E →
        ∃ f ∈ U, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
  obtain ⟨P, E, hP, hp, hd, hEG, hsize, ⟨Q, hQ, hdiv, hcoeff⟩, hz⟩ :=
    actual_witnesses φ dom δ u hn ht fam
  obtain ⟨U, hU, hsum, hcard, hcover⟩ := factor_cover P hP hp
  exact ⟨Q, U, E, hQ, hcoeff, fun f hf => ⟨(hU f hf).1, (hU f hf).2.1,
    (hU f hf).2.2.trans hdiv⟩, hsum.trans_le hd, hcard.trans hd, hEG, hsize,
    fun z hzg hze => hcover _ _ (hz z hzg hze)⟩

#print axioms factor_cover
#print axioms actual_components
#print axioms primitive_surface
#print axioms all_actual_witnesses
#print axioms actual_witnesses
end ArkLib.ProximityGap.Frontier.SecondPrimePrimitiveSurface
