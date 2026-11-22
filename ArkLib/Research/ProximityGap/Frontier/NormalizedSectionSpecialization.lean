/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Specialization on the normalization along a simple polynomial section -/

noncomputable section

open Polynomial
open scoped PowerSeries

namespace ArkLib.ProximityGap.NormalizedSectionSpecialization

/-- For any root, the reciprocal with numerator the value at the chosen
anchor is integral over the original coefficient ring. -/
theorem reciprocal_integral {R E : Type*} [CommRing R] [Field E] (i : R →+* E)
    (F : R[X]) (a : R) (Y : E) (hY : F.eval₂ i Y = 0) :
    i.IsIntegralElem (i (F.eval a) / (Y - i a)) := by
  by_cases hc : F.eval a = 0
  · simpa [hc] using i.isIntegralElem_zero
  by_cases hy : Y - i a = 0
  · simpa [hy] using i.isIntegralElem_zero
  let f := F.taylor a
  have hz : f.eval₂ i (Y - i a) = 0 := by
    rw [show f = F.comp (X+C a) from taylor_apply ..,eval₂_comp]
    simpa using hY
  let _ := invertibleOfNonzero hy
  have hr := (eval₂_reverse_eq_zero_iff i (Y-i a) f).mpr hz
  have hlead : f.reverse.leadingCoeff=F.eval a := by
    rw [reverse_leadingCoeff,trailingCoeff,natTrailingDegree_eq_zero_of_constantCoeff_ne_zero]
    · exact taylor_coeff_zero ..
    · simpa [f,constantCoeff] using hc
  have hInt := i.isIntegralElem_leadingCoeff_mul f.reverse (⅟(Y-i a)) hr
  simpa only [hlead,invOf_eq_inv,div_eq_mul_inv] using hInt

/-- The Taylor map embeds the generic scalar coordinate into the power
series ring and evaluates at the chosen label under the constant term. -/
def expansion {L : Type*} [Field L] (z : L) : L[X] →+* L⟦X⟧ :=
  Polynomial.coeToPowerSeries.ringHom.comp (taylorEquiv z).toRingEquiv.toRingHom

theorem expansion_injective {L : Type*} [Field L] (z : L) :
    Function.Injective (expansion z) :=
  (Polynomial.coe_injective L).comp (taylor_injective z)

theorem constant_expansion {L : Type*} [Field L] (z : L) (p : L[X]) :
    PowerSeries.constantCoeff (expansion z p)=p.eval z := by
  change PowerSeries.constantCoeff ((p.taylor z : L[X]) : L⟦X⟧) = _
  rw [Polynomial.constantCoeff_coe,taylor_coeff_zero]

/-- A simple residue root lifts over the full power series ring as soon as the
leading coefficient is a unit, as it is at every retained section. -/
theorem simple_lift {L : Type*} [Field L] (f : L⟦X⟧[X]) (b : L)
    (hl : IsUnit f.leadingCoeff) (h₀ : PowerSeries.constantCoeff (f.eval (PowerSeries.C b)) = 0)
    (h₁ : PowerSeries.constantCoeff (f.derivative.eval (PowerSeries.C b)) ≠ 0) :
    ∃ y : L⟦X⟧, f.eval y=0 ∧ PowerSeries.constantCoeff y=b := by
  let g := hl.unit⁻¹ • f
  have hg : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hl
  let I : Ideal L⟦X⟧ := Ideal.span {PowerSeries.X}
  have he : g = C (↑hl.unit⁻¹ : L⟦X⟧)*f := by
    rw [←smul_eq_C_mul]
    rfl
  have hmem : g.eval (PowerSeries.C b) ∈ I := by
    rw [Ideal.mem_span_singleton,PowerSeries.X_dvd_iff,he]
    simp [h₀]
  have hd : IsUnit (Ideal.Quotient.mk I (g.derivative.eval (PowerSeries.C b))) := by
    apply IsUnit.map
    rw [he,derivative_C_mul,eval_mul,eval_C]
    exact hl.unit⁻¹.isUnit.mul
      (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h₁))
  obtain ⟨y,hy,hc⟩ := HenselianRing.is_henselian g hg _ hmem hd
  refine ⟨y,?_,?_⟩
  · rw [IsRoot,he,eval_mul,eval_C] at hy
    exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)
  · rw [Ideal.mem_span_singleton,PowerSeries.X_dvd_iff] at hc
    exact sub_eq_zero.mp (by simpa using hc)

/-- For a compatible map from a generic function algebra into a fraction
field, an integral element lands in the integrally closed local ring.
Its residue belongs to the integrally closed base if the residue of every
generic coefficient belongs to that base. Both levels use the same monic witness. -/
theorem integral_residue {A E R S L Q : Type*} [CommRing A] [CommRing E] [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Field L] [Field Q] [Algebra R L] [IsFractionRing R L] [Algebra S Q] [IsFractionRing S Q]
    (i : A →+* E) (φ : E →+* Q) (t : A →+* S) (τ : S →+* L) (ev : A →+* R)
    (hφ : φ.comp i = (algebraMap S Q).comp t)
    (hτ : τ.comp t = (algebraMap R L).comp ev)
    (x : E) (hx : i.IsIntegralElem x) :
    ∃ (s : S) (r : R), algebraMap S Q s = φ x ∧ algebraMap R L r = τ s := by
  obtain ⟨f,hm,hf⟩ := hx
  have hq : (f.map t).eval₂ (algebraMap S Q) (φ x)=0 := by
    rw [eval₂_map,←hφ,←hom_eval₂,hf,map_zero]
  obtain ⟨s,hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (show IsIntegral S (φ x) from ⟨f.map t,hm.map _,hq⟩)
  have hS : f.eval₂ t s=0 := by
    apply IsFractionRing.injective S Q
    rw [hom_eval₂,hs,map_zero,←eval₂_map,hq]
  have hL : (f.map ev).eval₂ (algebraMap R L) (τ s)=0 := by
    rw [eval₂_map,←hτ,←hom_eval₂,hS,map_zero]
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (show IsIntegral R (τ s) from ⟨f.map ev,hm.map _,hL⟩)
  exact ⟨s,r,hs,hr⟩

/-- The value-scaled derivative of the generic ordinate is regular at the
section when the derivation preserves the integral closure. This only needs
the ordinate itself to be regular on the chosen branch. -/
theorem derivative_regular {A E : Type*} [CommRing A] [Field E] [Algebra ℤ E]
    (i : A →+* E) (F : A[X])
    (Y : E) (hY : F.eval₂ i Y = 0) (D : Derivation ℤ E E)
    (hD : ∀ x, i.IsIntegralElem x → i.IsIntegralElem (D x))
    (O : Subring E) (hi : ∀ x, i.IsIntegralElem x → x ∈ O)
    (hr : Y ∈ O) (a : A) (hne : Y ≠ i a) : i (F.eval a) * D Y ∈ O := by
  let W := Y-i a
  let A₀ := i (F.eval a)
  let S := A₀/W
  have hs : i.IsIntegralElem S := reciprocal_integral i F a Y hY
  have ha : i.IsIntegralElem A₀ := i.isIntegralElem_map
  have hIa : i.IsIntegralElem (i a) := i.isIntegralElem_map
  have hw : W∈O := O.sub_mem hr (hi _ hIa)
  have hv : S*W=A₀ := div_mul_cancel₀ _ (sub_ne_zero.mpr hne)
  have hd := congrArg D hv
  rw [D.leibniz] at hd
  change S*D (Y-i a)+W*D S=D A₀ at hd
  rw [map_sub] at hd
  have he : A₀*D Y = W*D A₀ - W^2*D S + A₀*D (i a) := by
    linear_combination W*hd + (D (i a)-D Y)*hv
  rw [show i (F.eval a) = A₀ from rfl,he]
  exact O.add_mem (O.sub_mem (O.mul_mem hw (hi _ (hD _ ha)))
    (O.mul_mem (O.pow_mem hw _) (hi _ (hD _ hs)))) (O.mul_mem (hi _ ha) (hi _ (hD _ hIa)))

/-- Apply a derivation to each coefficient while fixing the ordinate. -/
def coefficientDerivative {A : Type*} [CommRing A] (δ : Derivation ℤ A A) (f : A[X]) : A[X] :=
  PolynomialModule.equivPolynomial (δ.mapCoeffs f)

/-- The chain rule for a coefficient derivation and a moving generic root. -/
theorem coefficient_chain {A E : Type*} [CommRing A] [CommRing E] [Algebra ℤ E]
    (i : A →+* E) (δ : Derivation ℤ A A) (D : Derivation ℤ E E) (hδ : ∀ c, D (i c) = i (δ c))
    (Y : E) (f : A[X]) :
    D (f.eval₂ i Y) = (coefficientDerivative δ f).eval₂ i Y + f.derivative.eval₂ i Y*D Y := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [coefficientDerivative,map_add,eval₂_add,add_mul] at *
    rw [hp,hq]; ring
  | monomial n c =>
    simp only [coefficientDerivative,Derivation.mapCoeffs_monomial,
      PolynomialModule.equivPolynomial_single,eval₂_monomial,derivative_monomial,
      D.leibniz,D.leibniz_pow,smul_eq_mul,nsmul_eq_mul,map_mul,map_natCast,hδ]
    ring

section Branch

variable {E S Q R L : Type*} [CommRing E] [CommRing S] [CommRing Q] [CommRing R] [CommRing L]
variable (φ : E →+* Q) (J : S →+* Q) (τ : S →+* L) (j : R →+* L)

/-- Elements on the chosen branch which have a power series representative
and specialize to the requested coefficient ring. -/
def branchRing : Subring E where
  carrier := {x | ∃ s r, J s=φ x ∧ j r=τ s}
  one_mem' := ⟨1,1,by simp,by simp⟩
  zero_mem' := ⟨0,0,by simp,by simp⟩
  add_mem' := by
    rintro a b ⟨s,r,h₁,h₂⟩ ⟨s',r',h₁',h₂'⟩
    exact ⟨s+s',r+r',by simp [h₁,h₁'],by simp [h₂,h₂']⟩
  mul_mem' := by
    rintro a b ⟨s,r,h₁,h₂⟩ ⟨s',r',h₁',h₂'⟩
    exact ⟨s*s',r*r',by simp [h₁,h₁'],by simp [h₂,h₂']⟩
  neg_mem' := by
    rintro a ⟨s,r,h₁,h₂⟩
    exact ⟨-s,-r,by simp [h₁],by simp [h₂]⟩

/-- All regular branch values are evaluated by one ring homomorphism. -/
theorem branch_hom (hJ : Function.Injective J) (hj : Function.Injective j) :
    ∃ σ : branchRing φ J τ j →+* R, ∀ (x : branchRing φ J τ j) (s : S) (r : R),
      J s=φ (x:E) → j r=τ s → σ x=r := by
  let O := branchRing φ J τ j
  have h (x : O) : ∃ s r, J s=φ (x:E) ∧ j r=τ s := x.property
  choose s v hs hv using h
  have unique (x : O) (s' : S) (r : R) (hs' : J s'=φ (x:E)) (hr : j r=τ s') : v x=r := by
    apply hj
    rw [hv,hr,hJ ((hs x).trans hs'.symm)]
  refine ⟨{ toFun := v,
            map_zero' := unique _ 0 0 (by simp) (by simp),
            map_one' := unique _ 1 1 (by simp) (by simp),
            map_add' := fun x y => unique _ (s x+s y) _ (by simp [hs]) (by simp [hv]),
            map_mul' := fun x y => unique _ (s x*s y) _ (by simp [hs]) (by simp [hv]) }, unique⟩

end Branch

section Section

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- Expand scalar polynomials over `R` at the retained scalar label. -/
def scalarExpansion (z : R) : R[X] →+* L⟦X⟧ :=
  (expansion (algebraMap R L z)).comp (mapRingHom (algebraMap R L))

theorem scalar_constant (z : R) : PowerSeries.constantCoeff.comp (scalarExpansion (L := L) z) =
    (algebraMap R L).comp (evalRingHom z) := by
  apply RingHom.ext
  intro p
  change PowerSeries.constantCoeff (expansion _ (p.map _))=_
  rw [constant_expansion]
  exact eval_map_apply ..

/-- The generic coefficient map sends the scalar variable into its rational function field. -/
def genericCoeffs : R[X] →+* FractionRing L[X] :=
  (algebraMap L[X] (FractionRing L[X])).comp (mapRingHom (algebraMap R L))

/-- Embed the scalar rational function field into fractions of the power series ring. -/
def fieldExpansion (z : L) : FractionRing L[X] →+* FractionRing L⟦X⟧ :=
  IsFractionRing.lift (g:=(algebraMap L⟦X⟧ (FractionRing L⟦X⟧)).comp (expansion z))
    ((IsFractionRing.injective L⟦X⟧ (FractionRing L⟦X⟧)).comp
    (expansion_injective z) : Function.Injective
      ((algebraMap L⟦X⟧ (FractionRing L⟦X⟧)).comp (expansion z)))

theorem fieldExpansion_coeffs (z : R) :
    (fieldExpansion (algebraMap R L z)).comp (genericCoeffs (R := R) (L := L)) =
      (algebraMap L⟦X⟧ (FractionRing L⟦X⟧)).comp (scalarExpansion z) := by
  apply RingHom.ext
  intro p
  unfold fieldExpansion genericCoeffs
  simp only [RingHom.comp_apply,IsFractionRing.lift_algebraMap]
  rfl

/-- The actual simple section induces a map of the generic root algebra
into formal Laurent fractions. Every element integral over the plane coefficient
ring specializes to an ordinary element of the base, with its value determined
by the constant term of the formal branch. -/
theorem simple_section [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R L]
    (F : R[X][X]) (z q : R) (hl : (F.leadingCoeff).eval z ≠ 0)
    (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0) :
    let P := F.map (genericCoeffs (R := R) (L := L))
    let i := (AdjoinRoot.of P).comp (genericCoeffs (R := R) (L := L))
    ∃ (y : L⟦X⟧) (φ : AdjoinRoot P →+* FractionRing L⟦X⟧),
      PowerSeries.constantCoeff y = algebraMap R L q ∧
      φ (AdjoinRoot.root P) = algebraMap L⟦X⟧ (FractionRing L⟦X⟧) y ∧
      φ.comp i = (algebraMap L⟦X⟧ (FractionRing L⟦X⟧)).comp (scalarExpansion z) ∧
      ∀ x : AdjoinRoot P, i.IsIntegralElem x → ∃ (s : L⟦X⟧) (r : R),
        algebraMap L⟦X⟧ (FractionRing L⟦X⟧) s = φ x ∧
        algebraMap R L r = PowerSeries.constantCoeff s := by
  let j := algebraMap R L
  let t := scalarExpansion (L := L) z
  let J := algebraMap L⟦X⟧ (FractionRing L⟦X⟧)
  let P := F.map (genericCoeffs (R := R) (L := L))
  let f := F.map t
  let l := fieldExpansion (j z)
  have hconst (a : R[X]) : PowerSeries.constantCoeff (t a) = j (a.eval z) :=
    DFunLike.congr_fun (scalar_constant (L := L) z) a
  have he (F' : R[X][X]) : PowerSeries.constantCoeff ((F'.map t).eval (PowerSeries.C (j q))) =
      j ((F'.map (evalRingHom z)).eval q) := by
    simp only [eval_map,hom_eval₂,PowerSeries.constantCoeff_C]
    rw [scalar_constant]
  have hn : j (F.leadingCoeff.eval z) ≠ 0 := by
    simpa only [j,map_zero] using (IsFractionRing.injective R L).ne hl
  have htl : t F.leadingCoeff ≠ 0 := fun h =>
    hn (by simpa only [h,map_zero] using (hconst F.leadingCoeff).symm)
  have hlead : IsUnit f.leadingCoeff := by
    rw [show f.leadingCoeff=t F.leadingCoeff from leadingCoeff_map_of_leadingCoeff_ne_zero _ htl,
      PowerSeries.isUnit_iff_constantCoeff,hconst,isUnit_iff_ne_zero]
    exact hn
  have hf₀ : PowerSeries.constantCoeff (f.eval (PowerSeries.C (j q))) = 0 := by
    rw [he,h₀,map_zero]
  have hf₁ : PowerSeries.constantCoeff (f.derivative.eval (PowerSeries.C (j q))) ≠ 0 := by
    change PowerSeries.constantCoeff ((F.map t).derivative.eval _)≠0
    rw [derivative_map,he]
    simpa only [j,map_zero] using (IsFractionRing.injective R L).ne h₁
  obtain ⟨y,hy,hy₀⟩ := simple_lift f (j q) hlead hf₀ hf₁
  have hroot : P.eval₂ l (J y)=0 := by
    change (F.map _).eval₂ l (J y)=0
    rw [eval₂_map,fieldExpansion_coeffs,←hom_eval₂]
    rw [←eval_map]
    change J (f.eval y)=0
    rw [hy,map_zero]
  let φ := AdjoinRoot.lift l (J y) hroot
  have hφ : φ.comp ((AdjoinRoot.of P).comp (genericCoeffs (R := R) (L := L))) = J.comp t := by
    rw [←RingHom.comp_assoc,AdjoinRoot.lift_comp_of]
    exact fieldExpansion_coeffs z
  exact ⟨y,φ,hy₀,AdjoinRoot.lift_root hroot,hφ,fun x hx =>
    integral_residue _ φ t PowerSeries.constantCoeff (evalRingHom z) hφ (scalar_constant z) x hx⟩

/-- A single ring of branch-regular functions contains the entire integral
closure and the generic ordinate, even when that ordinate is not integral.
Every scalar-ordinate polynomial evaluates at exactly the prescribed section. -/
theorem section_ring [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R L]
    (F : R[X][X]) (z q : R) (hl : F.leadingCoeff.eval z ≠ 0)
    (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0) :
    let P := F.map (genericCoeffs (R := R) (L := L))
    let i := (AdjoinRoot.of P).comp (genericCoeffs (R := R) (L := L))
    ∃ (O : Subring (AdjoinRoot P)) (σ : O →+* R),
      (∀ x, i.IsIntegralElem x → x ∈ O) ∧
      (∃ Y : O, (Y:AdjoinRoot P)=AdjoinRoot.root P ∧ σ Y=q) ∧
      ∀ G : R[X][X], ∃ x : O,
        (x : AdjoinRoot P) = AdjoinRoot.mk P (G.map (genericCoeffs (R := R) (L := L))) ∧
        σ x = (G.map (evalRingHom z)).eval q := by
  let j := algebraMap R L
  let J := algebraMap L⟦X⟧ (FractionRing L⟦X⟧)
  let t := scalarExpansion (L := L) z
  let P := F.map (genericCoeffs (R := R) (L := L))
  let i := (AdjoinRoot.of P).comp (genericCoeffs (R := R) (L := L))
  obtain ⟨y,φ,hy,hroot,hφ,hint⟩ := simple_section (L := L) F z q hl h₀ h₁
  let O := branchRing φ J PowerSeries.constantCoeff j
  obtain ⟨σ,hσ⟩ := branch_hom φ J PowerSeries.constantCoeff j
    (IsFractionRing.injective _ _) (IsFractionRing.injective _ _)
  have hu : AdjoinRoot.root P∈O := ⟨y,q,hroot.symm,hy.symm⟩
  refine ⟨O,σ,hint,⟨⟨_,hu⟩,rfl,hσ _ y q hroot.symm hy.symm⟩,?_⟩
  intro G
  let x := AdjoinRoot.mk P (G.map (genericCoeffs (R := R) (L := L)))
  let s := (G.map t).eval y
  let r := (G.map (evalRingHom z)).eval q
  have hx : J s=φ x := by
    change J ((G.map t).eval y) = φ (AdjoinRoot.mk P (G.map _))
    rw [←AdjoinRoot.aeval_eq,aeval_def,eval_map,eval₂_map,hom_eval₂,hom_eval₂]
    change _ = G.eval₂ (φ.comp i) (φ (AdjoinRoot.root P))
    rw [hφ,hroot]
  have hr : j r=PowerSeries.constantCoeff s := by
    simp only [r,s,eval_map,hom_eval₂,hy]
    rw [show PowerSeries.constantCoeff.comp t = j.comp (evalRingHom z) from scalar_constant z]
  have hmem : x ∈ O := ⟨s,r,hx,hr⟩
  exact ⟨⟨x,hmem⟩,rfl,hσ _ s r hx hr⟩

/-- The generic root algebra over the scalar rational function field. -/
abbrev Curve (F : R[X][X]) := AdjoinRoot (F.map (genericCoeffs (R := R) (L := L)))

/-- The inclusion of the original scalar polynomial ring in the generic root algebra. -/
def planeBase (F : R[X][X]) : R[X] →+* Curve (L := L) F :=
  (AdjoinRoot.of _).comp (genericCoeffs (R := R) (L := L))

/-- A polynomial evaluated at the generic ordinate. -/
def planeValue (F G : R[X][X]) : Curve (L := L) F :=
  AdjoinRoot.mk _ (G.map (genericCoeffs (R := R) (L := L)))

/-- Actual specialized divisibility for a tangent derivative presented as a
ratio of two scalar-ordinate polynomials. The geometric input is preservation
of the integral closure by the derivation on the generic root field. -/
theorem section_derivative_divides [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R L]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (z q : R) (hl : F.leadingCoeff.eval z ≠ 0)
    (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0)
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD : ∀ x, (planeBase (L := L) F).IsIntegralElem x →
      (planeBase (L := L) F).IsIntegralElem (D x))
    (a : R[X]) (ha : AdjoinRoot.root _ ≠ planeBase (L := L) F a)
    (N Q : R[X][X]) (hv : planeValue (L := L) F Q * D (AdjoinRoot.root _) = planeValue F N) :
    (Q.map (evalRingHom z)).eval q ∣ (F.eval a).eval z * (N.map (evalRingHom z)).eval q := by
  let P := F.map (genericCoeffs (R := R) (L := L))
  let i := planeBase (L := L) F
  let Y := AdjoinRoot.root P
  have hroot : F.eval₂ i Y=0 := by
    change F.eval₂ ((AdjoinRoot.of P).comp _) Y=0
    rw [←eval₂_map]
    exact AdjoinRoot.eval₂_root P
  obtain ⟨O,σ,hint,⟨y,hy,_⟩,hpoly⟩ := section_ring (L := L) F z q hl h₀ h₁
  have hY : Y ∈ O := by change AdjoinRoot.root _∈O; rw [←hy]; exact y.property
  have hreg := derivative_regular i F Y hroot D hD O hint hY a ha
  let b : O := ⟨i (F.eval a) * D Y,hreg⟩
  obtain ⟨A',hA,hσA⟩ := hpoly (C (F.eval a))
  obtain ⟨Q',hQ,hσQ⟩ := hpoly Q
  obtain ⟨N',hN,hσN⟩ := hpoly N
  have hA' : (A':Curve (L := L) F)=i (F.eval a) := by simpa [i,planeBase] using hA
  have hh : A'*N'=Q'*b := by
    apply Subtype.ext
    change (A':Curve (L := L) F)*(N':Curve (L := L) F) =
      (Q':Curve (L := L) F)*(i (F.eval a) * D Y)
    rw [hA',hN,hQ,mul_left_comm]
    exact congrArg (i (F.eval a)*·) hv.symm
  have hr := congrArg σ hh
  simp only [map_mul,hσA,hσN,hσQ,map_C,eval_C,coe_evalRingHom] at hr
  exact ⟨σ b,hr⟩

private theorem planeValue_eq_eval₂ (F G : R[X][X]) :
    planeValue (L := L) F G = G.eval₂ (planeBase (L := L) F) (AdjoinRoot.root _) := by
  unfold planeValue planeBase
  rw [←eval₂_map,←AdjoinRoot.algebraMap_eq,←aeval_def,AdjoinRoot.aeval_eq]

/-- Specialized denominator divisibility obtained from implicit differentiation
itself. The numerator here is the polynomial with the base derivation applied
to every coefficient of the generic equation. -/
theorem implicit_derivative_divides [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R L]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (z q : R) (hl : F.leadingCoeff.eval z ≠ 0)
    (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0)
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD : ∀ x, (planeBase (L := L) F).IsIntegralElem x →
      (planeBase (L := L) F).IsIntegralElem (D x))
    (δ : Derivation ℤ R[X] R[X]) (hδ : ∀ c, D (planeBase (L := L) F c) = planeBase F (δ c))
    (a : R[X]) (ha : AdjoinRoot.root _ ≠ planeBase (L := L) F a) :
    (F.derivative.map (evalRingHom z)).eval q ∣
      (F.eval a).eval z * ((coefficientDerivative δ F).map (evalRingHom z)).eval q := by
  let i := planeBase (L := L) F
  let Y := AdjoinRoot.root (F.map (genericCoeffs (R := R) (L := L)))
  have hF : F.eval₂ i Y=0 := by
    change F.eval₂ ((AdjoinRoot.of _).comp _) Y=0
    rw [←eval₂_map]
    exact AdjoinRoot.eval₂_root _
  have hh := coefficient_chain i δ D hδ Y F
  rw [hF,map_zero] at hh
  have hv : planeValue (L := L) F F.derivative * D Y =
      planeValue F (-(coefficientDerivative δ F)) := by
    simp only [planeValue_eq_eval₂,eval₂_neg]
    change F.derivative.eval₂ i Y * D Y= -(coefficientDerivative δ F).eval₂ i Y
    linear_combination -hh
  have hc := section_derivative_divides F z q hl h₀ h₁ D hD a ha _ _ hv
  simpa only [Polynomial.map_neg,eval_neg,mul_neg,dvd_neg] using hc

end Section

end ArkLib.ProximityGap.NormalizedSectionSpecialization

#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.reciprocal_integral
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.simple_lift
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.integral_residue
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.simple_section
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.section_ring
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.section_derivative_divides
#print axioms ArkLib.ProximityGap.NormalizedSectionSpecialization.implicit_derivative_divides
