/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LogarithmicSectionHeights
import ArkLib.Research.ProximityGap.Frontier.HeightOneNormalization

/-! # Specializing the tangent at a repeated received root -/

namespace ArkLib.ProximityGap.RepeatedSectionSpecialization

open Polynomial NormalizedSectionSpecialization HeightOneNormalization

/-- A polynomial of a rational ordinate can be cleared by a power of any common denominator. -/
private theorem clear_evaluation {A E : Type*} [CommRing A] [CommRing E]
    (C : Subring E) (i : A →+* E) (hi : ∀ a, i a ∈ C) (s y : E)
    (hs : s ∈ C) (hsy : s * y ∈ C) (P : A[X]) :
    ∃ n : ℕ, s^n * P.eval₂ i y ∈ C := by
  induction P using Polynomial.induction_on' with
  | monomial n a =>
    refine ⟨n, ?_⟩
    rw [eval₂_monomial, show s^n * (i a * y^n) = i a * (s*y)^n by ring]
    exact C.mul_mem (hi a) (C.pow_mem hsy n)
  | add P Q hP hQ =>
    obtain ⟨m, hm⟩ := hP
    obtain ⟨n, hn⟩ := hQ
    refine ⟨m+n, ?_⟩
    rw [eval₂_add, pow_add, show s^m*s^n*(P.eval₂ i y+Q.eval₂ i y) =
      s^n*(s^m*P.eval₂ i y)+s^m*(s^n*Q.eval₂ i y) by ring]
    exact C.add_mem (C.mul_mem (C.pow_mem hs _) hm) (C.mul_mem (C.pow_mem hs _) hn)

private def restrictDerivation {E : Type*} [Field E] [Algebra ℤ E] (C : Subring E)
    (D : Derivation ℤ E E) (h : ∀ x ∈ C, D x ∈ C) : Derivation ℤ C C :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun x ↦ ⟨D (x:E), h x x.property⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y ↦ Subtype.ext (by simp) })
    (fun x y ↦ Subtype.ext (D.leibniz _ _))

/-- A nonvanishing cofactor may be canceled at the residue point before differentiating a
repeated root, even when it has no global inverse. -/
private theorem weighted_vanishing {C k : Type*} [CommRing C] [Field k]
    (D : Derivation ℤ C C) (φ : C →+* k) (π h t q : C) (j : ℕ)
    (hπ : D π = 0) (hp : φ π = 0) (hh : φ h = 0) (ht : φ t ≠ 0)
    (hj : 0 < j) (hfact : (j.factorial : k) ≠ 0) (heq : h ^ j * t = π * q) : φ (D h) = 0 := by
  let I : Ideal C := Ideal.span {π}
  have stable (x : C) (hx : x ∈ I) : D x ∈ I := by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [D.leibniz, hπ]
    simp only [smul_eq_mul, mul_zero, add_zero]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  have kill (x : C) (hx : x ∈ I) : φ x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    simp [hp]
  have hi : (h*t)^j ∈ I := by
    cases j with
    | zero => omega
    | succ n =>
      apply Ideal.mem_span_singleton.mpr
      refine ⟨q*t^n, ?_⟩
      rw [mul_pow, pow_succ' t, ← mul_assoc, heq, mul_assoc]
  have hz := Frontier.LogarithmicSectionHeights.derivative_vanishes D I stable φ kill
    (h*t) j (by simp [hh]) hfact hi
  rw [D.leibniz] at hz
  simpa [smul_eq_mul, hh, ht] using hz

variable {A E k : Type*} [CommRing A] [Field E] [Algebra ℤ E] [Field k]

/-- The scaled tangent to a repeated received root lies in the section ring and vanishes at
its actual residue point. Good anchors and good cofactors need only be nonzero at that point.
The original generic ordinate need not be integral over the base. -/
theorem repeated_site_clearance (O : Subring E) (r : A →+* O) (y : O) (φ : O →+* k)
    (F : A[X]) (a ℓ π : A) (B Q : A[X]) (j : ℕ) (D : Derivation ℤ E E)
    (hD : ∀ x, (O.subtype.comp r).IsIntegralElem x → (O.subtype.comp r).IsIntegralElem (D x))
    (hO : ∀ x, (O.subtype.comp r).IsIntegralElem x → x ∈ O)
    (hF : F.eval₂ r y = 0) (hA : φ (r (F.eval a)) ≠ 0)
    (hπ : D (r π : E) = 0) (hp : φ (r π) = 0) (hy : φ y = φ (r ℓ))
    (hB : φ (B.eval₂ r y) ≠ 0) (hj : 0 < j) (hfact : (j.factorial : k) ≠ 0)
    (heq : (y - r ℓ) ^ j * B.eval₂ r y = r π * Q.eval₂ r y) :
    ∃ g : O, (g:E) = (r (F.eval a):E) * D ((y:E)-(r ℓ:E)) ∧ φ g = 0 := by
  have ha : (y:E) ≠ (r a:E) := by
    intro hh
    rw [show y = r a from Subtype.ext hh, eval₂_at_apply] at hF
    exact hA (by rw [hF, map_zero])
  let i := O.subtype.comp r
  let : Algebra A E := i.toAlgebra
  let C := (integralClosure A E).toSubring
  have hc : C ≤ O := fun x hx ↦ hO x hx
  let ι := Subring.inclusion hc
  let ψ := φ.comp ι
  let δ := restrictDerivation C D hD
  let s := i (F.eval a) / ((y:E)-i a)
  have hs : s ∈ C := reciprocal_integral i F a y
    (by simpa [hF] using (hom_eval₂ F r O.subtype y).symm)
  let sc : C := ⟨s, hs⟩
  let so : O := ι sc
  have he : s*((y:E)-i a) = i (F.eval a) := div_mul_cancel₀ _ (sub_ne_zero.mpr ha)
  have heo : so*(y-r a) = r (F.eval a) := Subtype.ext he
  have hso : φ so ≠ 0 := by
    intro hz
    apply hA
    rw [← heo, map_mul, hz, zero_mul]
  have hb (x : A) : i x ∈ C := i.isIntegralElem_map
  have hsy : s*(y:E) ∈ C := by
    rw [show s*(y:E) = i (F.eval a)+s*i a by linear_combination he]
    exact C.add_mem (hb _) (C.mul_mem hs (hb _))
  let h : C := ⟨s*((y:E)-i ℓ), by
    rw [mul_sub]
    exact C.sub_mem hsy (C.mul_mem hs (hb _))⟩
  have hho : ι h = so*(y-r ℓ) := rfl
  have hψ : ψ h = 0 := by
    change φ (ι h) = 0
    rw [hho, map_mul, map_sub, hy, sub_self, mul_zero]
  obtain ⟨b, hb'⟩ := clear_evaluation C i hb s y hs hsy B
  obtain ⟨d, hd'⟩ := clear_evaluation C i hb s y hs hsy Q
  let t : C := ⟨s^d * (s^b * B.eval₂ i y), C.mul_mem (C.pow_mem hs _) hb'⟩
  let q : C := ⟨s^j * s^b * (s^d * Q.eval₂ i y),
    C.mul_mem (C.mul_mem (C.pow_mem hs _) (C.pow_mem hs _)) hd'⟩
  have hco (P : A[X]) : ((P.eval₂ r y:O):E) = P.eval₂ i (y:E) := hom_eval₂ P r O.subtype y
  have hto : ι t = so^d*(so^b*B.eval₂ r y) := by
    apply Subtype.ext
    change s^d * (s^b * B.eval₂ i y) = s^d * (s^b * ((B.eval₂ r y:O):E))
    rw [hco]
  have hψt : ψ t ≠ 0 := by
    change φ (ι t) ≠ 0
    rw [hto, map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hso) (mul_ne_zero (pow_ne_zero _ hso) hB)
  let pc : C := ⟨i π, hb _⟩
  have hrel : h^j*t = pc*q := by
    apply Subtype.ext
    have heq' := congrArg (fun u : O ↦ (u:E)) heq
    change ((y:E)-i ℓ)^j * ((B.eval₂ r y:O):E) = i π * ((Q.eval₂ r y:O):E) at heq'
    rw [hco, hco] at heq'
    change (s*((y:E)-i ℓ))^j * (s^d*(s^b*B.eval₂ i y)) =
      i π*(s^j*s^b*(s^d*Q.eval₂ i y))
    rw [mul_pow]
    linear_combination s^j*s^b*s^d*heq'
  have hz := weighted_vanishing δ ψ pc h t q j (Subtype.ext hπ) hp hψ hψt hj hfact hrel
  let ds := ι (δ sc)
  let dh := ι (δ h)
  let g := (y-r a)*(dh - (y-r ℓ)*ds)
  refine ⟨g, ?_, ?_⟩
  · have hdiff := D.leibniz s ((y:E)-i ℓ)
    change D (s*((y:E)-i ℓ)) = s*D ((y:E)-i ℓ) + ((y:E)-i ℓ)*D s at hdiff
    change ((y:E)-i a) * (D (s*((y:E)-i ℓ))-((y:E)-i ℓ)*D s) =
      i (F.eval a)*D ((y:E)-i ℓ)
    rw [hdiff]
    linear_combination D ((y:E)-i ℓ)*he
  · change φ ((y-r a)*(dh - (y-r ℓ)*ds)) = 0
    simp only [map_mul, map_sub, hy, sub_self, zero_mul, sub_zero]
    rw [show φ dh = 0 from hz, mul_zero]

private theorem fiber_remainder {R k : Type*} [CommRing R] [Field k]
    (ev : R →+* k) (π : R) (hker : ∀ r, ev r = 0 → π ∣ r)
    (P : R[X][X]) (hP : P.map (mapRingHom ev) = 0) :
    C (C π) ∣ P := by
  refine (C_dvd_iff_dvd_coeff _ _).mpr fun n ↦ (C_dvd_iff_dvd_coeff _ _).mpr fun m ↦ hker _ ?_
  have h := congrArg (fun f : k[X][X] ↦ (f.coeff n).coeff m) hP
  simpa using h

section Plane

variable {R L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field L]
  [Algebra R L] [IsFractionRing R L]

/-- A simple section through a repeated received root has a polynomial scaled tangent
whose value at the specified site vanishes. Its polynomial identity with the implicit
derivative holds on the entire section, including degree drops of the specialized fiber. -/
theorem section_tangent_vanishes (F : R[X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (z q : R) (hl : F.leadingCoeff.eval z ≠ 0) (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0)
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD : ∀ x, (planeBase (L := L) F).IsIntegralElem x → (planeBase F).IsIntegralElem (D x))
    (δ : Derivation ℤ R[X] R[X]) (hδ : ∀ c, D (planeBase (L := L) F c) = planeBase F (δ c))
    (a ℓ : R[X])
    (ev : R →+* k) (π : R) (hker : ∀ r, ev r = 0 → π ∣ r) (hp : ev π = 0)
    (hdπ : δ (C π) = 0) (hy : ev q = ev (ℓ.eval z)) (hA : ev ((F.eval a).eval z) ≠ 0)
    (j : ℕ) (hj : 0 < j) (hfact : (j.factorial : k) ≠ 0) (B : R[X][X])
    (hB : ev ((B.map (evalRingHom z)).eval q) ≠ 0)
    (hfac : F.map (mapRingHom ev) = (X - C (ℓ.map ev)) ^ j * B.map (mapRingHom ev)) :
    ∃ g : R, ev g = 0 ∧ (F.derivative.map (evalRingHom z)).eval q * g =
      - (F.eval a).eval z * (((coefficientDerivative δ F).map (evalRingHom z)).eval q +
        (F.derivative.map (evalRingHom z)).eval q * (δ ℓ).eval z) := by
  let i := planeBase (L := L) F
  let Y := AdjoinRoot.root (F.map (genericCoeffs (R := R) (L := L)))
  obtain ⟨O, σ, hi, y, hpoly⟩ := section_ring (L := L) F z q hl h₀ h₁
  obtain ⟨y, hyY, hyq⟩ := y
  let r : R[X] →+* O := i.codRestrict O fun _ ↦ hi _ i.isIntegralElem_map
  have hy' : (y : Curve (L := L) F) = Y := hyY
  have hev (P : R[X][X]) : ((P.eval₂ r y : O) : Curve (L := L) F) = P.eval₂ i Y := by
    rw [show i = O.subtype.comp r from rfl, ← hy']
    exact hom_eval₂ P r O.subtype y
  have hP (P : R[X][X]) : σ (P.eval₂ r y) = (P.map (evalRingHom z)).eval q := by
    obtain ⟨v, hv, hv'⟩ := hpoly P
    have he : v = P.eval₂ r y := by
      apply Subtype.ext
      rw [hv, hev]
      change _ = P.eval₂ ((AdjoinRoot.of _).comp _) Y
      rw [← eval₂_map, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
    rwa [← he]
  have hr (c : R[X]) : σ (r c) = c.eval z := by simpa using hP (C c)
  have hF : F.eval₂ r y = 0 := by
    apply Subtype.ext
    rw [hev]
    change F.eval₂ ((AdjoinRoot.of _).comp _) Y = 0
    rw [← eval₂_map]
    exact AdjoinRoot.eval₂_root _
  obtain ⟨Q, hQ⟩ := fiber_remainder ev π hker ((X-C ℓ)^j*B-F) (by simp [hfac])
  have heq : (y-r ℓ)^j * B.eval₂ r y = r (C π) * Q.eval₂ r y := by
    have h := congrArg (fun p : R[X][X] ↦ p.eval₂ r y) hQ
    simpa [hF, eval₂_pow] using h
  let φ := ev.comp σ
  obtain ⟨g, hg, hzero⟩ := repeated_site_clearance O r y φ F a ℓ (C π) B Q j D hD hi hF
    (by simpa [φ, hr] using hA)
    (by change D (i (C π)) = 0; rw [hδ, hdπ, map_zero])
    (by simp [φ, hr, hp]) (by simpa [φ, hr, hyq] using hy)
    (by simpa [φ, hP] using hB) hj hfact heq
  refine ⟨σ g, hzero, ?_⟩
  have hfzero : F.eval₂ i Y = 0 := by rw [← hev, hF]; rfl
  have hd := coefficient_chain i δ D hδ Y F
  rw [hfzero, map_zero] at hd
  have he : F.derivative.eval₂ r y * g =
      -r (F.eval a)*((coefficientDerivative δ F).eval₂ r y + F.derivative.eval₂ r y * r (δ ℓ)) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_neg, Subring.coe_add, hev, hg, hy', map_sub]
    change F.derivative.eval₂ i Y * (i (F.eval a) * (D Y - D (i ℓ))) = _
    rw [hδ]
    change _ = -i (F.eval a) * ((coefficientDerivative δ F).eval₂ i Y +
      F.derivative.eval₂ i Y * i (δ ℓ))
    linear_combination -i (F.eval a)*hd
  simpa only [map_mul, map_add, map_neg, hP, hr] using congrArg σ he

omit [IsIntegrallyClosed R] in
private theorem reduced_value {T A H W u g N Q : R} (ev : R →+* k) (hT : T ≠ 0)
    (hA : ev A ≠ 0) (hH : ev H ≠ 0) (hg : ev g = 0)
    (he : T * g = -A * (H * W + T * (H * u))) (hv : T * N = -W * Q)
    (hcop : IsCoprime Q N) : ev Q ≠ 0 ∧ ev N = ev Q * ev u := by
  have hc : A*H*N = Q*(g+A*H*u) := by
    apply mul_left_cancel₀ hT
    linear_combination A*H*hv-Q*he
  have hd : Q ∣ A*H := hcop.dvd_of_dvd_mul_right ⟨_, hc⟩
  have hAH : ev (A*H) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hA hH
  have hQ : ev Q ≠ 0 := by
    obtain ⟨s, hs⟩ := hd
    intro hz
    exact hAH (by rw [hs, map_mul, hz, zero_mul])
  refine ⟨hQ, mul_left_cancel₀ hAH ?_⟩
  have hz := congrArg ev hc
  simp only [map_mul, map_add, hg, zero_add] at hz ⊢
  linear_combination hz

/-- Differentiate in the scalar variable while fixing the coefficient ring. -/
noncomputable def scalarDerivative (R : Type*) [CommRing R] : Derivation ℤ R[X] R[X] :=
  Polynomial.derivative'.restrictScalars ℤ

omit [IsDomain R] [IsIntegrallyClosed R] in
private theorem coeff_scaled (H : R[X]) (F : R[X][X]) :
    coefficientDerivative (H • scalarDerivative R) F =
      C H * coefficientDerivative (scalarDerivative R) F := by
  ext n
  rw [coeff_C_mul]
  rfl

/-- With a reduced numerator and denominator for the scalar tangent, the denominator is
nonzero at a good repeated site and the tangent agrees with the derivative of the received line. -/
theorem reduced_section_tangent (F : R[X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (z q : R) (hl : F.leadingCoeff.eval z ≠ 0) (h₀ : (F.map (evalRingHom z)).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom z)).eval q ≠ 0)
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD : ∀ x, (planeBase (L := L) F).IsIntegralElem x → (planeBase F).IsIntegralElem (D x))
    (H : R[X]) (hδ : ∀ c, D (planeBase (L := L) F c) = planeBase F (H * c.derivative))
    (a ℓ : R[X])
    (ev : R →+* k) (π : R) (hker : ∀ r, ev r = 0 → π ∣ r) (hp : ev π = 0)
    (hy : ev q = ev (ℓ.eval z)) (hA : ev ((F.eval a).eval z) ≠ 0) (hH : ev (H.eval z) ≠ 0)
    (j : ℕ) (hj : 0 < j) (hfact : (j.factorial : k) ≠ 0) (B : R[X][X])
    (hB : ev ((B.map (evalRingHom z)).eval q) ≠ 0)
    (hfac : F.map (mapRingHom ev) = (X - C (ℓ.map ev)) ^ j * B.map (mapRingHom ev))
    (N Q : R) (hcop : IsCoprime Q N)
    (hv : (F.derivative.map (evalRingHom z)).eval q * N =
      -((coefficientDerivative (scalarDerivative R) F).map (evalRingHom z)).eval q * Q) :
    ev Q ≠ 0 ∧ ev N = ev Q * ev (ℓ.derivative.eval z) := by
  obtain ⟨g, hg, he⟩ := section_tangent_vanishes F z q hl h₀ h₁ D hD
    (H • scalarDerivative R) hδ a ℓ ev π hker hp
    (show H * (C π).derivative = 0 by simp) hy hA j hj hfact B hB hfac
  apply reduced_value ev h₁ hA hH hg _ hv hcop
  rw [coeff_scaled] at he
  change _ = _ * (_ + _ * (H * ℓ.derivative).eval z) at he
  simpa only [Polynomial.map_mul, map_C, eval_mul, eval_C, coe_evalRingHom] using he

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- A good reduced fiber has a constant avoiding its ordinate roots in every field
with more elements than the value degree. Surjectivity lifts that constant to the original base. -/
private theorem anchor (ev : R →+* k) (hsur : Function.Surjective ev)
    (F B : R[X][X]) (z q : R) (ℓ : R[X]) (j : ℕ)
    (hcard : (F.natDegree : Cardinal) < Cardinal.mk k)
    (hB : ev ((B.map (evalRingHom z)).eval q) ≠ 0)
    (hfac : F.map (mapRingHom ev) = (X - C (ℓ.map ev)) ^ j * B.map (mapRingHom ev)) :
    ∃ a : R[X], ev ((F.eval a).eval z) ≠ 0 := by
  let v := ev.comp (evalRingHom z)
  have hcomm : v = (evalRingHom (ev z)).comp (mapRingHom ev) := by
    ext <;> simp [v]
  have hB' : (B.map v).eval (ev q) ≠ 0 := by
    simpa only [v, eval_map, ← hom_eval₂] using hB
  have hF : F.map v ≠ 0 := by
    have hm := congrArg (fun P : k[X][X] ↦ P.map (evalRingHom (ev z))) hfac
    simp only [map_map, ← hcomm, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_sub, map_X, map_C] at hm
    rw [hm]
    apply mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
    exact fun hz ↦ hB' (by rw [hz, eval_zero])
  have hdeg : ((F.map v).natDegree : Cardinal) ≤ F.natDegree := by exact_mod_cast natDegree_map_le
  obtain ⟨a, ha⟩ := exists_eval_ne_zero_of_natDegree_lt_card (F.map v) hF (hdeg.trans_lt hcard)
  obtain ⟨a', rfl⟩ := hsur a
  refine ⟨C a', ?_⟩
  change v (F.eval (C a')) ≠ 0
  rw [← eval₂_at_apply, ← eval_map]
  simpa [v] using ha

end Plane

section Received

variable {L : Type*} [Field L] [Algebra k[X] L] [IsFractionRing k[X] L]

/-- Lift a received affine line at one coordinate to the scalar polynomial over the base. -/
noncomputable def receivedLine (u₀ u₁ : k) : k[X][X] :=
  C (C u₀) + C (C u₁)*X

/-- Reduced numerator and denominator of the actual implicit scalar tangent. -/
noncomputable def tangentPair (F : k[X][X][X]) (z : k) (q : k[X]) : k[X] × k[X] :=
  let t := (F.derivative.map (evalRingHom (C z))).eval q
  let w := ((coefficientDerivative (scalarDerivative k[X]) F).map (evalRingHom (C z))).eval q
  let v := -algebraMap k[X] L w / algebraMap k[X] L t
  (IsFractionRing.num k[X] v, IsFractionRing.den k[X] v)

private theorem tangentPair_spec (F : k[X][X][X]) (z : k) (q : k[X])
    (ht : (F.derivative.map (evalRingHom (C z))).eval q ≠ 0) :
    let t := (F.derivative.map (evalRingHom (C z))).eval q
    let w := ((coefficientDerivative (scalarDerivative k[X]) F).map (evalRingHom (C z))).eval q
    let v := tangentPair (L := L) F z q
    IsCoprime v.2 v.1 ∧ t*v.1 = -w*v.2 := by
  let t := (F.derivative.map (evalRingHom (C z))).eval q
  let w := ((coefficientDerivative (scalarDerivative k[X]) F).map (evalRingHom (C z))).eval q
  let v := -algebraMap k[X] L w / algebraMap k[X] L t
  refine ⟨(IsFractionRing.num_den_reduced k[X] v).symm.isCoprime, ?_⟩
  apply IsFractionRing.injective k[X] L
  change algebraMap k[X] L (t*IsFractionRing.num k[X] v) =
    algebraMap k[X] L (-w*(IsFractionRing.den k[X] v : k[X]))
  have h := (IsFractionRing.num_mul_den_eq_num_iff_eq (A := k[X]) (x := v) (y := v)).mpr rfl
  have h₁ : algebraMap k[X] L t ≠ 0 := by simpa using (IsFractionRing.injective k[X] L).ne ht
  rw [map_mul, map_mul, map_neg, ← h]
  dsimp only [v]
  field_simp

/-- At a good site of any multiplicity below the characteristic, the reduced tangent pair
has nonzero denominator and agrees with both received rows. The good anchor is constructed. -/
theorem received_tangent (F : k[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := k[X]) (L := L))))]
    (x z u₀ u₁ : k) (q : k[X]) (hl : F.leadingCoeff.eval (C z) ≠ 0)
    (h₀ : (F.map (evalRingHom (C z))).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom (C z))).eval q ≠ 0)
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD : regularOnPlaneBranches F D)
    (H : k[X][X]) (hδ : ∀ c, D (planeBase (L := L) F c) = planeBase F (H * c.derivative))
    (hH : (H.eval (C z)).eval x ≠ 0) (hy : q.eval x = u₀ + z * u₁)
    (j : ℕ) (hj : 0 < j) (hfact : (j.factorial : k) ≠ 0)
    (hcard : (F.natDegree : Cardinal) < Cardinal.mk k)
    (B : k[X][X]) (hB : (B.map (evalRingHom z)).eval (q.eval x) ≠ 0)
    (hfac : F.map (mapRingHom (evalRingHom x)) = (X - C (C u₀ + C u₁ * X)) ^ j * B) :
    let v := tangentPair (L := L) F z q
    v.2.eval x ≠ 0 ∧ v.1.eval x = u₁*v.2.eval x ∧
      q.eval x*v.2.eval x-z*v.1.eval x = u₀*v.2.eval x := by
  let N := (tangentPair (L := L) F z q).1
  let Q := (tangentPair (L := L) F z q).2
  obtain ⟨hcop, hv⟩ := tangentPair_spec (L := L) F z q h₁
  have hnorm := plane_regular_preserves_normalization F (C z) q h₁ D hD
  let ev := evalRingHom x
  let s := (C : k →+* k[X])
  let ell := receivedLine u₀ u₁
  let B' := B.map (mapRingHom s)
  have hv0 : ev.comp s = RingHom.id k := by ext a; exact eval_C
  have hline : ell.map ev = C u₀+C u₁*X := by simp [ell, receivedLine, ev]
  have hBmap : B'.map (mapRingHom ev) = B := by
    simp only [B', map_map, mapRingHom_comp, hv0, mapRingHom_id, map_id]
  have hf : F.map (mapRingHom ev) = (X-C (ell.map ev))^j * B'.map (mapRingHom ev) := by
    rw [hline, hBmap]; exact hfac
  have hφ : ev.comp (evalRingHom (C z)) = (evalRingHom z).comp (mapRingHom ev) := by
    ext <;> simp [ev]
  have hB' : ev ((B'.map (evalRingHom (C z))).eval q) ≠ 0 := by
    rw [eval_map, hom_eval₂, hφ, ← eval₂_map, hBmap, ← eval_map]
    exact hB
  obtain ⟨a, ha⟩ := anchor ev (fun b ↦ ⟨C b, eval_C⟩) F B' (C z) q ell j hcard hB' hf
  have hy' : ev q = ev (ell.eval (C z)) := by
    simpa only [ell, receivedLine, ev, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X,
      mul_comm u₁ z] using hy
  obtain ⟨hQ, hN⟩ := reduced_section_tangent F (C z) q hl h₀ h₁ D hnorm H hδ a ell ev (X-C x)
    (fun _ hr ↦ dvd_iff_isRoot.mpr hr) (by simp [ev]) hy' ha hH j hj hfact B' hB' hf N Q hcop hv
  have hvel : N.eval x = u₁ * Q.eval x := by
    simpa only [ev, ell, receivedLine, coe_evalRingHom, derivative_add, derivative_C,
      derivative_C_mul_X, zero_add, eval_C, mul_comm (Q.eval x) u₁] using hN
  exact ⟨hQ, hvel, by rw [hy, hvel]; ring⟩

end Received

end ArkLib.ProximityGap.RepeatedSectionSpecialization

#print axioms ArkLib.ProximityGap.RepeatedSectionSpecialization.repeated_site_clearance
#print axioms ArkLib.ProximityGap.RepeatedSectionSpecialization.section_tangent_vanishes
#print axioms ArkLib.ProximityGap.RepeatedSectionSpecialization.received_tangent
