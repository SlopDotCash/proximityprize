/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChart
import ArkLib.Research.ProximityGap.Frontier.ApolarFixedPencil

/-! # Data for the sharp predecessor bound in a normalized pair of affine charts -/

open Finset Polynomial Matrix Code
open scoped NNReal
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarSparseSpecialization ProximityGap.ApolarChartNormalization
open ProximityGap.ApolarRootTransition ProximityGap.ApolarUnitChart
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.ApolarFixedPencil

namespace ProximityGap.ApolarUnitChartData

variable {K : Type*} [Field K] [DecidableEq K]

/-- The concrete binary polynomial on the chosen coordinate chart. All scalar
and coordinate labels retain their maps back to the original finite sets. -/
structure Data (H S : Finset K) (e d r l : ℕ) where
  parameterShift : K
  x : K
  z : K
  distinct : x ≠ z
  x_out : x ∉ H
  z_out : z ∉ H
  D : Finset K
  G : Finset K
  sites : D=H.image (site x z)
  parameters : ∀ t : K, t ∈ G ↔ t+parameterShift ∈ S
  card_sites : D.card=H.card
  card_parameters : G.card=S.card
  sites_unit : 0 ∉ D
  parameters_unit : 0 ∉ G
  f : K[X][X]
  degree : f.natDegree=r
  top_height : (f.coeff r).natDegree=l
  bottom_height : (f.coeff 0).natDegree=l
  bottom_nonzero : f.coeff 0≠0
  height : ∀ j, (f.coeff j).natDegree ≤ l
  primitive : ∀ t, f.map (evalRingHom t) ≠ 0
  w : K → K[X]
  weights_affine : ∀ y ∈ D, (w y).natDegree ≤ 1
  apolar : ApolarThrough (measure D (C : K → K[X]) w) f (d-r)
  minimal : ∀ b < r, ∀ p : K[X][X], p.natDegree ≤ b →
    ApolarThrough (measure D (C : K → K[X]) w) p (d-b) → p=0
  sparse : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ e ∧ ∃ b : K → K,
    (∀ p : K[X], p.natDegree ≤ d →
      ((measure D (C : K → K[X]) w) (p.map C)).eval t=weighted E (RingHom.id K) b p) ∧
    (∀ p : K[X], p.natDegree ≤ d →
      ((measure D (C : K → K[X]) w) ((reflect d p).map C)).eval t=
        weighted (E.image Inv.inv) (RingHom.id K) (fun y => b y⁻¹*(y⁻¹)^d) p)

/-- Normalize any affine sparse pencil with a positive-height minimal chart. -/
theorem normalize [Infinite K] (H S : Finset K) (m : ℕ → K[X]) (w : K → K[X])
    (hw : ∀ y ∈ H, (w y).natDegree ≤ 1) (e d r : ℕ) (hr : r ≤ d)
    (hm : ∀ j ≤ d, m j=∑ y ∈ H,w y*C (y^j))
    (hsp : ∀ t ∈ S, ∃ E ⊆ H, E.card ≤ e ∧ ∃ b : K → K,
      ∀ j ≤ d, (m j).eval t = ∑ y ∈ E, b y*y^j)
    (v : Fin (r+1) → K[X]) (hk : catalecticant m d r *ᵥ v=0)
    (hmin : ∀ b < r, ∀ p, catalecticant m d b *ᵥ p=0 → p=0)
    (hprim : ∀ t, (family v).eval (C t) ≠ 0)
    (x z : K) (hx : x ∉ H) (hz : z ∉ H) (hxz : x ≠ z) (hl : 0 < (family v).natDegree)
    (hxfull : ((family v).map (evalRingHom x)).natDegree=(family v).natDegree)
    (hzfull : ((family v).map (evalRingHom z)).natDegree=(family v).natDegree) :
    Nonempty (Data H S e d r (family v).natDegree) := by
  classical
  obtain ⟨a,_,G,hG,h0G,hmem⟩ := translate_parameters S
  let D := H.image (site x z)
  have h0D : 0 ∉ D := by
    intro h
    obtain ⟨y,hy,he⟩ := mem_image.mp h
    exact (isUnit_iff_ne_zero.mp (site_unit x z H hx hz hy)) he
  let f := locator a x z r (form v)
  let W := chartWeight a x z d w
  let L := normalizedFunctional m a x z d
  have heq (p : K[X][X]) (hp : p.natDegree ≤ d) : L p=measure D (C : K → K[X]) W p :=
    whole_measure m w H a x z hxz hz hm p hp
  obtain ⟨hdeg,hbottom,htop,hbot⟩ := locator_endpoints a x z (form v) hl (form_degree _)
    (by rwa [eval_form]) (by rwa [eval_form])
  have hcard : D.card=H.card := (ApolarCoordinateTransport.error_measure_substitute x z hxz H hz (fun _ => 0) d).1
  refine ⟨⟨a,x,z,hxz,hx,hz,D,G,rfl,hmem,hcard,hG,h0D,h0G,f,hdeg,htop,hbottom,hbot,
    locator_height v a x z,locator_no_zero_fiber a x z hxz _ (form_degree _) (primitive_form v hprim),
    W,chartWeight_degree a x z hxz H hz d w hw,?_,?_,?_⟩⟩
  · intro p hp
    have hd : (f*p).natDegree ≤ d := natDegree_mul_le.trans
      (by change f.natDegree+p.natDegree ≤ d; change f.natDegree=r at hdeg; omega)
    rw [←heq _ hd]
    exact normalized_apolar m hr v hk a x z hxz p hp
  · intro b hb p hp ha
    apply normalized_minimal m (by omega : b ≤ d) a x z hxz (hmin b hb) p hp
    intro q hq
    rw [show normalizedFunctional m a x z d (p*q) = measure D (C : K → K[X]) W (p*q) from
      heq _ (natDegree_mul_le.trans (by omega))]
    exact ha q hq
  · intro t ht
    obtain ⟨E,hE,hn,b,hb⟩ := hsp (t+a) ((hmem t).mp ht)
    let E' := E.image (site x z)
    have hE' : E' ⊆ D := image_subset_image hE
    obtain ⟨hcard',b',hb'⟩ := normalized_atoms m a x z t hxz E (fun h => hz (hE h)) b hb
    have hforward (p : K[X]) (hp : p.natDegree ≤ d) :
        ((measure D (C : K → K[X]) W) (p.map C)).eval t=weighted E' (RingHom.id K) b' p := by
      rw [←heq _ (natDegree_map_le.trans hp)]
      exact hb' p hp
    refine ⟨E',hE',hcard'.trans_le hn,b',hforward,?_⟩
    intro p hp
    exact (hforward (reflect d p) (natDegree_reflect_le.trans (max_le le_rfl hp))).trans
      (inverse_atoms E' (fun h => h0D (hE' h)) b' p hp)

/-- With more than e+1 actual bad parameters, the locator has positive coordinate
and parameter degrees. The finite data then exist on the coefficient extension,
with the sharp determinant degree estimate and the original domain cardinalities. -/
theorem of_mca_family {F L ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field L] [IsAlgClosed L] [Infinite L] [DecidableEq L]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (φ : F →+* L) {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hsize : e+1 < bad.card) (hed : e ≤ d) (hlen : 2*e ≤ d+1) (hk : 1 ≤ k)
    (hd : k+d < Fintype.card ι) (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) :
    let ψ : F ↪ L := ⟨φ,φ.injective⟩
    let H := ((univ : Finset ι).map dom).map ψ
    ∃ r ≤ e, ∃ l, 0<r ∧ 0<l ∧ (d+2-2*r)*l ≤ r ∧ Nonempty (Data H (bad.map ψ) e d r l) := by
  classical
  let ψ : F ↪ L := ⟨φ,φ.injective⟩
  let H₀ := (univ : Finset ι).map dom
  let H := H₀.map ψ
  let S := bad.map ψ
  let u₀ := ApolarMcaSyndrome.coordinateRow dom (u 0)
  let u₁ := ApolarMcaSyndrome.coordinateRow dom (u 1)
  let m (j : ℕ) := (ApolarHankelMinors.moment H₀ u₀ u₁ j).map φ
  have hbad (t : F) (ht : t ∈ bad) := (fam.mem_G_iff t).mp (hsub ht)
  obtain ⟨r,hre,hmin,v,hv,hker,hp,x,hx,z,hz,hxz,hxf,hzf,hc⟩ :=
    minimal_chart_of_mca_events φ dom u bad hsize hed hk hd he hbad H
  change catalecticant m d r *ᵥ v=0 at hker
  have hnon : form v ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun p : L[X][X] => p.coeff i.val) h
  have hapos : ApolarThrough (functional m) (form v) (d-r) := by
    apply (equations_iff_apolar m v).mp
    intro j hj
    exact congrFun hker ⟨j,by omega⟩
  have hfdeg := form_degree v
  have hr : 0<r := by
    by_contra! hn
    have hqdeg : (form v).natDegree=0 := by omega
    have hh := count_le_of_constant_quotient φ fam bad hsub (by omega) (1:L[X]) one_ne_zero
      (form v) hnon hqdeg (d-r) e hk (by simp; omega) he (by omega) (by simpa using hapos)
    rw [natDegree_one] at hh
    omega
  have hl : 0 < (family v).natDegree := by
    by_contra! hn
    let G := form (fun i => (v i).coeff 0)
    have hg : G.map C=form v := by
      rw [show G=form (fun i => (v i).coeff 0) from rfl,map_form]
      congr 1
      funext i
      exact (eq_C_of_natDegree_le_zero ((coefficient_height v i).trans hn)).symm
    have hG : G ≠ 0 := fun h => hnon (by rw [←hg,h,Polynomial.map_zero])
    have hGd : G.natDegree ≤ r := form_degree _
    have hh := count_le_of_constant_quotient φ fam bad hsub (by omega) G hG
      (1:L[X][X]) one_ne_zero natDegree_one (d-r) e hk (by omega) he (by omega)
      (by simpa only [mul_one,hg] using hapos)
    omega
  obtain ⟨w,hw,hwrep⟩ := original_weights φ H₀ u₀ u₁
  have hsp := extended_mca_atoms φ dom u bad hk hd he hbad
  have hData := normalize H S m w hw e d r (by omega) (fun j _ => hwrep j) hsp v hker hmin hp
    x z hx hz hxz hl hxf hzf
  refine ⟨r,hre,(family v).natDegree,hr,hl,?_,hData⟩
  cases r with
  | zero => omega
  | succ b =>
    have hdeg (j : ℕ) (_ : j ≤ d) : (m j).natDegree ≤ 1 := by
      dsimp only [m,ApolarHankelMinors.moment]
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]
      compute_degree
    have hh := ApolarMinimalDegree.minimal_chart_degree m (d:=d) (r:=b) (by omega) (by omega) hdeg
      v hker (hmin b (by omega)) x z hxz hzf hc
    simpa only [show d+2-2*(b+1)=d-2*b by omega] using hh

#print axioms of_mca_family
#print axioms normalize

end ProximityGap.ApolarUnitChartData
