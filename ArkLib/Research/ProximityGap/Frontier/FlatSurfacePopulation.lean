/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SectionNumeratorCharts
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-! # Populations on a component of the actual received interpolation surface

A generic affine head over the scalar rational-function field descends to
every selected polynomial on the original surface component. The flat and
transverse estimates thus give a finite alternative for actual bad labels.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.FlatSurfacePopulation
open SecondPrimeCoordinateWeight SecondPrimeScalarChart MovingCubicVanishingBranch WeightedSylvesterDegree
open SectionNumeratorCharts
variable {K : Type} [Field K]

def receivedTest (f : Surface K) (x u v : K) : K[X] :=
  f.eval₂ (mapRingHom (evalRingHom x)) (C u+Polynomial.X*C v)

theorem received_degree (f : Surface K) (x u v : K) (m : ℕ) (hf : TotalDegreeLe f m) :
    (receivedTest f x u v).natDegree ≤ m := by
  have hL : (C u + Polynomial.X*C v).natDegree ≤ 1 := natDegree_add_le_of_degree_le (by simp)
    (natDegree_mul_le.trans (by simp))
  rw [receivedTest, eval₂_eq_sum]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h := hf i (mem_support_iff.mp hi)
  apply LE.le.trans _ h
  apply natDegree_mul_le.trans (Nat.add_le_add natDegree_map_le (natDegree_pow_le.trans ?_))
  simpa using Nat.mul_le_mul_left i hL

theorem actual_site (f : Surface K) (x u v z : K) (q : K[X])
    (hq : f.eval₂ (evalRingHom (C z)) q = 0) (hfit : q.eval x = u+z*v) :
    (receivedTest f x u v).eval z = 0 := by
  have he := congrArg (evalRingHom x) hq
  rw [hom_eval₂, map_zero] at he
  have hmaps : (evalRingHom x).comp (evalRingHom (C z)) =
      (evalRingHom z).comp (mapRingHom (evalRingHom x)) := by
    apply RingHom.ext
    intro P
    change (P.eval (C z)).eval x = (P.map (evalRingHom x)).eval z
    simpa using (eval_map_apply (p := P) (evalRingHom x) (C z)).symm
  change (evalRingHom z) (receivedTest f x u v) = 0
  rw [receivedTest, hom_eval₂, ← hmaps]
  change f.eval₂ _ ((C u+Polynomial.X*C v).eval z) = 0
  simpa only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, hfit] using he

theorem generic_site (f : Surface K) (x u v : K) :
    ((scalarChart f).map (evalRingHom (RatFunc.C x))).eval (RatFunc.C u+RatFunc.X*RatFunc.C v) =
      algebraMap K[X] (RatFunc K) (receivedTest f x u v) := by
  let χ := algebraMap K[X] (RatFunc K)
  have hmaps : ((evalRingHom (RatFunc.C x)).comp (mapRingHom χ)).comp Bivariate.swap.toRingHom =
      χ.comp (mapRingHom (evalRingHom x)) := by
    apply RingHom.ext
    intro P
    change ((Bivariate.swap P).map χ).eval (RatFunc.C x) = χ (P.map (evalRingHom x))
    have hc : χ (C x) = RatFunc.C x := RatFunc.algebraMap_C _
    rw [← hc, eval_map_apply]
    apply congrArg χ
    simpa only [Bivariate.evalY, Bivariate.evalX_eq_map, Bivariate.swap_swap_apply] using
      Bivariate.evalY_eq_evalX_swap x (Bivariate.swap P)
  unfold scalarChart receivedTest
  rw [hom_eval₂]
  simp only [eval_map,eval₂_map,RingHom.comp_assoc] at hmaps ⊢
  rw [hmaps]
  simp only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rfl

def rawHead (A B : K[X]) : K[X][X] := C A + Polynomial.X*C B

private theorem raw_head_chart (A B : K[X]) :
    (mapRingHom (algebraMap K[X] (RatFunc K))) (Bivariate.swap (rawHead A B)) =
      A.map RatFunc.C + C RatFunc.X * B.map RatFunc.C := by
  simp [rawHead, Bivariate.swap_Y, Bivariate.swap_C, Polynomial.map_map]
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
/-- Descent from the generic affine section to every original scalar fiber. -/
theorem selected_on_head (f : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree)
    (A B : K[X]) (hhead : AdjoinRoot.root (genericEquation (scalarChart f)) =
      (A.map ((algebraMap (RatFunc K) _).comp RatFunc.C) +
        C (algebraMap (RatFunc K) _ RatFunc.X) * B.map ((algebraMap (RatFunc K) _).comp RatFunc.C)).eval
          (AdjoinRoot.of (genericEquation (scalarChart f)) RatFunc.X))
    (z : K) (q : K[X]) (hq : f.eval₂ (evalRingHom (C z)) q = 0) :
    q = A+C z*B := by
  let g := genericEquation (scalarChart f)
  have hir := generic_irreducible f hi hb
  let _ : Fact (Irreducible g) := ⟨hir⟩
  let L := AdjoinRoot g
  let σ := ((algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))).comp
      (mapRingHom (algebraMap K[X] (RatFunc K)))).comp Bivariate.swap.toRingHom
  have hσ : Function.Injective σ := (RatFunc.algebraMap_injective (RatFunc K)).comp
    ((map_injective _ (RatFunc.algebraMap_injective K)).comp Bivariate.swap.injective)
  let H : Surface K := Polynomial.X - C (rawHead A B)
  have hv : (AdjoinRoot.of g) (σ (rawHead A B)) =
      (A.map ((algebraMap (RatFunc K) L).comp RatFunc.C) +
        C (algebraMap (RatFunc K) L RatFunc.X) * B.map ((algebraMap (RatFunc K) L).comp RatFunc.C)).eval
          (AdjoinRoot.of g RatFunc.X) := by
    change AdjoinRoot.of g (algebraMap (RatFunc K)[X] _ ((mapRingHom _) (Bivariate.swap _))) = _
    rw [raw_head_chart, map_add, map_mul, map_add, map_mul]
    simp only [eval_add, eval_mul]
    have hh (P : K[X]) :
        (AdjoinRoot.of g) (algebraMap (RatFunc K)[X] (RatFunc (RatFunc K)) (P.map RatFunc.C)) =
        (P.map ((algebraMap (RatFunc K) L).comp RatFunc.C)).eval ((AdjoinRoot.of g) RatFunc.X) := by
      have Hφ : (AdjoinRoot.of g).comp (algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))) =
          eval₂RingHom (algebraMap (RatFunc K) L) ((AdjoinRoot.of g) RatFunc.X) := by
        ext a
        · simp [RatFunc.algebraMap_C]
          rfl
        · change (AdjoinRoot.of g) RatFunc.X = Polynomial.eval₂ _ _ Polynomial.X
          rw [eval₂_X]
      change ((AdjoinRoot.of g).comp _) _ = _
      rw [Hφ, coe_eval₂RingHom, eval₂_map, eval_map]
    rw [hh A, hh B, RatFunc.algebraMap_C]
    change _ = _ + (Polynomial.C _ : L[X]).eval _ * _
    rw [eval_C]
    rfl
  have hdvd : f.map σ ∣ H.map σ := by
    have heq : f.map σ = g := by
      change _ = ((f.map _).map _).map _
      rw [Polynomial.map_map, Polynomial.map_map]
    rw [heq]
    apply AdjoinRoot.mk_eq_zero.mp
    simp only [H, Polynomial.map_sub, map_X, map_C, map_sub]
    exact sub_eq_zero.mpr (hhead.trans hv.symm)
  have hraw := SecondPrimeReverseChart.descends σ hσ f H hi hb hdvd
  obtain ⟨T,hT⟩ := hraw
  have Hq := congrArg (fun P : Surface K => P.eval₂ (evalRingHom (C z)) q) hT
  simp only [H, rawHead, eval₂_sub, eval₂_X, eval₂_C, coe_evalRingHom, eval_add, eval_mul,
    eval_C, eval_X, eval₂_mul, hq, zero_mul] at Hq
  exact sub_eq_zero.mp Hq

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open scoped NNReal
/-- For an irreducible component of the actual surface, the exceptional labels
either satisfy the flat agreement-surplus bound, lie on a single affine head,
or satisfy the transverse resultant bound. -/
theorem component_bound {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p] (hp : p.Prime) (f : Surface K) (hi : Irreducible f)
    (hpos : 0 < f.natDegree) (m b d t : ℕ) (hb : 2 ≤ b) (hm : b ≤ m)
    (htri : TotalDegreeLe f m) (hfy : f.natDegree ≤ b) (hsep : f.natDegree < p)
    (hd : d < p) (hw : weight d f < p) (hdt : d < t) (htn : t ≤ Fintype.card I)
    (dom : I ↪ K) (δ : ℝ≥0) (u : Code.WordStack K (Fin 2) I)
    (fam : BadScalarRichPointFamily dom (d+1) δ u)
    (ht : t ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (M : Finset K) (hM : M ⊆ fam.G)
    (hroot : ∀ z ∈ M, f.eval₂ (evalRingHom (C z)) (fam.q z) = 0) :
    M.card*(t-d) ≤ (Fintype.card I-d)*m ∨ M.card ≤ Fintype.card I ∨
      M.card ≤ b*(m+2*d*(m-1))+(b+2*d*(b-1))*m-b*(b+2*d*(b-1)) := by
  classical
  by_cases hdiv : f ∣ rawNumerator f d
  swap
  · exact Or.inr (Or.inr (transverse_population f hi hpos m b d hb hm htri hfy hdiv M fam.q
      (fun z hz => Nat.le_of_lt_succ (fam.degree_lt z (hM hz))) hroot))
  let F := scalarChart f
  have hdeg : F.natDegree = f.natDegree := value_degree f
  have hir := SecondPrimeReceivedJetColumns.chart_irreducible f hi hpos
  have hpr : F.IsPrimitive := hir.isPrimitive (hdeg.trans_ne hpos.ne')
  have hder : F.derivative ≠ 0 := fun h =>
    (hdeg.trans_ne hpos.ne') (PositiveCharacteristicHeightDescent.natDegree_eq_zero_of_derivative_eq_zero
      F (hdeg.trans_lt hsep) h)
  have hdvd : genericEquation F ∣ genericEquation (coordinateNumerator F d) := by
    obtain ⟨g,hg⟩ := hdiv
    rw [← scalarChart_rawNumerator, hg]
    unfold genericEquation scalarChart
    simp only [Polynomial.map_mul]
    exact dvd_mul_right _ _
  let R := fun i => receivedTest f (dom i) (u 0 i) (u 1 i)
  have hmany (z : K) (hz : z ∈ M) :
      t ≤ (Finset.univ.filter fun i => (R i).eval z = 0).card := by
    apply (ht.trans (fam.threshold_le z (hM hz))).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, actual_site f _ _ _ z (fam.q z) (hroot _ hz)
      (Finset.mem_filter.mp hi).2⟩
  have hident (i : I) (_ : i ∈ Finset.univ) (hr : R i = 0) :
      (F.map (evalRingHom (RatFunc.C (dom i)))).eval (RatFunc.C (u 0 i)+RatFunc.X*RatFunc.C (u 1 i)) = 0 := by
    change ((scalarChart _).map _).eval _ = 0
    rw [generic_site]
    change algebraMap K[X] (RatFunc K) (R i) = 0
    rw [hr, map_zero]
  rcases FlatSectionWeightedDescent.component_small_or_head hp F (generic_irreducible f hi hpos)
    hpr hder d t m hd ((chart_weight f d).trans_lt hw) hdvd RatFunc.C RatFunc.X
    Finset.univ dom (u 0) (u 1) M R hdt (by simpa using htn)
    (fun i _ => received_degree f _ _ _ m htri) hmany hident with h | ⟨A,B,hA,hB,hH⟩
  · exact Or.inl (by simpa using h)
  · have hall (z) (hz : z ∈ M) := selected_on_head f hi hpos A B hH z (fam.q z) (hroot z hz)
    have hpack := fam.line_core_packing A B M (Nat.lt_succ_of_le hA) (Nat.lt_succ_of_le hB) hM hall
    have hh : M.card ≤ M.card * max 1 (⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ -
        (jointCore dom (u 0) (u 1) A B).card) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact Or.inr (Or.inl (by omega))

end ArkLib.ProximityGap.Frontier.FlatSurfacePopulation

open ArkLib.ProximityGap.Frontier.FlatSurfacePopulation in
#print axioms component_bound
