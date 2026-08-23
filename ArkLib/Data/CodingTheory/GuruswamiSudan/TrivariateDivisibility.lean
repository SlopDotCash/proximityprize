/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.TrivariateInterpolation
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import ArkLib.Data.CodingTheory.GuruswamiSudan.DictionaryHasse
import ArkLib.Data.CodingTheory.GuruswamiSudan.ToPolyDegree
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BivariateVanishing

/-!
# Trivariate Guruswami–Sudan factorization & curve list-size ([BCIKS20] §5, second half)

The factorization / root-extraction half of the trivariate curve GS construction, building on the
interpolation existence in `TrivariateInterpolation.lean`. Introduces the missing
`CoeffSpace3 → F[X][Y]` Z-slice dictionary (`sliceAt`/`sliceToPoly`), transports order-`m` vanishing
through it (`vanishesToOrder_sliceToPoly`), extracts roots (`dvd_eval_sliceToPoly`,
`dvd_sliceToPoly_of_agreement` — the trivariate analogue of `GuruswamiSudan.dvd_property`), and
concludes the curve list-size bound `curve_listSize_le`: distinct close codewords (with nonzero
`Z`-slice) number `≤ D`, via lifting linear factors to `RatFunc F`. Together with
`exists_ne_zero_vanishesToOrder3` this formalizes both halves of the BCIKS20 §5 curve list-decoding
construction; what remains for `RSCurveListSizeResidual` is the good-set/slice wiring and the
`√ρ`-radius optimization.
-/

open Finset Polynomial
namespace GS3
open GSMultInterp
variable {F : Type} [Field F] [DecidableEq F]

/-! # ROUTE F1: Trivariate (curve) Guruswami–Sudan divisibility / root-extraction (issue #62)

This is the FACTORIZATION / ROOT-EXTRACTION half of the strict-Johnson RS curve list-size
residual. It mirrors the in-tree bivariate `GuruswamiSudan.dvd_property` machinery, lifted to
the trivariate (curve) interpolant produced by `GS3.exists_ne_zero_vanishesToOrder3`.

Mechanism: fix the curve parameter `Z = z₀`. The `Z`-slice of the trivariate coefficient vector
is a bivariate polynomial `sliceToPoly cf z₀ : F[X][Y]`. Its order-`m` vanishing is inherited
from the trivariate vanishing (`vanishesToOrder_sliceToPoly`). The substitution lemma
`ArkLib.GS.vanishesToOrder.dvd_eval` then root-extracts: each codeword `P` agreeing with the
curve on `> D/m` points becomes a `Y`-root (`Y - C P ∣ sliceToPoly`). Distinct codewords become
distinct `Y`-roots over the rational-function field `F(X)`, so the list size is `≤ deg_Y < D`. -/

/-- Project a trivariate weighted-degree triple to its `(X,Y)` bidegree, in `monoIdx k D`. -/
lemma bidegree_mem_monoIdx (k ρ D : ℕ) (hk : 0 < k) {abc : ℕ × ℕ × ℕ}
    (h : abc ∈ monoIdx3 k ρ D) : (abc.1, abc.2.1) ∈ GSMultInterp.monoIdx k D := by
  rw [mem_monoIdx3] at h; rw [GSMultInterp.mem_monoIdx_of_pos hk]; dsimp only; omega

/-- The bivariate **Z-slice** of a trivariate coefficient vector at `z₀`: the `(s,t)`-coefficient
is `∑_{c : (s,t,c)∈monoIdx3} cf(s,t,c)·z₀^c`, i.e. the `Z`-polynomial evaluated at `z₀`. -/
noncomputable def sliceAt (k ρ D : ℕ) (cf : CoeffSpace3 (F := F) k ρ D) (z₀ : F) :
    CoeffSpace (F := F) k D :=
  fun st => ∑ stu : {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D},
    if (stu.1.1, stu.1.2.1) = st.1 then cf stu * z₀ ^ stu.1.2.2 else 0

omit [DecidableEq F] in
/-- **Slice/Hasse compatibility.** The bivariate order-`(a,b)` Hasse coefficient of the Z-slice
`sliceAt cf z₀` at `(x₀,y₀)` equals the trivariate order-`(a,b,0)` Hasse coefficient of `cf` at
`(x₀,y₀,z₀)`. -/
lemma hasseCoeff_sliceAt (k ρ D : ℕ) (hk : 0 < k) (cf : CoeffSpace3 (F := F) k ρ D)
    (a b : ℕ) (x₀ y₀ z₀ : F) :
    GSMultInterp.hasseCoeff k D (sliceAt k ρ D cf z₀) a b x₀ y₀
      = hasseCoeff3 k ρ D cf a b 0 x₀ y₀ z₀ := by
  rw [show hasseCoeff3 k ρ D cf a b 0 x₀ y₀ z₀
        = ∑ stu : {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D},
          (Nat.choose stu.1.1 a : F) * (Nat.choose stu.1.2.1 b : F)
            * cf stu * x₀ ^ (stu.1.1 - a) * y₀ ^ (stu.1.2.1 - b) * z₀ ^ stu.1.2.2 from by
        simp only [hasseCoeff3, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
        apply Finset.sum_congr rfl; intro stu _; ring]
  simp only [GSMultInterp.hasseCoeff, sliceAt]
  have hterm : ∀ st : {ab : ℕ × ℕ // ab ∈ GSMultInterp.monoIdx k D},
      (Nat.choose st.1.1 a : F) * (Nat.choose st.1.2 b : F)
        * (∑ stu : {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D},
            if (stu.1.1, stu.1.2.1) = st.1 then cf stu * z₀ ^ stu.1.2.2 else 0)
        * x₀ ^ (st.1.1 - a) * y₀ ^ (st.1.2 - b)
      = ∑ stu : {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D},
          (if (stu.1.1, stu.1.2.1) = st.1 then
            (Nat.choose stu.1.1 a : F) * (Nat.choose stu.1.2.1 b : F)
              * cf stu * x₀ ^ (stu.1.1 - a) * y₀ ^ (stu.1.2.1 - b) * z₀ ^ stu.1.2.2 else 0) := by
    intro st
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro stu _
    by_cases heq : (stu.1.1, stu.1.2.1) = st.1
    · rw [if_pos heq, if_pos heq]
      have h1 : stu.1.1 = st.1.1 := congrArg Prod.fst heq
      have h2 : stu.1.2.1 = st.1.2 := congrArg Prod.snd heq
      rw [h1, h2]; ring
    · rw [if_neg heq, if_neg heq]; ring
  rw [Finset.sum_congr rfl (fun st _ => hterm st)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro stu _
  rw [Finset.sum_eq_single ⟨(stu.1.1, stu.1.2.1), bidegree_mem_monoIdx k ρ D hk stu.2⟩]
  · rw [if_pos rfl]
  · intro st _ hne
    exact if_neg (fun hcontra => hne (Subtype.ext hcontra.symm))
  · intro h; exact absurd (Finset.mem_univ _) h

omit [DecidableEq F] in
/-- **Z-slice vanishing (coefficient form).** Trivariate order-`m` vanishing at `(x₀,y₀,z₀)`
implies the Z-slice `sliceAt cf z₀` vanishes to order `m` at `(x₀,y₀)`. -/
lemma vanishesToOrder_sliceAt (k ρ D m : ℕ) (hk : 0 < k) (cf : CoeffSpace3 (F := F) k ρ D)
    (x₀ y₀ z₀ : F) (hv : vanishesToOrder3 k ρ D m cf x₀ y₀ z₀) :
    GSMultInterp.vanishesToOrder k D m (sliceAt k ρ D cf z₀) x₀ y₀ := by
  intro a b hab
  rw [hasseCoeff_sliceAt k ρ D hk]
  exact hv a b 0 (by omega)

/-- **Z-slice interpolant** as an honest `F[X][Y]` polynomial: fix `Z = z₀` in `cf`. -/
noncomputable def sliceToPoly (k ρ D : ℕ) (cf : CoeffSpace3 (F := F) k ρ D) (z₀ : F) :
    Polynomial (Polynomial F) :=
  GSMultInterp.toPoly k D (sliceAt k ρ D cf z₀)

/-- The Z-slice interpolant vanishes (`Polynomial`-side) to order `m` at any curve point. -/
theorem vanishesToOrder_sliceToPoly (k ρ D m : ℕ) (hk : 0 < k) (cf : CoeffSpace3 (F := F) k ρ D)
    (x₀ y₀ z₀ : F) (hv : vanishesToOrder3 k ρ D m cf x₀ y₀ z₀) :
    ArkLib.GS.vanishesToOrder m (sliceToPoly k ρ D cf z₀) x₀ y₀ := by
  rw [sliceToPoly, GSMultInterp.vanishesToOrder_toPoly_iff]
  exact vanishesToOrder_sliceAt k ρ D m hk cf x₀ y₀ z₀ hv

/-- The outer (`Y`) degree of the Z-slice interpolant is `< D`. -/
theorem sliceToPoly_natDegree_lt (k ρ D : ℕ) (hk : 0 < k) (hD : 0 < D)
    (cf : CoeffSpace3 (F := F) k ρ D) (z₀ : F) :
    (sliceToPoly k ρ D cf z₀).natDegree < D := by
  have hwd : Bivariate.natWeightedDegree (sliceToPoly k ρ D cf z₀) 1 k < D :=
    GSMultInterp.toPoly_natWeightedDegree_lt k D hD _
  have hbound := Polynomial.Bivariate.weight_le_natWeightedDegree_of_lt_natDegree_succ
    (f := sliceToPoly k ρ D cf z₀) (u := 1) (v := k)
    (n := (sliceToPoly k ρ D cf z₀).natDegree) (Nat.lt_succ_self _)
  set nd := (sliceToPoly k ρ D cf z₀).natDegree
  have hkn : nd ≤ k * nd := Nat.le_mul_of_pos_left nd hk
  omega

/-- **Trivariate curve root-extraction (single point).** If `cf` vanishes to order `m` at the
curve point `(x₀,y₀,z₀)` and `P.eval x₀ = y₀`, then `(X - C x₀)^m ∣ (sliceToPoly cf z₀).eval P`. -/
theorem dvd_eval_sliceToPoly (k ρ D m : ℕ) (hk : 0 < k) (cf : CoeffSpace3 (F := F) k ρ D)
    (x₀ y₀ z₀ : F) (hv : vanishesToOrder3 k ρ D m cf x₀ y₀ z₀)
    (P : Polynomial F) (hP : P.eval x₀ = y₀) :
    (Polynomial.X - Polynomial.C x₀) ^ m ∣ (sliceToPoly k ρ D cf z₀).eval P :=
  (vanishesToOrder_sliceToPoly k ρ D m hk cf x₀ y₀ z₀ hv).dvd_eval P hP

set_option maxHeartbeats 1200000 in
/-- **Trivariate curve divisibility (`Y`-root form) — the ROUTE F1 analogue of `dvd_property`.**
Fix `z₀`. If `cf` vanishes to order `m` at every curve point `(ωs i, f i, z₀)`, `P` is a codeword
(degree `≤ k-1`) agreeing with the curve on a set `A` with `m·|A| > D`, then `(Y - C P)` divides
the `Z`-slice interpolant. -/
theorem dvd_sliceToPoly_of_agreement
    {n : ℕ} (k ρ D m : ℕ) (hk : 0 < k) (hD : 0 < D) (ωs : Fin n ↪ F) (f : Fin n → F)
    (z₀ : F) (cf : CoeffSpace3 (F := F) k ρ D)
    (hv : ∀ i, vanishesToOrder3 k ρ D m cf (ωs i) (f i) z₀)
    (P : Polynomial F) (hPdeg : P.natDegree ≤ k - 1)
    (A : Finset (Fin n)) (hA : ∀ i ∈ A, P.eval (ωs i) = f i)
    (hcount : D < m * A.card) :
    (Polynomial.X - Polynomial.C P : Polynomial (Polynomial F)) ∣ sliceToPoly k ρ D cf z₀ := by
  suffices hRzero : (sliceToPoly k ρ D cf z₀).eval P = 0 from
    dvd_iff_isRoot.mpr (show IsRoot _ _ from hRzero)
  by_contra hRne
  have hmult : ∀ i ∈ A, m ≤ rootMultiplicity (ωs i) ((sliceToPoly k ρ D cf z₀).eval P) := by
    intro i hi
    rw [le_rootMultiplicity_iff hRne]
    exact dvd_eval_sliceToPoly k ρ D m hk cf (ωs i) (f i) z₀ (hv i) P (hA i hi)
  have hdegR : ((sliceToPoly k ρ D cf z₀).eval P).natDegree < D := by
    have h1 : ((sliceToPoly k ρ D cf z₀).eval P).natDegree
        ≤ Bivariate.natWeightedDegree (sliceToPoly k ρ D cf z₀) 1 (k - 1) :=
      GuruswamiSudan.degree_eval_le_weightedDegree _ P k hPdeg
    have h2 : Bivariate.natWeightedDegree (sliceToPoly k ρ D cf z₀) 1 k < D :=
      GSMultInterp.toPoly_natWeightedDegree_lt k D hD _
    have h3 : Bivariate.natWeightedDegree (sliceToPoly k ρ D cf z₀) 1 (k - 1)
        ≤ Bivariate.natWeightedDegree (sliceToPoly k ρ D cf z₀) 1 k := by
      simp only [Bivariate.natWeightedDegree]
      apply Finset.sup_mono_fun
      intro b _
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    omega
  exact hRne (GuruswamiSudan.roots_le_degree_of_deg_lt_roots (ωs := ωs) _ m A hmult
    (by rw [mul_comm] at hcount ⊢; omega))

/-- **Distinct linear factors bound the degree** (generic field). If `Q ≠ 0` over a field `K` is
divisible by `(X - C a)` for each `a` in a finite set `S` of distinct scalars, `|S| ≤ Q.natDegree`. -/
theorem card_le_natDegree_of_linear_dvd {K : Type*} [Field K] (Q : Polynomial K) (hQ : Q ≠ 0)
    (S : Finset K) (hdvd : ∀ a ∈ S, (Polynomial.X - Polynomial.C a : Polynomial K) ∣ Q) :
    S.card ≤ Q.natDegree := by
  classical
  have hprod_dvd : (∏ a ∈ S, (Polynomial.X - Polynomial.C a : Polynomial K)) ∣ Q := by
    refine Finset.prod_dvd_of_coprime ?_ (fun a ha => hdvd a ha)
    intro x hx y hy hxy
    exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy))
  have hdeg := Polynomial.natDegree_le_of_dvd hprod_dvd hQ
  rw [Polynomial.natDegree_prod _ _ (fun a _ => X_sub_C_ne_zero a)] at hdeg
  simpa [Polynomial.natDegree_X_sub_C] using hdeg

set_option maxHeartbeats 1200000 in
/-- **Trivariate curve list-size bound (ROUTE F1 capstone, issue #62).**
Fix `z₀`. If `cf` vanishes to order `m` at every curve point, the Z-slice interpolant is nonzero,
and `S` is a set of *distinct* codeword polynomials (degree `≤ k-1`), each agreeing with the curve
value `f` on a set `Agr P` with `m·|Agr P| > D`, then the list size obeys `|S| ≤ D`.

This is the Sudan curve list-size bound `L ≤ deg_Y Q < D`: distinct close codewords become
distinct `Y`-roots over the rational-function field `F(X)`, capped by the `Y`-degree. -/
theorem curve_listSize_le
    {n : ℕ} (k ρ D m : ℕ) (hk : 0 < k) (hD : 0 < D) (ωs : Fin n ↪ F) (f : Fin n → F)
    (z₀ : F) (cf : CoeffSpace3 (F := F) k ρ D)
    (hv : ∀ i, vanishesToOrder3 k ρ D m cf (ωs i) (f i) z₀)
    (hslice_ne : sliceToPoly k ρ D cf z₀ ≠ 0)
    (S : Finset (Polynomial F))
    (hPdeg : ∀ P ∈ S, P.natDegree ≤ k - 1)
    (Agr : Polynomial F → Finset (Fin n))
    (hAgr : ∀ P ∈ S, ∀ i ∈ Agr P, P.eval (ωs i) = f i)
    (hcount : ∀ P ∈ S, D < m * (Agr P).card) :
    S.card ≤ D := by
  classical
  set φ := algebraMap (Polynomial F) (RatFunc F) with hφ
  set Qrf := (sliceToPoly k ρ D cf z₀).map φ with hQrf
  have hQrf_ne : Qrf ≠ 0 := by
    rw [hQrf, Ne, Polynomial.map_eq_zero_iff (RatFunc.algebraMap_injective F)]
    exact hslice_ne
  have hdvd_rf : ∀ Prf ∈ S.image φ,
      (Polynomial.X - Polynomial.C Prf : Polynomial (RatFunc F)) ∣ Qrf := by
    intro Prf hPrf
    rw [Finset.mem_image] at hPrf
    obtain ⟨P, hPS, rfl⟩ := hPrf
    have hbase := dvd_sliceToPoly_of_agreement (ωs := ωs) (f := f) k ρ D m hk hD z₀ cf hv
      P (hPdeg P hPS) (Agr P) (hAgr P hPS) (hcount P hPS)
    have := Polynomial.map_dvd φ hbase
    simpa using this
  have hcard_img : (S.image φ).card ≤ Qrf.natDegree :=
    card_le_natDegree_of_linear_dvd Qrf hQrf_ne (S.image φ) hdvd_rf
  have hQrf_deg : Qrf.natDegree ≤ (sliceToPoly k ρ D cf z₀).natDegree :=
    Polynomial.natDegree_map_le
  have hinj : (S.image φ).card = S.card :=
    Finset.card_image_of_injective S (RatFunc.algebraMap_injective F)
  have hslice_deg : (sliceToPoly k ρ D cf z₀).natDegree < D :=
    sliceToPoly_natDegree_lt k ρ D hk hD cf z₀
  omega

#print axioms bidegree_mem_monoIdx
#print axioms hasseCoeff_sliceAt
#print axioms vanishesToOrder_sliceAt
#print axioms vanishesToOrder_sliceToPoly
#print axioms sliceToPoly_natDegree_lt
#print axioms dvd_eval_sliceToPoly
#print axioms dvd_sliceToPoly_of_agreement
#print axioms card_le_natDegree_of_linear_dvd
#print axioms curve_listSize_le
end GS3
