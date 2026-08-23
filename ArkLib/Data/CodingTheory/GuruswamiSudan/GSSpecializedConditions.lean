/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegerRepresentative

/-!
# Hab25 §3 Step S10 converse — the GS `Conditions` survive specialization at every good `z`

`GSIntegerRepresentative.lean` proved the **forward** half of the Theorem-2 cover: every
`K = F(Z)`-decoded affine pair divides every specialization `Q₀|_{Z:=z}` of the integer
representative. This file proves the **converse** half: at every good `z` (the cofinite set
where `Q₀|_{Z:=z} ≠ 0`), the specialized integer interpolant is itself a valid GS interpolant
for the scalar fold `f_z = f₀ + z·f₁`, so the in-tree single-function `gs_divisibility`
applies and **every `δ`-close scalar fold's decoded polynomial divides `Q₀|_{Z:=z}`**.

The work is showing each field of `GuruswamiSudan.Conditions` transfers:

* *degree* (`natWeightedDegree_map_le`, `natWeightedDegree_map_eq_of_injective`,
  `natWeightedDegree_C_C_mul_le`): weighted degrees only drop under coefficientwise ring
  maps, are preserved by injective ones, and ignore the constant denominator factor
  `C(C d)`; chaining gives `wdeg(Q₀|_z) ≤ wdeg_K(Q) ≤ D`.

* *roots* (`map_mapRingHom_evalEval` chain): the bivariate evaluation at the integral points
  `(C ω_i, C(f₀ i) + Z·C(f₁ i))` vanishes already over `F[Z]` (the `K`-level root, pushed
  through the injective embedding, with the constant factor evaluating to a unit), hence
  vanishes at every specialization.

* *multiplicity* (`shift_map`, `shift_C_C_mul`,
  `shift_coeff_eq_zero_of_le_rootMultiplicity`): the order-`< m` coefficients of the
  Taylor shift vanish over `K` (extraction from the `Conditions` multiplicity bound via
  `rootMultiplicity₀_ge_iff`), the shift commutes with coefficientwise ring maps and absorbs
  the constant factor, so the vanishing descends to `F[Z]` and re-specializes at every `z`;
  `rootMultiplicity_ge_of_shift_zero` reassembles the bound.

Capstones:

* `specialized_conditions` — `Conditions k m D ωs f_z (Q₀|_{Z:=z})` at every `z` with
  `Q₀|_{Z:=z} ≠ 0`;
* `scalar_fold_decoded_divides_specialization` — the S10 converse: every degree-`< k`
  codeword within the GS Johnson radius of the scalar fold `f_z` has
  `(Y − C p_z) ∣ Q₀|_{Z:=z}`.

Together with `decoded_affine_pair_divides_specialization` (forward), the per-`z` decoded
lists on both sides land in the factor structure of the *same* specialized interpolant —
the complete S10 divisibility bridge. Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-! ## Weighted-degree transfer lemmas -/

section WeightedDegree

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The weighted degree only drops under a coefficientwise ring map. -/
lemma natWeightedDegree_map_le (σ : R →+* S) (p : R[X][Y]) (u v : ℕ) :
    natWeightedDegree (p.map (Polynomial.mapRingHom σ)) u v ≤ natWeightedDegree p u v := by
  refine Finset.sup_le fun t ht => ?_
  have hmem : t ∈ p.support := Polynomial.support_map_subset _ _ ht
  have hdeg : ((p.map (Polynomial.mapRingHom σ)).coeff t).natDegree ≤
      (p.coeff t).natDegree := by
    rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact Polynomial.natDegree_map_le
  exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left u hdeg) _)
    (Finset.le_sup (f := fun t => u * (p.coeff t).natDegree + v * t) hmem)

/-- The weighted degree is preserved by an injective coefficientwise ring map. -/
lemma natWeightedDegree_map_eq_of_injective {σ : R →+* S}
    (hσ : Function.Injective σ) (p : R[X][Y]) (u v : ℕ) :
    natWeightedDegree (p.map (Polynomial.mapRingHom σ)) u v = natWeightedDegree p u v := by
  have hΨ : Function.Injective (Polynomial.map σ) := Polynomial.map_injective σ hσ
  show ((p.map (Polynomial.mapRingHom σ)).support.sup fun t =>
      u * ((p.map (Polynomial.mapRingHom σ)).coeff t).natDegree + v * t) = _
  rw [show p.map (Polynomial.mapRingHom σ) = p.map (Polynomial.mapRingHom σ) from rfl]
  have hsupp : (p.map (Polynomial.mapRingHom σ)).support = p.support :=
    Polynomial.support_map_of_injective p (by rw [Polynomial.coe_mapRingHom]; exact hΨ)
  rw [hsupp]
  refine Finset.sup_congr rfl fun t _ => ?_
  rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective hσ]

/-- The weighted degree ignores a constant (in both variables) factor. -/
lemma natWeightedDegree_C_C_mul_le (e : R) (p : R[X][Y]) (u v : ℕ) :
    natWeightedDegree (Polynomial.C (Polynomial.C e) * p) u v ≤
      natWeightedDegree p u v := by
  refine Finset.sup_le fun t ht => ?_
  have hmem : t ∈ p.support := by
    rw [Polynomial.mem_support_iff] at ht ⊢
    intro h0
    rw [Polynomial.coeff_C_mul, h0, mul_zero] at ht
    exact ht rfl
  have hdeg : ((Polynomial.C (Polynomial.C e) * p).coeff t).natDegree ≤
      (p.coeff t).natDegree := by
    rw [Polynomial.coeff_C_mul]
    exact Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_C])
  exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left u hdeg) _)
    (Finset.le_sup (f := fun t => u * (p.coeff t).natDegree + v * t) hmem)

end WeightedDegree

/-! ## Shift transfer lemmas (for the multiplicity field) -/

section Shift

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The bivariate Taylor shift commutes with coefficientwise ring maps. -/
lemma shift_map (σ : R →+* S) (p : R[X][Y]) (x y : R) :
    Polynomial.Bivariate.shift (p.map (Polynomial.mapRingHom σ)) (σ x) (σ y) =
      (Polynomial.Bivariate.shift p x y).map (Polynomial.mapRingHom σ) := by
  unfold Polynomial.Bivariate.shift
  have h1 : (p.map (Polynomial.mapRingHom σ)).comp
      (Polynomial.X + Polynomial.C (Polynomial.C (σ y))) =
      (p.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).map
        (Polynomial.mapRingHom σ) := by
    rw [Polynomial.map_comp]
    congr 1
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
  rw [h1, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun q => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.coe_mapRingHom]
  rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

/-- The bivariate Taylor shift absorbs a constant factor. -/
lemma shift_C_C_mul (e : R) (p : R[X][Y]) (x y : R) :
    Polynomial.Bivariate.shift (Polynomial.C (Polynomial.C e) * p) x y =
      Polynomial.C (Polynomial.C e) * Polynomial.Bivariate.shift p x y := by
  unfold Polynomial.Bivariate.shift
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.coe_compRingHom_apply, Polynomial.C_comp]

end Shift

/-- **Extraction from the `Conditions` multiplicity bound.** If
`m ≤ rootMultiplicity f x y` then all Taylor-shift coefficients of total degree `< m`
vanish — the converse of `rootMultiplicity_ge_of_shift_zero`, via the in-tree
characterization `rootMultiplicity₀_ge_iff`. -/
lemma shift_coeff_eq_zero_of_le_rootMultiplicity {K : Type*} [CommSemiring K]
    [DecidableEq K] {f : K[X][Y]} {x y : K} {m : ℕ}
    (h : (m : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity f x y) :
    ∀ s t, s + t < m →
      ((Polynomial.Bivariate.shift f x y).coeff t).coeff s = 0 := by
  intro s t hst
  have hchar := (Polynomial.Bivariate.rootMultiplicity₀_ge_iff
    (Polynomial.Bivariate.shift f x y) m).mpr ?_ s t hst
  · exact hchar
  · intro m' hm'
    rw [Polynomial.Bivariate.rootMultiplicity, Option.mem_def] at *
    rw [hm'] at h
    exact_mod_cast h

variable {F : Type} [Field F]

/-! ## The integral evaluation points -/

/-- The integral `X`-point: `ω_i` as a constant of `F[Z]`. -/
noncomputable def intPointX {n : ℕ} (ωs : Fin n ↪ F) (i : Fin n) : F[X] :=
  Polynomial.C (ωs i)

/-- The integral `Y`-point: the generic fold value `f₀ i + Z·f₁ i ∈ F[Z]`. -/
noncomputable def intPointY {n : ℕ} (f₀ f₁ : Fin n → F) (i : Fin n) : F[X] :=
  Polynomial.C (f₀ i) + Polynomial.X * Polynomial.C (f₁ i)

lemma algebraMap_C_eq (a : F) :
    algebraMap F[X] (RatFunc F) (Polynomial.C a) = algebraMap F (RatFunc F) a := by
  rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), Polynomial.algebraMap_eq]

lemma map_intPointX {n : ℕ} (ωs : Fin n ↪ F) (i : Fin n) :
    algebraMap F[X] (RatFunc F) (intPointX ωs i) = liftedDomain ωs i := by
  rw [intPointX, algebraMap_C_eq]
  rfl

lemma map_intPointY {n : ℕ} (f₀ f₁ : Fin n → F) (i : Fin n) :
    algebraMap F[X] (RatFunc F) (intPointY f₀ f₁ i) = genericFold f₀ f₁ i := by
  rw [intPointY, map_add, map_mul, algebraMap_C_eq, algebraMap_C_eq, RatFunc.algebraMap_X]
  rfl

lemma eval_intPointX {n : ℕ} (ωs : Fin n ↪ F) (i : Fin n) (z : F) :
    Polynomial.evalRingHom z (intPointX ωs i) = ωs i := by
  simp [intPointX]

lemma eval_intPointY {n : ℕ} (f₀ f₁ : Fin n → F) (i : Fin n) (z : F) :
    Polynomial.evalRingHom z (intPointY f₀ f₁ i) = f₀ i + z * f₁ i := by
  rw [intPointY, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X]

/-! ## The capstone: specialized `Conditions` -/

/-- **Hab25 §3 S10 converse core — the GS `Conditions` survive specialization.**

Let `Q` be a GS interpolant of the generic fold over `K = F(Z)` (the S2 `Conditions`) and
`(d, Q₀)` an integer representative. Then at **every** `z ∈ F` where the specialization
does not collapse (`Q₀|_{Z:=z} ≠ 0` — a cofinite set), the specialized polynomial
`Q₀|_{Z:=z} ∈ F[X][Y]` is a valid GS interpolant for the scalar fold `f_z = f₀ + z·f₁`:
nonzero, same weighted-degree bound, with roots of multiplicity `≥ m` at every
`(ω_i, f₀ i + z·f₁ i)`. -/
theorem specialized_conditions {n k m D : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m D (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0) :
    GuruswamiSudan.Conditions k m D ωs (fun i => f₀ i + z * f₁ i)
      (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) := by
  classical
  set φ := algebraMap F[X] (RatFunc F) with hφ
  have hφinj : Function.Injective φ := RatFunc.algebraMap_injective F
  set σ := Polynomial.evalRingHom z with hσ
  refine ⟨hz, ?_, ?_, ?_⟩
  · -- weighted degree
    have h1 : natWeightedDegree (Q₀.map (Polynomial.mapRingHom σ)) 1 (k - 1) ≤
        natWeightedDegree Q₀ 1 (k - 1) := natWeightedDegree_map_le σ Q₀ 1 (k - 1)
    have h2 : natWeightedDegree Q₀ 1 (k - 1) =
        natWeightedDegree (Q₀.map (Polynomial.mapRingHom φ)) 1 (k - 1) :=
      (natWeightedDegree_map_eq_of_injective hφinj Q₀ 1 (k - 1)).symm
    have h3 : natWeightedDegree (Q₀.map (Polynomial.mapRingHom φ)) 1 (k - 1) ≤
        natWeightedDegree Q 1 (k - 1) := by
      rw [hrep]
      exact natWeightedDegree_C_C_mul_le _ Q 1 (k - 1)
    have h4 : natWeightedDegree Q 1 (k - 1) ≤ D := by
      have h := hQ.Q_deg
      rw [weightedDegree_eq_natWeightedDegree] at h
      exact_mod_cast h
    rw [weightedDegree_eq_natWeightedDegree]
    exact_mod_cast le_trans h1 (le_trans (h2.le.trans h3) h4)
  · -- roots
    intro i
    -- the root holds integrally over `F[Z]`
    have h0 : ((Q₀.eval (Polynomial.C (intPointY f₀ f₁ i))).eval (intPointX ωs i)) = 0 := by
      apply hφinj
      rw [map_zero]
      have hcomm := Polynomial.map_mapRingHom_evalEval (f := φ)
        (intPointX ωs i) (intPointY f₀ f₁ i) (p := Q₀)
      calc φ ((Q₀.eval (Polynomial.C (intPointY f₀ f₁ i))).eval (intPointX ωs i))
          = (Q₀.map (Polynomial.mapRingHom φ)).evalEval
              (φ (intPointX ωs i)) (φ (intPointY f₀ f₁ i)) := hcomm.symm
        _ = (Polynomial.C (Polynomial.C (φ d)) * Q).evalEval
              (liftedDomain ωs i) (genericFold f₀ f₁ i) := by
            rw [hrep, map_intPointX, map_intPointY]
        _ = (Polynomial.C (Polynomial.C (φ d))).evalEval
              (liftedDomain ωs i) (genericFold f₀ f₁ i) *
            Q.evalEval (liftedDomain ωs i) (genericFold f₀ f₁ i) :=
            Polynomial.evalEval_mul _ _ _ _
        _ = 0 := by
            have hroot := hQ.Q_roots i
            show _ * ((Q.eval (Polynomial.C (genericFold f₀ f₁ i))).eval
              (liftedDomain ωs i)) = 0
            rw [hroot, mul_zero]
    -- specialize at `z`
    have hcomm := Polynomial.map_mapRingHom_evalEval (f := σ)
      (intPointX ωs i) (intPointY f₀ f₁ i) (p := Q₀)
    show ((Q₀.map (Polynomial.mapRingHom σ)).eval
      (Polynomial.C (f₀ i + z * f₁ i))).eval (ωs i) = 0
    calc ((Q₀.map (Polynomial.mapRingHom σ)).eval
        (Polynomial.C (f₀ i + z * f₁ i))).eval (ωs i)
        = (Q₀.map (Polynomial.mapRingHom σ)).evalEval
            (σ (intPointX ωs i)) (σ (intPointY f₀ f₁ i)) := by
          rw [eval_intPointX, eval_intPointY]
      _ = σ ((Q₀.eval (Polynomial.C (intPointY f₀ f₁ i))).eval (intPointX ωs i)) := hcomm
      _ = 0 := by rw [h0, map_zero]
  · -- multiplicity
    intro i
    apply GuruswamiSudan.rootMultiplicity_ge_of_shift_zero hz
    intro s t hst
    -- extraction over `K`
    have hKvan := shift_coeff_eq_zero_of_le_rootMultiplicity (hQ.Q_multiplicity i) s t hst
    -- descend to `F[Z]`
    have h0 : ((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
        (intPointY f₀ f₁ i)).coeff t).coeff s = 0 := by
      apply hφinj
      rw [map_zero]
      have hsm := shift_map φ Q₀ (intPointX ωs i) (intPointY f₀ f₁ i)
      rw [hrep, map_intPointX, map_intPointY] at hsm
      calc φ (((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
            (intPointY f₀ f₁ i)).coeff t).coeff s)
          = ((((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
              (intPointY f₀ f₁ i)).map (Polynomial.mapRingHom φ)).coeff t)).coeff s := by
            rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
        _ = (((Polynomial.Bivariate.shift
              (Polynomial.C (Polynomial.C (φ d)) * Q)
              (liftedDomain ωs i) (genericFold f₀ f₁ i)).coeff t)).coeff s := by
            rw [← hsm]
        _ = φ d * (((Polynomial.Bivariate.shift Q (liftedDomain ωs i)
              (genericFold f₀ f₁ i)).coeff t)).coeff s := by
            rw [shift_C_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
        _ = 0 := by rw [hKvan, mul_zero]
    -- re-specialize at `z`
    have hsm := shift_map σ Q₀ (intPointX ωs i) (intPointY f₀ f₁ i)
    rw [eval_intPointX, eval_intPointY] at hsm
    rw [hsm, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h0,
      map_zero]

/-- **The S10 converse, composed with the in-tree GS list decoder.**

At every good `z` (where `Q₀|_{Z:=z} ≠ 0`), every degree-`< k` codeword within the GS
Johnson radius of the scalar fold `f_z = f₀ + z·f₁` divides the specialized integer
interpolant: `(Y − C p_z) ∣ Q₀|_{Z:=z}`. Together with the forward half
(`decoded_affine_pair_divides_specialization`), both the `K`-level affine pairs and the
per-`z` decoded codewords land in the factor structure of the **same** polynomial
`Q₀|_{Z:=z}` — the complete S10 divisibility bridge for the Theorem-2 cover. -/
theorem scalar_fold_decoded_divides_specialization {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (p : ReedSolomon.code ωs k)
    (h_dist :
      (hammingDist (fun i => f₀ i + z * f₁ i)
          (fun i => (ReedSolomon.codewordToPoly p).eval (ωs i)) : ℝ) / n <
        gs_johnson k n m) :
    Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  exact GuruswamiSudan.gs_divisibility (m := m) hk hm p
    (specialized_conditions ωs f₀ f₁ hQ hrep z hz) h_dist

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.natWeightedDegree_map_le
#print axioms GuruswamiSudan.OverRatFunc.natWeightedDegree_map_eq_of_injective
#print axioms GuruswamiSudan.OverRatFunc.natWeightedDegree_C_C_mul_le
#print axioms GuruswamiSudan.OverRatFunc.shift_map
#print axioms GuruswamiSudan.OverRatFunc.shift_C_C_mul
#print axioms GuruswamiSudan.OverRatFunc.shift_coeff_eq_zero_of_le_rootMultiplicity
#print axioms GuruswamiSudan.OverRatFunc.specialized_conditions
#print axioms GuruswamiSudan.OverRatFunc.scalar_fold_decoded_divides_specialization
