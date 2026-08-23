/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed

/-!
# BCIKS20 curves — assembly of the decoded family and good-coefficient cardinality bounds

This file assembles the coefficientwise decoded family `P z = ∑ i, z^i A_i` from per-coefficient
polynomials (`decoded_family_coefficients_of_coeff_polys`) and packages the cardinality bounds on
the good-coefficient-curve set (`goodCoeffsCurve_card_bounds_of_ennreal_threshold` and its
positive variant), along with reindexing helpers (`curve_sum_reindex_equiv`,
`RS_goodCoeffsCurve_finCongr`) used by the curve correlated-agreement development.
-/

namespace ProximityGap

open Polynomial
open scoped BigOperators LinearCode ProbabilityTheory
open Code
open NNReal

section CoreResults

variable {F : Type} [Field F]

private lemma coeff_zero_of_natDegree_lt {p : Polynomial F} {d j : ℕ}
    (hp : p.natDegree < d) (hj : d ≤ j) :
    p.coeff j = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hj)

/-- Coefficientwise low-degree dependence on `z` assembles a decoded family as
`P z = ∑ i, z^i A_i`. -/
theorem decoded_family_coefficients_of_coeff_polys {l deg : ℕ} [NeZero deg]
    {S' : Finset F} {P : F → Polynomial F}
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < l + 2)
    (hPdeg : ∀ z ∈ S', (P z).natDegree < deg)
    (hcoeff : ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    ∃ A : Fin (l + 2) → Polynomial F,
      (∀ i, (A i).natDegree < deg) ∧
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i := by
  classical
  let A : Fin (l + 2) → Polynomial F := fun i =>
    ∑ j ∈ Finset.range deg, Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j
  have hAdeg : ∀ i, (A i).natDegree < deg := by
    intro i
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    refine lt_of_le_of_lt ?_ (Nat.pred_lt (Nat.ne_of_gt hdegpos))
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.range deg)
      (f := fun j => Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j)
      (n := deg - 1) ?_
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le ((B j).coeff (i : ℕ)) j).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hj))
  refine ⟨A, hAdeg, ?_⟩
  intro z hz
  ext j
  by_cases hj : j < deg
  · rw [hcoeff z hz j hj]
    have hBsum : (B j).eval z =
        ∑ i : Fin (l + 2), (B j).coeff (i : ℕ) * z ^ (i : ℕ) := by
      have hnat := hBdeg j hj
      rw [Polynomial.eval_eq_sum_range' hnat]
      rw [← Fin.sum_univ_eq_sum_range (fun i => (B j).coeff i * z ^ i)]
    rw [hBsum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Polynomial.coeff_C_mul]
    have hcoeffX : (A i).coeff j = (B j).coeff (i : ℕ) := by
      change (∑ x ∈ Finset.range deg,
        Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j =
          (B j).coeff (i : ℕ)
      rw [Polynomial.finset_sum_coeff]
      calc
        (∑ x ∈ Finset.range deg,
            (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
            = (Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j).coeff j := by
                exact Finset.sum_eq_single_of_mem
                  (s := Finset.range deg)
                  (f := fun x =>
                    (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
                  j (Finset.mem_range.mpr hj)
                  (by
                    intro b hb hbj
                    have hjb : j ≠ b := fun h => hbj h.symm
                    change (Polynomial.C ((B b).coeff (i : ℕ)) * Polynomial.X ^ b).coeff j = 0
                    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
                    simp [hjb])
        _ = (B j).coeff (i : ℕ) := by
          simp [Polynomial.coeff_C_mul]
    simp [hcoeffX, mul_comm]
  · have hjge : deg ≤ j := Nat.le_of_not_gt hj
    have hPj : (P z).coeff j = 0 := coeff_zero_of_natDegree_lt (hPdeg z hz) hjge
    rw [hPj, Polynomial.finset_sum_coeff]
    symm
    refine Finset.sum_eq_zero ?_
    intro i _
    have hAj : (A i).coeff j = 0 := coeff_zero_of_natDegree_lt (hAdeg i) hjge
    rw [Polynomial.coeff_C_mul, hAj, mul_zero]

end CoreResults

section CurveAssemblyBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
/-- Convert an ENNReal lower bound on a finite set cardinality into a natural
number strict cardinality bound. -/
theorem finset_card_gt_of_natCast_le_ennreal_lt {α : Type} {S : Finset α}
    {m : ℕ} {x : ENNReal}
    (hm : (m : ENNReal) ≤ x) (hx : x < (S.card : ENNReal)) :
    S.card > m := by
  exact Nat.cast_lt.mp (lt_of_le_of_lt hm hx)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
/-- Convert an ENNReal lower bound on a finite set cardinality into a natural
number weak cardinality bound. The predecessor is convenient because strict
ENNReal comparison against `S.card` only directly yields a strict natural
inequality. -/
theorem finset_card_ge_of_pred_natCast_le_ennreal_lt {α : Type} {S : Finset α}
    {m : ℕ} {x : ENNReal}
    (hm : ((m - 1 : ℕ) : ENNReal) ≤ x) (hx : x < (S.card : ENNReal)) :
    S.card ≥ m := by
  rcases m with _ | m
  · exact Nat.zero_le S.card
  · have hm' : (m : ENNReal) ≤ x := by
      simpa using hm
    exact Nat.succ_le_of_lt (finset_card_gt_of_natCast_le_ennreal_lt hm' hx)

omit [Nonempty ι] [DecidableEq ι] in
/-- Package an ENNReal lower bound on the full good curve set into the two
natural-number cardinality hypotheses used by the coefficient-polynomial
assembly bridge. -/
theorem goodCoeffsCurve_card_bounds_of_ennreal_threshold {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (u : Fin (l + 2) → ι → F) {x : ENNReal}
    (hx :
      x <
        ((RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall : ((l + 1 : ℕ) : ENNReal) ≤ x)
    (hlarge : ((((Fintype.card ι + 1) * (l + 1) : ℕ) - 1 : ℕ) : ENNReal) ≤ x) :
    (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card >
        l + 1 ∧
      (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * (l + 1) := by
  constructor
  · exact finset_card_gt_of_natCast_le_ennreal_lt hsmall hx
  · exact finset_card_ge_of_pred_natCast_le_ennreal_lt hlarge hx

omit [Nonempty ι] [DecidableEq ι] in
/-- Positive-`k` cardinal-bounds form of
`goodCoeffsCurve_card_bounds_of_ennreal_threshold`, matching the natural index
shape of `correlatedAgreement_affine_curves`. -/
theorem goodCoeffsCurve_card_bounds_of_ennreal_threshold_of_pos {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (u : Fin (k + 1) → ι → F) {x : ENNReal}
    (hx :
      x <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall : (k : ENNReal) ≤ x)
    (hlarge : ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤ x) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k ∧
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k := by
  constructor
  · exact finset_card_gt_of_natCast_le_ennreal_lt hsmall hx
  · exact finset_card_ge_of_pred_natCast_le_ennreal_lt hlarge hx

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Reindex a finite sum of curve coefficient words. This is the algebraic
part of changing the coefficient index type in `RS_goodCoeffsCurve`. -/
theorem curve_sum_reindex_equiv {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ ≃ κ') (z : F) (u : κ' → ι → F) (pow : κ' → ℕ) :
    (∑ t : κ, (z ^ pow (e t)) • u (e t)) =
      ∑ t' : κ', (z ^ pow t') • u t' := by
  simpa using (Equiv.sum_comp e (fun t' : κ' => (z ^ pow t') • u t'))

omit [Nonempty ι] [DecidableEq ι] in
/-- `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its
`Fin (k + 1)` coefficient words. -/
theorem RS_goodCoeffsCurve_finCongr {k k' deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (h : k + 1 = k' + 1) (u : WordStack F (Fin (k' + 1)) ι) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
        (fun i => u (finCongr h i)) δ =
      RS_goodCoeffsCurve (k := k') (deg := deg) (domain := domain) u δ := by
  classical
  ext z
  have hsum :
      (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u (finCongr h t)) =
        ∑ t' : Fin (k' + 1), (z ^ (t' : ℕ)) • u t' := by
    simpa using
      (curve_sum_reindex_equiv (F := F) (ι := ι) (e := finCongr h) z u
        (fun t' : Fin (k' + 1) => (t' : ℕ)))
  simp only [RS_goodCoeffsCurve, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsum]

omit [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] in
/-- `jointAgreement` is invariant under reindexing the coefficient words by an
equivalence. This packages the casts needed when a curve helper is stated with
an index type definitionally different from the caller's `Fin (k + 1)`. -/
theorem jointAgreement_reindex_equiv {κ κ' : Type}
    {C : Set (ι → F)} {δ : ℝ≥0}
    {W : κ → ι → F} {W' : κ' → ι → F}
    (e : κ ≃ κ')
    (hW : ∀ i x, W' (e i) x = W i x)
    (h : jointAgreement (C := C) (δ := δ) (W := W')) :
    jointAgreement (C := C) (δ := δ) (W := W) := by
  classical
  obtain ⟨S, hS_card, v', hv'⟩ := h
  refine ⟨S, hS_card, fun i => v' (e i), ?_⟩
  intro i
  constructor
  · exact (hv' (e i)).1
  · intro x hx
    have hx' := (hv' (e i)).2 hx
    rw [Finset.mem_filter] at hx' ⊢
    exact ⟨hx'.1, by simpa [hW i x] using hx'.2⟩

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge where the remaining list-decoding
output is coefficientwise low-degree dependence on the curve parameter.

For every decoded selector `P`, if each coefficient `(P z).coeff j` agrees on
`S'` with a polynomial in `z` of degree `< l + 2`, then the decoded selector
assembles into a Reed-Solomon codeword curve and the original coefficient words
have joint agreement. This is the curve-facing consumer for the §5 extraction
output. -/
theorem subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < l + 2) ∧
            ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    Code.jointAgreement (F := F) (κ := Fin (l + 2)) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  refine subset_goodCoeffsCurve_assembled_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    hS'_card hS'_card₁ hS' ?_
  intro P hdecoded
  obtain ⟨B, hBdeg, hcoeff⟩ := hcoeffPoly P hdecoded
  obtain ⟨A, hAdeg, hPcoeff⟩ :=
    decoded_family_coefficients_of_coeff_polys
      (l := l) (deg := deg) (S' := S') (P := P) B
      hBdeg (fun z hz => (hdecoded z hz).1) hcoeff
  exact decoded_family_coefficients_assemble_codeword_curve
    (deg := deg) (domain := domain) P A hAdeg hPcoeff

omit [DecidableEq ι] in
/-- Full-good-set specialization of
`subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement`.

This is the form expected in the list-decoding branch after the probability
hypothesis has been converted into cardinality lower bounds for
`RS_goodCoeffsCurve`. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    (hS_card :
      (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card >
        l + 1)
    (hS_card₁ :
      (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * (l + 1))
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < l + 2) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  exact subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    (S' := RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    hS_card hS_card₁ (fun z hz => hz) hcoeffPoly

omit [DecidableEq ι] in
/-- Positive-`k` front door for
`goodCoeffsCurve_coeff_polys_implies_jointAgreement`.

The curve theorem is naturally indexed by `Fin (k + 1)`, while the assembly
bridge is stated with `Fin (l + 2)`. For `0 < k`, this specializes the assembly
bridge at `l = k - 1` and transports the result back to the original index
type. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F}
    (hS_card :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k)
    (hS_card₁ :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let l : ℕ := k - 1
  have hlk : l + 1 = k := by omega
  have hlen : l + 2 = k + 1 := by omega
  let u' : Fin (l + 2) → ι → F := fun i => u (finCongr hlen i)
  have hgood_eq :
      RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ =
        RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ := by
    simpa [u', hlk] using
      (RS_goodCoeffsCurve_finCongr (F := F) (ι := ι)
        (k := l + 1) (k' := k) (deg := deg) (domain := domain) (δ := δ)
        (by omega : (l + 1) + 1 = k + 1) u)
  have hja' :
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u') := by
    refine goodCoeffsCurve_coeff_polys_implies_jointAgreement
      (deg := deg) (domain := domain) (δ := δ) (u := u')
      ?_ ?_ ?_
    · simpa [hgood_eq, hlk] using hS_card
    · simpa [hgood_eq, hlk] using hS_card₁
    · intro P hdecoded
      have hdecoded_orig :
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            (P z).natDegree < deg ∧
              δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ domain) ≤ δ := by
        intro z hz
        have hz' :
            z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ := by
          simpa [hgood_eq] using hz
        have hsum :
            (∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u' t) =
              ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
          simpa [u'] using
            (curve_sum_reindex_equiv (F := F) (ι := ι) (e := finCongr hlen) z u
              (fun t : Fin (k + 1) => (t : ℕ)))
        exact ⟨(hdecoded z hz').1, by simpa [hsum] using (hdecoded z hz').2⟩
      obtain ⟨B, hBdeg, hcoeff⟩ := hcoeffPoly P hdecoded_orig
      · refine ⟨B, ?_, ?_⟩
        · intro j hj
          simpa [hlen] using hBdeg j hj
        · intro z hz j hj
          exact hcoeff z (by simpa [hgood_eq] using hz) j hj
  exact jointAgreement_reindex_equiv
    (F := F) (ι := ι) (C := ReedSolomon.code domain deg) (δ := δ)
    (W := u) (W' := u') (e := (finCongr hlen).symm)
    (by intro i x; simp [u'])
    hja'

omit [DecidableEq ι] in
/-- Positive-`k` assembly bridge in the ENNReal-threshold form produced by the
probability calculation in `correlatedAgreement_affine_curves`.

The caller supplies a threshold `x` with `x < |RS_goodCoeffsCurve|`; this theorem
turns lower bounds on `x` into the natural cardinality assumptions required by
`goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos`. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_ennreal
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F} {x : ENNReal}
    (hx :
      x <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall : (k : ENNReal) ≤ x)
    (hlarge : ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤ x)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  have hS_card :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k :=
    finset_card_gt_of_natCast_le_ennreal_lt hsmall hx
  have hS_card₁ :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k :=
    finset_card_ge_of_pred_natCast_le_ennreal_lt hlarge hx
  exact goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos
    (deg := deg) (domain := domain) (δ := δ) hk hS_card hS_card₁ hcoeffPoly

omit [DecidableEq ι] in
/-- Positive-`k` assembly bridge in the exact threshold form produced by
`goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt` in the curve theorem.

After the probability calculation, the remaining proof obligations are the two
lower bounds on this threshold and the coefficient-polynomial extraction
witness. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_prob_threshold
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F}
    (hx :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_ennreal
    (deg := deg) (domain := domain) (δ := δ) hk
    (x := ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
      (Fintype.card F : ENNReal))
    hx hsmall hlarge hcoeffPoly

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed list-decoding assembly theorem.

`Curves.lean` cannot import `ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed`
directly, because that file itself imports the curve front doors.  This module sits
above both sides of the dependency graph, so it can expose the final canonical §5
residual shape under the `ProximityGap` namespace. -/
theorem correlatedAgreement_affine_curves_of_section5_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hExtract : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        ArkLib.CorrelatedAgreementListDecodingClosed.Section5StrictData
          (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed
    (deg := deg) (domain := domain) (δ := δ) hδ hExtract hBoundary

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed canonical coefficient-polynomial
assembly theorem.

This is the uniform canonical-family shape produced after the §5 data have
already been converted into coefficient-polynomial witnesses and uniqueness on
the good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_section5_canonical_coeff_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed_canonical
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalCoeff hBoundaryCard

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed canonical coefficient-polynomial
assembly theorem with canonical coefficient data required only in the strict
Johnson branch. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_coeff_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∃ P₀ : F → Polynomial F,
        (∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
        ∀ P : F → Polynomial F,
          (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            (P z).natDegree < deg ∧
              δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ domain) ≤ δ) →
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed_of_strict_canonical_coeff
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalCoeff hBoundary

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed canonical evaluation-polynomial
assembly theorem with canonical evaluation data required only in the strict
Johnson branch. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_eval_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalEval :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P₀ z).eval (domain x) = (E x).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed_of_strict_canonical_eval
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalEval hBoundary

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed list-decoding assembly theorem
with the strict branch phrased as canonical §5 extraction data for one decoded
family, plus uniqueness. -/
theorem correlatedAgreement_affine_curves_of_section5_canonical_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hCanonicalExtract :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          ∃ _ : ArkLib.CorrelatedAgreementListDecodingClosed.Section5StrictData
            (k := k) (deg := deg) (domain := domain) (δ := δ) u P₀,
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed_of_section5_canonical
    (deg := deg) (domain := domain) (δ := δ) hδ hCanonicalExtract hBoundaryCard

omit [DecidableEq ι] in
/-- Non-cyclic public wrapper for the closed list-decoding assembly theorem
with canonical §5 extraction data required only in the strict Johnson branch. -/
theorem correlatedAgreement_affine_curves_of_strict_section5_canonical_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hCanonicalExtract : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.CorrelatedAgreementListDecodingClosed.StrictCanonicalSection5Data
        (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  open ArkLib.CorrelatedAgreementListDecodingClosed in
  exact correlatedAgreement_affine_curves_listDecoding_closed_of_strict_section5_canonical
    (deg := deg) (domain := domain) (δ := δ) hδ hCanonicalExtract hBoundary

end CurveAssemblyBridge

end ProximityGap
