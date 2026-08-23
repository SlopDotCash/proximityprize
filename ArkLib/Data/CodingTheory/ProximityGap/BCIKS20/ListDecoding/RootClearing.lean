/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction
import ArkLib.Data.Polynomial.ClearDenomY

/-!
# BCIKS20 §5 list decoding: root clearing across the `Z`-specialization

This file relates roots of the trivariate candidate `Q : F[Z][X][Y]` along the `Z`-evaluation
to common roots of its denominator-cleared form.  It proves the evaluation transport identity
`pg_eval_on_Z_eval_eval_eq_evalEval_evalX` and uses it to turn candidate roots into common
roots of the cleared polynomial (`candidate_eval_roots_to_common_roots_cleared` and the
`pg_candidate_roots_to_common_roots_cleared` variants), bounds the candidate fiber image
(`pg_candidate_fiber_image_card_eq`), and derives the divisibility statements
`embedding_clearDenomY_of_large_candidate_fiber` and
`H_tilde'_dvd_clearDenomY_of_large_candidate_fiber` for a sufficiently large candidate fiber.
-/

namespace ProximityGap

open Polynomial Polynomial.Bivariate
open scoped BigOperators Polynomial.Bivariate

variable {F : Type} [Field F]

theorem pg_eval_on_Z_eval_eval_eq_evalEval_evalX
    (x₀ z : F) (R : F[Z][X][Y]) (P : F[X]) :
    ((pg_eval_on_Z (F := F) R z).eval P).eval x₀ =
      Polynomial.evalEval z (P.eval x₀) (Bivariate.evalX (Polynomial.C x₀) R) := by
  classical
  have evalX_eq_map {R : Type} [CommSemiring R] (a : R) (f : Polynomial (Polynomial R)) :
      Bivariate.evalX a f = f.map (Polynomial.evalRingHom a) := by
    ext n
    simp [Bivariate.evalX, Polynomial.coeff_map]
    simp [Polynomial.coeff]
  let fZ : F[X] →+* F := Polynomial.evalRingHom z
  let q : F[Z][X] := P.map (Polynomial.C)
  let r : F[X] := Polynomial.C x₀
  have hqmap : q.map fZ = P := by
    have hf : fZ.comp (Polynomial.C) = (RingHom.id F) := by
      ext a
      simp [fZ]
    simp [q, Polynomial.map_map, hf]
  have hr : fZ r = x₀ := by
    simp [fZ, r]
  have hcommZ :
      ((pg_eval_on_Z (F := F) R z).eval P).eval x₀ = fZ ((R.eval q).eval r) := by
    have h := Polynomial.map_mapRingHom_eval_map_eval (f := fZ) (p := R) (q := q) r
    simpa [pg_eval_on_Z, fZ, hqmap, hr] using h
  set p := Bivariate.evalX (Polynomial.C x₀) R with hp
  have hp_map : p = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) := by
    exact hp.trans (pg_evalX_eq_map_evalRingHom (F := F) x₀ R)
  have hYX : (R.eval q).eval r = (p.eval (q.eval r)) := by
    have h := (Polynomial.eval₂_hom (p := R) (f := Polynomial.evalRingHom r) q)
    have h' : (R.map (Polynomial.evalRingHom r)).eval ((Polynomial.evalRingHom r) q) =
        (Polynomial.evalRingHom r) (R.eval q) := by
      simpa [Polynomial.eval₂_eq_eval_map] using h
    have h'' : (R.eval q).eval r = (R.map (Polynomial.evalRingHom r)).eval (q.eval r) := by
      simpa [Polynomial.coe_evalRingHom] using h'.symm
    simpa [hp_map, Polynomial.coe_evalRingHom] using h''
  have hfz_eq : fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := by
    have : fZ ((R.eval q).eval r) = fZ (p.eval (q.eval r)) := by
      simp [hYX]
    have h' : (p.map fZ).eval (fZ (q.eval r)) = fZ (p.eval (q.eval r)) := by
      simp
    simp [this, h']
  have hfz_q : fZ (q.eval r) = P.eval x₀ := by
    simp [fZ, q, r]
  calc
    ((pg_eval_on_Z (F := F) R z).eval P).eval x₀ = fZ ((R.eval q).eval r) := hcommZ
    _ = (p.map fZ).eval (fZ (q.eval r)) := hfz_eq
    _ = (p.map fZ).eval (P.eval x₀) := by simp [hfz_q]
    _ = Polynomial.evalEval z (P.eval x₀) p := by
      rw [← _root_.BCIKS20AppendixA.eval_evalX_eq_evalEval p z (P.eval x₀)]
      rw [evalX_eq_map (R := F)]
    _ = Polynomial.evalEval z (P.eval x₀) (Bivariate.evalX (Polynomial.C x₀) R) := by
      rw [hp]

theorem evalEval_evalX_eq_zero_of_pg_eval_on_Z_eval_eq_zero
    (x₀ z : F) {R : F[Z][X][Y]} {P : F[X]}
    (hroot : (pg_eval_on_Z (F := F) R z).eval P = 0) :
    Polynomial.evalEval z (P.eval x₀) (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  have hx := congrArg (fun g : F[X] => g.eval x₀) hroot
  simpa [pg_eval_on_Z_eval_eval_eq_evalEval_evalX x₀ z R P] using hx

/-- A candidate-pair root and a second root become common roots after clearing the
same leading-coefficient denominator introduced by `H_tilde'`. -/
theorem candidate_eval_roots_to_common_roots_cleared
    {H P : F[X][Y]} (hH : 0 < H.natDegree) {z t : F}
    (hHroot : (Bivariate.evalX z H).eval t = 0)
    (hProot : Polynomial.evalEval z t P = 0)
    {e : ℕ} (he : P.natDegree ≤ e) :
    ∃ t' : F,
      Polynomial.evalEval z t' (_root_.BCIKS20AppendixA.H_tilde' H) = 0 ∧
        Polynomial.evalEval z t'
          (Polynomial.clearDenomY (H.coeff H.natDegree) e P) = 0 := by
  refine ⟨(H.coeff H.natDegree).eval z * t, ?_, ?_⟩
  · exact _root_.BCIKS20AppendixA.evalEval_H_tilde'_eq_zero_of_evalX_eq_zero H hH hHroot
  · exact Polynomial.evalEval_clearDenomY_eq_zero_of_evalEval_eq_zero
      (H.coeff H.natDegree) he hProot

theorem pg_candidate_roots_to_common_roots_cleared
    (x₀ z : F) {R : F[Z][X][Y]} {H : F[Z][X]} {P : F[X]}
    (hH : 0 < H.natDegree)
    (hRroot : (pg_eval_on_Z (F := F) R z).eval P = 0)
    (hHroot : (Bivariate.evalX z H).eval (P.eval x₀) = 0)
    {e : ℕ} (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e) :
    ∃ t' : F,
      Polynomial.evalEval z t' (_root_.BCIKS20AppendixA.H_tilde' H) = 0 ∧
        Polynomial.evalEval z t'
          (Polynomial.clearDenomY (H.coeff H.natDegree) e
            (Bivariate.evalX (Polynomial.C x₀) R)) = 0 := by
  exact candidate_eval_roots_to_common_roots_cleared hH hHroot
    (evalEval_evalX_eq_zero_of_pg_eval_on_Z_eval_eq_zero x₀ z hRroot) he

theorem pg_candidate_roots_to_common_roots_cleared'
    (x₀ z : F) {R : F[Z][X][Y]} {H : F[Z][X]} {P : F[X]}
    (hH : 0 < H.natDegree)
    (hroots :
      (pg_eval_on_Z (F := F) R z).eval P = 0 ∧
        (Bivariate.evalX z H).eval (P.eval x₀) = 0)
    {e : ℕ} (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e) :
    ∃ t' : F,
      Polynomial.evalEval z t' (_root_.BCIKS20AppendixA.H_tilde' H) = 0 ∧
        Polynomial.evalEval z t'
          (Polynomial.clearDenomY (H.coeff H.natDegree) e
            (Bivariate.evalX (Polynomial.C x₀) R)) = 0 :=
  pg_candidate_roots_to_common_roots_cleared x₀ z hH hroots.1 hroots.2 he

variable [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ} {k : ℕ} {δ : ℚ}
variable {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}

omit [DecidableEq (RatFunc F)] in
theorem pg_candidate_fiber_image_common_roots_cleared
    (x₀ : F) {R : F[Z][X][Y]} {H : F[Z][X]}
    (hH : 0 < H.natDegree) {e : ℕ}
    (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e) :
    ∀ z ∈
      (Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1),
      ∃ t' : F,
        Polynomial.evalEval z t' (_root_.BCIKS20AppendixA.H_tilde' H) = 0 ∧
          Polynomial.evalEval z t'
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) = 0 := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨zS, hzS, rfl⟩
  have hroots := (Finset.mem_filter.mp hzS).2
  exact pg_candidate_roots_to_common_roots_cleared' x₀ zS.1 hH hroots he

omit [DecidableEq (RatFunc F)] in
theorem pg_candidate_fiber_image_card_eq
    (x₀ : F) (R : F[Z][X][Y]) (H : F[Z][X]) :
    ((Finset.univ.filter
      (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
        let P : F[X] :=
          Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
        (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
          (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1)).card =
      (Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).card := by
  exact Finset.card_image_of_injective _
    (fun a b h => Subtype.ext h)

omit [DecidableEq (RatFunc F)] in
theorem embedding_clearDenomY_of_large_candidate_fiber
    (x₀ : F) {R : F[Z][X][Y]} {H : F[Z][X]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {e D : ℕ}
    (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e)
    (hD : D ≥ Bivariate.totalDegree H)
    (hcard :
      (((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1)).card :
          WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ)) :
    _root_.BCIKS20AppendixA.embeddingOf𝒪Into𝕃 H
      (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
        (Polynomial.clearDenomY (H.coeff H.natDegree) e
          (Bivariate.evalX (Polynomial.C x₀) R)) :
        _root_.BCIKS20AppendixA.𝒪 H) = 0 := by
  exact common_roots_force_lift_zero hH D hD
    (pg_candidate_fiber_image_common_roots_cleared x₀ hH he) hcard

omit [DecidableEq (RatFunc F)] in
theorem embedding_clearDenomY_of_large_candidate_fiber_card
    (x₀ : F) {R : F[Z][X][Y]} {H : F[Z][X]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {e D : ℕ}
    (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e)
    (hD : D ≥ Bivariate.totalDegree H)
    (hcard :
      ((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).card : WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ)) :
    _root_.BCIKS20AppendixA.embeddingOf𝒪Into𝕃 H
      (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
        (Polynomial.clearDenomY (H.coeff H.natDegree) e
          (Bivariate.evalX (Polynomial.C x₀) R)) :
        _root_.BCIKS20AppendixA.𝒪 H) = 0 := by
  have hcard_image :
      (((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1)).card :
          WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ) := by
    rw [pg_candidate_fiber_image_card_eq (F := F) (k := k) (ωs := ωs)
      (δ := δ) (u₀ := u₀) (u₁ := u₁) x₀ R H]
    exact hcard
  exact embedding_clearDenomY_of_large_candidate_fiber
    (F := F) (n := n) (k := k) (δ := δ) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
    x₀ hH he hD hcard_image

omit [DecidableEq (RatFunc F)] in
theorem H_tilde'_dvd_clearDenomY_of_large_candidate_fiber
    (x₀ : F) {R : F[Z][X][Y]} {H : F[Z][X]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {e D : ℕ}
    (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e)
    (hD : D ≥ Bivariate.totalDegree H)
    (hcard :
      (((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1)).card :
          WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ)) :
    _root_.BCIKS20AppendixA.H_tilde' H ∣
      Polynomial.clearDenomY (H.coeff H.natDegree) e
        (Bivariate.evalX (Polynomial.C x₀) R) := by
  exact H_tilde'_dvd_of_embedding_mk_eq_zero hH
    (embedding_clearDenomY_of_large_candidate_fiber
      (F := F) (n := n) (k := k) (δ := δ) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
      x₀ hH he hD hcard)

omit [DecidableEq (RatFunc F)] in
theorem H_tilde'_dvd_clearDenomY_of_large_candidate_fiber_card
    (x₀ : F) {R : F[Z][X][Y]} {H : F[Z][X]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {e D : ℕ}
    (he : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e)
    (hD : D ≥ Bivariate.totalDegree H)
    (hcard :
      ((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).card : WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ)) :
    _root_.BCIKS20AppendixA.H_tilde' H ∣
      Polynomial.clearDenomY (H.coeff H.natDegree) e
        (Bivariate.evalX (Polynomial.C x₀) R) := by
  have hcard_image :
      (((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          let P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
            (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).image
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1)).card :
          WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hH
          (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
            (Polynomial.clearDenomY (H.coeff H.natDegree) e
              (Bivariate.evalX (Polynomial.C x₀) R)) :
            _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ) := by
    rw [pg_candidate_fiber_image_card_eq (F := F) (k := k) (ωs := ωs)
      (δ := δ) (u₀ := u₀) (u₁ := u₁) x₀ R H]
    exact hcard
  exact H_tilde'_dvd_clearDenomY_of_large_candidate_fiber
    (F := F) (n := n) (k := k) (δ := δ) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
    x₀ hH he hD hcard_image

end ProximityGap
