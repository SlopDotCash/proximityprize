/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Katerina Hristova,
         Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.Probability.Instances
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-! # Polynomial bounds for VCVio uniform sampling

The native PMF bounds remain available unchanged. These adapters expose the same counting
bounds through VCVio's uniform sampler, for use by packing's batching strategies.
-/

open scoped ENNReal
namespace Probability

/-- A nonzero polynomial has at most its degree divided by the field size probability of zero. -/
lemma prob_schwartz_zippel_mv_polynomial_of_totalDegree_le
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n d : ℕ} (p : MvPolynomial (Fin n) R) (hne : p ≠ 0) (hdeg : p.totalDegree ≤ d) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r p = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have h := _root_.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le p hne hdeg
  rw [prob_uniform_eq_card_filter_div_card] at h
  simpa using h

/-- The `d := n` specialization of
`prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`. -/
lemma prob_schwartz_zippel_mv_polynomial
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n : ℕ}
    (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0) (h_deg : P.totalDegree ≤ n) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r P = 0] ≤
      (n : ℝ≥0∞) / Fintype.card R :=
  prob_schwartz_zippel_mv_polynomial_of_totalDegree_le P h_nonzero h_deg

/-- Scalar-challenge form of the polynomial root bound for one variable. -/
lemma prob_schwartz_zippel_single_variable
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    (p : MvPolynomial (Fin 1) R) {d : ℕ} (hne : p ≠ 0) (hdeg : p.totalDegree ≤ d) :
    Pr{let γ ← $ᵗ R}[MvPolynomial.eval (fun _ : Fin 1 => γ) p = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R :=
  (SampleableType.prEvent_uniformSample_equiv (Equiv.funUnique (Fin 1) R).symm
    (fun r => MvPolynomial.eval r p = 0)).trans_le
      (prob_schwartz_zippel_mv_polynomial_of_totalDegree_le p hne hdeg)


end Probability
