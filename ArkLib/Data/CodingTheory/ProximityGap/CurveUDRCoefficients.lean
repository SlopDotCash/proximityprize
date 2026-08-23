/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Curve-UDR stage 1: codeword-curve coefficient extraction (issues #302/#301/#304)

The mathematical heart of the planned curve unique-decoding-regime MCA bound
(`epsMCACurve_udr_le`, plan: issue #302 comment `4668760311`), generalizing the proven pair
machinery of `MCAUDRBound` to degree-`<L` curves:

* `exists_curve_coeffs` — given `L` codewords indexed by `L` distinct scalar nodes, the
  coordinatewise degree-`<L` Lagrange interpolation through them yields coefficient vectors
  `c_0, …, c_{L−1}` that (a) all lie in the code (each is an `F`-linear combination of the
  given codewords, with node-only scalars), and (b) agree with the data rows `u_k` at every
  coordinate where the node values lie on the data curve `∑_k γ^k·u_k` — by uniqueness of
  degree-`<L` interpolation.

Stage 2 (the UD collapse over `⋂ S(γᵢ)` and the per-coordinate root counting, mirroring
`badCount_udr_le`) assembles this into the curve bad-scalar bound and, through the proven seam
`hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`, into Cor 4.11 at every arity in the curve
UD regime. Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.CurveUDR

variable {F : Type} [Field F]
variable {ι : Type}

/-- **Curve-coefficient extraction (stage 1 of the curve-UDR bound).** Given `L` codewords
indexed by `L` distinct scalar nodes, the degree-`<L` interpolating curve through them (taken
coordinatewise) has all its coefficient vectors in the code, and wherever the node values agree
with a degree-`<L` data curve, the extracted coefficients agree with the data rows. -/
theorem exists_curve_coeffs (C : Submodule F (ι → F)) (L : ℕ)
    (nodes : Finset F) (hcard : nodes.card = L)
    (w : F → ι → F) (hwC : ∀ γ ∈ nodes, w γ ∈ C) :
    ∃ c : Fin L → ι → F, (∀ k, c k ∈ C) ∧
      ∀ (i : ι) (u : Fin L → F),
        (∀ γ ∈ nodes, w γ i = ∑ k : Fin L, γ ^ (k : ℕ) * u k) →
        ∀ k : Fin L, c k i = u k := by
  classical
  -- the coordinatewise interpolating polynomial and its coefficients
  set c : Fin L → ι → F := fun k i =>
    (Lagrange.interpolate nodes id (fun γ => w γ i)).coeff k with hc
  refine ⟨c, ?_, ?_⟩
  · -- membership: the coefficient is an `F`-linear combination of the codewords
    intro k
    have hrepr : c k = fun i => ∑ γ ∈ nodes,
        ((∏ γ' ∈ nodes.erase γ, (Polynomial.X - Polynomial.C γ')).coeff k
          / ∏ γ' ∈ nodes.erase γ, (γ - γ')) * w γ i := by
      funext i
      rw [hc]
      simp only
      rw [Lagrange.interpolate_eq_sum]
      rw [Polynomial.finset_sum_coeff]
      refine Finset.sum_congr rfl (fun γ hγ => ?_)
      rw [Polynomial.coeff_C_mul]
      simp only [id]
      ring
    rw [hrepr]
    have : (fun i => ∑ γ ∈ nodes,
        ((∏ γ' ∈ nodes.erase γ, (Polynomial.X - Polynomial.C γ')).coeff k
          / ∏ γ' ∈ nodes.erase γ, (γ - γ')) * w γ i)
        = ∑ γ ∈ nodes,
          ((∏ γ' ∈ nodes.erase γ, (Polynomial.X - Polynomial.C γ')).coeff k
            / ∏ γ' ∈ nodes.erase γ, (γ - γ')) • w γ := by
      funext i
      rw [Finset.sum_apply]
      rfl
    rw [this]
    exact Submodule.sum_mem C (fun γ hγ => Submodule.smul_mem C _ (hwC γ hγ))
  · -- agreement: uniqueness of degree-<L interpolation
    intro i u hu k
    have hinj : Set.InjOn (id : F → F) nodes := Function.injective_id.injOn
    set p : F[X] := ∑ k : Fin L, Polynomial.C (u k) * Polynomial.X ^ (k : ℕ) with hp
    have hdeg : p.degree < nodes.card := by
      rw [hcard, hp]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe L)]
      intro b _
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast b.isLt
    have heval : ∀ γ ∈ nodes, p.eval (id γ) = w γ i := by
      intro γ hγ
      rw [hp]
      rw [Polynomial.eval_finset_sum]
      rw [hu γ hγ]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      simp [id]
      ring
    have hpeq : Lagrange.interpolate nodes id (fun γ => w γ i) = p := by
      symm
      exact Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg heval
    rw [hc]
    simp only [hpeq, hp]
    rw [Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun h => hbk ((Fin.ext h).symm)), mul_zero]
    · intro habs
      exact absurd (Finset.mem_univ k) habs

end ArkLib.ProximityGap.CurveUDR

#print axioms ArkLib.ProximityGap.CurveUDR.exists_curve_coeffs
