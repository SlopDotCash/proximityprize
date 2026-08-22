/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# CS25 #82: the Fourier/Parseval identity (deliverable 2 b/d)

For a finite-dimensional code `C ⊆ Fⁿ` and a finite set `B`, the number of pairs in `B` whose
difference lies in `C` equals a character sum over the quotient `G = Fⁿ⧸C`:

  `|G| · #{(w,f) ∈ B² : w - f ∈ C} = ∑_{ψ : Ĝ} Ŝ(ψ)·Ŝ(-ψ)`,  where `Ŝ(ψ) = ∑_{w∈B} ψ(⟦w⟧)`.

This is the MacWilliams/Fourier reduction of the CS25 second-moment off-diagonal: the `ψ = 0` term
contributes `|B|²`, so the off-diagonal is `q^{k-n} ∑_{ψ≠0} ‖Ŝ(ψ)‖²` — a dual-code character sum,
the elegant replacement for the ball-intersection multinomial.

The proof uses only the additive-character orthogonality `∑_ψ ψ g = |G|·[g=0]`
(`AddChar.sum_apply_eq_ite`) and `(-ψ)(a) = ψ(-a)`; no conjugation/`RCLike` norm is needed.
-/

open scoped BigOperators

namespace ArkLib.CS25

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Fourier/Parseval identity.** `|G| · #{(w,f)∈B² : w-f∈C} = ∑_ψ Ŝ(ψ)·Ŝ(-ψ)`. -/
theorem fourier_pair_identity (C : Submodule F (ι → F))
    [Fintype ((ι → F) ⧸ C)] [DecidableEq ((ι → F) ⧸ C)] (B : Finset (ι → F)) :
    (∑ ψ : AddChar ((ι → F) ⧸ C) ℂ,
        (∑ w ∈ B, ψ (C.mkQ w)) * (∑ f ∈ B, (-ψ) (C.mkQ f)))
      = (Fintype.card ((ι → F) ⧸ C) : ℂ)
          * (((B ×ˢ B).filter (fun wf : (ι → F) × (ι → F) => wf.1 - wf.2 ∈ C)).card : ℂ) := by
  classical
  -- per-pair character orthogonality
  have key : ∀ w f : ι → F,
      (∑ ψ : AddChar ((ι → F) ⧸ C) ℂ, ψ (C.mkQ w) * (-ψ) (C.mkQ f))
        = if w - f ∈ C then (Fintype.card ((ι → F) ⧸ C) : ℂ) else 0 := by
    intro w f
    have hpt : ∀ ψ : AddChar ((ι → F) ⧸ C) ℂ,
        ψ (C.mkQ w) * (-ψ) (C.mkQ f) = ψ (C.mkQ (w - f)) := by
      intro ψ
      rw [AddChar.neg_apply', ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, map_sub]
      congr 1; abel
    simp_rw [hpt]
    rw [AddChar.sum_apply_eq_ite]
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- assemble
  have hL :
      (∑ ψ : AddChar ((ι → F) ⧸ C) ℂ, (∑ w ∈ B, ψ (C.mkQ w)) * (∑ f ∈ B, (-ψ) (C.mkQ f)))
        = ∑ w ∈ B, ∑ f ∈ B, (if w - f ∈ C then (Fintype.card ((ι → F) ⧸ C) : ℂ) else 0) := by
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    exact key w f
  rw [hL, ← Finset.sum_product']
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end ArkLib.CS25
