/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.ZMod

/-!
# Parseval for the discrete Fourier transform on `ZMod N` (#407 — DFT-uncertainty substrate)

The #407 thread's late reframing (comments "the smooth-domain hardness IS the weakness of the DFT
uncertainty principle on `Z_{2^μ}`", mechanism Chebotarev): the BGK floor is an instance of the
discrete uncertainty principle, and `2`-power groups have the worst uncertainty constant
(subgroup indicators saturate Donoho–Stark). The foundational analytic input — **Parseval** for
the unnormalized `ZMod N` DFT — is not in Mathlib (`Analysis.Fourier.ZMod` has the `dft`
`LinearEquiv`, inversion, and `dft_dft`, but no Plancherel). This file lands it:

> `∑_k ‖𝓕 Φ k‖² = N · ∑_j ‖Φ j‖²`  (unnormalized DFT, `𝓕 Φ k = ∑_j ψ(−jk)·Φ j`).

Proof mirrors `SubgroupGaussSumSecondMoment`: expand `𝓕Φ·conj 𝓕Φ`, swap sums, collapse the inner
`∑_k ψ(−jk)·conj ψ(−j'k) = ∑_k ψ((j'−j)k) = N·[j=j']` via `AddChar.sum_mulShift` (`stdAddChar`
primitive). This is the substrate for the Donoho–Stark support uncertainty
`|supp Φ|·|supp 𝓕Φ| ≥ N` (the next brick), itself the cited mechanism for the prize floor on
`μ_{2^μ}`. Axiom-clean. Issue #407.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.ZModDFTParseval

variable {N : ℕ} [NeZero N]

/-- **Parseval / Plancherel for the unnormalized `ZMod N` DFT:**
`∑_k ‖𝓕 Φ k‖² = N · ∑_j ‖Φ j‖²`. -/
theorem dft_parseval (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have hchar : (0 : ℕ) < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne N)
  have hconj : ∀ a : ZMod N, conj (stdAddChar a) = stdAddChar (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- inner-product orthogonality of the DFT rows
  have hortho : ∀ j j' : ZMod N,
      (∑ k : ZMod N, stdAddChar (-(j * k)) * conj (stdAddChar (-(j' * k))))
        = if j = j' then (N : ℂ) else 0 := by
    intro j j'
    have hterm : ∀ k : ZMod N,
        stdAddChar (-(j * k)) * conj (stdAddChar (-(j' * k))) = stdAddChar (k * (j' - j)) := by
      intro k
      rw [hconj (-(j' * k)), neg_neg, ← AddChar.map_add_eq_mul]
      congr 1; ring
    simp_rw [hterm]
    rw [AddChar.sum_mulShift (j' - j) (isPrimitive_stdAddChar N)]
    simp [sub_eq_zero, eq_comm, ZMod.card]
  -- complex bilinear identity
  have hcomplex : (∑ k : ZMod N, (𝓕 Φ) k * conj ((𝓕 Φ) k))
      = (N : ℂ) * ∑ j : ZMod N, Φ j * conj (Φ j) := by
    calc ∑ k : ZMod N, (𝓕 Φ) k * conj ((𝓕 Φ) k)
        = ∑ k : ZMod N, ∑ j : ZMod N, ∑ j' : ZMod N,
            (stdAddChar (-(j * k)) * Φ j) * conj (stdAddChar (-(j' * k)) * Φ j') := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [dft_apply]
          simp only [smul_eq_mul, map_sum, Finset.sum_mul_sum]
      _ = ∑ j : ZMod N, ∑ j' : ZMod N, (Φ j * conj (Φ j')) *
            (∑ k : ZMod N, stdAddChar (-(j * k)) * conj (stdAddChar (-(j' * k)))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j' _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_mul]; ring
      _ = ∑ j : ZMod N, ∑ j' : ZMod N, (Φ j * conj (Φ j')) * (if j = j' then (N : ℂ) else 0) := by
          simp_rw [hortho]
      _ = (N : ℂ) * ∑ j : ZMod N, Φ j * conj (Φ j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_eq_single j]
          · simp; ring
          · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
          · intro h; exact absurd (Finset.mem_univ j) h
  -- read off the norms
  have hL : (∑ k : ZMod N, (𝓕 Φ) k * conj ((𝓕 Φ) k)) = ((∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [RCLike.mul_conj]; norm_cast
  have hR : (∑ j : ZMod N, Φ j * conj (Φ j)) = ((∑ j : ZMod N, ‖Φ j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RCLike.mul_conj]; norm_cast
  rw [hL, hR] at hcomplex
  have := hcomplex
  push_cast at this
  exact_mod_cast this

end ProximityGap.Frontier.ZModDFTParseval

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ZModDFTParseval.dft_parseval
