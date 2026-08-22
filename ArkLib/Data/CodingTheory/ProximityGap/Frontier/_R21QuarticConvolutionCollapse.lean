/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20JacobiParseval

/-!
# LANE B2 (#466 round 21): the quartic collapse in CONVOLUTION-ENERGY form — the tower is
  self-similar

Rounds 19–20 put every face of corrected Problem B in Jacobi normal form: the pure character
part of the face is `T(s) = ∑_{j≠0} J_j·λ_j(s)` with Parseval-tight coefficients.  This brick
lands the exact quartic collapse:

  `T(s)² = ∑_{c ∈ ℤ/m} A(c)·λ_c(s)`   with   `A = J ∗ J` (additive convolution on `ℤ/m`),

  **`quartic_convolution_collapse`** :
  `∑_{s≠0} ‖T(s)‖⁴ = (q−1) · ∑_{c ∈ ℤ/m} ‖A(c)‖²`.

Two structural payoffs:

* **Manifest nonnegativity/normal form.**  The r = 2 Jacobi correlation
  `∑_{j₁+j₂=k₁+k₂} J J conj(J) conj(J)` is EXACTLY the convolution energy `∑_c ‖(J∗J)(c)‖²` —
  no signs, no cancellation bookkeeping; the r = 2 rung at any deg is a statement about the
  additive smoothness of the Jacobi-coefficient sequence on `ℤ/m`.
* **Self-similarity of the tower.**  By discrete Parseval on `ℤ/m`,
  `∑_c ‖(J∗J)(c)‖² = (1/m)·∑_t ‖Ĵ(t)‖⁴`: the fourth moment of the face equals the fourth
  moment of the DFT of its own coefficient sequence — the corrected tower is a fixed point of
  the spectrum ↦ coefficients renormalization.  The deep-depth wall is this self-similarity
  iterated `log q` times; the r = 3 open object is its first non-classical rung.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 21, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- The pure character part of the Jacobi normal form: `T(s) = ∑_{j≠0} J_j·λ_j(s)`
(coefficients `J : ℤ/m → ℂ` abstract — instantiate with `jacobiCoeff`). -/
noncomputable def pureFace (J : ZMod m → ℂ) (lam : ZMod m → F → ℂ) (s : F) : ℂ :=
  ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, J j * lam j s

/-- The additive self-convolution of the coefficient sequence, restricted to nonzero indices:
`A(c) = ∑_{j≠0, c−j≠0} J_j·J_{c−j}`. -/
noncomputable def selfConv (J : ZMod m → ℂ) (c : ZMod m) : ℂ :=
  ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0), J j * J (c - j)

/-- **The square of the face is the `λ`-expansion of the self-convolution**:
`T(s)² = ∑_c A(c)·λ_c(s)` for `s ≠ 0`. -/
theorem pureFace_sq (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) (s : F) :
    (pureFace J lam s) ^ 2 = ∑ c : ZMod m, selfConv J c * lam c s := by
  classical
  rw [pureFace, sq, Finset.sum_mul_sum]
  have hpt : ∀ j ∈ Finset.univ \ {(0 : ZMod m)}, ∀ k ∈ Finset.univ \ {(0 : ZMod m)},
      (J j * lam j s) * (J k * lam k s) = J j * J k * lam (j + k) s := by
    intro j _ k _
    rw [hgrp.add_eq_mul j k s]
    ring
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => hpt j hj k hk))]
  -- RHS: expand selfConv, swap to (j, c), reindex c = j + k
  symm
  calc ∑ c : ZMod m, selfConv J c * lam c s
      = ∑ c : ZMod m, ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0),
          J j * J (c - j) * lam c s := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [selfConv, Finset.sum_mul]
    _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          ∑ c ∈ Finset.univ.filter (fun c => c - j ≠ 0), J j * J (c - j) * lam c s := by
        refine Finset.sum_comm' ?_
        intro c j
        simp only [Finset.mem_univ, Finset.mem_filter, Finset.mem_sdiff,
          Finset.mem_singleton, true_and, and_comm]
    _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ k ∈ Finset.univ \ {(0 : ZMod m)},
          J j * J k * lam (j + k) s := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_bij' (fun c _ => c - j) (fun k _ => j + k) ?_ ?_ ?_ ?_ ?_
        · intro c hc
          have h1 := (Finset.mem_filter.mp hc).2
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using h1⟩
        · intro k hk
          have h1 : k ≠ 0 := by
            have := (Finset.mem_sdiff.mp hk).2; simpa using this
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa using h1
        · intro c _; dsimp only; ring
        · intro k _; dsimp only; ring
        · intro c _
          dsimp only
          congr 2
          ring

/-- **THE QUARTIC CONVOLUTION COLLAPSE (round-21 main theorem).**
`∑_{s≠0} ‖T(s)‖⁴ = (q−1)·∑_{c∈ℤ/m} ‖(J∗J)(c)‖²` — the r = 2 Jacobi correlation is EXACTLY the
additive convolution energy of the coefficient sequence.  Pure orthogonality; no analytic
input. -/
theorem quartic_convolution_collapse (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 4
      = ((Fintype.card F - 1 : ℕ) : ℝ) * ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 := by
  classical
  -- pass to ℂ: Σ ‖T‖⁴ = Σ (T²)·conj(T²), expand T² by pureFace_sq, collapse by orthogonality
  have hcx : ((∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 4 : ℝ) : ℂ)
      = ((Fintype.card F - 1 : ℕ) : ℂ) * ∑ c : ZMod m, ((‖selfConv J c‖ ^ 2 : ℝ) : ℂ) := by
    have hz : ∀ s : F, ((‖pureFace J lam s‖ ^ 4 : ℝ) : ℂ)
        = (pureFace J lam s ^ 2) * (starRingEnd ℂ) (pureFace J lam s ^ 2) := by
      intro s
      have h1 : (pureFace J lam s ^ 2) * (starRingEnd ℂ) (pureFace J lam s ^ 2)
          = ((‖pureFace J lam s ^ 2‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.mul_conj]; norm_cast
      rw [h1, norm_pow]
      push_cast
      ring
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun s _ => hz s)]
    have hexp : ∀ s ∈ Finset.univ.erase (0 : F),
        (pureFace J lam s ^ 2) * (starRingEnd ℂ) (pureFace J lam s ^ 2)
          = ∑ c : ZMod m, ∑ c' : ZMod m,
              selfConv J c * (starRingEnd ℂ) (selfConv J c')
                * (lam c s * (starRingEnd ℂ) (lam c' s)) := by
      intro s _
      rw [pureFace_sq hgrp J s]
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl hexp]
    rw [Finset.sum_comm]
    have hc : ∀ c : ZMod m,
        ∑ s ∈ Finset.univ.erase (0 : F), ∑ c' : ZMod m,
          selfConv J c * (starRingEnd ℂ) (selfConv J c')
            * (lam c s * (starRingEnd ℂ) (lam c' s))
        = ((Fintype.card F - 1 : ℕ) : ℂ) * ((‖selfConv J c‖ ^ 2 : ℝ) : ℂ) := by
      intro c
      rw [Finset.sum_comm]
      have hc' : ∀ c' : ZMod m,
          ∑ s ∈ Finset.univ.erase (0 : F),
            selfConv J c * (starRingEnd ℂ) (selfConv J c')
              * (lam c s * (starRingEnd ℂ) (lam c' s))
          = (if c = c' then selfConv J c * (starRingEnd ℂ) (selfConv J c)
              * ((Fintype.card F - 1 : ℕ) : ℂ) else 0) := by
        intro c'
        rw [← Finset.mul_sum, sum_lam_mul_conj_erase_zero hfam hgrp c c']
        by_cases h : c = c'
        · subst h; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h, if_neg h, mul_zero]
      rw [Finset.sum_congr rfl (fun c' _ => hc' c')]
      rw [Finset.sum_ite_eq (Finset.univ : Finset (ZMod m)) c
        (fun _ => selfConv J c * (starRingEnd ℂ) (selfConv J c)
          * ((Fintype.card F - 1 : ℕ) : ℂ))]
      rw [if_pos (Finset.mem_univ _)]
      have : selfConv J c * (starRingEnd ℂ) (selfConv J c) = ((‖selfConv J c‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.mul_conj]; norm_cast
      rw [this]
      ring
    rw [Finset.sum_congr rfl (fun c _ => hc c), ← Finset.mul_sum]
  have hcast : ((∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 4 : ℝ) : ℂ)
      = ((((Fintype.card F - 1 : ℕ) : ℝ) * ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcx]
    push_cast
    ring
  exact_mod_cast hcast

end ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse.pureFace_sq
#print axioms
  ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse.quartic_convolution_collapse
