/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21QuarticConvolutionCollapse

/-!
# LANE B2 (#466 round 22): the SEXTIC convolution collapse — the campaign's open r = 3 object
  in manifestly-nonnegative normal form, machine-stated

Round 21 collapsed the quartic: `∑_{s≠0}‖T‖⁴ = (q−1)·∑_c‖(J∗J)(c)‖²`.  This brick factors the
mechanism into a generic λ-Parseval lemma and lands the sextic:

  `T(s)³ = ∑_d (J∗J∗J)(d)·λ_d(s)`   and   `∑_{s≠0}‖T(s)‖⁶ = (q−1)·∑_d ‖(J∗J∗J)(d)‖²`.

**The open core of corrected Problem B (rounds 18–21) is now EXACTLY the statement**

  `∑_{d∈ℤ/m} ‖(J∗J∗J)(d)‖²  ≤  C·(Wick scale)`   —   triple-convolution energy of the
Jacobi-coefficient sequence.  Manifestly nonnegative, no cancellation bookkeeping left: all
the analytic difficulty is the additive smoothness of `J∗J∗J` on `ℤ/m` (Katz-equidistribution
territory; per-tuple Weil is provably insufficient in the prize window β ∈ (4,6), round 18).
The generic lemma `lamExpansion_parseval` collapses EVERY tower rung the same way:
`T^r = (J^{∗r})·λ` and `∑_{s≠0}‖T‖^{2r} = (q−1)·∑‖J^{∗r}‖²`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 22, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **Generic λ-Parseval**: any `λ`-expansion `∑_c f(c)·λ_c(s)` has punctured second moment
`(q−1)·∑_c ‖f(c)‖²`.  This is the collapse mechanism for every rung of the tower. -/
theorem lamExpansion_parseval (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (f : ZMod m → ℂ) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖∑ c : ZMod m, f c * lam c s‖ ^ 2
      = ((Fintype.card F - 1 : ℕ) : ℝ) * ∑ c : ZMod m, ‖f c‖ ^ 2 := by
  classical
  have hcx : ((∑ s ∈ Finset.univ.erase (0 : F), ‖∑ c : ZMod m, f c * lam c s‖ ^ 2 : ℝ) : ℂ)
      = ((Fintype.card F - 1 : ℕ) : ℂ) * ∑ c : ZMod m, ((‖f c‖ ^ 2 : ℝ) : ℂ) := by
    have hz : ∀ s : F, ((‖∑ c : ZMod m, f c * lam c s‖ ^ 2 : ℝ) : ℂ)
        = (∑ c : ZMod m, f c * lam c s)
            * (starRingEnd ℂ) (∑ c : ZMod m, f c * lam c s) := by
      intro s
      rw [RCLike.mul_conj]
      norm_cast
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun s _ => hz s)]
    have hexp : ∀ s ∈ Finset.univ.erase (0 : F),
        (∑ c : ZMod m, f c * lam c s) * (starRingEnd ℂ) (∑ c : ZMod m, f c * lam c s)
          = ∑ c : ZMod m, ∑ c' : ZMod m,
              f c * (starRingEnd ℂ) (f c') * (lam c s * (starRingEnd ℂ) (lam c' s)) := by
      intro s _
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl hexp]
    rw [Finset.sum_comm]
    have hc : ∀ c : ZMod m,
        ∑ s ∈ Finset.univ.erase (0 : F), ∑ c' : ZMod m,
          f c * (starRingEnd ℂ) (f c') * (lam c s * (starRingEnd ℂ) (lam c' s))
        = ((Fintype.card F - 1 : ℕ) : ℂ) * ((‖f c‖ ^ 2 : ℝ) : ℂ) := by
      intro c
      rw [Finset.sum_comm]
      have hc' : ∀ c' : ZMod m,
          ∑ s ∈ Finset.univ.erase (0 : F),
            f c * (starRingEnd ℂ) (f c') * (lam c s * (starRingEnd ℂ) (lam c' s))
          = (if c = c' then f c * (starRingEnd ℂ) (f c)
              * ((Fintype.card F - 1 : ℕ) : ℂ) else 0) := by
        intro c'
        rw [← Finset.mul_sum, sum_lam_mul_conj_erase_zero hfam hgrp c c']
        by_cases h : c = c'
        · subst h; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h, if_neg h, mul_zero]
      rw [Finset.sum_congr rfl (fun c' _ => hc' c')]
      rw [Finset.sum_ite_eq (Finset.univ : Finset (ZMod m)) c
        (fun _ => f c * (starRingEnd ℂ) (f c) * ((Fintype.card F - 1 : ℕ) : ℂ))]
      rw [if_pos (Finset.mem_univ _)]
      have : f c * (starRingEnd ℂ) (f c) = ((‖f c‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.mul_conj]; norm_cast
      rw [this]
      ring
    rw [Finset.sum_congr rfl (fun c _ => hc c), ← Finset.mul_sum]
  have hcast : ((∑ s ∈ Finset.univ.erase (0 : F),
      ‖∑ c : ZMod m, f c * lam c s‖ ^ 2 : ℝ) : ℂ)
      = ((((Fintype.card F - 1 : ℕ) : ℝ) * ∑ c : ZMod m, ‖f c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcx]
    push_cast
    ring
  exact_mod_cast hcast

/-- The triple convolution `(J∗J∗J)(d) = ∑_{j≠0} (J∗J)(d−j)·J_j`. -/
noncomputable def tripleConv (J : ZMod m → ℂ) (d : ZMod m) : ℂ :=
  ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, selfConv J (d - j) * J j

/-- **The cube of the face is the λ-expansion of the triple convolution**:
`T(s)³ = ∑_d (J∗J∗J)(d)·λ_d(s)`. -/
theorem pureFace_cube (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) (s : F) :
    (pureFace J lam s) ^ 3 = ∑ d : ZMod m, tripleConv J d * lam d s := by
  classical
  have h3 : (pureFace J lam s) ^ 3 = (pureFace J lam s) ^ 2 * pureFace J lam s := by ring
  rw [h3, pureFace_sq hgrp J s, pureFace, Finset.sum_mul_sum]
  -- LHS = Σ_c Σ_j A(c) J_j λ_c λ_j = Σ_c Σ_j A(c) J_j λ_{c+j}
  have hpt : ∀ c : ZMod m, ∀ j ∈ Finset.univ \ {(0 : ZMod m)},
      (selfConv J c * lam c s) * (J j * lam j s)
        = selfConv J c * J j * lam (c + j) s := by
    intro c j _
    rw [hgrp.add_eq_mul c j s]
    ring
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j hj => hpt c j hj))]
  -- swap, reindex c = d − j
  rw [Finset.sum_comm]
  symm
  calc ∑ d : ZMod m, tripleConv J d * lam d s
      = ∑ d : ZMod m, ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          selfConv J (d - j) * J j * lam d s := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [tripleConv, Finset.sum_mul]
    _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ d : ZMod m,
          selfConv J (d - j) * J j * lam d s := Finset.sum_comm
    _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ c : ZMod m,
          selfConv J c * J j * lam (c + j) s := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_nbij' (fun d => d - j) (fun c => c + j) ?_ ?_ ?_ ?_ ?_
        · intro d _; exact Finset.mem_univ _
        · intro c _; exact Finset.mem_univ _
        · intro d _; dsimp only; ring
        · intro c _; dsimp only; ring
        · intro d _
          dsimp only
          congr 2
          ring

/-- **THE SEXTIC CONVOLUTION COLLAPSE (round-22 main theorem).**
`∑_{s≠0} ‖T(s)‖⁶ = (q−1)·∑_{d∈ℤ/m} ‖(J∗J∗J)(d)‖²`.

The campaign's delimited open object (the r = 3 rung, rounds 18–21) is exactly the RHS being
Wick-small: the triple-convolution energy of the Jacobi-coefficient sequence on `ℤ/m`.
Manifestly nonnegative; all analytic difficulty is now additive smoothness of `J∗J∗J`. -/
theorem sextic_convolution_collapse (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 6
      = ((Fintype.card F - 1 : ℕ) : ℝ) * ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 := by
  classical
  have hpt : ∀ s : F, ‖pureFace J lam s‖ ^ 6 = ‖(pureFace J lam s) ^ 3‖ ^ 2 := by
    intro s
    rw [norm_pow]
    ring
  rw [Finset.sum_congr rfl (fun s _ => hpt s)]
  rw [Finset.sum_congr rfl (fun s _ => by rw [pureFace_cube hgrp J s])]
  exact lamExpansion_parseval hfam hgrp (tripleConv J)

end ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse.lamExpansion_parseval
#print axioms ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse.pureFace_cube
#print axioms
  ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse.sextic_convolution_collapse
