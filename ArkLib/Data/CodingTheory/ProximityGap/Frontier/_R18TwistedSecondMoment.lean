/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18FourthMomentTwist
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18SigmaGate

/-!
# Round 18: twisted second-moment core for Σ-equidistribution

This file extracts the first analytic component from the red `_R18SigmaEquidistribution` draft:

* exact expansion of the `χ`-twisted second moment of the period weights into Gauss sums;
* the triangle/Gauss-sum bound
  `‖∑_b χ(b)‖η_b‖²‖ ≤ |G|(|G|-1)√q`.

Together with the Σ gate in `_R18SigmaGate`, this is one of the pieces needed to discharge the
`hSig` input of the r = 2 Weil rung from actual character orthogonality.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum

namespace ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `χ`-twisted second moment expands exactly into Gauss sums indexed by pairs
`(x,y) ∈ G²`. -/
theorem twisted_secondMoment_eq_gaussSums
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) :
    ∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))
      = ∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y)) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, conj' (ψ a) = ψ (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))
      = ∑ b : F, ∑ x ∈ G, ∑ y ∈ G, χ b * ψ (b * (x - y)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : conj' (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
          rw [eta, map_sum (starRingEnd ℂ)]
          exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
        rw [hconjeta, eta, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have harg : b * x + -(b * y) = b * (x - y) := by ring
        rw [← AddChar.map_add_eq_mul, harg]
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ b : F, χ b * ψ (b * (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y)) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [gaussSum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [AddChar.mulShift_apply, mul_comm (x - y) b]

/-- Triangle bound on the twisted second moment: the diagonal pairs contribute zero for
nontrivial `χ`; each off-diagonal pair contributes one Gauss sum of norm `√q`. -/
theorem norm_twisted_secondMoment_le
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) :
    ‖∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))‖
      ≤ (G.card : ℝ) * ((G.card : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
  classical
  rw [twisted_secondMoment_eq_gaussSums χ ψ G]
  have hterm : ∀ x ∈ G, ∀ y ∈ G,
      ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖
        = if x = y then 0 else Real.sqrt (Fintype.card F : ℝ) := by
    intro x _ y _
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, sub_self, AddChar.mulShift_zero]
      have h0 : gaussSum χ (1 : AddChar F ℂ) = 0 := by
        rw [gaussSum]
        have h1 : ∀ b : F, χ b * (1 : AddChar F ℂ) b = χ b := by
          intro b
          rw [AddChar.one_apply, mul_one]
        rw [Finset.sum_congr rfl (fun b _ => h1 b)]
        exact MulChar.sum_eq_zero_of_ne_one hχ
      rw [h0, norm_zero]
    · rw [if_neg hxy]
      exact norm_gaussSum_eq_sqrt hχ (mulShift_isPrimitive hψ (sub_ne_zero_of_ne hxy))
  have hle : ‖∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y))‖
      ≤ ∑ x ∈ G, ∑ y ∈ G, ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun x _ => norm_sum_le _ _
  refine hle.trans ?_
  have hinner : ∀ x ∈ G, ∑ y ∈ G, ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖
      = ((G.card : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
    intro x hx
    rw [Finset.sum_congr rfl (fun y hy => hterm x hx y hy)]
    rw [← Finset.add_sum_erase G _ hx, if_pos rfl, zero_add]
    have hstep : ∀ y ∈ G.erase x,
        (if x = y then (0 : ℝ) else Real.sqrt (Fintype.card F : ℝ))
          = Real.sqrt (Fintype.card F : ℝ) := by
      intro y hy
      exact if_neg (fun h => (Finset.ne_of_mem_erase hy) h.symm)
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem hx]
    have hpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [Nat.cast_sub hpos, Nat.cast_one]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **Indicator decomposition of subgroup spectral mass.**  For `χ` cutting out the subgroup
`Gχ = {b : χ b = 1}`, multiplying the `Gχ`-restricted second moment by `orderOf χ` equals the sum
of the `χ^j`-twisted second moments over `j < orderOf χ`. -/
theorem sigma_indicator_decomp (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) :
    (orderOf χ : ℂ) * ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b)
      = ∑ j ∈ Finset.range (orderOf χ),
          ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
  classical
  rw [Finset.sum_comm]
  symm
  calc ∑ b : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) b
        * (eta ψ G b * conj' (eta ψ G b))
      = ∑ b : F, (∑ j ∈ Finset.range (orderOf χ), (χ ^ j) b)
          * (eta ψ G b * conj' (eta ψ G b)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ b : F, (if χ b = 1 then (orderOf χ : ℂ) else 0)
          * (eta ψ G b * conj' (eta ψ G b)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [mulChar_pow_sum_all]
    _ = ∑ b : F, if χ b = 1 then
          (orderOf χ : ℂ) * (eta ψ G b * conj' (eta ψ G b)) else 0 := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        simp only [ite_mul, zero_mul]
    _ = ∑ b ∈ Gchi χ, (orderOf χ : ℂ) * (eta ψ G b * conj' (eta ψ G b)) := by
        rw [Gchi, Finset.sum_filter]
    _ = (orderOf χ : ℂ) * ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b) := by
        rw [Finset.mul_sum]

/-- The zero frequency period is the cardinality of the support. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  rw [eta]
  have h : ∀ y ∈ G, ψ (0 * y) = 1 := by
    intro y _
    rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ### The Σ lower envelope -/

/-- The trivial-character term:
`∑_b 1(b)·‖η_b‖² = |G|·q − |G|²` (Parseval minus the DC term). -/
theorem trivial_term_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
      = ((G.card : ℂ)) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2 := by
  classical
  have hsplit : ∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
      = (∑ b : F, eta ψ G b * conj' (eta ψ G b))
        - eta ψ G 0 * conj' (eta ψ G 0) := by
    have hterm : ∀ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
        = (eta ψ G b * conj' (eta ψ G b))
          - (if b = 0 then eta ψ G b * conj' (eta ψ G b) else 0) := by
      intro b
      rcases eq_or_ne b 0 with rfl | hb
      · rw [MulChar.map_nonunit (1 : MulChar F ℂ) not_isUnit_zero, zero_mul, if_pos rfl]
        ring
      · rw [MulChar.one_apply hb.isUnit, one_mul, if_neg hb]
        ring
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ 0 (fun b => eta ψ G b * conj' (eta ψ G b)),
      if_pos (Finset.mem_univ 0)]
  have hpars : (∑ b : F, eta ψ G b * conj' (eta ψ G b))
      = ((G.card : ℂ)) * (Fintype.card F : ℂ) := by
    have hnorm : ∀ b : F, eta ψ G b * conj' (eta ψ G b)
        = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      intro b
      rw [RCLike.mul_conj]
      norm_cast
    rw [Finset.sum_congr rfl (fun b _ => hnorm b), ← Complex.ofReal_sum,
      subgroup_gaussSum_secondMoment hψ G]
    push_cast
    ring
  have hdc : eta ψ G 0 * conj' (eta ψ G 0) = (G.card : ℂ) ^ 2 := by
    rw [eta_zero, map_natCast, sq]
  rw [hsplit, hpars, hdc]

/-- **The Σ lower bound, unconditional**:
`n·q − n² − (m−1)n(n−1)√q ≤ m·Σ`, where
`Σ = ∑_{b∈Gχ} ‖η_b‖²` and `m = orderOf χ`. -/
theorem sigma_lower_bound {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hm : 1 ≤ orderOf χ) :
    (G.card : ℝ) * (Fintype.card F : ℝ) - (G.card : ℝ) ^ 2
        - ((orderOf χ : ℝ) - 1) * ((G.card : ℝ) * ((G.card : ℝ) - 1)
            * Real.sqrt (Fintype.card F : ℝ))
      ≤ (orderOf χ : ℝ) * ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 := by
  classical
  set m : ℕ := orderOf χ with hmdef
  set Sig : ℝ := ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 with hSigdef
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hnorm : ∀ b : F, eta ψ G b * conj' (eta ψ G b)
      = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [RCLike.mul_conj]
    norm_cast
  have hSigC : ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b) = ((Sig : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun b _ => hnorm b), ← Complex.ofReal_sum]
  have hdecomp := sigma_indicator_decomp χ ψ G
  have h0mem : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr hm
  have hsplit : ∑ j ∈ Finset.range m,
        ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))
      = (∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b)))
        + ∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
    rw [← Finset.add_sum_erase _ _ h0mem, pow_zero]
  have htail_bound : ‖∑ j ∈ (Finset.range m).erase 0,
        ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖
      ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ j ∈ (Finset.range m).erase 0,
        ‖∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖
          ≤ n * (n - 1) * Real.sqrt q := by
      intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      exact norm_twisted_secondMoment_le (pow_ne_one_of_lt_orderOf hj.1 hj.2) hψ G
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h0mem, Finset.card_range]
    have hm1 : 1 ≤ m := Finset.mem_range.mp h0mem
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hkey : ‖((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ)‖
      ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := by
    have hcx : (((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)
        = ∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
      have hlhs : ((m : ℂ)) * ((Sig : ℝ) : ℂ)
          = (∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b)))
            + ∑ j ∈ (Finset.range m).erase 0,
                ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
        rw [← hSigC, ← hsplit, ← hdecomp]
      rw [trivial_term_eq hψ G] at hlhs
      have : (((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)
          = ((m : ℂ)) * ((Sig : ℝ) : ℂ)
            - (((G.card : ℂ)) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2) := by
        push_cast [hndef, hqdef]
        ring
      rw [this, hlhs]
      ring
    calc ‖((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ)‖
        = ‖(((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
      _ = ‖∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖ := by rw [hcx]
      _ ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := htail_bound
  have habs := abs_le.mp (by rwa [Real.norm_eq_abs] at hkey)
  linarith [habs.1]

/-- The unconditional Σ-equidistribution estimate in the abstract `SigmaLowerEnvelope` form used
by `_R18SigmaGate`. -/
theorem sigmaLowerEnvelope_of_gchi {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (hm : 1 ≤ orderOf χ) :
    ArkLib.ProximityGap.Frontier.R18SigmaGate.SigmaLowerEnvelope
      (orderOf χ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
      (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) := by
  exact sigma_lower_bound (χ := χ) hψ G hm

/-- Compact-core `hSig` corollary: in the R17 regime `16m²n² ≤ q`, the character subgroup
`Gχ` carries at least half its expected period mass. -/
theorem hSig_of_gchi {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) * (Fintype.card F : ℝ)
      ≤ 2 * (orderOf χ : ℝ) * ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 := by
  exact ArkLib.ProximityGap.Frontier.R18SigmaGate.hSig_of_sigmaLowerEnvelope_field
    ψ G (Gchi χ) (by exact_mod_cast hm) hn hreg
    (sigmaLowerEnvelope_of_gchi (χ := χ) hψ G (le_trans (by norm_num) hm))

/-- Compact r = 2 consumer with both R18 plumbing inputs discharged: `hSig` comes from this
file's twisted-second-moment estimate, and `FourthMomentTwistBound` comes from the quartic
Weil/Hasse adapter. -/
theorem wickAwayAtWithConstant_two_of_gchi_quarticWeil
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.WickAwayAtWithConstant
      ψ G (Gchi χ) D 2
      (32 * (6 * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3) :=
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.wickAwayAtWithConstant_two_of_weil
    ψ G (Gchi χ) D X g (orderOf χ) (le_trans (by norm_num) hm) (by norm_num)
    hdec hg
    (ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
      G X hW hn4q)
    hq1 hnq
    (hSig_of_gchi hψ G hm hn hreg)

end ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.twisted_secondMoment_eq_gaussSums
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.norm_twisted_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigma_indicator_decomp
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.eta_zero
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.trivial_term_eq
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigma_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigmaLowerEnvelope_of_gchi
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.hSig_of_gchi
#print axioms
  ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.wickAwayAtWithConstant_two_of_gchi_quarticWeil
