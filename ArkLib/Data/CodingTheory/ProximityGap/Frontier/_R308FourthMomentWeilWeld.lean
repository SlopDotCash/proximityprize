/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FullTowerCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R307MomentSandwich

/-!
# LANE B2 (#466, r=3 rung, R308): the Weil weld — the moment stack IS the R27
  tower (master identity, all r), so `FourthMomentBound` is DISCHARGED modulo
  the ladder's existing `TwoCharacterWeilInput`, and the absolute-C r=3 rung
  reduces to the r=4 tower rung alone

## The master identity (formalized; probe `probe_466_r3_weil_weld.py`,
   machine precision at r = 1..4)

R27's iterated convolution is exactly the convolution powers of the
zero-removed ladder: `iterConv J 1 = Sfun J` (`iterConv_one_eq_sfun`), the
DFT diagonalizes the recursion (`hatF_iterConv : (J^{∗r})^(a) = Ŝ(a)^r`),
and Parseval gives, for EVERY depth `r`:

  **`∑_a ‖Ŝ(a)‖^{2r} = m · ∑_c ‖(J^{∗r})(c)‖²`**
  (`evenMoment_eq_iterConv_energy`)

— the R302–R307 moment stack and the R27 `IterConvEnergyWick` ladder are the
SAME objects in two coordinate systems, with the Wick factor `r!` matching
the complex-Gaussian moment `E‖G‖^{2r} = r!·var^r` exactly.  Consequently:

* `fourthMomentBound_of_iterConvWick_two`:
  `IterConvEnergyWick J q 2 C₂ ⟹ FourthMomentBound (2·C₂²)`;
* `eighthMomentBound_of_iterConvWick_four`:
  `IterConvEnergyWick J q 4 C₄ ⟹ EighthMomentBound (24·C₄⁴)`;
* **headline** `distStratum_absoluteC_of_towerRungs`:
  `IterConvEnergyWick J q 2 C₂ ∧ IterConvEnergyWick J q 4 C₄ ⟹
   DistStratumEnergyBound (3·√(2C₂²·(24C₄⁴)) + 1215)` — absolute constant.

## Does the proven-mod-Weil r=2 machinery discharge `FourthMomentBound`? YES.

The in-tree theorem
`iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget`
(R144) derives `IterConvEnergyWick (jacobiCoeff χ lam) q 2 C` from the NAMED
classical input `TwoCharacterWeilInput` under explicit cap/budget hypotheses
(the prize-regime conditions).  Composed with this file:
**`TwoCharacterWeilInput (+ caps) ⟹ FourthMomentBound (2C²)`** — the quartic
input of R303/R307 is classical-modulo-caps, NOT a new open object.  Probe:
the implied tower constants are `C₂ → 0.96`, `C₄ → 0.89` (sub-Gaussian,
rising to the Gaussian value 1) at m ≤ 1200.

## Why the transfer works at r=2 and stops at r=4 (the precise mechanism)

The incidence-side r=2 rung (`wickAwayAt_two_of_weil`, R17) and the
ladder-side r=2 rung (R144) both succeed because their fourth-moment
expansions retain a FREE `F_q`-variable — a length-`q` complete character
sum per tuple (Weil on curves: `≤ C·√q` each), with the regime condition
(`√q ≥ 16n²`, resp. the R144 caps) letting the q-average beat the tuple
count.  This is NOT the per-tuple structure R304 refuted: R304's obstruction
concerned the ℤ/m-mode average (m modes, Jacobi products of modulus exactly
`q²`, no free `F_q`-variable) — a different decomposition of the same
object.  At r = 4 the same two-character route has no in-tree discharge
(R144 stops at r ≤ 3), and the tuple-count-vs-average bookkeeping worsens
with depth; `IterConvEnergyWick J q 4 C₄` is therefore the SINGLE remaining
open average behind the absolute-C r=3 rung:

  **absolute-C r=3 ⟸ TwoCharacterWeilInput (classical, named, capped)
                      ∧ IterConvEnergyWick@4 (open; probe C₄ ≈ 0.9).**

CORE OPEN, ON-BGK.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R307MomentSandwich
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

/-! ### The master identity: even moments = tower energies -/

section Master

variable {u' : ℕ} [NeZero u']

/-- `iterConv` at depth 1 is the zero-removed ladder. -/
theorem iterConv_one_eq_sfun (J : ZMod (3 * u') → ℂ) :
    iterConv J 1 = Sfun J := by
  funext c
  show (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))},
      iterConv J 0 (c - j) * J j) = Sfun J c
  by_cases hc : c = 0
  · subst hc
    rw [show Sfun (J) (0 : ZMod (3 * u')) = 0 from by unfold Sfun; simp]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj0 : j ≠ 0 := by
      rcases Finset.mem_sdiff.mp hj with ⟨_, hj'⟩
      simpa using hj'
    have : (0 : ZMod (3 * u')) - j ≠ 0 := by
      intro h
      exact hj0 (by linear_combination -h)
    show (if (0 : ZMod (3 * u')) - j = 0 then (1 : ℂ) else 0) * J j = 0
    rw [if_neg this, zero_mul]
  · rw [show Sfun J c = J c from by unfold Sfun; rw [if_pos hc]]
    rw [Finset.sum_eq_single c]
    · show (if c - c = 0 then (1 : ℂ) else 0) * J c = J c
      rw [sub_self, if_pos rfl, one_mul]
    · intro j hj hjc
      have : c - j ≠ 0 := by
        intro h
        have hcj : c = j := by linear_combination h
        exact hjc hcj.symm
      show (if c - j = 0 then (1 : ℂ) else 0) * J j = 0
      rw [if_neg this, zero_mul]
    · intro hc'
      exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, by simpa using hc⟩) hc'

/-- The `iterConv` recursion is `conv2` against the zero-removed ladder. -/
theorem iterConv_succ_eq_conv2 (J : ZMod (3 * u') → ℂ) (r : ℕ) :
    iterConv J (r + 1) = conv2 (Sfun J) (iterConv J r) := by
  funext c
  show (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, iterConv J r (c - j) * J j)
      = ∑ j : ZMod (3 * u'), Sfun J j * iterConv J r (c - j)
  rw [show (Finset.univ \ {(0 : ZMod (3 * u'))})
      = Finset.univ.filter (fun j : ZMod (3 * u') => j ≠ 0) from by ext j; simp,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold Sfun
  by_cases hj : j ≠ 0
  · rw [if_pos hj, if_pos hj]
    ring
  · rw [if_neg hj, if_neg hj, zero_mul]

/-- **The DFT diagonalizes the tower**: `(J^{∗r})^(a) = Ŝ(a)^r`. -/
theorem hatF_iterConv (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ) (r : ℕ)
    (a : ZMod (3 * u')) :
    hatF ψ (iterConv J r) a = (hatF ψ (Sfun J) a) ^ r := by
  induction r with
  | zero =>
    show (∑ x : ZMod (3 * u'), ψ (a * x) * (if x = 0 then (1 : ℂ) else 0)) = 1
    rw [Finset.sum_eq_single (0 : ZMod (3 * u'))]
    · rw [if_pos rfl, mul_one, mul_zero, AddChar.map_zero_eq_one]
    · intro x _ hx
      rw [if_neg hx, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ r ih =>
    rw [iterConv_succ_eq_conv2, hatF_conv2, ih]
    ring

/-- **THE MASTER IDENTITY**: for every depth `r`, the `2r`-th moment of the
DFT is `N` times the R27 tower energy — the R302–R307 moment stack and the
`IterConvEnergyWick` ladder are the same objects. -/
theorem evenMoment_eq_iterConv_energy {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) (J : ZMod (3 * u') → ℂ) (r : ℕ) :
    ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ (2 * r)
      = ((3 * u' : ℕ) : ℝ) * ∑ c : ZMod (3 * u'), ‖iterConv J r c‖ ^ 2 := by
  have hpt : ∀ a : ZMod (3 * u'),
      ‖hatF ψ (Sfun J) a‖ ^ (2 * r) = ‖hatF ψ (iterConv J r) a‖ ^ 2 := by
    intro a
    rw [hatF_iterConv ψ J r a, norm_pow]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a)]
  exact hatF_parseval hψ (iterConv J r)

end Master

/-! ### The weld: tower rungs discharge the moment inputs -/

section Weld

variable {u' : ℕ} [NeZero u']

/-- **The r=2 weld**: the ladder's second tower rung (discharged in-tree
modulo `TwoCharacterWeilInput` by R144) gives the quartic moment input at
`K₄ = 2·C₂²`. -/
theorem fourthMomentBound_of_iterConvWick_two {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {C₂ : ℝ}
    (h2 : IterConvEnergyWick J q 2 C₂) :
    FourthMomentBound ψ J q (2 * C₂ ^ 2) := by
  unfold FourthMomentBound
  have hid := evenMoment_eq_iterConv_energy hψ J 2
  unfold IterConvEnergyWick at h2
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
      = ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ (2 * 2) := by norm_num
    _ = ((3 * u' : ℕ) : ℝ) * ∑ c : ZMod (3 * u'), ‖iterConv J 2 c‖ ^ 2 := hid
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * (C₂ ^ 2 * ((2 : ℕ).factorial : ℝ)
            * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * C₂ ^ 2) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by
        rw [show ((2 : ℕ).factorial : ℝ) = 2 from by norm_num [Nat.factorial]]
        ring

/-- **The r=4 weld**: the fourth tower rung gives the octic moment input at
`K₈ = 24·C₄⁴`. -/
theorem eighthMomentBound_of_iterConvWick_four {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {C₄ : ℝ}
    (h4 : IterConvEnergyWick J q 4 C₄) :
    EighthMomentBound ψ J q (24 * C₄ ^ 4) := by
  unfold EighthMomentBound
  have hid := evenMoment_eq_iterConv_energy hψ J 4
  unfold IterConvEnergyWick at h4
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8
      = ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ (2 * 4) := by norm_num
    _ = ((3 * u' : ℕ) : ℝ) * ∑ c : ZMod (3 * u'), ‖iterConv J 4 c‖ ^ 2 := hid
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * (C₄ ^ 4 * ((4 : ℕ).factorial : ℝ)
            * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) ^ 4) := by
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (24 * C₄ ^ 4) * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4 := by
        rw [show ((4 : ℕ).factorial : ℝ) = 24 from by norm_num [Nat.factorial]]
        ring

/-- **THE ABSOLUTE-C RUNG FROM TOWER RUNGS (headline)**: the r=2 and r=4
rungs of the existing R27 ladder give the r=3 DIST rung with an absolute
constant.  With R144, the r=2 hypothesis is classical modulo
`TwoCharacterWeilInput` (+ caps); the r=4 rung is the single remaining open
average.  Probe: implied constants `C₂ ≈ 0.96`, `C₄ ≈ 0.89`. -/
theorem distStratum_absoluteC_of_towerRungs {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {C₂ C₄ : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₄ : 0 ≤ C₄)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (h2 : IterConvEnergyWick J q 2 C₂)
    (h4 : IterConvEnergyWick J q 4 C₄) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      (3 * Real.sqrt ((2 * C₂ ^ 2) * (24 * C₄ ^ 4)) + 1215) :=
  distStratum_absoluteC_of_fourth_and_eighth hψ
    (by positivity) (by positivity) hJ
    (fourthMomentBound_of_iterConvWick_two hψ h2)
    (eighthMomentBound_of_iterConvWick_four hψ h4)

end Weld

end ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms iterConv_one_eq_sfun
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms iterConv_succ_eq_conv2
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms hatF_iterConv
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms evenMoment_eq_iterConv_energy
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms fourthMomentBound_of_iterConvWick_two
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms eighthMomentBound_of_iterConvWick_four
open ArkLib.ProximityGap.Frontier.R308FourthMomentWeilWeld in
#print axioms distStratum_absoluteC_of_towerRungs
