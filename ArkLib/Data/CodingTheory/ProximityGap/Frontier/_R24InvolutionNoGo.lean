/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput

/-!
# LANE B2 (#466 round 24): the renormalization is an INVOLUTION — descent strategies are
  structurally closed (no-go), with the supporting exact quotient facts

Round 21 observed the tower is a fixed point of the spectrum ↦ coefficients map and asked
whether a contraction argument could descend the wall.  This brick closes that strategy class:

* `lam_eq_one_on_G` — each `λ_j` is trivial on `G` (derived from the indicator identity plus
  unit modulus by the triangle-equality argument: `∑_j λ_j(w) = m` with `m` unit vectors
  forces every `λ_j(w) = 1`);
* `zero_notMem_of_dualFamily` — `0 ∉ G` (the indicator at `w = 0` vanishes);
* `pureFace_mul_invariant` — the face `T` factors through the quotient `F*/G`:
  `T(u·s) = T(s)` for `u ∈ G`.

**The no-go.**  Since `λ_j(s)` depends only on the coset of `s` and `F*/G ≅ ℤ/m`, the face
`T` restricted to a transversal IS the inverse DFT of the coefficient sequence `J` on `ℤ/m`.
Hence the "level-1 renormalization" `spectrum ↦ coefficients` is the discrete Fourier
transform — an INVOLUTION (up to normalization), not a descent: the level-1 statistics are
isomorphic to the level-0 statistics, and iterating gains nothing.  Any proof of
`TripleConvEnergyBound` must inject genuinely new arithmetic input (the Gauss-angle
equidistribution) rather than renormalize; combined with the round-18 verdict that per-tuple
Weil is insufficient in the prize window, the live proof routes for the r = 3 core narrow to:
(i) Katz-type vertical equidistribution for the Jacobi angle family, or (ii) a fourth,
as-yet-unnamed idea.  This is a REFUTATION-grade round for the contraction strategy
(strategy-level no-go; no new named target).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 24, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R24InvolutionNoGo

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- `0 ∉ G`: the indicator identity at `w = 0` forces it. -/
theorem zero_notMem_of_dualFamily (hfam : SubgroupDualFamily G m lam) : (0 : F) ∉ G := by
  intro h0
  have hind := hfam.indicator 0
  rw [if_pos h0, mul_one] at hind
  have hz : ∑ j : ZMod m, lam j (0 : F) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => hfam.map_zero j), Finset.sum_const, smul_zero]
  rw [hz] at hind
  have hm : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (NeZero.ne m)
  exact hm hind.symm

/-- **Each `λ_j` is trivial on `G`** — the triangle-equality argument: `m` unit vectors
summing to `m` are all `1`. -/
theorem lam_eq_one_on_G (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {u : F} (hu : u ∈ G) (j : ZMod m) :
    lam j u = 1 := by
  classical
  have hu0 : u ≠ 0 := fun h => zero_notMem_of_dualFamily hfam (h ▸ hu)
  have hind := hfam.indicator u
  rw [if_pos hu, mul_one] at hind
  -- real parts: ∑_j Re(λ_j u) = m with Re(λ_j u) ≤ 1 each ⟹ all Re = 1
  have hre : ∑ j' : ZMod m, (lam j' u).re = (m : ℝ) := by
    have := congrArg Complex.re hind
    rw [Complex.re_sum] at this
    simpa using this
  have hre_le : ∀ j' : ZMod m, (lam j' u).re ≤ 1 := by
    intro j'
    have h1 := hgrp.norm_one j' u hu0
    have h2 := Complex.abs_re_le_norm (lam j' u)
    have h3 : |(lam j' u).re| ≤ 1 := by rw [← h1]; exact h2
    exact le_trans (le_abs_self _) h3
  have hre_eq : ∀ j' : ZMod m, (lam j' u).re = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨j₀, hj₀⟩ := hne
    have hlt : (lam j₀ u).re < 1 := lt_of_le_of_ne (hre_le j₀) hj₀
    have hsum_lt : ∑ j' : ZMod m, (lam j' u).re < (m : ℝ) := by
      have hcard : (Finset.univ : Finset (ZMod m)).card = m := by simp [ZMod.card]
      calc ∑ j' : ZMod m, (lam j' u).re
          < ∑ _j' : ZMod m, (1 : ℝ) := by
            refine Finset.sum_lt_sum (fun j' _ => hre_le j') ⟨j₀, Finset.mem_univ _, hlt⟩
        _ = (m : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    linarith [hre]
  -- unit modulus + real part 1 ⟹ the value is 1
  have h1 := hgrp.norm_one j u hu0
  have h2 := hre_eq j
  have him : (lam j u).im = 0 := by
    have hnormsq : (lam j u).re ^ 2 + (lam j u).im ^ 2 = 1 := by
      have := Complex.sq_norm (lam j u)
      rw [h1] at this
      have h4 : Complex.normSq (lam j u) = 1 := by
        rw [← this]; norm_num
      rw [Complex.normSq_apply] at h4
      nlinarith [h4]
    nlinarith [hnormsq, h2, sq_nonneg (lam j u).im]
  exact Complex.ext (by simpa using h2) (by simpa using him)

/-- **The face factors through the quotient `F*/G`**: `T(u·s) = T(s)` for `u ∈ G`.
Consequently the face on a transversal is the inverse DFT of the coefficient sequence — the
renormalization is an involution (see module docstring: the descent-strategy no-go). -/
theorem pureFace_mul_invariant (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {u : F} (hu : u ∈ G) (s : F) :
    pureFace J lam (u * s) = pureFace J lam s := by
  unfold pureFace
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hfam.map_mul j u s, lam_eq_one_on_G hfam hgrp hu j, one_mul]

end ArkLib.ProximityGap.Frontier.R24InvolutionNoGo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R24InvolutionNoGo.zero_notMem_of_dualFamily
#print axioms ArkLib.ProximityGap.Frontier.R24InvolutionNoGo.lam_eq_one_on_G
#print axioms ArkLib.ProximityGap.Frontier.R24InvolutionNoGo.pureFace_mul_invariant
