/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS4Depth3PatternDecomposition

/-!
# R327: above the annihilator height, depth-3 wraparound excess vanishes

Unlike the C3 collision consumer, this uses FS3 directly on the arbitrary
six-term pattern polynomial appearing in FS4.  Thus it genuinely covers the
whole excess filter, not only duplicated-index patterns.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing

open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition

theorem wraparoundExcess_eq_zero_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    wraparoundExcess ζ (2 ^ k) = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro t ht hbad
  rcases hbad with ⟨hnonzero, hroot⟩
  have hcomponents :
      t.1 < 2 * (2 ^ k) ∧ t.2.1 < 2 * (2 ^ k) ∧
        t.2.2.1 < 2 * (2 ^ k) ∧ t.2.2.2.1 < 2 * (2 ^ k) ∧
        t.2.2.2.2.1 < 2 * (2 ^ k) ∧ t.2.2.2.2.2 < 2 * (2 ^ k) := by
    simpa [tupleSet] using ht
  obtain ⟨N, hN, hheight, hdiv⟩ := pattern_annihilator_exists_with_height
    (k := k) (b := 3)
    (g := pp (2 ^ k) t) hnonzero (by
      simpa [pp] using patternPoly_natDegree_lt (m := 2 ^ k) (by positivity)
        hcomponents.1 hcomponents.2.1 hcomponents.2.2.1 hcomponents.2.2.2.1
        hcomponents.2.2.2.2.1 hcomponents.2.2.2.2.2) (by
      intro i
      simpa [pp] using patternPoly_coeff_abs_le (2 ^ k) t.1 t.2.1 t.2.2.1
        t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 i)
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hlt : N < prime := lt_of_le_of_lt hheight hprime
  have hle : prime ≤ N := Nat.le_of_dvd hpos
    (hdiv F inferInstance prime inferInstance ζ hhalfTurn (by
      simpa [pp] using hroot))
  omega

end ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing

#print axioms
  ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing.wraparoundExcess_eq_zero_of_characteristic_above_height
