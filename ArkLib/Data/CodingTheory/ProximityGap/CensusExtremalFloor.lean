/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAGeneralLowerBound

/-!
# Red team: `CensusUpperExtremal` is FALSE at empty-census rungs — and the floor repair

Adversarial review of the just-landed census-conditional pin chain, applied to its own
named hypothesis. **Finding:** `CensusUpperExtremal` (the formalization of the O138
"corrected extremality conjecture", `ε_mca·|F| = #census`) is **refutable today**:

* every proper linear code has the unconditional floor `ε_mca(C, δ) ≥ 1/|F|` at every
  below-capacity radius (`epsMCA_ge_inv_card_of_finrank_lt` — the zero/non-codeword stack
  fires at `γ = 0`);
* but the O139/O140 probes *measured empty census rungs inside the window* (the family
  death radius: at `(16,4)`, agreement `a = 7`, the constrained census is empty at every
  `p ≥ 97`); at such a rung the hypothesis demands `ε_mca ≤ 0/|F| = 0` — contradiction.

`censusUpperExtremal_false_of_empty` machine-checks this: empty census at any in-range
agreement above the crossing + below-capacity rank refutes the hypothesis. **The O138
conjecture as posted cannot be exactly right at death radii.**

**The minimal repair** (`CensusUpperExtremalFloor`): absorb the floor —
`ε_mca(C, 1 − a/n) ≤ (#census + 1)/|F|`. The repaired conditional pin
(`mcaDeltaStar_eq_of_censusCrossingFloor`) goes through verbatim with the `+1` carried in
the numerics, and the F₅ instantiation still pins `δ* = 1/4`
(`mcaDeltaStar_F5_via_censusFloor`) — the repair is non-destructive.

**Honest status of the repaired hypothesis.** `+1` asserts that at death radii *nothing
takes over*: the only badness beyond the adjacent-pair census is the universal floor.
That is exactly O139's registered open question ("does anything take over below the death
radius?") — so the higher-monomial death-radius scan is now precisely a *falsifier of the
repaired hypothesis*, and the hypothesis is falsified iff some family takes over. The
red-team loop is closed: the named input to the δ* pin is no longer trivially false, and
its falsification surface is an already-registered probe.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (O138/O139/O140; the census-conditional pin arc); `DISPROOF_LOG.md` entry.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.CensusExtremalFloor

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.MCAGeneralLower

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The refutation -/

/-- The grid radius coerces to `ℝ` as expected. -/
theorem grid_coe {a : ℕ} (han : a ≤ Fintype.card ι) :
    (((1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0)) : ℝ≥0) : ℝ)
      = 1 - (a : ℝ) / (Fintype.card ι : ℝ) := by
  have hn0 : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hle : (a : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 := by
    rw [div_le_one hn0]
    exact_mod_cast han
  rw [NNReal.coe_sub hle]
  push_cast
  norm_num

/-- **The red-team refutation:** an empty census at any in-range agreement above the
crossing, for a code of rank `< a` (below capacity at that radius), refutes
`CensusUpperExtremal` outright — the universal `1/|F|` floor survives where the census
dies. The O139 death-radius measurement instantiates the hypotheses at `(16,4)`,
`a = 7`, `p ≥ 97`. -/
theorem censusUpperExtremal_false_of_empty
    (C : Submodule F (ι → F)) (H : Finset F) {k ac a : ℕ}
    (hac : ac < a) (han : a ≤ Fintype.card ι)
    (hempty : constrainedCensus H k a = ∅)
    (hrank : (Module.finrank F ↥C : ℝ) < (a : ℝ)) :
    ¬ CensusUpperExtremal (F := F) (A := F) (↑C : Set (ι → F)) H k ac := by
  intro hext
  have h := hext a hac han
  rw [hempty] at h
  simp only [Finset.card_empty, Nat.cast_zero, ENNReal.zero_div] at h
  have hfloor : (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (↑C : Set (ι → F))
          (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
    refine epsMCA_ge_inv_card_of_finrank_lt C _ ?_
    rw [grid_coe han]
    have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hgrid : (1 - (1 - (a : ℝ) / (Fintype.card ι : ℝ))) * (Fintype.card ι : ℝ)
        = (a : ℝ) := by
      field_simp
      ring
    rw [hgrid]
    exact hrank
  have hpos : (0 : ℝ≥0∞) < 1 / (Fintype.card F : ℝ≥0∞) :=
    ENNReal.div_pos one_ne_zero (ENNReal.natCast_ne_top _)
  exact absurd (le_trans hfloor h) (not_le.mpr hpos)

/-! ## The floor repair -/

/-- **The repaired named hypothesis:** above the crossing agreement, no stack beats the
census *plus the universal floor*. The `+1` is itself conjectural — it asserts that at
death radii nothing takes over beyond the floor; the registered higher-monomial
death-radius scan is its falsifier. -/
def CensusUpperExtremalFloor (C : Set (ι → F)) (H : Finset F) (k ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ Fintype.card ι →
    epsMCA (F := F) (A := F) C (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0))
      ≤ (((constrainedCensus H k a).card + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

/-- **The repaired census-conditional δ\* pin.** Identical to
`mcaDeltaStar_eq_of_censusCrossing'`, with the floor-absorbing `+1` carried through the
numerics; the lower side is still the census-law theorem `census_le_epsMCA`. -/
theorem mcaDeltaStar_eq_of_censusCrossingFloor (dom : ι → F)
    (hinj : Function.Injective dom) (k : ℕ) (εstar : ℝ≥0∞) {ac : ℕ}
    (hk : 1 ≤ k) (hkac : k + 1 ≤ ac) (hacn : ac ≤ Fintype.card ι)
    (hupper : CensusUpperExtremalFloor (F := F)
      (evalCode dom k : Set (ι → F)) (Finset.univ.image dom) k ac)
    (hcensus : ∀ a : ℕ, ac < a → a ≤ Fintype.card ι →
      (((constrainedCensus (Finset.univ.image dom) k a).card + 1 : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hbad : εstar < ((constrainedCensus (Finset.univ.image dom) k ac).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F) (evalCode dom k : Set (ι → F)) εstar
      = 1 - (ac : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  have hlower : εstar < epsMCA (F := F) (A := F) (evalCode dom k : Set (ι → F))
      (1 - (ac : ℝ≥0) / (Fintype.card ι : ℝ≥0)) :=
    lt_of_lt_of_le hbad (census_le_epsMCA dom hinj hk hkac hacn)
  refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump _ _ tsub_le_self ?_ hlower
  intro δ hδ
  rw [epsMCA_eq_grid (evalCode dom k : Set (ι → F)) δ]
  set n := Fintype.card ι with hn
  set a := agreeOf n δ with ha
  have hac_lt : ac < a := by
    have h1 : δ + (ac : ℝ≥0) / (n : ℝ≥0) < 1 := by
      have := hδ
      rwa [lt_tsub_iff_right] at this
    have h2 : (ac : ℝ≥0) / (n : ℝ≥0) < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (ac : ℝ≥0) / (n : ℝ≥0) + δ = δ + (ac : ℝ≥0) / (n : ℝ≥0) := add_comm _ _
        _ < 1 := h1
    have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by
      exact_mod_cast Fintype.card_pos
    have h3 : (ac : ℝ≥0) < (1 - δ) * (n : ℝ≥0) := by
      have := mul_lt_mul_of_pos_right h2 hn0
      rwa [div_mul_cancel₀ _ (ne_of_gt hn0)] at this
    rw [ha]
    unfold agreeOf
    exact Nat.lt_ceil.mpr h3
  exact le_trans (hupper a hac_lt (agreeOf_le n δ)) (hcensus a hac_lt (agreeOf_le n δ))

/-! ## Non-destructiveness: the F₅ pin survives the repair -/

section F5

open ProximityGap.MCADeltaStarExactPoint

/-- The F₅ domain, as the image of `gdom`. -/
theorem image_gdom : Finset.univ.image gdom = ({1, 2, 4, 3} : Finset F5) := by decide

/-- The census at agreement 4 over the literal domain. -/
theorem census_F5_a4' : constrainedCensus ({1, 2, 4, 3} : Finset F5) 2 4 = {0} := by
  decide

/-- The census at agreement 3 over the literal domain. -/
theorem census_F5_a3' :
    constrainedCensus ({1, 2, 4, 3} : Finset F5) 2 3 = {1, 2, 3, 4} := by
  decide

/-- The degree-`< 2` evaluation code on `gdom` is proper. -/
theorem evalCode_gdom_proper : (evalCode gdom 2 : Set (Fin 4 → F5)) ≠ Set.univ := by
  intro huniv
  have hmem : (fun i => if i = 3 then (1 : F5) else 0) ∈
      (evalCode gdom 2 : Set (Fin 4 → F5)) := by
    rw [huniv]; trivial
  obtain ⟨q, hq, hf⟩ := (mem_evalCode _).mp hmem
  have h0 : (0 : F5) = q.eval (gdom 0) := by simpa using hf 0
  have h1 : (0 : F5) = q.eval (gdom 1) := by simpa using hf 1
  have h2 : (0 : F5) = q.eval (gdom 2) := by simpa using hf 2
  have h3 : (1 : F5) = q.eval (gdom 3) := by simpa using hf 3
  have hq0 : q = 0 := by
    by_contra hqne
    have hsub : ({1, 2, 4} : Finset F5) ⊆ q.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hqne]
      fin_cases hx
      · show q.IsRoot 1
        rw [Polynomial.IsRoot, show (1 : F5) = gdom 0 from rfl]
        exact h0.symm
      · show q.IsRoot 2
        rw [Polynomial.IsRoot, show (2 : F5) = gdom 1 from rfl]
        exact h1.symm
      · show q.IsRoot 4
        rw [Polynomial.IsRoot, show (4 : F5) = gdom 2 from rfl]
        exact h2.symm
    have hcount : 3 ≤ q.natDegree := by
      calc 3 = ({1, 2, 4} : Finset F5).card := by decide
        _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
        _ ≤ q.natDegree := Polynomial.card_roots' q
    omega
  rw [hq0] at h3
  simp at h3

/-- The repaired upper hypothesis holds at F₅ (with room: `ε_mca(0) = 1/5 ≤ 2/5`). -/
theorem censusUpperExtremalFloor_F5 :
    CensusUpperExtremalFloor (F := F5)
      (evalCode gdom 2 : Set (Fin 4 → F5)) (Finset.univ.image gdom) 2 3 := by
  intro a ha3 ha4
  rw [Fintype.card_fin] at ha4
  interval_cases a
  -- a = 4: ε_mca(C, 0) = 1/5 ≤ (1+1)/5
  rw [grid_radius_a4, image_gdom, census_F5_a4', Finset.card_singleton]
  have hsmall : (0 : ℝ≥0) * (Fintype.card (Fin 4) : ℝ≥0) < 1 := by
    rw [zero_mul]; norm_num
  rw [epsMCA_eq_inv_card_of_small_radius (evalCode gdom 2) hsmall]
  · gcongr
    exact_mod_cast one_le_two
  · exact evalCode_gdom_proper

/-- The repaired numerics at F₅: `(census(4) + 1)/5 = 2/5 ≤ 2/5`. -/
theorem censusGoodFloor_F5 : ∀ a : ℕ, 3 < a → a ≤ Fintype.card (Fin 4) →
    (((constrainedCensus (Finset.univ.image gdom) 2 a).card + 1 : ℕ) : ℝ≥0∞)
      / (Fintype.card F5 : ℝ≥0∞) ≤ (2/5 : ℝ≥0∞) := by
  intro a ha3 ha4
  rw [Fintype.card_fin] at ha4
  interval_cases a
  rw [image_gdom, census_F5_a4', Finset.card_singleton, ZMod.card]
  simp only [Nat.reduceAdd, Nat.cast_ofNat]
  exact le_refl _

/-- The crossing at F₅: `2/5 < census(3)/5 = 4/5`. -/
theorem censusBadFloor_F5 :
    (2/5 : ℝ≥0∞) < ((constrainedCensus (Finset.univ.image gdom) 2 3).card : ℝ≥0∞)
      / (Fintype.card F5 : ℝ≥0∞) := by
  rw [image_gdom, census_F5_a3', ZMod.card,
    show (({1, 2, 3, 4} : Finset F5)).card = 4 from by decide]
  simp only [Nat.cast_ofNat]
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- **The repair is non-destructive:** the F₅ exact point still pins through the repaired
hypothesis, entirely via census counting (`δ* = 1/4`). -/
theorem mcaDeltaStar_F5_via_censusFloor :
    mcaDeltaStar (F := F5) (A := F5) (evalCode gdom 2 : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞)
      = 1/4 := by
  have h := mcaDeltaStar_eq_of_censusCrossingFloor gdom gdom_injective 2 (2/5 : ℝ≥0∞)
    (by norm_num) (by norm_num) (by rw [Fintype.card_fin]; norm_num)
    censusUpperExtremalFloor_F5 censusGoodFloor_F5 censusBadFloor_F5
  rw [grid_radius_a3] at h
  exact h

end F5

/-! ## Source audit -/

#print axioms censusUpperExtremal_false_of_empty
#print axioms mcaDeltaStar_eq_of_censusCrossingFloor
#print axioms mcaDeltaStar_F5_via_censusFloor

end ProximityGap.CensusExtremalFloor
