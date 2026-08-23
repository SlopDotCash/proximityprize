/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor

/-!
# The campaign reduction `CORE ⇔ Sh(n)=O(1)`, instantiated on a CONCRETE worst-period family (#444)

**Lane-2 capstone rung — joining the abstract campaign equivalence to the REAL Gauss-period object.**

The abstract family capstone `ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound`
proves `prize ⇔ Sh(n)=O(1)` for an *abstract* family `M : ι → ℝ`.  The concrete per-instance bridge
`ConcreteShawValueBridge.prizeBound_worstPeriod_iff_shawValue_le` proves the SINGLE-instance
equivalence on the real worst period `M(μ_n) = worstPeriod ψ G hne`, and
`ConcreteShawValueThinFloor` gives the per-instance clean corridor `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)`.

What had NOT been stated anywhere: the **family-level** campaign equivalence over a CONCRETE
worst-period family — i.e. `(∃ C, ∀ i, M(μ_{n_i}) ≤ C·√(n_i·L_i)) ⇔ (∃ C, ∀ i, Sh_i ≤ C)`, with the
raw `M_i` being the *actual* character-sum worst period of the `i`-th thin instance, together with the
UNIFORM (`n`-independent) lower companion `1/√(2L_i) ≤ Sh_i` that makes the bounded-Shaw side a genuine
two-sided sandwich on the real object (not a vacuous `∃C`).

This is the exact statement a referee wants: "the proximity prize, for the real family of thin
Gauss-period sup norms, is equivalent to a uniform bound on Shaw's value, and that value is already
known to sit on the floor `1/√(2L)` from below."

## What this file supplies

A bundled per-index thin instance `ThinInstance ι` (each index carries its own field `F_i`, primitive
additive character `ψ_i`, subgroup `G_i`, with the thin-regime guards `1 ≤ |G_i|`, `2|G_i| ≤ |F_i|`,
`0 < L_i`, and the nonempty-frequency witness).  Then:

* `corePrizeBound_iff_shawBounded` — the **family campaign equivalence** on the concrete worst-period
  family: a uniform raw prize bound is exactly a uniform Shaw-value bound (same constant), for the REAL
  `M_i = worstPeriod ψ_i G_i`.
* `shawValue_floor_uniform` — the **uniform `n`-independent floor** `1/√(2L_i) ≤ Sh_i` on every member.
* `shawBounded_sandwich` — the bounded-Shaw side is a genuine two-sided sandwich:
  `1/√(2L_i) ≤ Sh_i ≤ C` for all `i`, so the campaign predicate is NON-vacuous on the real object.

## Honesty (the prize is the GAP, untouched)

Pure Lane-2 INSTANTIATION + bundling.  Every analytic input (the Parseval/thin floor, the trivial
ceiling, the normalization equivalence) is an already-proven, in-tree, axiom-clean theorem; this file
only quantifies them over a concrete family and conjoins them.  NO anti-concentration, NO completion,
NO moment, NO cancellation, NO capacity claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` (equivalently the
existence of an absolute `C` with `Sh_i ≤ C` uniformly, at `L_i = log(p_i/n_i)`) stays OPEN; every
member of the family is, by `shawValue_floor_uniform`, already pinned `≥ 1/√(2L_i)` from below, so the
open content is exactly the UNIFORM upper constant — the `√(n/2)`-wide corridor CORE must collapse.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ProximityGap.Frontier.ConcreteShawValueBridge
open ProximityGap.Frontier.WorstPeriodSqrtNFloor
open ProximityGap.Frontier.ConcreteShawValueThinFloor

namespace ProximityGap.Frontier.ConcreteShawFamilyReduction

/-- A bundled thin prize instance: a finite field `F`, a primitive additive character `ψ`, a subgroup
`G` (the thin multiplicative subgroup `μ_n`), the nonempty-frequency witness, the thinness guards
`1 ≤ |G|` and `2|G| ≤ |F|` (i.e. `q ≥ 2n`, automatic at `q = n^β`, `β > 1`), and a positive
logarithmic thinness parameter `L` (in the prize regime `L = log(q/n)`).  All side conditions of the
concrete Shaw-value corridor are packaged here, so a family is just `ι → ThinInstance`. -/
structure ThinInstance where
  /-- The ambient finite field of the instance. -/
  F : Type
  [field : Field F]
  [fintype : Fintype F]
  [decEq : DecidableEq F]
  /-- The additive character used to form the Gauss periods. -/
  ψ : AddChar F ℂ
  /-- Primitivity of the additive character. -/
  hψ : ψ.IsPrimitive
  /-- The thin multiplicative subgroup `μ_n` (as a `Finset`). -/
  G : Finset F
  /-- There is at least one nonzero frequency. -/
  hne : (nonzeroFreqs F).Nonempty
  /-- Lower size guard `1 ≤ |G|`. -/
  hn1 : 1 ≤ (G.card : ℝ)
  /-- Thin-regime guard `2|G| ≤ |F|` (i.e. `q ≥ 2n`). -/
  hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)
  /-- The logarithmic thinness parameter `L` (prize regime `L = log(q/n)`), positive. -/
  L : ℝ
  /-- Positivity of the thinness parameter. -/
  hL : 0 < L

attribute [instance] ThinInstance.field ThinInstance.fintype ThinInstance.decEq

variable {ι : Type*}

/-- The subgroup size `n_i = |G_i|` of the `i`-th instance, as a real. -/
noncomputable def nFam (T : ι → ThinInstance) (i : ι) : ℝ := ((T i).G.card : ℝ)

/-- The thinness parameter `L_i` of the `i`-th instance. -/
noncomputable def LFam (T : ι → ThinInstance) (i : ι) : ℝ := (T i).L

/-- **The concrete worst-period family** `M_i = M(μ_{n_i}) = worstPeriod ψ_i G_i`: the actual
character-sum sup norm of the `i`-th thin instance. -/
noncomputable def worstFam (T : ι → ThinInstance) (i : ι) : ℝ :=
  worstPeriod (T i).ψ (T i).G (T i).hne

/-- Pointwise positivity of the prize scale `√(n_i·L_i)` across the family. -/
theorem prizeScale_pos_fam (T : ι → ThinInstance) (i : ι) :
    0 < prizeScale (nFam T i) (LFam T i) :=
  prizeScale_pos (lt_of_lt_of_le one_pos (T i).hn1) (T i).hL

/-- **Family campaign equivalence on the CONCRETE worst-period family.**  A uniform raw prize bound
`∀ i, M(μ_{n_i}) ≤ C·√(n_i·L_i)` by an absolute constant `C` is exactly a uniform Shaw-value bound
`∀ i, Sh_i ≤ C` by the same `C`, for the REAL Gauss-period worst periods.  This is the campaign
slogan `CORE ⇔ Sh(n)=O(1)` stated over the actual family of character-sum sup norms. -/
theorem corePrizeBound_iff_shawBounded (T : ι → ThinInstance) (C : ℝ) :
    rawPrizeFamilyBound (worstFam T) (nFam T) (LFam T) C
      ↔ shawValueFamilyBound (worstFam T) (nFam T) (LFam T) C :=
  rawPrizeFamilyBound_iff_shawValueFamilyBound (fun i => prizeScale_pos_fam T i)

/-- Existential-constant form: an absolute raw prize constant for the concrete worst-period family
exists iff an absolute Shaw-value constant exists.  This is the `∃C`-level `prize ⇔ Sh(n)=O(1)`
reduction on the real object. -/
theorem exists_corePrizeBound_iff_exists_shawBounded (T : ι → ThinInstance) :
    (∃ C, rawPrizeFamilyBound (worstFam T) (nFam T) (LFam T) C)
      ↔ (∃ C, shawValueFamilyBound (worstFam T) (nFam T) (LFam T) C) :=
  exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound
    (fun i => prizeScale_pos_fam T i)

/-- **Uniform `n`-independent Shaw-value floor on every family member.**  In the thin regime, the
normalized worst period of each instance is at least `1/√(2L_i)` — the clean Plancherel floor,
independent of `n_i`.  Hence the bounded-Shaw side of the reduction is never vacuous: it is trapped
between the floor `1/√(2L_i)` and the uniform constant `C`. -/
theorem shawValue_floor_uniform (T : ι → ThinInstance) (i : ι) :
    1 / Real.sqrt (2 * LFam T i)
      ≤ shawValue (worstFam T i) (nFam T i) (LFam T i) := by
  exact shawValue_worstPeriod_floor_clean (T i).hψ (T i).G (T i).hne (T i).hn1 (T i).hq2n
    (prizeScale_pos_fam T i)

/-- **The bounded-Shaw side is a genuine two-sided sandwich on the real object.**  If `C` is a uniform
Shaw-value bound for the concrete worst-period family, then every member satisfies
`1/√(2L_i) ≤ Sh_i ≤ C`.  In particular the campaign predicate `Sh(n)=O(1)` is NON-vacuous on the real
Gauss periods: the only open content is the uniform *upper* constant `C`, the floor being already
proven. -/
theorem shawBounded_sandwich (T : ι → ThinInstance) {C : ℝ}
    (hC : shawValueFamilyBound (worstFam T) (nFam T) (LFam T) C) (i : ι) :
    1 / Real.sqrt (2 * LFam T i) ≤ shawValue (worstFam T i) (nFam T i) (LFam T i)
      ∧ shawValue (worstFam T i) (nFam T i) (LFam T i) ≤ C :=
  ⟨shawValue_floor_uniform T i, hC i⟩

/-- **The concrete corridor transferred to the campaign reduction.**  Combining the equivalence with
the uniform floor: a uniform raw prize bound `C` for the concrete worst-period family forces every
normalized worst period into the corridor `1/√(2L_i) ≤ Sh_i ≤ C`.  This is the citable headline — the
proximity prize for the REAL thin Gauss-period family is equivalent to a uniform Shaw bound, and that
bound necessarily sits above the proven floor `1/√(2L_i)`. -/
theorem corePrizeBound_forces_sandwich (T : ι → ThinInstance) {C : ℝ}
    (hC : rawPrizeFamilyBound (worstFam T) (nFam T) (LFam T) C) (i : ι) :
    1 / Real.sqrt (2 * LFam T i) ≤ shawValue (worstFam T i) (nFam T i) (LFam T i)
      ∧ shawValue (worstFam T i) (nFam T i) (LFam T i) ≤ C :=
  shawBounded_sandwich T ((corePrizeBound_iff_shawBounded T C).1 hC) i

end ProximityGap.Frontier.ConcreteShawFamilyReduction

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.prizeScale_pos_fam
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.corePrizeBound_iff_shawBounded
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.exists_corePrizeBound_iff_exists_shawBounded
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.shawValue_floor_uniform
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.shawBounded_sandwich
#print axioms ProximityGap.Frontier.ConcreteShawFamilyReduction.corePrizeBound_forces_sandwich
