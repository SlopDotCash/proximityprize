/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.BGKExponentReduction

/-!
# di Benedetto Thm 3.1: the β-validity window and its nontriviality edge β = 191/40 (#444)

`BGKExponentReduction.lean` pins `diBenedettoDelta = 31/2880` as the SOTA cancellation exponent
and records (in prose) that it is the *corollary* of di Benedetto Thm 3.1 "`for n > p^{1/4}`":
the raw bound there is `B ≲ n^{2689/2880} · p^{1/72}`. It proves `0 < 31/2880 < 1/2`, but it
**never discharges** the raw bound's β-dependence — exactly the fact the near-Sidon /
di-Benedetto improvement lane (`_DiBenedettoNearSidonImprovement.lean`) and the DISPROOF_LOG D13/D14
ledger LEAN ON: *the raw saving is a function of β that DIES at a finite upper edge.*

This file discharges that prose into theorems. With `p = n^β`, di Benedetto Thm 3.1's raw bound
`B ≲ n^{2689/2880} · p^{1/72}` has **total exponent in `n`**

  `rawExponent β = 2689/2880 + β/72`,

so the cancellation saving is `1 − rawExponent β`. The content (all exact, field-universal `ℚ/ℝ`
arithmetic — `norm_num`/`linarith`, no analytic input):

* **`rawExponent_at_four`** — at the prize point `β = 4` (`n = p^{1/4}`) the raw exponent is
  `2849/2880 = 1 − 31/2880`, *recovering the `BGKExponentReduction.diBenedettoDelta` headline EXACTLY*
  (the brick pins the two files together: the headline `31/2880` is `rawExponent 4`'s saving).
* **`saving_eq`** — the saving is **affine** in `β`: `1 − rawExponent β = 31/2880 + (4 − β)/72`.
* **`upper_edge`** — the saving **vanishes exactly** at `β = 191/40 = 4.775`
  (`rawExponent (191/40) = 1`): the upper nontriviality edge.
* **`nontrivial_iff`** — `rawExponent β < 1 ↔ β < 191/40`: the precise **validity window** in which
  Thm 3.1 gives a genuine sub-`n^1` power saving.
* **`trivial_beyond_edge`** — for `β ≥ 191/40` the raw bound is **TRIVIAL** (`1 ≤ rawExponent β`):
  no power saving at all (matches DISPROOF_LOG D13's "Burgess barrier", and the §0.4 note that the
  generic bound is empty for thin enough subgroups).
* **`saving_antitone`** — the saving is monotone **decreasing** in `β` (thinner subgroup ⟹ smaller
  saving, slope `−1/72`): the honest reason di Benedetto WEAKENS as `μ_n` thins toward the prize.
* **`prize_point_strictly_inside`** — `4 < 191/40`: the prize point β=4 sits **strictly inside** the
  validity window, so the headline saving `31/2880` is strictly positive (consistent with the D14
  correction that the *open-interval* `2 < β < 4` is the strictly-in-range part, with `β = 4` the
  closed endpoint at which the headline survives under the `≲`/`o(1)` convention).

**HONESTY (rules 1,3,6).** This is **field-universal exponent bookkeeping** (`ℝ`-arithmetic on a
named literature exponent), NOT thinness-essential, NOT a moment/census/orbit/pencil object, and
touches NEITHER `δ*` NOR the cliff-at-n/2 incidence object. It is a **negative boundary**: it pins
the β-window in which the SOTA di Benedetto bound is nontrivial and the finite edge `β = 191/40` past
which it says nothing — both ≫ the prize `1/2`. It neither proves nor disproves CORE
`M(μ_n) ≤ C·√(n·log(p/n))`; it makes the di-Benedetto lane's prose validity-window into theorems and
pins the headline `31/2880` to `rawExponent 4`. ASYMPTOTIC-CLAIM GUARD: no capacity/beyond-Johnson
claim, cliff untouched. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.DiBenedettoBetaValidityWindow

open ArkLib.ProximityGap.BGKExponentReduction

/-- The **total exponent of `n`** in di Benedetto Thm 3.1's raw bound `B ≲ n^{2689/2880}·p^{1/72}`
under the prize substitution `p = n^β`: `rawExponent β = 2689/2880 + β/72`. -/
noncomputable def rawExponent (β : ℝ) : ℝ := 2689 / 2880 + β / 72

/-- The **upper nontriviality edge** of Thm 3.1: `β = 191/40 = 4.775`. At this β the raw exponent
hits `1` (no saving); above it the bound is trivial. -/
noncomputable def burgessEdge : ℝ := 191 / 40

/-- **The prize point `β = 4` recovers the SOTA headline EXACTLY.** The raw exponent at `β = 4`
(`n = p^{1/4}`) is `2849/2880 = 1 − 31/2880`, i.e. its saving is exactly
`BGKExponentReduction.diBenedettoDelta = 31/2880`. This pins the named SOTA exponent to the raw
Thm 3.1 bound. -/
theorem rawExponent_at_four : rawExponent 4 = 1 - diBenedettoDelta := by
  unfold rawExponent diBenedettoDelta; norm_num

/-- **The saving is affine in `β`:** `1 − rawExponent β = 31/2880 + (4 − β)/72`. So a unit increase
in `β` (a thinner subgroup) costs exactly `1/72` of saving. -/
theorem saving_eq (β : ℝ) :
    1 - rawExponent β = diBenedettoDelta + (4 - β) / 72 := by
  unfold rawExponent diBenedettoDelta; ring

/-- **The saving vanishes EXACTLY at the upper edge `β = 191/40`:** `rawExponent (191/40) = 1`. -/
theorem upper_edge : rawExponent burgessEdge = 1 := by
  unfold rawExponent burgessEdge; norm_num

/-- **The validity window (headline):** Thm 3.1's raw bound is a genuine sub-`n^1` power saving
(`rawExponent β < 1`) **iff** `β < 191/40`. This is the exact β-interval in which the SOTA bound
says something nontrivial. -/
theorem nontrivial_iff (β : ℝ) : rawExponent β < 1 ↔ β < burgessEdge := by
  unfold rawExponent burgessEdge; constructor <;> intro h <;> linarith

/-- **Beyond the edge the bound is TRIVIAL:** for `β ≥ 191/40` the raw exponent is `≥ 1`, i.e. no
power saving (the Burgess-barrier death — DISPROOF_LOG D13). -/
theorem trivial_beyond_edge {β : ℝ} (h : burgessEdge ≤ β) : 1 ≤ rawExponent β := by
  unfold rawExponent burgessEdge at *; linarith

/-- **The saving is strictly DECREASING in `β`** (slope `−1/72`): a thinner subgroup gives a smaller
di-Benedetto saving. This is the honest mechanism by which the SOTA weakens toward the prize. -/
theorem saving_antitone {β β' : ℝ} (h : β < β') :
    1 - rawExponent β' < 1 - rawExponent β := by
  unfold rawExponent; linarith

/-- **The prize point β = 4 sits STRICTLY inside the validity window:** `4 < 191/40`. Hence the
headline saving `rawExponent 4`'s `31/2880` is strictly positive (`nontrivial_iff` at `β = 4`). -/
theorem prize_point_strictly_inside : (4 : ℝ) < burgessEdge := by
  unfold burgessEdge; norm_num

/-- **Corollary: the headline saving is strictly positive at the prize point.** Combining
`prize_point_strictly_inside` with `nontrivial_iff`: `rawExponent 4 < 1`. -/
theorem rawExponent_four_lt_one : rawExponent 4 < 1 :=
  (nontrivial_iff 4).mpr prize_point_strictly_inside

end ArkLib.ProximityGap.DiBenedettoBetaValidityWindow

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.rawExponent_at_four
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.saving_eq
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.upper_edge
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.nontrivial_iff
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.trivial_beyond_edge
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.saving_antitone
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.prize_point_strictly_inside
#print axioms ArkLib.ProximityGap.DiBenedettoBetaValidityWindow.rawExponent_four_lt_one
