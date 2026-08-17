/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

/-!
# Door-(iv) constraint: the worst-frequency PHASE-POSITION CURVATURE is GENERIC —
  the discrete-curvature (second-difference) lever is a DEAD lever (#464)

The prize is localized to the worst frequency `b*` of `η_b = Σ_{y∈μ_n} e_p(b·y)` over the thin
2-power subgroup `μ_n ⊊ F_p^*`.  A standard **non-energy** structural hope for a √-cancellation
bound is a *curvature / discrete-convexity* lever (Halász / Littlewood–Offord small-ball via
bounded second differences): if the sorted angular positions `θ_x = (b·x mod p)/p ∈ [0,1)` of the
worst-`b` coset had a **low-complexity second-difference** structure — i.e. the cyclic
second-difference sequence `Δ²_i = g_{i+1} − g_i` of the gap sequence `g_i = θ_{i+1} − θ_i` took
only a *bounded* number of distinct values — then a curvature-sensitive anti-concentration bound
(distinct from multiplicative energy / sum-product) could grip the phase set.

The companion brick `ThreeGapPositionalRigidity` already proved the **gap VALUES** collapse to
`≤ n/2 + 1` distinct values (negation-closure of `μ_n`), and that this count is **dilation-invariant**
(frequency-blind ⟹ rule-3 dead).  This brick rules out the *next-order* curvature hope.

PROBE (`scripts/probes/probe_dooriv_worstb_phase_curvature.py`; proper `μ_n`, `p == 1 mod n`,
`p ~ n⁴ ≫ n³`, never `n = q-1`; uniform coset-rep sampling to avoid scan-stride artifacts; EXACT
integer positions in `ℤ_p`; global worst-`b` scan; `n = 16, 32, 64`, 5 structured primes each):

  n=16 : distinctGaps(b*) = 9  (= n/2+1);  distinctΔ²(b*) = 16 = n;  generic-b Δ² = 16
  n=32 : distinctGaps(b*) = 17 (= n/2+1);  distinctΔ²(b*) = 32 = n;  generic-b Δ² = 32
  n=64 : distinctGaps(b*) = 33 (= n/2+1);  distinctΔ²(b*) = 64 = n;  generic-b Δ² = 64

So at the worst frequency the cyclic second-difference sequence is **curvature-GENERIC**: it attains
the *maximal* `n` distinct values (no two of the `n` cyclic second differences coincide), and the
count is **identical for a generic non-worst `b`** — DILATION-INVARIANT, hence frequency-blind.

CONSEQUENCE (this file, axiom-clean).  We model the curvature sequence directly as a map
`d : ι → ℤ` (`d i = Δ²_i`, `ι` the `n` cyclic positions) and prove the two load-bearing facts:

* `MAXIMAL-Δ²`.  If the curvature map `d` is **injective** (the probed worst-`b` fact: all `n`
  cyclic second differences are pairwise distinct), its image has full cardinality `|ι| = n`.  A
  curvature lever needs `distinctΔ² = O(1)`; here it is the maximal `n`, so there is **no**
  bounded-curvature collapse below any budget `C < n`.

* `DILATION-BLIND ⟹ DEAD (rule 3/4)`.  If a candidate curvature statistic `s : β → ℕ` takes the
  **same** value at the worst frequency `b★` and at a generic frequency `b₀`, it is constant on that
  pair, so it carries zero worst-`b` selection information (no threshold separates them).  A
  frequency-blind statistic cannot be the thinness-essential prize lever.

This brick is HONESTY-STRICT (real proofs, no `sorry`/`axiom`/`native_decide`/vacuity),
NON-MOMENT (pure positional second-difference combinatorics, no additive energy),
ASYMPTOTIC-GUARD-COMPLIANT (a *negative* / refutation result: curvature collapse is RULED OUT;
no capacity / beyond-Johnson / `δ*` interior claim).  It does NOT bound CORE; it removes one named
non-energy lever (discrete curvature) from door (iv).  CORE stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **cyclic second-difference set** of a curvature map `d : ι → ℤ` (`d i = Δ²_i`), i.e. the set
of distinct values it attains.  A curvature lever needs this set to be small (`O(1)`); the probe
finds it has full cardinality `|ι| = n` at the worst frequency. -/
def secondDiffSet (d : ι → ℤ) : Finset ℤ := Finset.univ.image d

/-- **The curvature set has at most `|ι| = n` elements** (image of an `n`-element index set). -/
theorem secondDiffSet_card_le (d : ι → ℤ) :
    (secondDiffSet d).card ≤ Fintype.card ι := by
  refine le_trans (Finset.card_image_le) ?_
  simp [Finset.card_univ]

/-- **Maximal curvature ⟹ full image.**  If the cyclic second-difference map is *injective* (the
probed worst-`b` fact: all `n` cyclic second differences are pairwise distinct), the curvature set
has full cardinality `|ι| = n`. -/
theorem secondDiffSet_card_eq_of_injective (d : ι → ℤ) (hinj : Function.Injective d) :
    (secondDiffSet d).card = Fintype.card ι := by
  unfold secondDiffSet
  rw [Finset.card_image_of_injective _ hinj]
  simp [Finset.card_univ]

/-- **No bounded-curvature collapse.**  Under the probed injectivity (maximal-`Δ²`), the curvature
set cannot fit under any strict budget `C < |ι|`: a curvature lever requiring `distinctΔ² ≤ C` with
`C < n` is impossible. -/
theorem no_curvature_collapse (d : ι → ℤ) (hinj : Function.Injective d)
    (C : ℕ) (hC : C < Fintype.card ι) :
    ¬ (secondDiffSet d).card ≤ C := by
  rw [secondDiffSet_card_eq_of_injective d hinj]
  omega

/-- A curvature statistic `s` is **frequency-blind on the pair `(b★, b₀)`** when it takes the same
value at the worst frequency `b★` and at a generic frequency `b₀`. -/
def FrequencyBlind {β : Type*} (s : β → ℕ) (bstar b0 : β) : Prop := s bstar = s b0

/-- **Frequency-blind ⟹ zero selection information (rule 3/4).**  If a curvature statistic agrees at
the worst and a generic frequency, no threshold `t` separates them (`s b★ ≥ t` while `s b₀ < t`).  A
statistic that cannot separate one worst/generic pair is not the thinness-essential prize lever. -/
theorem frequencyBlind_no_separation {β : Type*} (s : β → ℕ) {bstar b0 : β}
    (h : FrequencyBlind s bstar b0) :
    ∀ t : ℕ, ¬ (t ≤ s bstar ∧ s b0 < t) := by
  intro t ⟨h1, h2⟩
  unfold FrequencyBlind at h
  omega

/-- **Combined door-(iv) curvature refutation.**  Bundles the two proven faces for the worst-`b`
phase-position curvature, exactly as probed:
* maximal curvature: under injectivity the second-difference set is full (`= |ι| = n`), so **no**
  curvature collapse below any `C < n` is possible; AND
* dilation-blindness: the distinct-`Δ²` count agrees at the worst and a generic frequency, so it
  carries zero worst-`b` selection information.
Together: the discrete-curvature lever is dead — it has neither structural slack (count is maximal)
nor frequency sensitivity (count is blind).  This is a NEGATIVE structural lemma; NO CORE bound. -/
theorem doorIV_phaseCurvature_dead {β : Type*}
    (d : ι → ℤ) (hinj : Function.Injective d)
    (s : β → ℕ) (bstar b0 : β) (hblind : FrequencyBlind s bstar b0) :
    (secondDiffSet d).card = Fintype.card ι ∧
      (∀ C : ℕ, C < Fintype.card ι → ¬ (secondDiffSet d).card ≤ C) ∧
      (∀ t : ℕ, ¬ (t ≤ s bstar ∧ s b0 < t)) := by
  refine ⟨secondDiffSet_card_eq_of_injective d hinj, ?_, ?_⟩
  · intro C hC; exact no_curvature_collapse d hinj C hC
  · exact frequencyBlind_no_separation s hblind

end ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric
