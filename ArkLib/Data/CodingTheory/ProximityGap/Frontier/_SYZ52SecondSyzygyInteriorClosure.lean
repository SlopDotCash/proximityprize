import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ44MuBasisDegreeSum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ45ImbalanceBound

/-!
# SYZ52 — the second-syzygy upper bound closes `ι ≤ 1` on the *balanced interior*

## Context

SYZ44 proved the μ-basis **degree-sum law** `δ₁ + δ₂ = a + b + c =: S` (`degree_sum_of_hilbert`)
with the minimal generator `δ₁ ≤ δ₂`, and SYZ45 packaged the imbalance
`ι = SYZ45.imbalance a b c δ₁ = ⌊S/2⌋ − δ₁`.  SYZ47 then gave the **asymmetric imbalance floor**
`δ₁ ≥ max(a,b,c)` and used it to discharge `ι ≤ 1` **only** on the *unbalanced* band strip
(`imbalance_le_one_of_max_near_edge`, requiring `max(a,b,c) ≥ ⌊S/2⌋ − 1`, empirically ≈ 37.7 % of
band triples).  In the *balanced interior* (`a ≈ b ≈ c ≈ S/3`, ≈ 62.3 %) the `max`-floor degrades to
`ι ≤ ⌊S/2⌋ − ⌊S/3⌋ ≈ S/6` — **vacuous**.  Yet the exact GF(p) minimal-syzygy referee probe
(`fable_syz47_interior.py`, 4800 balanced-interior triples, `p ∈ {61,101,257}`, budgets
`{5,7,9,11}`) shows `ι > 1` **never** occurs: the interior obeys the sharper *symmetric* floor
`δ₁ ≥ ⌊S/2⌋ − 1` (the tight `ℕ` floor equivalent to `ι ≤ 1`; the referee's `⌈S/2⌉ − 1` phrasing is
loose for odd `S`, cf. `symmetric_floor_of_second_le`), field-independently.

The two-term collapse of SYZ47 structurally cannot see this: it discharges one slot (`s_AB = 0`) and
counts two degrees, producing a `max`-type (asymmetric) bound by construction.  The symmetric closure
needs the **second** generator degree: an *upper* bound `δ₂ ≤ ⌈S/2⌉ + 1`.

## Result (this file)

Pure-`ℕ`, axiom-clean, consuming only SYZ44's degree-sum law:

* `imbalance_le_one_of_second_le` — the **calibrated consumer**: `δ₂ ≤ ⌈S/2⌉ + 1` (equivalently
  `δ₂ ≤ (S+1)/2 + 1`, using `⌈S/2⌉ = (S+1)/2 = S − ⌊S/2⌋`) forces `ι ≤ 1` on the *full* interior,
  with **no** `max`-near-edge hypothesis.  This is the symmetric-floor half SYZ47 does not reach.
* `symmetric_floor_of_second_le` — the equivalent lower-bound reading `δ₁ ≥ ⌊S/2⌋ − 1` (the tight
  `ℕ` floor equivalent to `ι ≤ 1`), stated as `⌊S/2⌋ − 1 ≤ δ₁`.  NB the referee's `⌈S/2⌉ − 1` phrasing
  is *loose* for odd `S` (where `⌊S/2⌋ < ⌈S/2⌉`): e.g. `S = 21`, `δ₁ = 9` already gives
  `ι = ⌊S/2⌋ − δ₁ = 10 − 9 = 1 ≤ 1` even though `δ₁ < ⌈S/2⌉ − 1 = 10`.  The tight floor uses `⌊·⌋`.
* `second_le_iff_imbalance_le_one` — **exact calibration**: under the degree-sum law with `δ₁ ≤ δ₂`,
  `δ₂ ≤ ⌈S/2⌉ + 1 ↔ ι ≤ 1`.  So the second-syzygy bound is not a lossy sufficient condition; it is
  *equivalent* to the target `ι ≤ 1`.  Hence formalizing/closing the interior is **exactly** the
  content of the `δ₂` upper bound — no slack lost.
* `imbalance_le_one_of_second_le_of_hilbert` — packaged: from SYZ44's two structural inputs
  (`RankNullity`, `TwoRamp`) plus `δ₁ ≤ δ₂` and the `δ₂` bound, conclude `ι ≤ 1` end to end.

**Scope honesty.**  This closes the *combinatorial* half: it converts the referee-measured symmetric
interior floor into a proved `ι ≤ 1` **conditional on** the second-generator degree bound
`δ₂ ≤ ⌈S/2⌉ + 1`.  It does *not* prove that bound (that is the remaining commutative-algebra /
Hilbert–Burch content SYZ47's kb assigns to G56/Opus-core), and `ι ≤ 1` only closes SYZ44's
`uniformSylvester` at rate `1/2`; the production δ* wire still needs SYZ18 supports, `hrank`
realizability, strip-radius transport, and the `MCAThresholdLedger` BGK lower bound.  CORE remains
OPEN / ON-BGK.  What is new here is the *exact calibration*: the interior residual is now pinned to a
single `δ₂ ≤ ⌈S/2⌉ + 1` inequality that is provably equivalent to `ι ≤ 1`.

The ceiling is expressed in `ℕ` as `⌈S/2⌉ = (S + 1) / 2` (floor division), which equals
`S − ⌊S/2⌋`; both forms are used and proved interchangeable by `omega`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ52

open ArkLib.ProximityGap

/-! ## 1. Ceiling identity (pure `ℕ`) -/

/-- `⌈S/2⌉ = (S+1)/2 = S − ⌊S/2⌋` in `ℕ` floor division.  Recorded so both readings of the
second-syzygy bound coincide. -/
theorem ceilHalf_eq (S : ℕ) : (S + 1) / 2 = S - S / 2 := by omega

/-! ## 2. The calibrated consumer: `δ₂ ≤ ⌈S/2⌉ + 1 ⟹ ι ≤ 1` on the full interior -/

/-- **Second-syzygy upper bound ⟹ `ι ≤ 1` (balanced interior closure).**  Given the degree-sum law
`δ₁ + δ₂ = a + b + c =: S` with `δ₁ ≤ δ₂`, the second-generator bound `δ₂ ≤ ⌈S/2⌉ + 1`
(`(S+1)/2 + 1`) forces the μ-basis imbalance `ι = ⌊S/2⌋ − δ₁ ≤ 1`.

This is the *symmetric* interior floor the SYZ47 `max`-collapse cannot reach: no `max(a,b,c)`
hypothesis is used, so it discharges `ι ≤ 1` on the whole balanced interior (the ≈ 62.3 % band region
where the asymmetric floor is vacuous), exactly matching the referee probe. -/
theorem imbalance_le_one_of_second_le
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hsecond : δ₂ ≤ (a + b + c + 1) / 2 + 1) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  unfold SYZ45.imbalance; omega

/-- **Symmetric floor reading.**  The same hypotheses give the *lower* bound `δ₁ ≥ ⌊S/2⌋ − 1`,
i.e. `S/2 − 1 ≤ δ₁`.  This is the exact `ℕ`-tight symmetric floor equivalent to `ι ≤ 1` (via
`SYZ45.imbalance = ⌊S/2⌋ − δ₁`).  The referee's `⌈S/2⌉ − 1` phrasing is loose for odd `S`: there
`⌊S/2⌋ < ⌈S/2⌉`, so `ι = ⌊S/2⌋ − δ₁ ≤ 1` can hold with `δ₁` below `⌈S/2⌉ − 1`; the tight floor uses
`⌊S/2⌋`. -/
theorem symmetric_floor_of_second_le
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hsecond : δ₂ ≤ (a + b + c + 1) / 2 + 1) :
    (a + b + c) / 2 - 1 ≤ δ₁ := by omega

/-! ## 3. Exact calibration: the second-syzygy bound is *equivalent* to `ι ≤ 1` -/

/-- **Exact calibration.**  Under the degree-sum law with `δ₁ ≤ δ₂`, the second-generator bound
`δ₂ ≤ ⌈S/2⌉ + 1` is **equivalent** to the target `ι ≤ 1`.  So it is a genuinely *calibrated*
consumer, not a lossy sufficient condition: closing the balanced interior is *exactly* the content of
this one `δ₂` inequality.  (Forward is `imbalance_le_one_of_second_le`; the converse holds because
`δ₂ = S − δ₁` and `ι ≤ 1 ↔ ⌊S/2⌋ − 1 ≤ δ₁`.) -/
theorem second_le_iff_imbalance_le_one
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    δ₂ ≤ (a + b + c + 1) / 2 + 1 ↔ SYZ45.imbalance a b c δ₁ ≤ 1 := by
  unfold SYZ45.imbalance; omega

/-! ## 4. Packaged reduction from SYZ44's structural inputs -/

/-- **Packaged interior closure.**  From SYZ44's two structural inputs (`RankNullity hilb a b c D₀`
and `TwoRamp hilb δ₁ δ₂`) that yield the degree-sum law, plus `δ₁ ≤ δ₂` and the second-generator
bound `δ₂ ≤ ⌈S/2⌉ + 1`, conclude `ι ≤ 1` — the full balanced-interior discharge, end to end, with no
`max`-floor hypothesis. -/
theorem imbalance_le_one_of_second_le_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hsecond : δ₂ ≤ (a + b + c + 1) / 2 + 1) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact imbalance_le_one_of_second_le a b c δ₁ δ₂ hsum hle hsecond

end ArkLib.ProximityGap.SYZ52

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ52.ceilHalf_eq
#print axioms ArkLib.ProximityGap.SYZ52.imbalance_le_one_of_second_le
#print axioms ArkLib.ProximityGap.SYZ52.symmetric_floor_of_second_le
#print axioms ArkLib.ProximityGap.SYZ52.second_le_iff_imbalance_le_one
#print axioms ArkLib.ProximityGap.SYZ52.imbalance_le_one_of_second_le_of_hilbert
