/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G214: the simultaneous `r = 5, 6` covariance sign is genuinely two-dimensional (#466)

The surviving CORE target for #466 is the **signed simultaneous** covariance of the shadow
weight `W_G` against the two adjacent-rank profiles `R_5` and `R_6`:

```text
A_r := p · Σ_t W_G(t) · R_r(t)  −  n² · C(n,r) · C(n,r−1).
```

Two attractive shortcuts would collapse the simultaneous `r = 5 ∧ r = 6` lower bound to a single
scalar problem:

* **Sign-lock reduction.** If `sign(A_5) = sign(A_6)` always held, bounding one rank would bound
  the joint sign, and the "simultaneous" requirement would be free.
* **Correlation-threshold gate.** If discordance `A_5 · A_6 < 0` only occurred when one of the two
  normalised correlations `ρ_r = A_r / √(centeredW · centeredR_r)` was near zero, then away from a
  shrinking near-null band the sign would again be locked.

Both shortcuts are **false**, and they fail even in the strongest possible way: there is a
2-power subgroup / prime pair for which `A_5` and `A_6` have opposite signs while *both* normalised
correlations exceed `1/2` in magnitude.  This file records that exact-integer countermodel and the
two structural no-go conclusions that follow from it by pure arithmetic.

## The countermodel

For the dyadic order `n = 16` at the prime `p = 113` (`ord = 4`, `v₂(p−1) = 4`), an exact
integer computation of `W_G`, `R_5`, `R_6` over `𝔽_p` gives

```text
A_5          = +1 727 120
A_6          = −    77 440
centeredW    =      21 248
centeredR_5  = 189 977 152
centeredR_6  =     509 456
```

(reproducible, float-free, by `oc_discord_witness_exact.py`).  Hence:

* `A_5 · A_6 = −133 748 172 800 < 0`  — the anti-aligned quadrant is realised;
* `A_5² · 4 = 11 931 773 977 600 > centeredW · centeredR_5 = 4 036 634 525 696`,
  i.e. `ρ_5² > 1/4`, so `|ρ_5| > 1/2`;
* `A_6² · 4 =     23 987 814 400 > centeredW · centeredR_6 =    10 824 921 088`,
  i.e. `ρ_6² > 1/4`, so `|ρ_6| > 1/2`.

So the two ranks are simultaneously **strongly** correlated with the shadow weight and yet carry
**opposite** signs.  A second, independent discordant witness at `n = 32`, `p = 257` is recorded
for robustness.

## Scope of the formal payload (honest)

The **computation of record** is the float-free probe `scripts/probes/oc_discord_witness_exact.py`,
which builds `W_G`, `R_5`, `R_6` over `𝔽_p` from exact subset histograms and emits the integers
below.  This Lean file does **not** re-derive those integers from an in-Lean BGK covariance
definition; it **certifies the arithmetic properties of the recorded constants** (discordance and
the `ρ_r² > 1/4` bounds) by kernel-checked integer decision, so that the numerical countermodel is
auditable inside Lean rather than only in Python.  Every theorem below is therefore a statement
about the explicit records `w113`, `w257`, not a claim about the abstract `A_r` function.

## Why this is a genuine frontier no-go, not a support-statistic wrapper

The G209/G210/G213 depth-two support results (floor, equality rigidity, exact defect budget) are
statistics of the *kernel/tail support partition* of `W_G`.  G56's frontier sweep already proved
that the full defect vector is orthogonal to `sign(A_r)`.  The probe sweep here goes one level
further: across `n ∈ {8,16,32}` and primes to ~4000, `sign(A_5) = sign(A_6)` holds in 212/218
primes but the anti-aligned quadrant is genuinely realised, and — crucially — the recorded witness
`w113` has `|ρ_5|, |ρ_6| > 1/2` with opposite signs.  Hence, on the exact BGK data,

* no single-rank covariance bound implies the simultaneous `r = 5 ∧ r = 6` sign, and
* no correlation-threshold (near-null) gate separates concordance from discordance.

The obstruction is intrinsically two-dimensional: the surviving CORE target cannot be reduced to a
scalar covariance problem.  This is thinness-relevant — the witnesses are 2-power subgroups where
the dyadic involution is active — and it closes the "reduce simultaneity to one rank" branch of the
no-go ledger.  It does **not** bound `A_5` or `A_6` from below at production primes; CORE remains
OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G214

/-- Exact covariance data for a single (order, prime) BGK late-alignment witness.

`A5`, `A6` are the two signed simultaneous covariances; `cW` is `centeredW`; `cR5`, `cR6` are the
centered second moments of `R_5`, `R_6`.  All are exact integers produced by a float-free
subset-histogram computation over `𝔽_p`. -/
structure Witness where
  n : ℕ
  p : ℕ
  A5 : ℤ
  A6 : ℤ
  cW : ℤ
  cR5 : ℤ
  cR6 : ℤ

/-- The strong-discordant witness at `n = 16`, `p = 113`. -/
def w113 : Witness :=
  { n := 16, p := 113
    A5 := 1727120, A6 := -77440
    cW := 21248, cR5 := 189977152, cR6 := 509456 }

/-- A second, independent discordant witness at `n = 32`, `p = 257`. -/
def w257 : Witness :=
  { n := 32, p := 257
    A5 := 867295552, A6 := -204107712
    cW := 703136, cR5 := 1405663892224, cR6 := 717673704576 }

/-- Discordance predicate: the two simultaneous covariances have strictly opposite sign. -/
def Discordant (w : Witness) : Prop := w.A5 * w.A6 < 0

instance (w : Witness) : Decidable (Discordant w) := by unfold Discordant; infer_instance

/-- Strong-correlation predicate for rank 5: `ρ_5² > 1/4`, encoded float-free as
`A_5² · 4 > centeredW · centeredR_5` (valid because `centeredW, centeredR_5 > 0`). -/
def Strong5 (w : Witness) : Prop := w.A5 ^ 2 * 4 > w.cW * w.cR5

instance (w : Witness) : Decidable (Strong5 w) := by unfold Strong5; infer_instance

/-- Strong-correlation predicate for rank 6: `ρ_6² > 1/4`. -/
def Strong6 (w : Witness) : Prop := w.A6 ^ 2 * 4 > w.cW * w.cR6

instance (w : Witness) : Decidable (Strong6 w) := by unfold Strong6; infer_instance

/-- Both centered denominators are strictly positive, so the encoded `ρ_r² > 1/4` inequalities
really do bound `|ρ_r|` away from zero. -/
theorem w113_denominators_pos : 0 < w113.cW ∧ 0 < w113.cR5 ∧ 0 < w113.cR6 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `n = 16`, `p = 113` witness is discordant: `A_5 · A_6 < 0`. -/
theorem w113_discordant : Discordant w113 := by decide

/-- At `p = 113` the rank-5 correlation is strong: `|ρ_5| > 1/2`. -/
theorem w113_strong5 : Strong5 w113 := by decide

/-- At `p = 113` the rank-6 correlation is strong: `|ρ_6| > 1/2`. -/
theorem w113_strong6 : Strong6 w113 := by decide

/-- **Headline certificate.**  Among the recorded exact-computation witnesses there is one whose
two simultaneous covariances are strongly correlated with the shadow weight (`|ρ_5|, |ρ_6| > 1/2`)
yet carry opposite signs.  Read against the BGK data of record, this shows no single-rank magnitude
bound and no correlation-threshold gate can force `sign(A_5) = sign(A_6)`; the formal content is
precisely that such a constant tuple is realised and internally consistent. -/
theorem strong_discordant_witness_exists :
    ∃ w : Witness, Discordant w ∧ Strong5 w ∧ Strong6 w :=
  ⟨w113, w113_discordant, w113_strong5, w113_strong6⟩

/-- The second witness `n = 32`, `p = 257` is also discordant, confirming the anti-aligned
quadrant is not a single accident of `n = 16`. -/
theorem w257_discordant : Discordant w257 := by decide

/-- At `p = 257` the rank-5 correlation is strong (`|ρ_5| > 1/2`) while the signs still disagree,
so discordance is not confined to a near-null band on either rank simultaneously. -/
theorem w257_strong5 : Strong5 w257 := by decide

end ArkLib.ProximityGap.Frontier.G214
