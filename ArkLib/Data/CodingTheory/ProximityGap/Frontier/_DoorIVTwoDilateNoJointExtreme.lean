/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Door-(iv) Lane-1/3: the two-dilate sub-period coupling is STRUCTURELESS (#444)

The dilation form (`_DoorIVHalfMassDilationForm`, `223b4c0d2`) restated the prize as
`H(n) = max_b (S(b) + S(g·b))`, where `S(c) = ‖eta ψ μ_{n/2} c‖` is the sub-period magnitude and
`g` is the index-2 coset rep (`S` is `μ_{n/2}`-coset-invariant; the shift `c ↦ g·c` moves to the
sibling `μ_{n/2}`-coset inside the same `μ_n`-coset).  The natural door-(iv) hope is a
**recursive saving** from the shift coupling: if `S(b)` and `S(g·b)` were positively correlated at the
worst frequency they would *co-peak*, `H ≈ 2·maxS`, and a thinner-subgroup bound on `maxS` would
transfer.  Conversely a structured *anti*-correlation could push `H` below the marginal envelope.

## What the probe finds (`probe_dooriv_subperiod_shift_corr.py`)

PROPER thin `μ_n` (`n = 16,32,64`), `p ≫ n³`, structured + generic primes, FULL `F_p*` sub-period scan
at `n=16/32`, sampled larger, never `n = q−1`:

* The worst-`b` does **NOT** co-peak: `H / (2·maxS) ∈ [0.69, 0.91]` and **decreases with `n`** (≈0.9 at
  `n=16`, ≈0.78 at `n=32`, ≈0.72 at `n=64`).  The two halves are asymmetric (`S(b*)/maxS, S(gb*)/maxS`
  e.g. `0.545, 0.983`), an "one near-max + one substantial" argmax, not both-at-max.
* The actual two-dilate maximum is **at or BELOW an i.i.d.-surrogate** (max over a *random independent*
  pairing of the same `S`-multiset): `H/√n ≤ iidSurrogate/√n` in every case.  The shift-`g` pairing
  supplies **no excess positive correlation** (if anything mildly anti).

## Verdict (refuted-lever, with mechanism)

The dilation coupling in `H(n) = max_b (S(b) + S(g·b))` is **structureless**: it neither co-peaks
(no positive shift-correlation ⇒ no recursive `√`-saving) nor beats the independent-pairing envelope
(no structured anti-correlation below the marginal).  So bounding `H(n)` routes through the **marginal**
sub-period maximum `maxS` under near-independent pairing — i.e. back to the Gaussian-EVT marginal law
(dead door-(iii)), with no recursion to extract from the two-frequency `{b, g·b}` structure.  This
closes the "recursive-ascent via the dilation coupling" hope at the level of the dilation sum itself,
companion to `[door-iv-worstb-non-nested]`.  No CORE/cancellation/completion/moment/anti-concentration/
capacity claim.

This file packages the structural algebra of the obstruction: `H ≤ 2·maxS` always; a recursive bound
`H ≤ c·maxS` with `c < 2` is exactly a no-co-peak certificate; and the probed `H ≤ I ≤ 2·maxS`
(`I` = independent-pairing surrogate) localizes the burden onto the marginal envelope.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme

variable {ι : Type*}

/-- The two-dilate sum at a frequency: `S(b) + S(g·b)`, abstracted as `s b + s (σ b)` for the marginal
magnitude `s : ι → ℝ` and the shift `σ : ι → ι` (`σ b = g·b`). -/
def twoDilate (s : ι → ℝ) (σ : ι → ι) (b : ι) : ℝ := s b + s (σ b)

/-- **The two-dilate sum is at most twice the marginal max.**  For any frequency `b`, if `s b ≤ Smax`
and `s (σ b) ≤ Smax` then `S(b)+S(g·b) ≤ 2·Smax`.  This is the unconditional ceiling: the dilation sum
can never exceed the perfect joint extreme. -/
theorem twoDilate_le_two_mul_max {s : ι → ℝ} {σ : ι → ι} {Smax : ℝ} {b : ι}
    (h1 : s b ≤ Smax) (h2 : s (σ b) ≤ Smax) :
    twoDilate s σ b ≤ 2 * Smax := by
  unfold twoDilate
  linarith

/-- **No-co-peak is exactly a strict gap below `2·maxS`.**  If the worst-`b` two-dilate sum is bounded
by `c·Smax` with `c < 2` (the probed fact `H/(2·maxS) ≤ 0.91`, decreasing with `n`) and the marginal
max is positive (the real regime, `Smax ≈ 3·√n > 0`), then at that `b` the two halves cannot both equal
`Smax`: `s b + s (σ b) < 2·Smax`, so at least one half is strictly below the marginal maximum.  Hence
the worst frequency does NOT realize the perfect joint extreme. -/
theorem not_both_max_of_lt_two_mul {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax) (hbound : twoDilate s σ b ≤ c * Smax) :
    s b + s (σ b) < 2 * Smax := by
  unfold twoDilate at hbound
  have hstrict : c * Smax < 2 * Smax := by nlinarith
  linarith

/-- **A recursive `√`-saving needs co-peaking, which the probe refutes.**  A recursive bound transferring
a thinner-subgroup marginal control to the prize would, in the favorable case, give `H ≈ 2·maxS` (both
halves at the marginal max).  Contrapositively: if `H ≤ c·Smax` with `c < 2` (no co-peak, the probed
fact), then the two halves are NOT jointly extremal, so the dilation coupling supplies no `2×` co-peak to
recurse on — the marginal max `Smax` is approached by ONE half at a time, not both. -/
theorem no_copeak_recursion {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax) (hbound : twoDilate s σ b ≤ c * Smax)
    (hb : s b = Smax) :
    s (σ b) < Smax := by
  have hlt := not_both_max_of_lt_two_mul hc hSmax hbound
  rw [hb] at hlt
  linarith

/-- **No-co-peak is symmetric in the two dilates.**  The same strict gap below `2·Smax` rules out
the sibling frequency carrying the marginal maximum together with a maximal base frequency.  If the
shifted half is already at `Smax`, then the base half must be strictly below `Smax`.

This is the exact symmetric audit hook for the observed "one near-max + one substantial" worst-`b`
shape: a strict two-dilate envelope cannot hide a perfect joint extreme in either ordering. -/
theorem no_copeak_recursion_left {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax) (hbound : twoDilate s σ b ≤ c * Smax)
    (hb : s (σ b) = Smax) :
    s b < Smax := by
  have hlt := not_both_max_of_lt_two_mul hc hSmax hbound
  rw [hb] at hlt
  linarith

/-- **Strict two-dilate gap forbids a joint marginal extreme.**  If `H(b) ≤ c·Smax` with `c < 2`
and `Smax > 0`, then it is impossible for both dilates at that same `b` to equal the marginal maximum.
This packages the probe verdict as the minimal contradiction form: the coupling may have one large
half, but it cannot certify a recursive co-peak. -/
theorem not_joint_marginal_extreme_of_lt_two_mul {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax) (hbound : twoDilate s σ b ≤ c * Smax) :
    ¬ (s b = Smax ∧ s (σ b) = Smax) := by
  intro hboth
  have hlt := not_both_max_of_lt_two_mul hc hSmax hbound
  rw [hboth.1, hboth.2] at hlt
  linarith

/-- **Marginal-envelope localization.**  The probe shows `H ≤ I ≤ 2·Smax`, where `I` is the
independent-pairing surrogate maximum (no shift structure).  Abstractly: if the worst-`b` two-dilate sum
is dominated by a structureless surrogate `I` which is itself at most `2·Smax`, then `H ≤ 2·Smax` AND
the only way to push `H` down is to improve the MARGINAL `Smax` (or the surrogate) — the dilation
coupling adds nothing exploitable beyond the marginal envelope. -/
theorem dilate_le_surrogate_le_two_max {H I Smax : ℝ}
    (hHI : H ≤ I) (hI : I ≤ 2 * Smax) :
    H ≤ 2 * Smax :=
  le_trans hHI hI

/-- **Structureless coupling ⇒ no anti-concentration below the marginal.**  If the dilation maximum `H`
is at least the marginal max `Smax` (one half can reach `Smax`, so `H ≥ Smax`) and at most the
independent surrogate `I` (no positive shift correlation), then `Smax ≤ H ≤ I`: the dilation sum is
pinned between the marginal floor and the independent envelope, so it carries the marginal's
`√(n·log)` burden with no structured shift-cancellation that could beat it. -/
theorem dilate_pinned_between_marginal_and_surrogate {H I Smax : ℝ}
    (hfloor : Smax ≤ H) (hHI : H ≤ I) :
    Smax ≤ H ∧ H ≤ I :=
  ⟨hfloor, hHI⟩

end ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme

#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate_le_two_mul_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.not_both_max_of_lt_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.no_copeak_recursion
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.no_copeak_recursion_left
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.not_joint_marginal_extreme_of_lt_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.dilate_le_surrogate_le_two_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.dilate_pinned_between_marginal_and_surrogate
