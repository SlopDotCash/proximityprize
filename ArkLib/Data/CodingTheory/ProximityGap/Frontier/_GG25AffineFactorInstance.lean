/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GG25LineToAffine
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# GG25 §6.1 — the explicit affine-gap factor `ε·q/(q−1)`, instantiated (#444)

The abstract line→affine cover bound `card_bad_le_of_line_cover`
(`bad.card ≤ (#lines)·B`, in `_GG25LineToAffine.lean`) is the combinatorial core of the
[GG25] §6.1 averaging reduction (Thm 5.12 line gap ⟹ Thm 6.2 affine gap).  Its docstring
states — but does not land as a theorem — the **specialization** that recovers the headline
GG25 affine factor:

> instantiating `B ≤ ⌊ε·q⌋` (per-line close bound from the line gap) and
> `#lines = (|U|−1)/(q−1)` (the affine pencil count through a fixed non-close point)
> recovers `|bad| ≤ ε·q/(q−1)·(|U|−1)`.

This file lands that specialization as **two exact inequalities**, EXTENDING the just-proven cover
bound (it consumes `card_bad_le_of_line_cover` verbatim; the only new content is the arithmetic of
substituting the per-line cap `B = ⌊ε·q⌋` and the pencil count, with the affine-space size `Ucard` and
the count supplied as explicit data — the standard affine-geometry pencil fact `#lines·(q−1) = Ucard−1`,
NOT re-derived here, exactly as the GG25 obligation map records it as a cited input).

* `card_bad_le_pencil` — under the per-line cap `epsQ := ⌊ε·q⌋` and the pencil-count hypothesis
  `lineCount·(q−1) = Ucard−1`, the close set satisfies `bad.card·(q−1) ≤ (Ucard−1)·epsQ`.  This is the
  cross-multiplied (division-free) form of the GG25 `ε·q/(q−1)` affine factor — exact over `ℕ`, no
  real division, no vacuity.

* `card_bad_le_pencil_real` — the same statement divided into the citable rational shape
  `(bad.card : ℝ) ≤ ((Ucard−1)/(q−1)) · epsQ` (for `q > 1`, `Ucard ≥ 1`), the literal GG25 §6.1 density.

Honest scope (rules 1, 3, 6): this is the GG25 *folded/affine* lifting constant, NOT the plain-RS prize
wall.  GG25 gives the folded-RS proximity gap unconditionally *modulo* its cited third-party inputs (FRS
list-decoding at capacity, the line-gap `B`-constant), and this brick only formalizes the combinatorial
substitution that turns a per-line gap into the affine density.  It makes NO claim about `M(μ_n)`, no
`δ*`/capacity/beyond-Johnson/cliff claim; CORE `M(μ_n) ≤ C√(n·log(q/n))` is UNTOUCHED/OPEN.  The affine
size `Ucard` and the pencil count `#lines·(q−1) = Ucard−1` are HYPOTHESES (the standard affine-geometry
fact, cited not re-derived), so the statements are non-vacuous exactly in the GG25 §6.1 setting.

See `docs/kb/Iinf-campaign/29-GG25-obligation-map.md`; the abstract cover bound it extends is
`ArkLib.ProximityGap.GG25LineToAffine.card_bad_le_of_line_cover`.

Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.GG25AffineFactorInstance

open ArkLib.ProximityGap.GG25LineToAffine

variable {U L : Type*} [DecidableEq U]

/-- **GG25 §6.1 affine factor, division-free integer form.**
Given the line cover of the close set `bad` (each of the `lines` carrying at most the per-line cap
`epsQ := ⌊ε·q⌋` close points) and the affine pencil count `lines.card · (q − 1) = Ucard − 1`
(the standard count of lines through a fixed point of an affine space of size `Ucard` over `F_q`), the
close set satisfies the cross-multiplied GG25 affine bound

  `bad.card · (q − 1) ≤ (Ucard − 1) · epsQ`.

This is `card_bad_le_of_line_cover` substituted with `B = epsQ` and the pencil count; no division,
exact over `ℕ`. -/
theorem card_bad_le_pencil
    (bad : Finset U) (lines : Finset L) (member : L → Finset U)
    (q epsQ Ucard : ℕ)
    (hcov : bad ⊆ lines.biUnion member)
    (hbound : ∀ l ∈ lines, (bad ∩ member l).card ≤ epsQ)
    (hpencil : lines.card * (q - 1) = Ucard - 1) :
    bad.card * (q - 1) ≤ (Ucard - 1) * epsQ := by
  -- the cover bound: bad.card <= lines.card * epsQ
  have hcover : bad.card ≤ lines.card * epsQ :=
    card_bad_le_of_line_cover bad lines member epsQ hcov hbound
  -- multiply through by (q - 1) and fold in the pencil count
  have hstep : bad.card * (q - 1) ≤ (lines.card * epsQ) * (q - 1) := by gcongr
  have hrew : (lines.card * epsQ) * (q - 1) = (Ucard - 1) * epsQ := by
    rw [mul_right_comm, hpencil]
  omega

/-- **GG25 §6.1 affine factor, real-rational form.**
Dividing the integer bound by `q − 1 > 0`, the close-set size obeys the literal GG25 §6.1 density

  `(bad.card : ℝ) ≤ ((Ucard − 1) / (q − 1)) · epsQ`,

i.e. `|bad| ≤ ε·q/(q−1)·(Ucard−1)` with `epsQ = ⌊ε·q⌋` — the affine proximity-gap factor. -/
theorem card_bad_le_pencil_real
    (bad : Finset U) (lines : Finset L) (member : L → Finset U)
    (q epsQ Ucard : ℕ) (hq : 1 < q) (hU : 1 ≤ Ucard)
    (hcov : bad ⊆ lines.biUnion member)
    (hbound : ∀ l ∈ lines, (bad ∩ member l).card ≤ epsQ)
    (hpencil : lines.card * (q - 1) = Ucard - 1) :
    (bad.card : ℝ) ≤ (((Ucard : ℝ) - 1) / ((q : ℝ) - 1)) * (epsQ : ℝ) := by
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  -- the integer bound, cast to `ℝ`
  have hint := card_bad_le_pencil bad lines member q epsQ Ucard hcov hbound hpencil
  have h1le : 1 ≤ q := le_of_lt hq
  have hcastNatL : ((bad.card * (q - 1) : ℕ) : ℝ) = (bad.card : ℝ) * ((q : ℝ) - 1) := by
    push_cast [Nat.cast_sub h1le]; ring
  have hcastNatR : (((Ucard - 1) * epsQ : ℕ) : ℝ) = ((Ucard : ℝ) - 1) * (epsQ : ℝ) := by
    push_cast [Nat.cast_sub hU]; ring
  have hcast : (bad.card : ℝ) * ((q : ℝ) - 1) ≤ ((Ucard : ℝ) - 1) * (epsQ : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hint
    rwa [hcastNatL, hcastNatR] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hqm1pos]
  linarith [hcast]

end ArkLib.ProximityGap.GG25AffineFactorInstance

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.GG25AffineFactorInstance.card_bad_le_pencil
#print axioms ArkLib.ProximityGap.GG25AffineFactorInstance.card_bad_le_pencil_real
