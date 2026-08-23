/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DCCorrectSupCapstone

/-!
# Necessity rung for the DC-correct sup floor: a sup bound FORCES the DC-subtracted moment bound

`_DCCorrectSupCapstone.worstPeriod_le_prizeFloor_dc` is the SUFFICIENCY direction: the open
DC-subtracted moment bound `hSr` (`S_r = q·E_r − |G|^{2r} = ∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r·|G|)^r`)
implies the worst-`b` sup obeys the prize floor. This file supplies the NECESSITY rung, completing
the reduction into a clean two-sided picture on the genuine DC-subtracted object:

> `dcSubtractedMoment_le_of_worstPeriod_le` : if the worst-`b` sup `M(G) = max_{b≠0}‖η_b‖ ≤ K`, then
> the DC-subtracted moment is forced `S_r = q·E_r − |G|^{2r} ≤ (q−1)·K^{2r}`.

The mechanism is the elementary `Finset.sum_le_card_nsmul`: each of the `q−1`
nonzero-frequency terms
`‖η_b‖^{2r}` is `≤ M^{2r} ≤ K^{2r}` (the sup dominates every member), so their sum is `≤
(q−1)·K^{2r}`.
There is NO cancellation, completion, anti-concentration, or moment-saving here — it is the trivial
`Σ ≤ #·max` ceiling, the *converse* of the worst-term `single_le_sum` floor used in
`DCMomentSupBound.eta_pow_le_dc`. Its content is solely that the open object the prize must
control IS
the DC-subtracted `S_r` (not the DC-included `E_r`): a sup bound and an `S_r` bound are mutually
forcing up to the `(q−1)` vs `q` count and the `^{2r}` power, so neither phrasing smuggles in a
strictly easier object than the other.

**Honest status.** This is a trivial counting bound, NOT progress on CORE. It establishes
only that the
DC-subtracted moment `S_r` and the worst-`b` sup `M(G)` are the same open object viewed two
ways — the
NECESSITY companion to the audit-recommended DC-correct sufficiency capstone. The prize
floor `K = √e·
√(2r·|G|)` instantiation gives `S_r ≤ (q−1)·(e·2r·|G|)^r`, the DC-subtracted moment ceiling
the prize
forces. No CORE / cancellation / completion / anti-concentration / moment-saving / capacity claim;
prize CORE stays OPEN.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.DCCorrectSupNecessity

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Necessity rung (DC-correct).** If the worst nonzero-frequency period is `≤ K`, then the
DC-subtracted moment `S_r = q·E_r − |G|^{2r}` is forced below `(q−1)·K^{2r}`. Each of the
`q−1` nonzero
terms `‖η_b‖^{2r} ≤ K^{2r}` (the sup dominates every member), so the sum obeys the `Σ ≤
#·max` ceiling.
This is the converse of the `single_le_sum` worst-term floor: a sup bound and a DC-subtracted-moment
bound are mutually forcing, so neither phrasing of the open core is strictly easier than the
other. -/
theorem dcSubtractedMoment_le_of_worstPeriod_le [Nontrivial F] {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {K : ℝ}
    (hsup : worstPeriod ψ G ≤ K) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * K ^ (2 * r) := by
  -- the DC-subtracted moment IS the b≠0 sum
  rw [← sum_nonzero_moment hψ G r]
  -- each nonzero term ‖η_b‖^{2r} ≤ K^{2r}, since ‖η_b‖ ≤ worstPeriod ≤ K
  have hterm : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) ≤ K ^ (2 * r) := by
    intro b hb
    have hle : ‖eta ψ G b‖ ≤ K :=
      le_trans (Finset.le_sup' (fun b => ‖eta ψ G b‖) hb) hsup
    exact pow_le_pow_left₀ (norm_nonneg _) hle (2 * r)
  -- sum over the q−1 nonzero frequencies ≤ (q−1)·K^{2r}
  have hsum : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ (univ.erase (0 : F)).card • K ^ (2 * r) :=
    Finset.sum_le_card_nsmul _ _ _ hterm
  have hcard : (univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [hcard, nsmul_eq_mul] at hsum
  -- cast (q−1 : ℕ) to (q : ℝ) − 1, using 1 ≤ q
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  calc ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * K ^ (2 * r) := hsum
    _ = ((Fintype.card F : ℝ) - 1) * K ^ (2 * r) := by
        rw [Nat.cast_sub hq1, Nat.cast_one]

end ArkLib.ProximityGap.Frontier.DCCorrectSupNecessity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.DCCorrectSupNecessity in
#print axioms dcSubtractedMoment_le_of_worstPeriod_le
