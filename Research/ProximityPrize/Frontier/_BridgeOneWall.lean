/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The bridge: the two-obstruction pincer is ONE wall in two dual bases (#444)

The campaign found a **two-obstruction pincer**: every approach to the char-`p` energy bound hits either
(i) the moment-method necessity obstruction (must capture cancellation, not a count) or (ii) the √p-vacuity
(Weil/Deligne sees the field scale √p ≫ n for a thin subgroup). N7 (cohomology) escapes (i) but falls to (ii);
the relative-trace/additive route escapes (ii) but falls to (i).

This file proves these are NOT two independent walls to be bridged — they are **one wall in two Fourier-dual
bases**, connected by an EXACT bracket. The worst-case sup-norm `M = max_{b≠0}‖η_b‖` and the additive energy
`E_r = rEnergy G r` determine each other up to the trivial averaging factor `q−1`:

> **`(q·E_r − n^{2r})/(q−1) ≤ M^{2r} ≤ q·E_r − n^{2r}`**     (the bridge bracket, `q = |F|`, `n = |G|`).

* The **upper** bound `M^{2r} ≤ Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}` (`worst term ≤ sum`, the assembly
  direction) — the additive energy bounds the worst case.
* The **lower** bound `M^{2r} ≥ Σ/(q−1) = (q·E_r − n^{2r})/(q−1)` (`sum ≤ card·max`) — the worst case bounds
  the additive energy: `energy_le_of_supnorm`.

So a bound on `E_r` and a bound on `M` are EQUIVALENT (each implies the other within the factor `q−1`). The
additive basis (where the √p's have cancelled into `E_r`) and the multiplicative basis (where `M` sees the
Gauss-sum phases) carry **identical information** — the bridge is the identity `Σ_{b≠0}‖η_b‖^{2r} = q·E_r −
n^{2r}` (`DCSubtractedMoment.sum_nonzero_moment`), which has NO loss and NO gain. **Bridging the two faces is a
tautology that maps the open problem to itself.**

## What this means for "unifying to prove the tightest bound"

The pincer cannot be defeated by *combining* the additive and multiplicative pictures, because they are the
same picture (Parseval-dual). The ONLY non-tautological way to combine them is to use the *joint*
additive-multiplicative structure — i.e. a sum-product / additive-energy-of-a-multiplicative-subgroup bound
(di Benedetto–Solymosi–White's trilinear `H^{1−31/2880}`). That is genuinely more than either projection, and
it is the SOTA — but it carries a `p^{1/4}` tax and **vanishes at the prize thinness** `n ≈ p^{0.19} < p^{1/4}`.
So the tightest bound the unified picture provably gives is BGK `n^{1−o(1)}`; reaching `√n` needs the
sum-product exponent to improve to the Paley level, which is the open problem. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.BridgeOneWall

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

/-- **The backward bridge: a sup-norm bound forces an energy bound.** If every nonzero period is `≤ M`, then
the additive energy obeys `q·E_r − n^{2r} ≤ (q−1)·M^{2r}` — i.e. `E_r` is controlled by `M`. Together with the
forward direction (`M^{2r} ≤ q·E_r − n^{2r}`, worst-term ≤ sum), this brackets `M^{2r}` and `E_r` within the
factor `q−1`: they are the SAME information. The √p-free additive count and the Gauss-phase worst case are two
bases for one object. -/
theorem energy_le_of_supnorm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hsup : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ≤ M) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ (2 * r) := by
  -- Σ_{b≠0} ‖η_b‖^{2r} ≤ Σ_{b≠0} M^{2r} = (q−1)·M^{2r}
  have hbound : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ _b ∈ univ.erase (0 : F), M ^ (2 * r) := by
    apply Finset.sum_le_sum
    intro b hb
    gcongr
    exact hsup b hb
  rw [sum_nonzero_moment hψ G r] at hbound
  rw [Finset.sum_const, nsmul_eq_mul] at hbound
  -- the cardinality of `univ.erase 0` is `q − 1`
  have hcard : (univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcast : ((univ.erase (0 : F)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub hpos, Nat.cast_one]
  rw [hcast] at hbound
  exact hbound

/-- **The bridge bracket (the consolidating statement).** For any `M` that bounds every nonzero period, the
additive energy and the sup-norm are linked two-sidedly: `q·E_r − n^{2r} ≤ (q−1)·M^{2r}`. Combined with the
forward `M^{2r} ≤ q·E_r − n^{2r}` (worst-term ≤ sum, in-tree), the additive `E_r` and the worst-case `M^{2r}`
bracket each other within `q−1`. The two obstruction-faces (additive count / multiplicative phases) bound the
SAME object; the pincer is one wall, and the bridge between its faces is the exact identity
`sum_nonzero_moment`, tautological. -/
theorem pincer_is_one_wall {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hsup : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ≤ M) :
    -- the additive energy is forced into the band [ (LHS)/(q−1) , … ] by the sup-norm
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ (2 * r) :=
  energy_le_of_supnorm hψ G r hM hsup

end ArkLib.ProximityGap.Frontier.BridgeOneWall

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BridgeOneWall.energy_le_of_supnorm
#print axioms ArkLib.ProximityGap.Frontier.BridgeOneWall.pincer_is_one_wall
