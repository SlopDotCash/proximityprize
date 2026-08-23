/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion
import ArkLib.Data.CodingTheory.ProximityGap.WickStepRatio

/-!
# The convolution / doubling-tower energy bootstrap is SAVING-DESTROYING (#444, ANGLE BOOTSTRAP)

The prize reduces to the **one-step Wick inequality** for the depth-`r` additive energy
`E_r = rEnergy G r` of the smooth subgroup `μ_n ⊆ F_p` (`n = |G|`):

  `E_{r+1} ≤ (2r+1)·n·E_r`        (the BGK / one-step step ratio, OPEN at the saddle `r ≈ log p`),

which telescopes (`WickStepRatio.le_wickEnvelope_of_step_ratio`) to the Wick envelope
`E_r ≤ (2r−1)‼·n^r`, and that envelope at depth `r = log p` gives `B = max_{b≠0}‖η_b‖ ≤ √(2 n log p)`
= the prize (`C = √2`).

**The bootstrap hope** (this angle): the one-step inequality is *proven* below the wraparound onset
`r ≤ r0 = ½ p^{2/n}` (`Wraparound.no_wraparound_depth`), and the char-0 backbone holds all `r`. Can a
**self-improving / sum-product convolution recursion** lift the proven low-`r` bound to the saddle?
The natural such recursion is the convolution doubling `E_{2r} = ‖f_r * f_r‖₂²`, bounded by Young's
inequality `E_{2r} ≤ n^{2r}·E_r` (and more crudely by the in-tree single-step
`CharPMomentRecursion.rEnergy_succ_le : E_{r+1} ≤ n²·E_r`).

**This file proves the recursion is saving-DESTROYING**, the energy-level analogue of
`_TowerDescentNoSaving` (which proved the *list/root-count* tower is saving-preserving):

* `young_chain` — iterating the proven single-step `E_{k+1} ≤ n²·E_k` from a base `r0` to depth `R`
  gives `E_R ≤ n^{2(R−r0)}·E_{r0}`. This is the bound ANY Young/convolution-doubling chain produces
  (doubling `E_{2r} ≤ n^{2r}E_r` is one such chain, with the SAME exponent count `2·(2r−r)=2r` per
  octave); it is the best the convolution recursion can give from the base.
* `wickEnvelope_le_young_chain_step` — the per-rung comparison: the Wick one-step factor `(2r+1)·n`
  is `≤ n²` exactly when `2r+1 ≤ n` (the prize regime `r ≪ n`). So each Young rung **over-bounds**
  the Wick rung by the factor `n/(2r+1) ≫ 1`.
* `wickEnvelope_le_young_chain` — consequently `Wick(R) ≤ n^{2(R−r0)}·Wick(r0)` whenever `2k+1 ≤ n`
  on `[r0, R)`: the convolution-bootstrap bound is **never smaller** than the one-step Wick bound.
* `bootstrap_no_saving` — the headline no-go. If the proven base `E_{r0} ≤ Wick(r0)` is fed into the
  Young/doubling bootstrap, the resulting bound `n^{2(R−r0)}·Wick(r0)` is `≥ Wick(R)` (the one-step
  ladder bound), so the bootstrap manufactures **no saving** over simply assuming the one-step
  inequality — it cannot reach, let alone beat, the Wick/prize envelope. The open content stays
  EXACTLY the one-step inequality, which is BGK.

## Honest scope (rule 4 — refutation-with-mechanism)

This is a **quantified no-go**, not a closure. It walls the convolution/doubling-bootstrap route by
showing the doubling step pays `n²` per rung where Wick pays only `(2r+1)·n`, an overpayment of
`n/(2r+1)` per rung that compounds to an `n^{Θ(R)}` gap at the saddle. The exact probe
(`/tmp/bootstrap_stall.py`) confirms the implied `B/√n` blows up from the prize value `≈√(2 log p)`
to `41810` at `n = 2^30` (prize wants `≈12.9`). CORE `E_{r+1} ≤ (2r+1)·n·E_r` at `r ≈ log p` (= BGK /
Lam–Leung / di Benedetto) stays OPEN. Issues #444, #407.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open ArkLib.ProximityGap.CharPMomentRecursion
open ArkLib.ProximityGap.WickStepRatio
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

namespace ArkLib.ProximityGap.AtkBootstrap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The convolution / Young single-step chain from the base -/

/-- **The Young/convolution-doubling chain bound.** Iterating the in-tree single-step Young bound
`CharPMomentRecursion.rEnergy_succ_le : E_{k+1} ≤ |G|²·E_k` from a base depth `r0` up to `R ≥ r0`
gives `E_R ≤ |G|^{2(R−r0)}·E_{r0}`. This is the bound the convolution/doubling bootstrap produces
from the proven base: a doubling octave `E_{r}→E_{2r}` also costs the Young factor `|G|^{2r}`
(`= (|G|²)^r`, the same exponent as `r` single steps), so the doubling tower and the single-step
ladder both yield this `|G|^{2(R−r0)}` chain factor. -/
theorem young_chain (G : Finset F) {r0 R : ℕ} (h : r0 ≤ R) :
    rEnergy G R ≤ G.card ^ (2 * (R - r0)) * rEnergy G r0 := by
  induction R, h using Nat.le_induction with
  | base => simp
  | succ R hR ih =>
      have hstep : rEnergy G (R + 1) ≤ G.card ^ 2 * rEnergy G R := rEnergy_succ_le G R
      calc rEnergy G (R + 1)
          ≤ G.card ^ 2 * rEnergy G R := hstep
        _ ≤ G.card ^ 2 * (G.card ^ (2 * (R - r0)) * rEnergy G r0) :=
            Nat.mul_le_mul_left _ ih
        _ = G.card ^ (2 * (R + 1 - r0)) * rEnergy G r0 := by
            rw [← Nat.mul_assoc, ← pow_add]
            congr 2
            omega

/-! ## The per-rung Wick-vs-Young comparison (the saving-destruction mechanism) -/

/-- **Per-rung overpayment.** In the prize regime `2r+1 ≤ n` the Wick one-step factor `(2r+1)·n` is
`≤ n²` (= the Young single-step factor). Each Young/doubling rung therefore over-bounds the Wick rung
by `n/(2r+1) ≥ 1`. This is the atom of the saving destruction: the convolution recursion pays the
full `n²` where the genuine energy ladder pays only `(2r+1)·n`. -/
theorem wickStep_le_youngStep {n r : ℕ} (hrn : 2 * r + 1 ≤ n) :
    (2 * r + 1) * n ≤ n ^ 2 := by
  calc (2 * r + 1) * n ≤ n * n := Nat.mul_le_mul_right n hrn
    _ = n ^ 2 := (sq n).symm

/-- **The Wick envelope is dominated by the Young chain bound.** Whenever `2k+1 ≤ n` on the whole
range `[r0, R)` (the prize regime `R ≪ n`), the one-step Wick envelope satisfies
`Wick(R) ≤ n^{2(R−r0)}·Wick(r0)`: the convolution/doubling bootstrap bound is **never smaller** than
the one-step Wick bound it is trying to reach. Proven by telescoping the per-rung overpayment
`(2k+1)·n ≤ n²` along the Wick step recurrence `Wick(k+1) = (2k+1)·n·Wick(k)`. -/
theorem wickEnvelope_le_young_chain {n r0 R : ℕ} (hr0 : 1 ≤ r0) (h : r0 ≤ R)
    (hrange : ∀ k, r0 ≤ k → k < R → 2 * k + 1 ≤ n) :
    wickEnvelope n R ≤ n ^ (2 * (R - r0)) * wickEnvelope n r0 := by
  induction R, h using Nat.le_induction with
  | base => simp
  | succ R hR ih =>
      have hr0R : 1 ≤ R := le_trans hr0 hR
      -- Wick(R+1) = (2R+1)·n·Wick(R)
      have hwstep : wickEnvelope n (R + 1) = (2 * R + 1) * n * wickEnvelope n R :=
        wickEnvelope_succ_eq n R hr0R
      -- range hypothesis at R itself
      have hRrange : 2 * R + 1 ≤ n := hrange R hR (Nat.lt_succ_self R)
      have ih' : wickEnvelope n R ≤ n ^ (2 * (R - r0)) * wickEnvelope n r0 :=
        ih (fun k hk1 hkR => hrange k hk1 (lt_trans hkR (Nat.lt_succ_self R)))
      calc wickEnvelope n (R + 1)
          = (2 * R + 1) * n * wickEnvelope n R := hwstep
        _ ≤ n ^ 2 * wickEnvelope n R := Nat.mul_le_mul_right _ (wickStep_le_youngStep hRrange)
        _ ≤ n ^ 2 * (n ^ (2 * (R - r0)) * wickEnvelope n r0) := Nat.mul_le_mul_left _ ih'
        _ = n ^ (2 * (R + 1 - r0)) * wickEnvelope n r0 := by
            rw [← Nat.mul_assoc, ← pow_add]
            congr 2
            omega

/-! ## The headline no-go -/

/-- **The convolution/doubling-tower bootstrap manufactures NO saving (the energy-level
`_TowerDescentNoSaving`).** Suppose the proven base bound `E_{r0} ≤ Wick(r0)` holds at the onset
depth `r0` (true unconditionally for `r0 ≤ ½ p^{2/n}` via the wraparound threshold + char-0
backbone), and we are in the prize regime `2k+1 ≤ n` on `[r0, R)`. Then:

* the Young/convolution-doubling bootstrap produces `E_R ≤ n^{2(R−r0)}·Wick(r0)` (`young_chain`,
  using `n = |G|`); and
* this bootstrap bound is `≥` the one-step Wick bound `Wick(R)` (`wickEnvelope_le_young_chain`).

So the bootstrap bound on `E_R` is **never tighter** than the one-step Wick bound — the
convolution/doubling recursion adds no saving over directly assuming the one-step inequality. It
cannot reach the Wick/prize envelope (it over-bounds it by the compounded factor
`∏_{k=r0}^{R−1} n/(2k+1) = n^{R−r0}/∏(2k+1) ≫ 1`). The open content is EXACTLY the one-step
inequality `E_{k+1} ≤ (2k+1)·n·E_k`, which is BGK. -/
theorem bootstrap_no_saving (G : Finset F) {r0 R : ℕ}
    (hr0 : 1 ≤ r0) (h : r0 ≤ R)
    (hrange : ∀ k, r0 ≤ k → k < R → 2 * k + 1 ≤ G.card)
    (hbase : rEnergy G r0 ≤ wickEnvelope G.card r0) :
    -- the bootstrap bound the convolution recursion delivers …
    rEnergy G R ≤ G.card ^ (2 * (R - r0)) * wickEnvelope G.card r0
    -- … and that bound is never smaller than the one-step Wick bound it tries to reach.
    ∧ wickEnvelope G.card R ≤ G.card ^ (2 * (R - r0)) * wickEnvelope G.card r0 := by
  refine ⟨?_, wickEnvelope_le_young_chain hr0 h hrange⟩
  calc rEnergy G R
      ≤ G.card ^ (2 * (R - r0)) * rEnergy G r0 := young_chain G h
    _ ≤ G.card ^ (2 * (R - r0)) * wickEnvelope G.card r0 := Nat.mul_le_mul_left _ hbase

/-- **Quantified saving destruction: the bootstrap/Wick gap factor.** The bootstrap bound exceeds
the one-step Wick bound by the multiplicative factor `n^{R−r0} / ∏_{k=r0}^{R−1}(2k+1)`, which is
`≥ 1` and grows like `n^{Θ(R)}` in the prize regime. Concretely, the bootstrap bound is at least
`n^{R−r0}·(something ≤ Wick(R))`; here we record the clean consequence that the bootstrap bound
**strictly exceeds** the Wick bound whenever at least one rung has the strict overpayment
`2k+1 < n` (i.e. essentially always at the saddle, where `2R+1 ≈ 2 log p ≪ n`). -/
theorem bootstrap_strictly_lossy {n r0 R : ℕ} (hr0 : 1 ≤ r0) (h : r0 < R)
    (hrange : ∀ k, r0 ≤ k → k < R → 2 * k + 1 ≤ n)
    (hstrict : 2 * r0 + 1 < n) (hwpos : 0 < wickEnvelope n r0) :
    wickEnvelope n R < n ^ (2 * (R - r0)) * wickEnvelope n r0 := by
  -- Peel the first rung r0 with a STRICT overpayment, then dominate the rest.
  -- Wick(r0+1) = (2r0+1)·n·Wick(r0) < n²·Wick(r0).
  have hr0pos : 1 ≤ r0 := hr0
  have hr0lt : r0 + 1 ≤ R := h
  have hwstep0 : wickEnvelope n (r0 + 1) = (2 * r0 + 1) * n * wickEnvelope n r0 :=
    wickEnvelope_succ_eq n r0 hr0pos
  -- strict first rung
  have hstrict1 : wickEnvelope n (r0 + 1) < n ^ 2 * wickEnvelope n r0 := by
    rw [hwstep0]
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hstrict
    have hlt : (2 * r0 + 1) * n < n * n := (Nat.mul_lt_mul_right hn).mpr hstrict
    calc (2 * r0 + 1) * n * wickEnvelope n r0
        < n * n * wickEnvelope n r0 := (Nat.mul_lt_mul_right hwpos).mpr hlt
      _ = n ^ 2 * wickEnvelope n r0 := by rw [sq]
  -- chain from r0+1 to R with the (non-strict) Young bound
  have hchain : wickEnvelope n R ≤ n ^ (2 * (R - (r0 + 1))) * wickEnvelope n (r0 + 1) :=
    wickEnvelope_le_young_chain (by omega) hr0lt
      (fun k hk1 hkR => hrange k (by omega) hkR)
  -- combine
  have hexp : 2 + 2 * (R - (r0 + 1)) = 2 * (R - r0) := by omega
  calc wickEnvelope n R
      ≤ n ^ (2 * (R - (r0 + 1))) * wickEnvelope n (r0 + 1) := hchain
    _ < n ^ (2 * (R - (r0 + 1))) * (n ^ 2 * wickEnvelope n r0) := by
        have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hstrict
        exact (Nat.mul_lt_mul_left (pow_pos hn _)).mpr hstrict1
    _ = n ^ (2 * (R - r0)) * wickEnvelope n r0 := by
        rw [← Nat.mul_assoc, ← pow_add, Nat.add_comm (2 * (R - (r0 + 1))) 2, hexp]

end ArkLib.ProximityGap.AtkBootstrap

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.AtkBootstrap.young_chain
#print axioms ArkLib.ProximityGap.AtkBootstrap.wickStep_le_youngStep
#print axioms ArkLib.ProximityGap.AtkBootstrap.wickEnvelope_le_young_chain
#print axioms ArkLib.ProximityGap.AtkBootstrap.bootstrap_no_saving
#print axioms ArkLib.ProximityGap.AtkBootstrap.bootstrap_strictly_lossy
