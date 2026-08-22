/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf5M3_crossstep_ceiling
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail

/-!
# A constraint lemma: the loose Lam–Leung ceiling alone cannot discharge `M3CrossStepBound` for `r ≥ 2` (Issue #444)

The recursion-closure `_wf5M3_crossstep_ceiling` localizes the prize energy ladder onto the single
open `Prop`

    `M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}`,  `crossMass G r = E_{r+1} − n·E_r`.

`CrossStepRungOne` discharged the `r = 0, 1` rungs from the proven `r ≤ 2` energy ceilings. The
natural next question — *can the same loose ceiling argument keep going?* — is answered **NO** here,
with a precise constraint lemma. This is a frontier-movement *negative* result: it tells the fleet
exactly why the deep rungs are genuinely open (they need off-diagonal cancellation, not just a ceiling).

## The mechanism

The only ceiling/floor inputs available without new analytic work are:
- the Lam–Leung upper ceiling `E_{r+1} ≤ (2r+1)‼·n^{r+1}` (`LamLeungCeiling G (r+1)`), and
- the **unconditional diagonal floor** `E_r ≥ n^r` (`pow_card_le_rEnergy`, proven here: the `n^r`
  pairs `(v, v)` already give `∑v = ∑v`).

Combining (subtract the floor from the ceiling):

    `crossMass G r = E_{r+1} − n·E_r  ≤  (2r+1)‼·n^{r+1} − n·n^r  =  ((2r+1)‼ − 1)·n^{r+1}`.

The `M3` step target is `2r·(2r−1)‼·n^{r+1}`. Since `(2r+1)‼ = (2r+1)·(2r−1)‼`,

    `(2r+1)‼ − 1 − 2r·(2r−1)‼ = (2r−1)‼ − 1`.

So the loose-ceiling upper bound on `crossMass G r` **exceeds** the `M3` step target by exactly
`((2r−1)‼ − 1)·n^{r+1}`. This is `= 0` iff `(2r−1)‼ = 1`, i.e. iff `r ≤ 1` (`(−1)‼ = (1)‼ = 1`,
`(3)‼ = 3 > 1`). Hence:

> **The loose Lam–Leung ceiling + diagonal floor discharge `M3CrossStepBound r` ⟺ `r ≤ 1`.**
> For every `r ≥ 2` the ceiling argument overshoots the step target by `((2r−1)‼ − 1)·n^{r+1} > 0`
> (for `n ≥ 1`), so the deep rungs CANNOT be closed by ceilings alone — they require genuine
> off-diagonal autocorrelation cancellation (`C_r(δ) ≪ E_r` on average), which is the open BGK content.

## Results (axiom-clean)

* `pow_card_le_rEnergy`        : `|G|^r ≤ E_r(G)` — the unconditional diagonal floor.
* `crossMass_le_of_ceiling`    : `LamLeungCeiling G (r+1) ⟹ crossMass G r ≤ ((2r+1)‼ − 1)·n^{r+1}`
                                  (the best the loose ceiling+floor can give).
* `ceiling_slack_eq`           : `((2r+1)‼ − 1) − 2r·(2r−1)‼ = (2r−1)‼ − 1` — the exact overshoot identity.
* `ceiling_insufficient_of_two_le` : for `r ≥ 2`, `n ≥ 1`, the loose-ceiling bound STRICTLY exceeds the
                                  `M3` step target (overshoot `((2r−1)‼−1)·n^{r+1} > 0`) — the ceiling
                                  route is provably insufficient at every deep rung.

## Honest scope

NOT a CORE closure, NOT a refutation of `M3CrossStepBound` itself (which IS true — the probes confirm
`crossMass ≤` the step bound at every faithful rung). It is a refutation of one *proof strategy* (the
loose-ceiling route) for `r ≥ 2`, with the exact slack. A walled lane mapped precisely (rule 4). CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass LamLeungCeiling)

namespace ArkLib.ProximityGap.CrossStepCeilingInsufficient

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The unconditional diagonal floor `|G|^r ≤ E_r(G)`.** The `r`-fold energy
`E_r = #{(v,w) : ∑v = ∑w}` is at least the number of diagonal pairs `(v, v)` (each satisfies
`∑v = ∑v`), which is `#{v ∈ (Fin r → G)} = |G|^r`. -/
theorem pow_card_le_rEnergy (G : Finset F) (r : ℕ) :
    G.card ^ r ≤ rEnergy G r := by
  classical
  unfold rEnergy
  -- lower bound the inner w-sum by its diagonal term w = v
  have hdiag : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      (1 : ℕ) ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
        (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    calc (1 : ℕ)
        = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
      _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
            (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
          Finset.single_le_sum (f := fun w => (if ∑ i, v i = ∑ i, w i then (1:ℕ) else 0))
            (fun w _ => Nat.zero_le _) hv
  calc G.card ^ r
      = ∑ _v ∈ Fintype.piFinset (fun _ : Fin r => G), (1 : ℕ) := by
        rw [Finset.sum_const, Fintype.card_piFinset_const, smul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
        Finset.sum_le_sum hdiag

/-- **The best the loose ceiling+floor can give for `crossMass G r`.** From the recursion
`crossMass G r = E_{r+1} − n·E_r`, the Lam–Leung ceiling `E_{r+1} ≤ (2r+1)‼·n^{r+1}` and the
diagonal floor `E_r ≥ n^r`:
`crossMass G r ≤ (2r+1)‼·n^{r+1} − n·n^r = ((2r+1)‼ − 1)·n^{r+1}`. -/
theorem crossMass_le_of_ceiling (G : Finset F) (r : ℕ) (hceil : LamLeungCeiling G (r + 1)) :
    crossMass G r ≤ (Nat.doubleFactorial (2 * (r + 1) - 1) - 1) * G.card ^ (r + 1) := by
  unfold LamLeungCeiling at hceil
  -- recursion: E_{r+1} = |G|·E_r + crossMass G r
  have hrec := rEnergy_succ_crossMass G r
  -- floor: n^r ≤ E_r ⟹ n^{r+1} ≤ |G|·E_r
  have hfloor : G.card ^ (r + 1) ≤ G.card * rEnergy G r := by
    calc G.card ^ (r + 1) = G.card * G.card ^ r := by ring
      _ ≤ G.card * rEnergy G r := Nat.mul_le_mul_left _ (pow_card_le_rEnergy G r)
  have hDF1 : 1 ≤ Nat.doubleFactorial (2 * (r + 1) - 1) := Nat.doubleFactorial_pos _
  -- name the nonlinear atoms so omega can finish linearly
  set E1 := rEnergy G (r + 1) with hE1
  set NEr := G.card * rEnergy G r with hNEr
  set DF := Nat.doubleFactorial (2 * (r + 1) - 1) with hDF
  set P := G.card ^ (r + 1) with hP
  -- expand the RHS (DF - 1)·P = DF·P - P (subtraction distributes since DF ≥ 1, P ≥ 0)
  have hRHS : (DF - 1) * P = DF * P - P := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [hRHS]
  -- now: crossMass = E1 - NEr (hrec : E1 = NEr + crossMass), hceil : E1 ≤ DF·P, hfloor : P ≤ NEr
  omega

/-- **The exact overshoot identity.** `((2(r+1)−1)‼ − 1) − 2r·(2r−1)‼ = (2r−1)‼ − 1`. Since
`(2(r+1)−1)‼ = (2r+1)·(2r−1)‼` (`doubleFactorial_step`), the loose-ceiling coefficient minus the
`M3`-step coefficient is exactly `(2r−1)‼ − 1`. -/
theorem ceiling_slack_eq (r : ℕ) :
    (Nat.doubleFactorial (2 * (r + 1) - 1) - 1)
      = 2 * r * Nat.doubleFactorial (2 * r - 1) + (Nat.doubleFactorial (2 * r - 1) - 1) := by
  rw [ArkLib.ProximityGap.CrossStepCeiling.doubleFactorial_step r]
  have hDF1 : 1 ≤ Nat.doubleFactorial (2 * r - 1) := Nat.doubleFactorial_pos _
  -- (2r+1)·D - 1 = 2r·D + (D - 1)
  set D := Nat.doubleFactorial (2 * r - 1)
  have : (2 * r + 1) * D = 2 * r * D + D := by ring
  omega

/-- **THE CONSTRAINT LEMMA: for `r ≥ 2` the loose-ceiling route STRICTLY overshoots the `M3` step
target.** For `r ≥ 2` and `n ≥ 1`, the best loose-ceiling+floor bound on `crossMass G r`,
namely `((2(r+1)−1)‼ − 1)·n^{r+1}`, strictly exceeds the `M3CrossStepBound` target
`2r·(2r−1)‼·n^{r+1}` — by exactly `((2r−1)‼ − 1)·n^{r+1} > 0`. So no ceiling-only argument can
discharge `M3CrossStepBound r` at any deep rung; genuine off-diagonal cancellation is required.
(At `r ≤ 1` the overshoot `(2r−1)‼ − 1 = 0`, which is precisely why `CrossStepRungOne` succeeds there.) -/
theorem ceiling_insufficient_of_two_le (G : Finset F) (r : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ G.card) :
    2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1)
      < (Nat.doubleFactorial (2 * (r + 1) - 1) - 1) * G.card ^ (r + 1) := by
  set n := G.card with hn'
  set D := Nat.doubleFactorial (2 * r - 1) with hD
  have hpow : 1 ≤ n ^ (r + 1) := Nat.one_le_pow _ _ hn
  -- (2r-1)‼ - 1 > 0 for r ≥ 2:  2r-1 ≥ 3, and (2r-1)‼ = (2r-1)·(2r-3)‼ ≥ 3·1 = 3.
  have hDge3 : 3 ≤ D := by
    -- write 2r-1 = (2k+1)+2 with k = r-2, so (2r-1)‼ = (2r-1)·(2r-3)‼
    obtain ⟨k, hk⟩ : ∃ k, 2 * r - 1 = (2 * k + 1) + 2 := ⟨r - 2, by omega⟩
    rw [hD, hk, Nat.doubleFactorial_add_two]
    have hfac : 3 ≤ 2 * k + 1 + 2 := by omega
    have hpos : 1 ≤ Nat.doubleFactorial (2 * k + 1) := Nat.doubleFactorial_pos _
    calc 3 ≤ (2 * k + 1 + 2) * 1 := by omega
      _ ≤ (2 * k + 1 + 2) * Nat.doubleFactorial (2 * k + 1) :=
          Nat.mul_le_mul_left _ hpos
  -- coefficient strict inequality, then multiply by n^{r+1} ≥ 1
  have hcoef : 2 * r * D < Nat.doubleFactorial (2 * (r + 1) - 1) - 1 := by
    rw [ceiling_slack_eq r, ← hD]
    omega
  exact Nat.mul_lt_mul_of_lt_of_le hcoef (le_refl (n ^ (r + 1))) hpow

end ArkLib.ProximityGap.CrossStepCeilingInsufficient

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepCeilingInsufficient.pow_card_le_rEnergy
#print axioms ArkLib.ProximityGap.CrossStepCeilingInsufficient.crossMass_le_of_ceiling
#print axioms ArkLib.ProximityGap.CrossStepCeilingInsufficient.ceiling_slack_eq
#print axioms ArkLib.ProximityGap.CrossStepCeilingInsufficient.ceiling_insufficient_of_two_le
