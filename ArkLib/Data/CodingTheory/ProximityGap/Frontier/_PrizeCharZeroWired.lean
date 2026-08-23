/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeConditionalCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvPrize_MomentToSupCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselWickAllR

/-!
# Char-0 anchor wired into the prize capstone — discharge `hbessel` (+ `hsup`)

The prize moment/sup capstones (`prize_of_saddleEnergyBound` in `_PrizeConditionalCapstone`,
`prize_sup_of_saddle_concrete` in `_AvPrize_MomentToSupCapstone`) carry the char-0 anchor
`hbessel : E ≤ Wick` as a FREE hypothesis. The all-`r` char-0 Wick energy bound
`besselWick_allR : besselE r m ≤ wickRHS r m` (in `_AvW0_BesselWickAllR`, proven axiom-clean)
supplies exactly that content but lived in isolation — never instantiated into the capstones (a
wiring gap surfaced by the #444 chain audit: char-0 proven but not wired).

This leaf closes that gap. Instantiating the capstones with `E := besselE r m`
(= `E_r^{char0}(μ_{2m})`, the genuine char-0 energy via the antipodal-balance Bessel identity)
and `Wick := wickRHS r m` (= `(2r−1)‼·(2m)^r`), and discharging `hbessel` via the cast of
`besselWick_allR`:

* `prize_moment_of_saddle_charZeroWired` — the b≠0 moment is sub-Gaussian (`μ ≤ wickRHS r m`)
  from the SINGLE open input, the saddle energy bound (`SaddleEnergyBound` = BGK/Paley at β=4).
* `prize_sup_of_saddle_charZeroWired` — the full sup-form `|η b| ≤ 2√e·√(2m·log p)` for ANY
  family `η`, discharging BOTH `hbessel` (char-0) and `hsup` (sup-below-moment, via
  `Finset.single_le_sum`); only the saddle bound remains open. The supporting bridge
  `wickOdd_eq_doubleFactorial` proves `wickOdd r = (2r−1)‼`.

This does NOT close the prize — the saddle bound stays an explicit open hypothesis. It only
makes the (already-proven) char-0 + elementary discharges explicit, so the whole MOMENT FACE of
the reduction bottoms out on exactly one open Prop. (The incidence face — BCHKS 1.12 — is a
separate, non-machine-linked open Prop.) Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroWired

open ArkLib.ProximityGap.Frontier.AvW0
open ProximityGap.Frontier.MomentToSup

/-- **Char-0 anchor discharged moment capstone.** With the char-0 Bessel energy `besselE r m`
(= `E_r^{char0}(μ_{2m})`) as `E` and its proven Wick bound `wickRHS r m` (= `(2r−1)‼·(2m)^r`)
as `Wick`, the b≠0 moment `μ` is sub-Gaussian (`μ ≤ wickRHS r m`) given ONLY the saddle energy
bound `hsaddle` (BGK at β=4) and the normalization `hμ : μ·(p−1) = S`. The char-0 hypothesis is
discharged here (via `besselWick_allR`), not assumed. -/
theorem prize_moment_of_saddle_charZeroWired
    (S μ p : ℝ) (r m : ℕ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S)
    (hsaddle : S ≤ (p - 1) * (besselE r m : ℝ)) :
    μ ≤ (wickRHS r m : ℝ) :=
  ProximityGap.Frontier.PrizeCapstone.prize_of_saddleEnergyBound
    S (besselE r m : ℝ) (wickRHS r m : ℝ) μ p hp hμ hsaddle
    (by exact_mod_cast besselWick_allR r m)

/-- **Necessity, char-0 discharged.** Modulo the proven char-0 anchor, the saddle energy bound
is the load-bearing rung: if the sub-Gaussian moment conclusion fails (`wickRHS r m < μ`), the
saddle bound must fail too. -/
theorem saddle_necessary_charZeroWired
    (S μ p : ℝ) (r m : ℕ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S) (hfail : (wickRHS r m : ℝ) < μ) :
    (p - 1) * (besselE r m : ℝ) < S :=
  ProximityGap.Frontier.PrizeCapstone.saddleEnergyBound_necessary
    S (besselE r m : ℝ) (wickRHS r m : ℝ) μ p hp hμ
    (by exact_mod_cast besselWick_allR r m) hfail

/-- Bridge: the real product `wickOdd r = ∏_{i<r}(2i+1)` equals the odd double factorial
`(2r−1)‼`. -/
theorem wickOdd_eq_doubleFactorial (r : ℕ) :
    wickOdd r = (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
  induction r with
  | zero => simp [wickOdd, Nat.doubleFactorial]
  | succ k ih =>
    rw [wickOdd, Finset.prod_range_succ, ← wickOdd, ih]
    rcases k with _ | j
    · simp [Nat.doubleFactorial]
    · have e2 : 2 * (j + 1 + 1) - 1 = (2 * (j + 1) - 1) + 2 := by omega
      rw [e2, Nat.doubleFactorial]
      push_cast
      have e3 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [e3]
      push_cast
      ring

/-- **Full moment-lane reduction, char-0 + sup-below-moment discharged.** For ANY family
`η : ι → ℝ`, given ONLY the saddle energy bound on its `2r`-th moment
(`∑ |η i|^{2r} ≤ (p−1)·E_r^{char0}`, = `SaddleEnergyBound`/BGK@β=4), every entry is bounded by
the prize sup-form `|η b| ≤ 2√e·√(2m·log p)`. The char-0 anchor (via `besselWick_allR`) and the
elementary sup-below-moment (`hsup`, via `Finset.single_le_sum`) are discharged here; only the
saddle bound remains open. -/
theorem prize_sup_of_saddle_charZeroWired
    {ι : Type*} [Fintype ι] (η : ι → ℝ) (b : ι) (p : ℝ) (r m : ℕ)
    (hp : 3 ≤ p) (hr : 1 ≤ r)
    (hrlo : Real.log (p - 1) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ 2 * Real.log p)
    (hsaddle : (∑ i, |η i| ^ (2 * r)) ≤ (p - 1) * (besselE r m : ℝ)) :
    |η b| ≤ 2 * Real.sqrt (Real.exp 1) * Real.sqrt (((2 * m : ℕ) : ℝ) * Real.log p) := by
  have hsup : (|η b| ^ 2) ^ (r : ℝ) ≤ ∑ i, |η i| ^ (2 * r) := by
    rw [Real.rpow_natCast, ← pow_mul]
    exact Finset.single_le_sum (f := fun i => |η i| ^ (2 * r))
      (fun i _ => pow_nonneg (abs_nonneg (η i)) (2 * r)) (Finset.mem_univ b)
  have hbessel : (besselE r m : ℝ) ≤ wickOdd r * (((2 * m : ℕ) : ℝ)) ^ r := by
    have hb : (besselE r m : ℝ) ≤ (wickRHS r m : ℝ) := by exact_mod_cast besselWick_allR r m
    have hw : (wickRHS r m : ℝ)
        = (Nat.doubleFactorial (2 * r - 1) : ℝ) * (((2 * m : ℕ) : ℝ)) ^ r := by
      unfold wickRHS; push_cast; ring
    rw [wickOdd_eq_doubleFactorial]; linarith [hb, hw]
  exact prize_sup_of_saddle_concrete (|η b|) (((2 * m : ℕ) : ℝ)) p (∑ i, |η i| ^ (2 * r))
    (besselE r m : ℝ) r (abs_nonneg _) (by positivity) hp hr hrlo hrhi hsup hsaddle hbessel

end ProximityGap.Frontier.CharZeroWired

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ProximityGap.Frontier.CharZeroWired.prize_moment_of_saddle_charZeroWired
#print axioms ProximityGap.Frontier.CharZeroWired.saddle_necessary_charZeroWired
#print axioms ProximityGap.Frontier.CharZeroWired.wickOdd_eq_doubleFactorial
#print axioms ProximityGap.Frontier.CharZeroWired.prize_sup_of_saddle_charZeroWired
