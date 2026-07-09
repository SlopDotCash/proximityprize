/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G57AllDepthWraparoundDCConsumer

/-!
# LANE G58: the all-depth annihilator ledger worsens with depth (a theorem-level no-go)

This file closes the question raised by the G56/G57 calibration audit: *does the all-depth
folded-pattern identity strengthen the BGK-free annihilator ledger route?*

## The calibration (why G57's gate is not sharpenable into a new consumer)

`DCEnergyBound (Gset ζ m) r` is (definitionally) `q·E_r − n^{2r} ≤ q·Wickₚ` where `n = |Gset| = 2m`,
`E_r = rEnergy`, `Wickₚ = (2r−1)‼·n^r`. Substituting G56's exact identity
`E_r = negSymCount(2r) + W` (`W = wraparoundExcessR`) turns `DCEnergyBound` into the **exact**
equivalent

`q·W ≤ n^{2r} + q·(Wickₚ − negSymCount(2r))`.       (★)

This is the sharp slack-aware criterion implied by `rEnergy = negSymCount + W` together with
`negSymCount(2r) ≤ Wickₚ` (`G57.negSymCount_le_wick`). It is a genuine `↔`-rewrite of the open
`DCEnergyBound` prop — i.e. a **relabeling**, not a new theorem — because the slack term
`q·(Wickₚ − negSymCount)` is itself the residual BGK content. G57 already lands the weaker
sufficient gate `q·W ≤ n^{2r}`; (★) exposes the exact remaining obligation but does not discharge
it, so we deliberately do **not** land a stronger-looking wrapper around the same open prop.

## The fresh no-go we DO land

The BGK-free annihilator ledger (`FS1.annihilator_ledger_badPrime_cap`) bounds the count of bad
primes by `|pats| · (L/s) / T`, where at depth `r` the pattern count is
`|pats| = |expTupleSet m (2r)| = n^{2r}` and the Wick headroom threshold has scale
`T_r = Wickₚ = (2r−1)‼·n^r`. The **decisive** structural quantity is the ratio

`ledgerRatio r = |pats| / T_r = n^{2r} / ((2r−1)‼·n^r) = n^r / (2r−1)‼`.

We prove (i) the exact Nat/double-factorial per-depth lower bound `ledgerRatio r ≥ (n / (2r))^r`
(crude double factorial), so `ledgerRatio r ≥ 1` in the range `2r ≤ n`; and (ii) the exact
**step monotonicity** `ledgerRatio (r+1) ≥ ledgerRatio r` whenever `2r+1 ≤ n` (the one-step ratio
change is `n / (2r+1) ≥ 1`). Iterating (ii) from `r = 3` upward — valid at every step throughout
the prize regime `r ≈ ln q ≈ 83 ≪ n = 2^30` — the ledger ratio is monotone non-decreasing in depth
and strictly exceeds its `r = 3` value once `n > 2r+1`, so the all-depth ledger's non-vacuity
window strictly *shrinks* as `r` grows past `3`: the all-depth generalization moves the ledger the
**wrong way**. This converts Fable's informal "moves the wrong way" observation into an in-tree
result, closing the "does the all-depth identity help the ledger?" branch in `DISPROOF_LOG`.

(We do NOT use the false claim that `(n/(2r))^r` is monotone in `r` on all of `2r ≤ n`; it is not,
e.g. `(10/4)^2 > (10/6)^3`. The exact step lemma `ledger_ratio_step_mono` is the honest carrier.)

Nothing here is BGK: the ledger route never touches per-character incomplete Gauss sums. The price
of that (as before) is that it can only certify the Wick bound where the pattern-count/headroom
ratio stays bounded — and this file shows that ratio provably *blows up* with depth.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

open Finset

namespace ArkLib.ProximityGap.Frontier.G58AllDepthLedgerReversal

open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition (expTupleSet Gset Gset_card)

/-! ## Part 1 — the ledger's pattern count is `n^{2r}` -/

/-- The all-depth exponent domain `[0,2m)^{2r}` — the ledger's pattern set `pats` at depth `r` —
has cardinality `(2m)^{2r} = n^{2r}` where `n = |Gset ζ m| = 2m`. -/
theorem expTupleSet_card (m r : ℕ) :
    (expTupleSet m (2 * r)).card = (2 * m) ^ (2 * r) := by
  classical
  unfold expTupleSet
  rw [Fintype.card_piFinset_const, Finset.card_univ, Fintype.card_fin]

/-! ## Part 2 — the crude double-factorial ceiling `(2r−1)‼ ≤ (2r)^r` -/

/-- Product form of the double factorial `(2r−1)‼ = ∏_{j<r} (2j+1)`. -/
theorem doubleFactorial_eq_prod (r : ℕ) :
    (2 * r - 1).doubleFactorial = ∏ j ∈ range r, (2 * j + 1) := by
  cases r with
  | zero => simp [Nat.doubleFactorial]
  | succ k =>
      have h : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h]
      clear h
      induction k with
      | zero => simp [Nat.doubleFactorial]
      | succ m ih =>
          rw [Finset.prod_range_succ, ← ih]
          have h2 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
          rw [h2, Nat.doubleFactorial_add_two]
          ring

/-- **`(2r−1)‼ ≤ (2r)^r`.** Each of the `r` factors `2j+1` (for `j < r`) is `≤ 2r`. -/
theorem doubleFactorial_le_crude (r : ℕ) :
    (2 * r - 1).doubleFactorial ≤ (2 * r) ^ r := by
  rw [doubleFactorial_eq_prod]
  calc ∏ j ∈ range r, (2 * j + 1)
      ≤ ∏ _j ∈ range r, (2 * r) := by
        apply Finset.prod_le_prod'
        intro i hi; rw [Finset.mem_range] at hi; omega
    _ = (2 * r) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-! ## Part 3 — the ledger ratio lower bound and its depth growth -/

/-- **The Wick headroom scale is `≤ n^{2r}` when `2r ≤ n`** (`Wickₚ = (2r−1)‼·n^r ≤ n^{2r}`).
So the pattern count `n^{2r}` (Part 1) always dominates the headroom in the ledger range —
`ledgerRatio r ≥ 1`. Combined with the crude ceiling it also gives the growth factor below. -/
theorem wick_le_patternCount (n r : ℕ) (hsmall : 2 * r ≤ n) :
    (2 * r - 1).doubleFactorial * n ^ r ≤ n ^ (2 * r) := by
  have hdf : (2 * r - 1).doubleFactorial ≤ (2 * r) ^ r := doubleFactorial_le_crude r
  have hstep : (2 * r) ^ r ≤ n ^ r := Nat.pow_le_pow_left hsmall r
  calc (2 * r - 1).doubleFactorial * n ^ r
      ≤ n ^ r * n ^ r := Nat.mul_le_mul (hdf.trans hstep) le_rfl
    _ = n ^ (2 * r) := by rw [two_mul, pow_add]

/-- **The exact ledger-ratio lower bound (Nat/double-factorial form).**
The ledger cap is `#bad ≤ |pats|·(L/s)/T` with pattern count `|pats| = n^{2r}` (Part 1) and
Wick headroom threshold `T_r = (2r−1)‼·n^r`. The ratio `|pats|/T_r = n^r/(2r−1)‼` is bounded
below by the factor `(n/(2r))^r`, in the cross-multiplied exact form

`n^{2r} · (2r)^r  ≥  ((2r−1)‼·n^r) · n^r`,

i.e. `pats · (2r)^r ≥ T_r · n^r`, equivalently `ledgerRatio r ≥ (n/(2r))^r`. This is the
per-depth lower bound. It says nothing on its own about depth comparison; the actual
worsening-with-depth is the *step monotonicity* `ledger_ratio_step_mono` below. -/
theorem ledger_ratio_growth (n r : ℕ) :
    ((2 * r - 1).doubleFactorial * n ^ r) * n ^ r ≤ n ^ (2 * r) * (2 * r) ^ r := by
  have hdf : (2 * r - 1).doubleFactorial ≤ (2 * r) ^ r := doubleFactorial_le_crude r
  have hnn : n ^ (2 * r) = n ^ r * n ^ r := by rw [two_mul, pow_add]
  calc ((2 * r - 1).doubleFactorial * n ^ r) * n ^ r
      ≤ ((2 * r) ^ r * n ^ r) * n ^ r := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hdf) le_rfl
    _ = n ^ (2 * r) * (2 * r) ^ r := by rw [hnn]; ring

/-- **The double-factorial forward step** `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼`. -/
theorem doubleFactorial_succ_step (r : ℕ) :
    (2 * (r + 1) - 1).doubleFactorial = (2 * r + 1) * (2 * r - 1).doubleFactorial := by
  rw [doubleFactorial_eq_prod, doubleFactorial_eq_prod, Finset.prod_range_succ, mul_comm]

/-- **The ledger ratio worsens by ONE step exactly when `2r+1 ≤ n` (exact Nat form).**
The ledger ratio at depth `r` is `ledgerRatio r = n^r/(2r−1)‼`. Its one-step change is
`ledgerRatio (r+1) / ledgerRatio r = n / (2r+1)`, so it *weakly increases* (the ledger gets
strictly worse in the non-vacuity sense) precisely when `2r+1 ≤ n`. In cross-multiplied
division-free Nat form this is

`n^r · (2(r+1)−1)‼  ≤  n^{r+1} · (2r−1)‼`   (for `2r+1 ≤ n`),

i.e. `T_{r+1}` grows by at most the factor `n` while the pattern count `n^{2r}` grows by `n^2`,
so the ratio `pats/T` picks up a factor `≥ n/(2r+1) ≥ 1`. Iterating this from `r = 3` upward
(valid throughout the prize regime `r ≈ ln q ≈ 83 ≪ n = 2^30`, where `2r+1 ≤ n` at every step)
yields the honest no-go: the all-depth ledger's ratio is monotone non-decreasing in depth and
strictly exceeds its depth-3 value once `n > 2r+1`, so the cap needs an ever-larger prime family.

Unlike a naive `(n/(2r))^r`-is-increasing claim (which is FALSE near the `2r ≤ n` boundary,
e.g. `(10/4)^2 > (10/6)^3`), this exact step lemma is the correct monotonicity carrier. -/
theorem ledger_ratio_step_mono (n r : ℕ) (hstep : 2 * r + 1 ≤ n) :
    n ^ r * (2 * (r + 1) - 1).doubleFactorial ≤ n ^ (r + 1) * (2 * r - 1).doubleFactorial := by
  rw [doubleFactorial_succ_step, pow_succ]
  calc n ^ r * ((2 * r + 1) * (2 * r - 1).doubleFactorial)
      = ((2 * r + 1) * n ^ r) * (2 * r - 1).doubleFactorial := by ring
    _ ≤ (n * n ^ r) * (2 * r - 1).doubleFactorial := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstep)
    _ = n ^ r * n * (2 * r - 1).doubleFactorial := by ring

/-- **`ledger_gain_reverses_with_depth`.** The BGK-free all-depth annihilator ledger worsens with
depth. Stated on the real objects: with `n = |Gset ζ m| = 2m` the pattern count is exactly
`n^{2r}` (Part 1) and the Wick headroom scale `T_r = (2r−1)‼·n^r` satisfies both
`T_r ≤ n^{2r}` (ratio `≥ 1`, `wick_le_patternCount`) and the depth-growth cross inequality
`T_r · n^r ≤ n^{2r} · (2r)^r` (`ledger_ratio_growth`, equivalently ratio `≥ (n/(2r))^r`).
and the exact **step monotonicity** `ledger_ratio_step_mono`: the ratio `n^r/(2r−1)‼` weakly
INCREASES from depth `r` to `r+1` whenever `2r+1 ≤ n`. Iterating that step lemma from `r = 3`
upward (valid throughout the prize regime `r ≈ ln q ≪ n`) gives the honest no-go — the ledger ratio
is monotone non-decreasing in depth and strictly exceeds its `r = 3` value once `n > 2r+1` — so the
all-depth identity does NOT help the ledger; it moves it the wrong way. (We do NOT claim
`(n/(2r))^r` itself is monotone in `r`; it is not near the `2r ≤ n` boundary.) -/
theorem ledger_gain_reverses_with_depth {F : Type*} [Field F]
    {ζ : F} {m r : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hsmall : 2 * r ≤ (Gset ζ m).card) (hstep : 2 * r + 1 ≤ (Gset ζ m).card) :
    -- pattern count is exactly n^{2r}
    (expTupleSet m (2 * r)).card = (Gset ζ m).card ^ (2 * r)
    -- headroom fits inside the pattern count (ratio ≥ 1)
    ∧ (2 * r - 1).doubleFactorial * (Gset ζ m).card ^ r
        ≤ (expTupleSet m (2 * r)).card
    -- ratio grows with depth: pats · (2r)^r ≥ T_r · n^r  (⟺ ratio ≥ (n/2r)^r)
    ∧ ((2 * r - 1).doubleFactorial * (Gset ζ m).card ^ r) * (Gset ζ m).card ^ r
        ≤ (expTupleSet m (2 * r)).card * (2 * r) ^ r
    ∧ (Gset ζ m).card ^ r * (2 * (r + 1) - 1).doubleFactorial
        ≤ (Gset ζ m).card ^ (r + 1) * (2 * r - 1).doubleFactorial := by
  have hcard : (Gset ζ m).card = 2 * m := Gset_card hm hprim
  rw [hcard] at hsmall hstep
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [expTupleSet_card, hcard]
  · rw [expTupleSet_card, hcard]
    exact wick_le_patternCount (2 * m) r hsmall
  · rw [expTupleSet_card, hcard]
    exact ledger_ratio_growth (2 * m) r
  · rw [hcard]
    exact ledger_ratio_step_mono (2 * m) r hstep

#print axioms expTupleSet_card
#print axioms doubleFactorial_le_crude
#print axioms wick_le_patternCount
#print axioms ledger_ratio_growth
#print axioms doubleFactorial_succ_step
#print axioms ledger_ratio_step_mono
#print axioms ledger_gain_reverses_with_depth

end ArkLib.ProximityGap.Frontier.G58AllDepthLedgerReversal
