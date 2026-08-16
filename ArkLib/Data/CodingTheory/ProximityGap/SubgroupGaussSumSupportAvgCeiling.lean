/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSpectralSpread
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The spectral-support AVERAGE squared-period ceiling for the thin `μ_n` (#444)

The **typical-magnitude ceiling**: the dual upper companion of the proven Parseval *floor*
(`GaussPeriodParsevalFloor.exists_eta_sq_ge_parseval_floor`, which gives `M(n) ≥ √n` — the
Alon–Boppana lower half).  Here we bound the *average* squared period over the spectral support
from above by composing two **exact-moment** facts already landed for the thin `2`-power subgroup
`μ_n ⊂ F_p` (`n = 2^m`, `m ≥ 1`, `p > 2^n`):

* `subgroup_gaussSum_secondMoment` : the total `L²` mass is `∑_b ‖η_b‖² = q·n`, and
* `SubgroupGaussSumSpectralSpread.card_support_muN_mul_ge` : the support obeys
  `N₊ · q·(3n²−3n) ≥ (q·n)²`, i.e. `N₊ ≥ q·n / (3(n−1))`.

Combining, the **average squared period over the support** satisfies

> **`avg_eta_sq_on_support_le`** —
>   `(∑_b ‖η_b‖²) ≤ 3(n−1) · N₊`,  equivalently  `(∑_b ‖η_b‖²)/N₊ = q·n/N₊ ≤ 3(n−1) ≈ 3n`.

So the *typical* frequency on the support has `‖η_b‖ ≲ √(3n)` — the `√n` *prize scale on average*.

## Honest scope (rules 1, 3, 6) — this is an AVERAGE ceiling, NOT the worst-case sup

This bounds the **average / typical** magnitude over the support, NOT the worst-case
`M(n) = max_{b≠0} ‖η_b‖`.  The probe (`scripts/probes/probe_support_avg_typical_floor.py`, PROPER thin
`μ_n`, `p ≫ n³`, two primes per `n`, never `n = q−1`) confirms the average is `≈ n` (well under the
`3(n−1)` ceiling) while the **worst-case** `M` is far larger (`≈ 7.6` at `n = 8` vs typical `≈ 2.8`,
`≈ 13` at `n = 16` vs `≈ 4`).  The gap between this proven *typical* ceiling and the *worst-case* sup
is **exactly the open BGK / Paley `√`-cancellation content**.  No capacity over-claim; CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.

## Thinness-essential (rule 3)

The ceiling uses the **exact** thin-subgroup energy `3n²−3n` (the Sidon-mod-negation value).  For a
thick subgroup with `E ≫ 3n²` the same composition gives only `avg ≤ E/n ≫ 3n` — no `√n`-scale
typical ceiling.  The `≈ 3n` average ceiling is the thin-subgroup Sidon phenomenon.

See `SubgroupGaussSumSpectralSpread.lean` (the support lower bound) and
`GaussPeriodParsevalFloor.lean` (the matching `√n` floor — the lower half of the spectral frame).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumSpectralSpread
open ArkLib.ProximityGap.GaussPeriodParsevalFloor

namespace ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- The spectral support `{b : η_b(μ_n) ≠ 0}`. -/
noncomputable def support (ψ : AddChar (ZMod p) ℂ) (n : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter (fun b : ZMod p => eta ψ (nthRootsFinset n (1 : ZMod p)) b ≠ 0)

/-- **The spectral-support average-squared-period ceiling (multiplied form).**
For the thin `μ_n` (`n = 2^m`, `m ≥ 1`, `p > 2^n`), the total `L²` mass is at most `3(n−1)` times
the support size:

  `∑_b ‖η_b‖² ≤ 3(n−1) · N₊`,  `N₊ = #{b : η_b ≠ 0}`.

Proof: the total mass equals `q·n` (`subgroup_gaussSum_secondMoment`), and the support obeys
`N₊·q·(3n²−3n) ≥ (q·n)²` (`card_support_muN_mul_ge`); divide the latter by `q·n > 0` to get
`N₊·(3n−3) ≥ q·n = ∑_b ‖η_b‖²`. -/
theorem sum_eta_sq_le_mul_support (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn2le : 2 ≤ n) :
    ∑ b : ZMod p, ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2
      ≤ 3 * ((n : ℝ) - 1) * ((support ψ n).card : ℝ) := by
  classical
  set G : Finset (ZMod p) := nthRootsFinset n (1 : ZMod p) with hGdef
  have hn0 : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hcard : G.card = n := hω.card_nthRootsFinset
  -- the exact second moment: total L² mass = q·n
  have hmom2 : ∑ b : ZMod p, ‖eta ψ G b‖ ^ 2 = (Fintype.card (ZMod p) : ℝ) * n := by
    rw [subgroup_gaussSum_secondMoment hψ G, hcard]
  -- the support lower bound (multiplied form): N₊ · q·(3n²−3n) ≥ (q·n)²
  have hspread := card_support_muN_mul_ge hn2 hm hp hω hψ
  -- positivity facts
  have hqpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2le
  have hnpos_r : (0 : ℝ) < (n : ℝ) := by linarith
  set N : ℝ := ((support ψ n).card : ℝ) with hNdef
  -- rewrite hspread's filter to our `support` def (definitionally equal)
  have hspread' : N * ((Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n))
      ≥ ((Fintype.card (ZMod p) : ℝ) * n) ^ 2 := by
    have : N = ((Finset.univ.filter
        (fun b : ZMod p => eta ψ (nthRootsFinset n (1 : ZMod p)) b ≠ 0)).card : ℝ) := by
      rw [hNdef]; rfl
    rw [this]; exact hspread
  -- factor 3n²−3n = n·(3(n−1)) = n·(3n−3)
  have hfac : 3 * (n : ℝ) ^ 2 - 3 * n = (n : ℝ) * (3 * ((n : ℝ) - 1)) := by ring
  -- from hspread' : N · q · n · (3(n−1)) ≥ q²·n², divide by q·n > 0 ⟹ N·(3(n−1)) ≥ q·n
  have hqn : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) * n := mul_pos hqpos hnpos_r
  have hstep : N * (3 * ((n : ℝ) - 1)) ≥ (Fintype.card (ZMod p) : ℝ) * n := by
    have hrw : N * ((Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n))
        = ((Fintype.card (ZMod p) : ℝ) * n) * (N * (3 * ((n : ℝ) - 1))) := by
      rw [hfac]; ring
    rw [hrw] at hspread'
    have hsq : ((Fintype.card (ZMod p) : ℝ) * n) ^ 2
        = ((Fintype.card (ZMod p) : ℝ) * n) * ((Fintype.card (ZMod p) : ℝ) * n) := by ring
    rw [hsq] at hspread'
    exact le_of_mul_le_mul_left hspread' hqn
  -- combine: ∑‖η‖² = q·n ≤ N·3(n−1)
  rw [hmom2]
  have : (Fintype.card (ZMod p) : ℝ) * n ≤ N * (3 * ((n : ℝ) - 1)) := hstep
  linarith [this]

/-- **The spectral-support average-squared-period ceiling (divided / averaged form).**
The average squared period over the support is at most `3(n−1) ≈ 3n`:

  `(∑_b ‖η_b‖²) / N₊ = q·n / N₊ ≤ 3(n−1)`.

So the *typical* frequency on the support has `‖η_b‖ ≲ √(3n)` — the `√n` prize scale on **average**.
The worst-case sup `M(n) = max_{b≠0}‖η_b‖` is genuinely larger (the open BGK content); this bounds
only the average, not the worst case. -/
theorem avg_eta_sq_on_support_le (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn2le : 2 ≤ n) (hsupp_pos : 0 < (support ψ n).card) :
    (∑ b : ZMod p, ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2) / ((support ψ n).card : ℝ)
      ≤ 3 * ((n : ℝ) - 1) := by
  have hNpos : (0 : ℝ) < ((support ψ n).card : ℝ) := by exact_mod_cast hsupp_pos
  rw [div_le_iff₀ hNpos]
  have hmul := sum_eta_sq_le_mul_support hn2 hm hp hω hψ hn2le
  linarith [hmul]

/-- **Typical magnitude form.** Some frequency on the support has squared period at most the
support average `3(n−1)`; equivalently, NOT every supported frequency exceeds `3(n−1)`.  (A clean
existence dual of the floor `exists_eta_sq_ge_parseval_floor`: the floor says *some* `b ≠ 0` is at
least `≈ n`; this says *some* supported `b` is at most `≈ 3n` — the support cannot be uniformly at
the worst-case scale.) -/
theorem exists_support_eta_sq_le (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn2le : 2 ≤ n) (hsupp_pos : 0 < (support ψ n).card) :
    ∃ b : ZMod p, b ∈ support ψ n ∧
      ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2 ≤ 3 * ((n : ℝ) - 1) := by
  classical
  set G : Finset (ZMod p) := nthRootsFinset n (1 : ZMod p) with hGdef
  set S : Finset (ZMod p) := support ψ n with hSdef
  have hSne : S.Nonempty := Finset.card_pos.mp hsupp_pos
  -- the support sum equals the universe sum (off the support η = 0)
  have hsum_eq : ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 = ∑ b : ZMod p, ‖eta ψ G b‖ ^ 2 := by
    rw [hSdef, support]
    refine (Finset.sum_filter_of_ne (fun b _ hfb => ?_))
    intro hzero
    apply hfb
    rw [hzero]; simp
  -- the multiplied ceiling
  have hmul := sum_eta_sq_le_mul_support hn2 hm hp hω hψ hn2le
  rw [← hsum_eq] at hmul
  -- so the support-average is ≤ 3(n−1); pigeonhole ⟹ some term ≤ 3(n−1)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ b ∈ S, 3 * ((n : ℝ) - 1) < ‖eta ψ G b‖ ^ 2 := by
    intro b hb; exact hcon b hb
  have hsumgt : ∑ b ∈ S, (3 * ((n : ℝ) - 1)) < ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hSne hlt
  rw [Finset.sum_const, nsmul_eq_mul] at hsumgt
  -- hsumgt : (#S)·3(n−1) < ∑_S ‖η‖²;  hmul : ∑_S ‖η‖² ≤ 3(n−1)·#S — contradiction
  have hcomm : ((S.card : ℝ)) * (3 * ((n : ℝ) - 1)) = 3 * ((n : ℝ) - 1) * (S.card : ℝ) := by ring
  rw [hcomm] at hsumgt
  linarith [hmul, hsumgt]

/-! ### The UNCONDITIONAL average two-sided frame -/

/-- **The average two-sided spectral frame for the thin `μ_n` — both sides UNCONDITIONAL.**
The thin-`μ_n` spectrum is pinned to the `√n` scale *on average* from both sides, with NO open
hypothesis:

* (floor, `GaussPeriodParsevalFloor`) **some** `b ≠ 0` has `‖η_b‖² ≥ (q·n − n²)/(q − 1) ≈ n`, and
* (ceiling, this file) the **average** squared period over the support is `≤ 3(n−1) ≈ 3n`.

Contrast with `GaussPeriodSpectralFrame.spectral_frame`, whose *ceiling* is the OPEN
near-Ramanujan-`√log` hypothesis on **every** frequency: there the worst-case ceiling is conditional;
here the *average* ceiling is **proven**.  So the typical/average behaviour is unconditionally
`√n`-scale on both sides; ALL remaining open content is the worst-case deviation above the typical
scale — exactly the BGK / Paley `√`-cancellation `M(n) ≤ C√(n·log(q/n))`. -/
theorem avg_spectral_frame (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn2le : 2 ≤ n) (hsupp_pos : 0 < (support ψ n).card)
    (hq : 2 ≤ Fintype.card (ZMod p)) :
    -- floor: some nonzero frequency realises the ≈ n Parseval scale
    (∃ b : ZMod p, b ≠ 0 ∧
      ((Fintype.card (ZMod p) : ℝ) * (nthRootsFinset n (1 : ZMod p)).card
          - ((nthRootsFinset n (1 : ZMod p)).card : ℝ) ^ 2) / ((Fintype.card (ZMod p) : ℝ) - 1)
        ≤ ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2)
    -- ceiling: the average squared period over the support is ≤ 3(n−1)
    ∧ (∑ b : ZMod p, ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2) / ((support ψ n).card : ℝ)
        ≤ 3 * ((n : ℝ) - 1) := by
  refine ⟨exists_eta_sq_ge_parseval_floor hψ (nthRootsFinset n (1 : ZMod p)) hq, ?_⟩
  exact avg_eta_sq_on_support_le hn2 hm hp hω hψ hn2le hsupp_pos

end ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling.sum_eta_sq_le_mul_support
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling.avg_eta_sq_on_support_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling.exists_support_eta_sq_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSupportAvgCeiling.avg_spectral_frame
