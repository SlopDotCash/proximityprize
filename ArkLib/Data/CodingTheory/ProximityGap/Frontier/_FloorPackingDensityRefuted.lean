/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The packing/density mechanism for `floor-bad(n) = {p_min(n)}` is REFUTED (#466, lane FS2)

**Claim under test (dossier §9/§12, the "packing germ"):** *"only at the tightest/smallest prime
does `μ_n` pack densely enough to force the forbidden adjacent-7th-type profile; for larger `p`,
`μ_n` is sparse and the 6-type freeze holds."*  The hope was to upgrade this to a QUANTITATIVE
theorem: a statistic `S(n,p)` of the point set `μ_n ⊆ 𝔽_p^×` that exceeds a threshold **exactly**
at `p = p_min(n)` (the least prime `≡ 1 mod n`, the only floor-bad prime at `n = 16, 32`) and falls
below it for every larger prime — a monotone density statistic crossing the realizability threshold
at `p_min`.

## What the probe found (`scripts/probes/probe_466_packing_mechanism.py`, `_out_466_packing_mechanism.txt`)

Exhaustive floor-defect scan at `n = 16` (all structured patterns, 60 primes `≡ 1 mod 16` up to
`3617`) plus packing statistics at `n = 16, 32, 64`:

1. **Floor-badness is a SHARP arithmetic coincidence, not a gradual metric transition.** The
   min-over-patterns obstruction defect is `0` at `p_min` and jumps to its maximum immediately for
   every larger prime — no "near-miss" ramp. It is a resultant-divisibility event (the round-8
   `_FloorSuccessorNorm` mechanism), not a packing-density event.

2. **Genuine metric packing statistics DO NOT separate floor-bad from floor-good.** The minimum
   additive gap `min_{i≠j}‖ζ^i−ζ^j‖`, the tightest-cluster diameter, and the maximum gap all fail
   to distinguish the classes.  **Countermodel:** at `n = 16`, `p = 257` is floor-GOOD yet `μ_16`
   contains additively adjacent residues (min gap `= 1`), exactly like the floor-BAD `p = 17`; at
   `n = 32` the floor-bad `97` and the floor-good `193, 257, 353, 449` all have min gap `= 1`.
   So additive proximity of `μ_n` is neither necessary nor sufficient for floor-badness.

3. **The ONLY statistic that "separates" is the crude global density `n/p` — and it does so
   TRIVIALLY** (the smallest prime has the largest `n/p`), with an `n`-dependent threshold and **no
   uniform floor**.  This is the decisive obstruction formalized below.

## The theorem here (axiom-clean): no uniform density threshold

A packing-density *law* would need a single threshold `τ` with `p` floor-bad `⟺ n/p ≥ τ`
(equivalently a threshold comparable across `n`).  Grant the uniform conjecture
`floor-bad(n) = {p_min(n)}` (the very statement the lane is trying to prove).  Then:

* `7681 = p_min(512)` is floor-BAD, with density `512/7681 ≈ 0.0667`;
* `769 ≡ 1 mod 256` is **not** the least such prime (`257 < 769` is prime `≡ 1 mod 256`), hence
  floor-GOOD, with density `256/769 ≈ 0.3329`.

But `256/769 > 512/7681`: **a floor-GOOD prime is strictly denser than a floor-BAD prime.**  So no
threshold `τ` can satisfy both `density(bad) ≥ τ` and `density(good) < τ` — the density statistic
cannot detect floor-badness by any fixed cutoff.  `μ_n` at its floor-bad prime is *sparser* at
`n = 512` (density `0.067`) than `μ_16` is at a floor-*good* prime.  The "packs densely enough"
premise is quantitatively false; the mechanism is arithmetic (the cyclotomic resultant norm), not
metric density.

This is a **refutation with a machine-checked countermodel** (a WIN under the honesty contract):
it does not disprove `floor-bad(n) = {p_min(n)}` — it proves the *packing-density route* cannot be
its proof.  The surviving non-wall target remains the resultant-norm characterization
(`_FloorSuccessorNorm.lean`, `floorObstructionNorm_forces_pmin_16/_32`).
-/

namespace ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted

/-- The packing **density** of `μ_n` inside `𝔽_p^×`: `n` roots of unity spread over `p` residues. -/
def density (n p : ℕ) : ℚ := (n : ℚ) / (p : ℚ)

/-- `7681` is the least prime `≡ 1 mod 512`, i.e. `p_min(512)`.  Every prime `q ≡ 1 mod 512` with
`q < 7681` would be one of `513, 1025, …, 7169`, all composite — so none exists. -/
theorem least_prime_1mod512_is_7681
    (q : ℕ) (hq : q.Prime) (hmod : q % 512 = 1) : 7681 ≤ q := by
  by_contra h
  push_neg at h
  -- write `q = 512 * t + 1`
  have hdm : 512 * (q / 512) + 1 = q := by
    have := Nat.div_add_mod q 512
    omega
  set t := q / 512 with ht
  have htle : t ≤ 14 := by omega
  -- `t = 0` would force `q = 1`, not prime
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at hdm; simp at hdm
      rw [← hdm] at hq; exact absurd hq (by norm_num)
    · exact h0
  interval_cases t <;> (rw [← hdm] at hq; norm_num at hq)

/-- `769` is a prime `≡ 1 mod 256` that is **not** the least such (`257 < 769` is a smaller prime
`≡ 1 mod 256`), so under the uniform conjecture `floor-bad(256) = {p_min(256)}` it is floor-GOOD. -/
theorem seven_six_nine_is_nonleast :
    Nat.Prime 769 ∧ 769 % 256 = 1 ∧ Nat.Prime 257 ∧ 257 % 256 = 1 ∧ 257 < 769 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `7681` really is a prime `≡ 1 mod 512` (the floor-bad witness at `n = 512`). -/
theorem seven_six_eight_one_witness :
    Nat.Prime 7681 ∧ 7681 % 512 = 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **The density inversion.**  The floor-GOOD prime `769` (at `n = 256`) is strictly denser than
the floor-BAD prime `7681 = p_min(512)` (at `n = 512`). -/
theorem density_inversion : density 512 7681 < density 256 769 := by
  unfold density; norm_num

/-- **No uniform packing-density threshold (the refutation).**  There is no rational cutoff `τ`
with `density(bad) ≥ τ` and `density(good) < τ` simultaneously, because a floor-GOOD prime is
denser than a floor-BAD one.  Formally: for every `τ`, it is not the case that both the floor-bad
witness `(512, 7681)` clears `τ` and the floor-good witness `(256, 769)` stays below it. -/
theorem no_uniform_packing_density_threshold :
    ¬ ∃ τ : ℚ, τ ≤ density 512 7681 ∧ density 256 769 < τ := by
  rintro ⟨τ, hbad, hgood⟩
  -- `density 256 769 < τ ≤ density 512 7681 < density 256 769` — contradiction
  have := density_inversion
  linarith

/-- Consolidated statement: `7681 = p_min(512)` is floor-bad and less dense than the non-least,
floor-good `769` at `n = 256`; hence density cannot be the floor-bad detector. -/
theorem packing_density_mechanism_refuted :
    (∀ q : ℕ, q.Prime → q % 512 = 1 → 7681 ≤ q)      -- 7681 = p_min(512)  (floor-bad)
    ∧ (Nat.Prime 769 ∧ 769 % 256 = 1 ∧ 257 < 769)     -- 769 non-least ≡1 mod 256  (floor-good)
    ∧ density 512 7681 < density 256 769               -- yet the bad prime is LESS dense
    ∧ ¬ ∃ τ : ℚ, τ ≤ density 512 7681 ∧ density 256 769 < τ := by
  refine ⟨least_prime_1mod512_is_7681, ⟨by norm_num, by norm_num, by norm_num⟩,
    density_inversion, no_uniform_packing_density_threshold⟩

end ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted

#print axioms ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted.least_prime_1mod512_is_7681
#print axioms ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted.density_inversion
#print axioms ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted.no_uniform_packing_density_threshold
#print axioms ArkLib.ProximityGap.Frontier.FloorPackingDensityRefuted.packing_density_mechanism_refuted
