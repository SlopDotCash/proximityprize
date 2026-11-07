/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# height-gate-threshold: the ceiling of LEVER H under a conjectured norm proxy (#407)

**Audit status (2026-10-28).**  Everything formal in this file is arithmetic about the *defined
proxy* `worstNorm n = (n/2 − 1)^{n/4}` and the *lower* prime scale `prizeP n = n·2^128`.  No
cyclotomic field, subset, resultant, or actual norm is constructed.  The claims below that the
proxy "is" the realized maximum of non-antipodal subset norms, and that the threshold is
therefore *intrinsic* for all `n`, are **not proved** and are **false as an exact formula**: at
`n = 4`, `S = {0, 1}` is non-antipodal and `N_{ℚ(i)/ℚ}(1 + i) = 2 > 1 = worstNorm 4`
(`worstNorm_not_max_at_four`).  The probe table is finite-`n` evidence with only approximate
agreement (e.g. `n = 32`); it does not establish an all-scale maximum or bit-growth law.  And
since `prizeP` is the *lower* end of the allowed prime range, `prizeP n < worstNorm n` does not
show the proxy exceeds every allowed (larger) prime.  Read the sections below as the original
proxy analysis, with these qualifications.

## What this file decides

LEVER H (the structure-aware norm / height gate) closes the low-exponent direction of the prize
iff, for every non-antipodal `S ⊆ range(n)` (`n = 2^a`), the algebraic-integer norm of the
root-sum stays below the prize prime:

    `|N_{ℚ(ζ_n)/ℚ}(∑_{i∈S} ζ^i)| ≤ p`,   `p ~ n · 2^128`   (prize: `n = 2^30`, `p ~ 2^158`).

This file answers the **threshold-analysis** question precisely and quantitatively:

> *With the BEST POSSIBLE structure-aware norm bound, what is the largest `n` for which the gate
> `|N| ≤ p` is provable for all non-antipodal `S`, at the prize scale?*

**Answer for the proxy (proved here as arithmetic only):** `worstNorm 64 < prizeP 64` and
`prizeP (2^a) < worstNorm (2^a)` for `a ≥ 7`.  *If* `worstNorm` were a valid upper bound for all
non-antipodal subset norms, the gate would close at `n = 64` (for every prime `p ≥ prizeP 64`);
*if* it were also attained (it is not exactly — see the audit status), no bound could close the
gate at `n = 128` against the lower prime scale `prizeP 128`.  Neither premise is proved here, so
the original claim "information-theoretically impossible for `n ≥ 128`, regardless of proof
technique" is an unproved conjecture, not a result of this file.

## Why the threshold was believed intrinsic (heuristic; not proved)

Write `Σ_S(x) = ∑_{i∈S} x^i` (the 0/1 polynomial of `S`).  Since the `φ(n) = n/2` Galois
conjugates `σ_t : ζ ↦ ζ^t` (`t` odd) run over exactly the *primitive* `n`-th roots,

    `|N(Σ_S)| = ∏_{w primitive n-th root} |Σ_S(w)| = |Res(Σ_S, Φ_n)|`.

The crude **house** bound `|N| ≤ (#S)^{φ(n)} = (#S)^{n/2}` (in tree:
`HeightGateNormBound.abs_norm_sum_rootsOfUnity_le`) over-counts each factor as `#S` instead of its
true typical size `√(#S)`.  The conjectured-tight form `(n/2−1)^{n/4}` accounts for this
square-root cancellation (each `|Σ_S(w)| ≈ √(#S)` by Parseval: `(1/n)∑_j |Σ_S(ζ^j)|² = #S`).

Finite probe evidence (exact brute force / heavy local search over non-antipodal `S`, run from a
scratch `/tmp` probe that is not checked in) measured the realized worst-case `log₂|N|` at a few
`n`; agreement with the proxy is approximate, and the formula fails exactly at `n = 4`:

| `n`  | realized max `log₂|N|` | `log₂(n/2−1)^{n/4}` | ratio | `log₂ p = a+128` | gate? |
|------|------------------------|---------------------|-------|------------------|-------|
| 8    | 3.17                   | 3.17                | 1.000 | 131              | YES   |
| 16   | 11.23                  | 11.23               | 1.000 | 132              | YES   |
| 32   | 31.1                   | 31.3                | 0.99  | 133              | YES   |
| 64   | 79.3                   | 79.3                | 1.00  | 134              | YES   |
| 128  | 158 (random) → 191 max | 191.3               | —     | 135              | **NO**|

The original text concluded that the realized worst-case norm **equals** `(n/2−1)^{n/4}` and
hence that every valid upper bound `B(n)` satisfies `B(n) ≥ (n/2−1)^{n/4}`.  That inference needs
an actual witness subset with norm at least the proxy at every relevant `n`; the table gives
approximate agreement at five values of `n` only, and the exact formula is false at `n = 4`.
Any genuine lower bound on `max_S |N(Σ_S)|` (which *would* bound every method) must come from
explicit witnesses and actual norm computations, which this file does not supply.

## The proxy threshold, quantitatively

`worst(n) := (n/2−1)^{n/4}` and the lower prime scale `p(n) = n·2^128` (`log₂ p = a + 128`):

* `worst(64) = 31^16 = 727423121747185263828481` (80 bits) `< 2^134 ≤ p`
  → **proxy below every allowed prime, margin +54.7 bits**
* `worst(128) = 63^32` (192 bits) `> 2^135 = prizeP 128`
  → **proxy above the lower prime scale, margin −56.3 bits** (an allowed larger prime may
  still exceed it; this compares against `prizeP` only)

Solving `worst(n) = p(n)` continuously gives crossover `n* ≈ 96.7`, so the largest power of two
below it is `64`.  At the actual prize `n = 2^30`, `log₂ worst ≈ (n/4)·log₂(n/2) ≈ 7.8·10⁹ bits`,
versus `log₂ p = 158` — a gap of **~7.8 billion bits**.

## Verdict for LEVER H (conditional on the proxy)

*If* the conjectured-tight proxy were a proved upper bound, LEVER H would close the gate up to
`n = 64` at `ε* = 2^−128`, extending the proved-closed bracket from `n ≤ 32` (crude house) to
`n ≤ 64`.  The heuristic that it cannot go further — the worst-case norm growing like
`Θ(n log n)` bits while the prize prime grows like `Θ(log n)` bits — rests on the unproved
proxy-attainment interpretation and on comparing with the lower prime scale only.  It is offered as
evidence that LEVER H is unlikely to reach the prize `n = 2^30`, and that the thin regime is
better addressed by LEVER B/X (thinness-essential BGK); it is not a proof of impossibility.

## What is PROVED here (axiom-clean, pure arithmetic about the proxy)

* `worstNorm` / `prizeP` : the conjectured proxy `(n/2−1)^{n/4}` and the lower prime scale
  `n·2^128` (`log` scale `a+128`).
* `gate_closes_at_64` : `worstNorm 64 < prizeP 64`.
* `gate_fails_at_128`  : `prizeP 128 < worstNorm 128`.
* `gate_fails_above_128` : `prizeP (2^a) < worstNorm (2^a)` for every `a ≥ 7`.
* `house_strictly_worse_than_conj_at_64` : the crude house bound `64^32` already exceeds `2^135`,
  so the `n ≤ 32 → n ≤ 64` improvement would genuinely *need* the square-root-cancellation form.
* `worstNorm_not_max_at_four` : the proxy is *not* the realized maximum at `n = 4`
  (`worstNorm 4 = 1`, while the non-antipodal `S = {0, 1}` has Gaussian-integer norm
  `N(1 + i) = 2`).

The claimed deep fact (`realized max = (n/2−1)^{n/4}`) is neither formalized nor exactly true; a
genuine intrinsic threshold would need actual witness subsets with proved norm lower bounds at
every relevant `n`, compared against every allowed prime, not just `prizeP`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.HeightGateThreshold

/-! ## The two scales, on the integer (norm-value) axis -/

/-- The **conjectured norm proxy** `(n/2 − 1)^{n/4}` for the worst-case height
`max_{S non-antipodal} |N(∑_{i∈S} ζ^i)|` at `n = 2^a`.  This is only a proxy: finite probes show
approximate agreement at a few `n`, but it is *not* the exact realized maximum
(`worstNorm_not_max_at_four`), and no theorem here makes it a lower bound on valid norm bounds. -/
def worstNorm (n : ℕ) : ℕ := (n / 2 - 1) ^ (n / 4)

/-- The **prize prime lower scale** `p ~ n · 2^128` (`ε* = 2^−128`, `q = n·2^128`).  The gate needs
`worstNorm n ≤ p`; we use the conservative lower end `p ≥ n · 2^128`.  Because this is the *lower*
end, `worstNorm n ≤ prizeP n` implies the gate for every allowed prime, but
`prizeP n < worstNorm n` does **not** show failure against every allowed (larger) prime. -/
def prizeP (n : ℕ) : ℕ := n * 2 ^ 128

/-- **The proxy is not the realized maximum (already at `n = 4`).**  For `n = 4`, `ζ = i`, the
subset `S = {0, 1} ⊆ range 4` is non-antipodal and its root sum is `1 + i`, whose norm
`N_{ℚ(i)/ℚ}(1 + i)` equals the Gaussian-integer norm `Zsqrtd.norm (1 + i) = 2`; yet
`worstNorm 4 = 1`.  So `worstNorm` is not an exact formula for the worst-case norm. -/
theorem worstNorm_not_max_at_four :
    worstNorm 4 = 1 ∧ Zsqrtd.norm (⟨1, 1⟩ : GaussianInt) = 2 ∧
      (worstNorm 4 : ℤ) < Zsqrtd.norm (⟨1, 1⟩ : GaussianInt) := by
  refine ⟨by decide, by norm_num [Zsqrtd.norm_def], ?_⟩
  norm_num [Zsqrtd.norm_def, worstNorm]

/-! ## The hard threshold: closes at 64, fails at 128 -/

/-- **The proxy is below the prize prime at `n = 64`.**  The proxy `worstNorm 64 = 31^16 ≈ 2^79.3`
is below the lower prime scale `64·2^128 = 2^134` (margin `+54.7` bits), hence below every allowed
prime.  The gate would close at `n = 64` *if* the conjectured-tight proxy were a proved upper bound
on all non-antipodal subset norms; that is not proved here. -/
theorem gate_closes_at_64 : worstNorm 64 < prizeP 64 := by
  unfold worstNorm prizeP
  norm_num

/-- **The proxy exceeds the lower prime scale at `n = 128`.**  The proxy `worstNorm 128 = 63^32 ≈
2^191.3` exceeds `prizeP 128 = 128·2^128 = 2^135` (margin `−56.3` bits).  This shows only that the
proxy cannot certify the gate against the lower prime scale; it does not show that no valid bound
can (the proxy is not proved to be attained) nor that it exceeds every allowed larger prime. -/
theorem gate_fails_at_128 : prizeP 128 < worstNorm 128 := by
  unfold worstNorm prizeP
  norm_num

/-- **The proxy exceeds the lower prime scale for every `n = 2^a` with `a ≥ 7`** (`n ≥ 128`).
The proxy grows like `Θ(n log n)` bits while `log₂ prizeP = a + 128` grows linearly in `a`.
Concretely: `worstNorm (2^a) = (2^{a-1}-1)^{2^{a-2}}`, whose bit-length `≈ 2^{a-2}·(a-1)` dominates
`a + 128` for all `a ≥ 7`.  This is a statement about the proxy versus the lower prime scale
only (see `gate_fails_at_128`). -/
theorem gate_fails_above_128 {a : ℕ} (ha : 7 ≤ a) : prizeP (2 ^ a) < worstNorm (2 ^ a) := by
  -- It suffices to compare exponents/bit-lengths; we give the bound via a clean chain anchored at
  -- the proven `gate_fails_at_128` and the super-exponential growth of `worstNorm`.
  -- worstNorm (2^a) = (2^(a-1) - 1)^(2^(a-2)) ≥ (2^(a-1) - 1)^(2^(a-2)).
  -- prizeP (2^a) = 2^a · 2^128 = 2^(a+128).
  -- For a ≥ 7: 2^(a-1) - 1 ≥ 2^6 - 1 = 63 ≥ 2^5, and 2^(a-2) ≥ 2^5 = 32, so
  --   worstNorm ≥ (2^5)^(2^(a-2)) = 2^(5·2^(a-2)) ≥ 2^(5·32) = 2^160 > 2^(a+128) for moderate a,
  -- and grows strictly faster. We prove it by the explicit two-step bound.
  have hbase : (32 : ℕ) ≤ 2 ^ (a - 1) - 1 := by
    have : (2 : ℕ) ^ 6 ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- Key growth fact: `m + 27 ≤ 2^m` for all `m ≥ 5` (clean `Nat.le_induction`).
  have hgrow : ∀ m : ℕ, 5 ≤ m → m + 27 ≤ 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ b hb ih =>
      have h2 : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
      have hps : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [pow_succ]; omega
      omega
  -- Hence `5 · 2^(a-2) ≥ a + 128` for `a ≥ 7` (so `a - 2 ≥ 5`).
  have hexp : a + 128 < (5 : ℕ) * 2 ^ (a - 2) := by
    have hge : (a - 2) + 27 ≤ 2 ^ (a - 2) := hgrow (a - 2) (by omega)
    have hmul : 5 * ((a - 2) + 27) ≤ 5 * 2 ^ (a - 2) := Nat.mul_le_mul_left 5 hge
    omega
  calc prizeP (2 ^ a) = 2 ^ (a + 128) := by
            unfold prizeP; rw [pow_add]
        _ < 2 ^ (5 * 2 ^ (a - 2)) := Nat.pow_lt_pow_right (by norm_num) hexp
        _ = (2 ^ 5) ^ (2 ^ (a - 2)) := by rw [pow_mul]
        _ = (32 : ℕ) ^ (2 ^ (a - 2)) := by norm_num
        _ ≤ (2 ^ (a - 1) - 1) ^ (2 ^ (a - 2)) := Nat.pow_le_pow_left hbase _
        _ = worstNorm (2 ^ a) := by
            unfold worstNorm
            have hd2 : 2 ^ a / 2 = 2 ^ (a - 1) := by
              conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
              rw [Nat.mul_div_cancel _ (by norm_num)]
            have hd4 : 2 ^ a / 4 = 2 ^ (a - 2) := by
              conv_lhs => rw [show a = (a - 2) + 2 by omega, pow_add]
              rw [show (2:ℕ) ^ 2 = 4 by norm_num, Nat.mul_div_cancel _ (by norm_num)]
            rw [hd2, hd4]

/-! ## Why the improvement to 64 genuinely needs the square-root cancellation -/

/-- **The crude house bound is strictly worse and does NOT reach `n = 64`.**  The house estimate
`(#S)^{φ(n)} = 64^32 ≈ 2^192` already exceeds the prize prime `64·2^128 = 2^134`, so the
`n ≤ 32 → n ≤ 64` extension requires the conjectured-tight (square-root-cancellation) form, not the
generic house bound.  (This is the precise content of the `n ≤ 32` ceiling of
`HeightGateNormBound.houseGate_card_le_32_degree16_lt_twoPow128` and why `64` needs more.) -/
theorem house_strictly_worse_than_conj_at_64 :
    prizeP 64 < (64 : ℕ) ^ 32 ∧ worstNorm 64 < prizeP 64 := by
  refine ⟨?_, gate_closes_at_64⟩
  unfold prizeP
  norm_num

/-- **Proxy dichotomy at `64` / `128`.**  Packaged: the proxy is below the prime scale at `n = 64`
and above the lower prime scale at `n = 128`.  (The name records the original reading "LEVER H's
ceiling is 64"; that reading is conditional on the unproved proxy interpretation and on comparing
with the lower prime scale only.) -/
theorem leverH_ceiling_is_64 :
    worstNorm 64 < prizeP 64 ∧ prizeP 128 < worstNorm 128 :=
  ⟨gate_closes_at_64, gate_fails_at_128⟩

end ArkLib.ProximityGap.HeightGateThreshold

#print axioms ArkLib.ProximityGap.HeightGateThreshold.gate_closes_at_64
#print axioms ArkLib.ProximityGap.HeightGateThreshold.gate_fails_at_128
#print axioms ArkLib.ProximityGap.HeightGateThreshold.gate_fails_above_128
#print axioms ArkLib.ProximityGap.HeightGateThreshold.house_strictly_worse_than_conj_at_64
#print axioms ArkLib.ProximityGap.HeightGateThreshold.leverH_ceiling_is_64
#print axioms ArkLib.ProximityGap.HeightGateThreshold.worstNorm_not_max_at_four
