/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The antitone cross-excess decomposition: char-0 dominance vs the char-p correction (#444)

The prize reduces (`_OpenCoreRhoMonotone`) to `ρ(r)` antitone, i.e. the **cross-inequality**
`S_r·E_{r+1} − S_{r+1}·E_r ≥ 0`, where `S_r = Σ_{t≠0}|η_t|^{2r} = p·E_r(F_p) − n^{2r}` (b≠0 char-p energy) and
`E_r = E_r(ℂ)` (char-0 energy). This file records the **exact cross-excess decomposition** that splits it into a
provable char-0 part and the open char-p part — the cleanest statement of exactly where the proof stands.

**The exact identity (verified by `ring`, and by exact-integer probe at n=16, all r).** Writing
`E_r(F_p) = E_r + W_r` (`W_r ≥ 0` = the char-p wraparound excess) and `n^{2(r+1)} = n²·n^{2r}`:
```
   S_r·E_{r+1} − S_{r+1}·E_r  =  p·(W_r·E_{r+1} − W_{r+1}·E_r)  +  n^{2r}·(n²·E_r − E_{r+1}).
                                  └────── char-p part B ──────┘     └──── char-0 part A ────┘
```
* **Part A (char-0), provably ≥ 0:** `n²·E_r − E_{r+1} ≥ 0 ⟺ E_{r+1}(ℂ) ≤ n²·E_r(ℂ)` — the char-0 backbone, proven
  via the Wick ratio `E_{r+1} ≤ (2r+1)n·E_r ≤ n²·E_r` (for `2r+1 ≤ n`, i.e. the entire prize range `r ≍ log n ≪ n/2`;
  landed `_CharZeroBackboneAntitone`). Scaled by `n^{2r}`, Part A is large and positive.
* **Part B (char-p), exactly negative and adversarial:** exact-integer probe (n=16, β=4) shows the wraparound ratio
  `W_{r+1}/W_r ≈ 650–1455 ≫ E_{r+1}/E_r ≈ 110–253`, so `W_r·E_{r+1} − W_{r+1}·E_r < 0`. Part B is negative, scaled by
  `p`, with `|B|/A` climbing `0 → 0.11 → 0.26 → 0.40` (n=16) and `→ 0.96` (n=32, r=4) — **approaching 1 = the wall**.

**What this proves about the proof.** The antitone step is **not** a sum of two nonneg pieces: it is a
**near-cancellation** in which the positive char-0 Part A (`×n^{2r}`) must out-dominate the negative char-p Part B
(`×p`). Hence:
* **Wraparound-free regime** (`W_r = W_{r+1} = 0`, exact for `r ≤ 3` generically; `W_3 = 0`, `W_4 = 0` off-Fermat):
  Part B vanishes, so antitone `⟺` Part A `≥ 0`, which is **proven** — antitone holds outright there.
* **General regime:** antitone `⟺` `n^{2r}·(n²·E_r − E_{r+1}) ≥ p·(W_{r+1}·E_r − W_r·E_{r+1})` — the char-0 dominance
  margin, which the probes show `→ 1` at the saddle = the BGK/Paley wall. This is the exact open content.

**What this file proves (axiom-clean).** `cross_excess_decomp` (the exact identity, by `ring`),
`antitone_of_charZero_dominates` (Part A ≥ |Part B| ⟹ antitone), `antitone_iff_dominance` (the exact dominance
criterion), and `antitone_of_no_wraparound` (`W = 0` + Part A ≥ 0 ⟹ antitone — the proven wraparound-free case).
Issue #444.
-/

namespace ProximityGap.Frontier.AntitoneCrossExcess

/-- **The exact cross-excess decomposition.** With `S k = p·(E k + W k) − N k` (b≠0 char-p energy; `N k = n^{2k}`)
and `N (r+1) = nsq·N r` (`nsq = n²`), the antitone cross-excess splits exactly:
`S r·E (r+1) − S (r+1)·E r = p·(W r·E (r+1) − W (r+1)·E r) + N r·(nsq·E r − E (r+1))`. Pure `ring` identity. -/
theorem cross_excess_decomp (S E W N : ℕ → ℝ) (p nsq : ℝ) (r : ℕ)
    (hS : ∀ k, S k = p * (E k + W k) - N k) (hN : N (r + 1) = nsq * N r) :
    S r * E (r + 1) - S (r + 1) * E r
      = p * (W r * E (r + 1) - W (r + 1) * E r) + N r * (nsq * E r - E (r + 1)) := by
  rw [hS r, hS (r + 1), hN]; ring

/-- **Antitone from char-0 dominance.** If the char-0 part `N r·(nsq·E r − E (r+1))` is at least the magnitude of the
(negative) char-p part — packaged as `p·(W (r+1)·E r − W r·E (r+1)) ≤ N r·(nsq·E r − E (r+1))` — then the cross-excess
is `≥ 0`, i.e. the antitone step holds. -/
theorem antitone_of_charZero_dominates (S E W N : ℕ → ℝ) (p nsq : ℝ) (r : ℕ)
    (hS : ∀ k, S k = p * (E k + W k) - N k) (hN : N (r + 1) = nsq * N r)
    (hdom : p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (nsq * E r - E (r + 1))) :
    0 ≤ S r * E (r + 1) - S (r + 1) * E r := by
  rw [cross_excess_decomp S E W N p nsq r hS hN]; linarith

/-- **The exact dominance criterion.** The antitone step `S r·E (r+1) ≥ S (r+1)·E r` is *equivalent* to the char-0
dominance `p·(W (r+1)·E r − W r·E (r+1)) ≤ N r·(nsq·E r − E (r+1))` — the precise open content (char-0 Part A beats
char-p Part B). -/
theorem antitone_iff_dominance (S E W N : ℕ → ℝ) (p nsq : ℝ) (r : ℕ)
    (hS : ∀ k, S k = p * (E k + W k) - N k) (hN : N (r + 1) = nsq * N r) :
    (S (r + 1) * E r ≤ S r * E (r + 1))
      ↔ p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (nsq * E r - E (r + 1)) := by
  rw [← sub_nonneg, cross_excess_decomp S E W N p nsq r hS hN]
  constructor <;> intro h <;> linarith

/-- **The proven wraparound-free case.** When there is no wraparound (`W r = W (r+1) = 0`, exact for `r ≤ 3`
generically) and the char-0 part is nonneg (`E (r+1) ≤ nsq·E r`, the proven backbone), the antitone step holds
outright — `Part B` vanishes, so antitone `=` `Part A ≥ 0`. -/
theorem antitone_of_no_wraparound (S E W N : ℕ → ℝ) (p nsq : ℝ) (r : ℕ)
    (hS : ∀ k, S k = p * (E k + W k) - N k) (hN : N (r + 1) = nsq * N r)
    (hWr : W r = 0) (hWr1 : W (r + 1) = 0) (hNr : 0 ≤ N r) (hbackbone : E (r + 1) ≤ nsq * E r) :
    0 ≤ S r * E (r + 1) - S (r + 1) * E r := by
  apply antitone_of_charZero_dominates S E W N p nsq r hS hN
  rw [hWr, hWr1]
  have : 0 ≤ N r * (nsq * E r - E (r + 1)) := mul_nonneg hNr (by linarith)
  simpa using this

end ProximityGap.Frontier.AntitoneCrossExcess

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.AntitoneCrossExcess.cross_excess_decomp
#print axioms ProximityGap.Frontier.AntitoneCrossExcess.antitone_of_charZero_dominates
#print axioms ProximityGap.Frontier.AntitoneCrossExcess.antitone_iff_dominance
#print axioms ProximityGap.Frontier.AntitoneCrossExcess.antitone_of_no_wraparound
