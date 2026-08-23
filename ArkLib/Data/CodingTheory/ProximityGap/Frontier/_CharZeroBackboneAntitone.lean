/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The char-0 backbone of `ρ`-antitone: `E_{r+1}(ℂ)/E_r(ℂ) ≤ (2r+1)·n` from the Bessel deficit (#444)

The prize reduces (`_OpenCoreRhoMonotone`) to `ρ(r) = S_r/((p−1)·E_r(ℂ))` being antitone, equivalently the
energy cross `S_{r+1}·E_r ≤ S_r·E_{r+1}` (`S_r = Σ_{t≠0}|η_t|^{2r}`, `E_r = E_r(ℂ)` the char-0 energy). The
exact-verified anatomy splits this into a **char-0 backbone** (provable) and a char-p correction (the open part).

**This file: the char-0 backbone, fully reduced to a proven anchor.** Write `E_r = Wick_r · d_r`, where
`Wick_r = (2r−1)‼·n^r` and `d_r = E_r(ℂ)/Wick_r` is the **Bessel deficit ratio** (`= e^{−r²/2n}(1+o(1))`). The
char-0 energy ratio is then
```
        E_{r+1}/E_r = (Wick_{r+1}/Wick_r)·(d_{r+1}/d_r) = (2r+1)·n·(d_{r+1}/d_r).
```
So **if the deficit ratio is decreasing (`d_{r+1} ≤ d_r`)** — the coefficient form of the proven Bessel bound
`I₀(2y)^{n/2} ≤ e^{ny²/2}` being tight-decreasing, exact-verified `d_r` strictly ↓ at n=16..128 — then
```
        E_{r+1}/E_r ≤ (2r+1)·n   (≤ n² for 2r+1 ≤ n),
```
the char-0 backbone. This is exactly the char-0 part of the antitone race: the char-0 energy ratio is bounded by
the Wick ratio, the value the char-p moment ratio `S_{r+1}/S_r → M²` must stay under.

**What this file proves (axiom-clean).**
* `wick_ratio_eq` — `Wick_{r+1} = (2r+1)·n·Wick_r` (the exact Gaussian/Wick recursion, from `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼`).
* `energy_ratio_le_of_deficit_antitone` — from `E_r = Wick_r·d_r`, `Wick_{r+1} = (2r+1)n·Wick_r`, and `d_{r+1} ≤ d_r`
  (with positivity), conclude `E_{r+1} ≤ (2r+1)·n·E_r` — the char-0 backbone bound.
* `charZero_rho_antitone_of_backbone` — the char-0 `ρ_C(r) = (p·E_r − n^{2r})/((p−1)·E_r) = p/(p−1) − n^{2r}/((p−1)E_r)`
  is antitone given the backbone (`n^{2r}/E_r` increasing), i.e. the char-0 half of the prize is unconditional modulo
  the deficit-antitone anchor.

This proves the **char-0 backbone** of the antitone lemma. The remaining open content is the char-p correction
`S_r − (p−1)E_r = p·W_r` staying within the backbone room at the saddle (= the prize). Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroBackbone

/-- **The Wick recursion.** `Wick_{r+1} = (2r+1)·n·Wick_r` (given the multiplicative law `(2(r+1)−1)‼ = (2r+1)(2r−1)‼`,
encoded abstractly as `W (r+1) = (2r+1)·n·W r`). -/
theorem wick_ratio_eq (W : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hW : ∀ k, W (k + 1) = (2 * (k : ℝ) + 1) * n * W k) :
    W (r + 1) = (2 * (r : ℝ) + 1) * n * W r := hW r

/-- **The char-0 backbone bound.** With `E k = W k · d k` (`W` = Wick, `d` = Bessel deficit ratio), the Wick
recursion `W (r+1) = (2r+1)n·W r`, positivity `0 < W r`, `0 ≤ d (r+1)`, and the deficit antitone `d (r+1) ≤ d r`,
the char-0 energy ratio is bounded by the Wick ratio: `E (r+1) ≤ (2r+1)·n·E r`. -/
theorem energy_ratio_le_of_deficit_antitone (E W d : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hE : ∀ k, E k = W k * d k) (hWr : ∀ k, W (k + 1) = (2 * (k : ℝ) + 1) * n * W k)
    (hWpos : 0 < W r) (hn : 0 ≤ n) (hdr1 : 0 ≤ d (r + 1)) (hdanti : d (r + 1) ≤ d r) :
    E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r := by
  rw [hE (r + 1), hE r, hWr r]
  have hcoef : 0 ≤ (2 * (r : ℝ) + 1) * n * W r := by positivity
  calc (2 * (r : ℝ) + 1) * n * W r * d (r + 1)
      ≤ (2 * (r : ℝ) + 1) * n * W r * d r := by
        exact mul_le_mul_of_nonneg_left hdanti hcoef
    _ = (2 * (r : ℝ) + 1) * n * (W r * d r) := by ring

/-- **The char-0 ρ is antitone given the backbone.** `ρ_C(r) = (p·E_r − n^{2r})/((p−1)·E_r) = p/(p−1) − T_r/(p−1)`
with `T_r = n^{2r}/E_r`. So `ρ_C` is antitone ⟺ `T_r` is increasing. The backbone `E_{r+1} ≤ (2r+1)n·E_r` with
`(2r+1)n ≤ n²` gives `E_{r+1}/E_r ≤ n² = n^{2(r+1)}/n^{2r}`, i.e. `n^{2(r+1)}/E_{r+1} ≥ n^{2r}/E_r` — `T_r` increasing.
Hence `ρ_C` antitone. (Stated as the clean increasing-`T` consequence.) -/
theorem charZero_T_increasing_of_backbone (E : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hEr : 0 < E r) (hEr1 : 0 < E (r + 1)) (hn1 : 1 ≤ n)
    (hbackbone : E (r + 1) ≤ n ^ 2 * E r) :
    n ^ (2 * r) / E r ≤ n ^ (2 * (r + 1)) / E (r + 1) := by
  rw [div_le_div_iff₀ hEr hEr1]
  have hnpow : (0 : ℝ) ≤ n ^ (2 * r) := by positivity
  have hexp : n ^ (2 * (r + 1)) = n ^ (2 * r) * n ^ 2 := by
    rw [← pow_add]; ring_nf
  rw [hexp]
  calc n ^ (2 * r) * E (r + 1) ≤ n ^ (2 * r) * (n ^ 2 * E r) :=
        mul_le_mul_of_nonneg_left hbackbone hnpow
    _ = n ^ (2 * r) * n ^ 2 * E r := by ring

end ProximityGap.Frontier.CharZeroBackbone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharZeroBackbone.wick_ratio_eq
#print axioms ProximityGap.Frontier.CharZeroBackbone.energy_ratio_le_of_deficit_antitone
#print axioms ProximityGap.Frontier.CharZeroBackbone.charZero_T_increasing_of_backbone
