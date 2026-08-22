/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Char-0 backbone in the small-`r` (prize) regime: backbone ⟹ `T_r` increasing, end-to-end (#444)

`_CharZeroBackboneAntitone` proved the **sharp** char-0 backbone bound
```
        E_{r+1}(ℂ) ≤ (2r+1)·n · E_r(ℂ)      (from the Bessel deficit being antitone),
```
and, separately, `charZero_T_increasing_of_backbone`, which turns the **coarse** form
`E_{r+1} ≤ n²·E_r` into `T_r = n^{2r}/E_r` increasing (`= ` char-0 `ρ` antitone). The coarse form
was supplied there as a *hypothesis*; the bridge `(2r+1)n ≤ n²`, i.e. `2r+1 ≤ n`, was not composed.

**This file: the regime-explicit composition.** The bridge `(2r+1)·n ≤ n²` holds exactly when
`2r+1 ≤ n` (`1 ≤ n`). The prize saddle sits at `r ≈ β·log₂ n` (probe: `scripts/probes` β≈4.5), which
for every prize-regime `n = 2^a` is *comfortably inside* `2r+1 ≤ n` (e.g. `n=2^20`: saddle `r≈90`,
regime bound `(n−1)/2 ≈ 5.2·10^5`). So the sharp backbone, in the regime that the prize lives in,
**implies the coarse form unconditionally**, and hence the char-0 `T_r`-increasing / `ρ`-antitone half:

```
   sharp backbone   E_{r+1} ≤ (2r+1)n·E_r
   regime           2r+1 ≤ n,  0 ≤ E_r
   ───────────────────────────────────────  ⟹  E_{r+1} ≤ n²·E_r  ⟹  n^{2r}/E_r ≤ n^{2(r+1)}/E_{r+1}.
```

**What this file proves (axiom-clean).**
* `coarse_backbone_of_sharp_smallR` — the bridge: sharp backbone `E_{r+1} ≤ (2r+1)n·E_r` + `2r+1 ≤ n`
  + `1 ≤ n` + `0 ≤ E_r` ⟹ coarse backbone `E_{r+1} ≤ n²·E_r`.
* `charZero_T_increasing_of_sharp_smallR` — the end-to-end composition: sharp backbone + small-`r`
  regime ⟹ `n^{2r}/E_r ≤ n^{2(r+1)}/E_{r+1}` (`T_r` increasing = char-0 `ρ` antitone), with the
  coarse `n²` hypothesis **discharged** (no longer assumed).
* `charZero_T_increasing_of_deficit_smallR` — the *fully reduced* form: from `E = Wick·d`, the Wick
  recursion, deficit-antitone `d(r+1) ≤ d(r)`, and `2r+1 ≤ n`, conclude `T_r` increasing — chaining the
  backbone derivation (`_CharZeroBackboneAntitone.energy_ratio_le_of_deficit_antitone`, re-proved inline
  to keep this file standalone) all the way to the char-0 `ρ`-antitone step from the deficit anchor alone.

**Honest scope.** Char-0 ONLY. This packages the char-0 half of the antitone race end-to-end in the
prize regime; the char-p correction `S_r − (p−1)E_r = p·W_r` staying within the backbone room at the
saddle remains the open prize. No CORE upper bound, no capacity/growth-law claim. Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroBackboneSmallR

/-- **The bridge.** In the small-`r` regime `2r+1 ≤ n` (with `1 ≤ n`, `0 ≤ E_r`), the sharp backbone
`E_{r+1} ≤ (2r+1)·n·E_r` implies the coarse backbone `E_{r+1} ≤ n²·E_r`, since `(2r+1)·n ≤ n·n = n²`. -/
theorem coarse_backbone_of_sharp_smallR (E : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r)
    (hregime : 2 * (r : ℝ) + 1 ≤ n) (hn1 : 1 ≤ n) (hEr : 0 ≤ E r) :
    E (r + 1) ≤ n ^ 2 * E r := by
  refine hsharp.trans ?_
  have hcoef : (2 * (r : ℝ) + 1) * n ≤ n ^ 2 := by
    have hnpos : 0 ≤ n := le_trans zero_le_one hn1
    calc (2 * (r : ℝ) + 1) * n ≤ n * n :=
          mul_le_mul_of_nonneg_right hregime hnpos
      _ = n ^ 2 := by ring
  exact mul_le_mul_of_nonneg_right hcoef hEr

/-- **End-to-end (sharp backbone form).** Sharp backbone + small-`r` regime ⟹ `T_r = n^{2r}/E_r`
increasing (= char-0 `ρ` antitone), with the coarse `n²` hypothesis discharged via the bridge. -/
theorem charZero_T_increasing_of_sharp_smallR (E : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hEr : 0 < E r) (hEr1 : 0 < E (r + 1)) (hn1 : 1 ≤ n)
    (hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r)
    (hregime : 2 * (r : ℝ) + 1 ≤ n) :
    n ^ (2 * r) / E r ≤ n ^ (2 * (r + 1)) / E (r + 1) := by
  have hbackbone : E (r + 1) ≤ n ^ 2 * E r :=
    coarse_backbone_of_sharp_smallR E n r hsharp hregime hn1 (le_of_lt hEr)
  -- the coarse-form `T` increasing step (re-proved inline; mirrors
  -- `_CharZeroBackboneAntitone.charZero_T_increasing_of_backbone`)
  rw [div_le_div_iff₀ hEr hEr1]
  have hnpow : (0 : ℝ) ≤ n ^ (2 * r) := by positivity
  have hexp : n ^ (2 * (r + 1)) = n ^ (2 * r) * n ^ 2 := by
    rw [← pow_add]; ring_nf
  rw [hexp]
  calc n ^ (2 * r) * E (r + 1) ≤ n ^ (2 * r) * (n ^ 2 * E r) :=
        mul_le_mul_of_nonneg_left hbackbone hnpow
    _ = n ^ (2 * r) * n ^ 2 * E r := by ring

/-- **Fully reduced (deficit-anchor form).** From the Wick decomposition `E = Wick·d`, the Wick
recursion `W(k+1) = (2k+1)·n·W(k)`, positivity `0 < W r`, deficit-antitone `d(r+1) ≤ d(r)`
(with `0 ≤ d(r+1)`), and the small-`r` regime `2r+1 ≤ n`, conclude `T_r` increasing — the char-0
`ρ`-antitone step from the deficit anchor alone. (The sharp backbone is re-derived inline.) -/
theorem charZero_T_increasing_of_deficit_smallR (E W d : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hE : ∀ k, E k = W k * d k) (hWr : ∀ k, W (k + 1) = (2 * (k : ℝ) + 1) * n * W k)
    (hWpos : 0 < W r) (hn1 : 1 ≤ n) (hdr1 : 0 < d (r + 1)) (hdanti : d (r + 1) ≤ d r)
    (hdrpos : 0 < d r) (hregime : 2 * (r : ℝ) + 1 ≤ n) :
    n ^ (2 * r) / E r ≤ n ^ (2 * (r + 1)) / E (r + 1) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  -- sharp backbone (mirrors energy_ratio_le_of_deficit_antitone)
  have hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r := by
    rw [hE (r + 1), hE r, hWr r]
    have hcoef : 0 ≤ (2 * (r : ℝ) + 1) * n * W r := by positivity
    calc (2 * (r : ℝ) + 1) * n * W r * d (r + 1)
        ≤ (2 * (r : ℝ) + 1) * n * W r * d r :=
          mul_le_mul_of_nonneg_left hdanti hcoef
      _ = (2 * (r : ℝ) + 1) * n * (W r * d r) := by ring
  -- positivity of E r, E (r+1)
  have hEr : 0 < E r := by rw [hE r]; exact mul_pos hWpos hdrpos
  have hEr1 : 0 < E (r + 1) := by
    rw [hE (r + 1), hWr r]
    have hWnpos : 0 < (2 * (r : ℝ) + 1) * n * W r := by positivity
    exact mul_pos hWnpos hdr1
  exact charZero_T_increasing_of_sharp_smallR E n r hEr hEr1 hn1 hsharp hregime

end ProximityGap.Frontier.CharZeroBackboneSmallR

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharZeroBackboneSmallR.coarse_backbone_of_sharp_smallR
#print axioms ProximityGap.Frontier.CharZeroBackboneSmallR.charZero_T_increasing_of_sharp_smallR
#print axioms ProximityGap.Frontier.CharZeroBackboneSmallR.charZero_T_increasing_of_deficit_smallR
