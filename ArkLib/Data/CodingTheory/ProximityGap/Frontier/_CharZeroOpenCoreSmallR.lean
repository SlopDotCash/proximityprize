/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The char-0 open core holds in the small-`r` (prize) regime, end-to-end (#444)

`_OpenCoreRhoMonotone` reduced the prize to `ρ(r) ≤ 1` for all `r`, with `ρ(r) = S_r/((p−1)E_r)`,
`S_r = p·E_r(F_p) − n^{2r}` the char-p energy, via the antitone hypothesis `ρ(r+1) ≤ ρ(r)`.
`_CharZeroBackboneAntitone` + `_CharZeroBackboneSmallRRegime` proved the **char-0** half: with the
**char-0 surrogate** `ρ_C(r) := (p·E_r(ℂ) − n^{2r})/((p−1)·E_r(ℂ))` (i.e. `S_r` replaced by its
char-0 value `p·E_r(ℂ) − n^{2r}`), the backbone gives `T_r = n^{2r}/E_r(ℂ)` increasing in the regime
`2r+1 ≤ n`.

**This file: chains it to the open-core conclusion for the char-0 surrogate.** Two clean bricks:

* `rhoC_antitone_iff_T_increasing` — the EXACT algebra `ρ_C(r) = p/(p−1) − T_r/(p−1)`, so
  `ρ_C(r+1) ≤ ρ_C(r) ⟺ T_r ≤ T_{r+1}` (`p−1 > 0`). The char-0 `ρ` is antitone iff `T` is increasing.
* `charZero_open_core_le_one_smallR` — the end-to-end conclusion, **regime-bounded** (codex P2): for a
  target depth `R`, if `T_k` is increasing at every step `1 ≤ k < R` (which `_CharZeroBackboneSmallRRegime`
  supplies *exactly on the regime* `2k+1 ≤ n`, and only those steps are needed) and the base value
  `ρ_C(1) ≤ 1` (Parseval), then `ρ_C(R) ≤ 1`. The hypothesis is required ONLY on the steps `[1, R)`,
  never outside the regime where the backbone establishes monotonicity. (The bounded induction is
  re-proved inline; it mirrors `_OpenCoreRhoMonotone.open_core_of_rho_antitone` but only walks up to `R`.)

**Honest scope — this is the CHAR-0 SURROGATE, NOT the prize.** The real `ρ` uses the char-p energy
`S_r = p·E_r(F_p) − n^{2r}`; here `S_r` is replaced by its char-0 value `p·E_r(ℂ) − n^{2r}`. The two
differ by exactly `p·W_r` (`W_r = E_r(F_p) − E_r(ℂ)` the char-p coincidence excess). So this proves the
open core for the char-0 model where `W_r = 0`; the prize is precisely that the char-p correction `p·W_r`
stays inside the backbone room at the saddle. No CORE upper bound on the real `μ_n`, no capacity claim.
Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroOpenCoreSmallR

/-- **`ρ_C` antitone ⟺ `T` increasing (exact algebra).** With the char-0 surrogate
`ρ_C(r) = (p·E_r − n^{2r})/((p−1)·E_r) = p/(p−1) − T_r/(p−1)`, `T_r = n^{2r}/E_r`, and `p−1 > 0`,
`E_r, E_{r+1} > 0`, the antitone step `ρ_C(r+1) ≤ ρ_C(r)` is equivalent to `T_r ≤ T_{r+1}`. -/
theorem rhoC_antitone_iff_T_increasing (E : ℕ → ℝ) (n p : ℝ) (r : ℕ)
    (hp1 : 0 < p - 1) (hEr : 0 < E r) (hEr1 : 0 < E (r + 1)) :
    ((p * E (r + 1) - n ^ (2 * (r + 1))) / ((p - 1) * E (r + 1))
        ≤ (p * E r - n ^ (2 * r)) / ((p - 1) * E r))
      ↔ n ^ (2 * r) / E r ≤ n ^ (2 * (r + 1)) / E (r + 1) := by
  have hd1 : 0 < (p - 1) * E (r + 1) := by positivity
  have hd0 : 0 < (p - 1) * E r := by positivity
  rw [div_le_div_iff₀ hd1 hd0, div_le_div_iff₀ hEr hEr1]
  constructor
  · intro h; nlinarith [h, hp1, hEr, hEr1, mul_pos hEr hEr1]
  · intro h; nlinarith [h, hp1, hEr, hEr1, mul_pos hEr hEr1]

/-- **Char-0 open core in the regime, end-to-end (regime-bounded).** For a target depth `R`, if `T_k`
is increasing at every step `1 ≤ k < R` (`T_k ≤ T_{k+1}`, supplied by `_CharZeroBackboneSmallRRegime`
from the deficit anchor *exactly on the regime* `2k+1 ≤ n` — and ONLY these steps are consumed) and
the base `ρ_C(1) ≤ 1` (Parseval), then `ρ_C(R) ≤ 1`. The char-0 surrogate of the open core, with the
monotonicity hypothesis required only on `[1, R)` (never outside the regime). -/
theorem charZero_open_core_le_one_smallR (E : ℕ → ℝ) (n p : ℝ) (R : ℕ) (hR : 1 ≤ R)
    (hp1 : 0 < p - 1) (hEpos : ∀ k, 1 ≤ k → k ≤ R → 0 < E k)
    (hTinc : ∀ k, 1 ≤ k → k < R →
      n ^ (2 * k) / E k ≤ n ^ (2 * (k + 1)) / E (k + 1))
    (hbase : (p * E 1 - n ^ (2 * 1)) / ((p - 1) * E 1) ≤ 1) :
    (p * E R - n ^ (2 * R)) / ((p - 1) * E R) ≤ 1 := by
  -- the antitone step at k (ρ_C(k+1) ≤ ρ_C(k)), available only for k < R (regime + k,k+1 ≤ R)
  have hanti : ∀ k, 1 ≤ k → k < R →
      (p * E (k + 1) - n ^ (2 * (k + 1))) / ((p - 1) * E (k + 1))
        ≤ (p * E k - n ^ (2 * k)) / ((p - 1) * E k) := by
    intro k hk hkR
    have hEk := hEpos k hk (le_of_lt hkR)
    have hEk1 := hEpos (k + 1) (le_trans hk (Nat.le_succ k)) hkR
    exact (rhoC_antitone_iff_T_increasing E n p k hp1 hEk hEk1).mpr (hTinc k hk hkR)
  -- helper: ρ_C(m) ≤ 1 for every 1 ≤ m ≤ R, by Nat.le_induction on m from 1 (walks only [1,R])
  suffices h : ∀ m, 1 ≤ m → m ≤ R →
      (p * E m - n ^ (2 * m)) / ((p - 1) * E m) ≤ 1 from h R hR (le_refl R)
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro _; exact hbase
  | succ k hk ih =>
    intro hkR
    -- k < R since k+1 ≤ R; step ρ_C(k+1) ≤ ρ_C(k), then ih (k ≤ R)
    have hklt : k < R := Nat.lt_of_succ_le hkR
    exact le_trans (hanti k hk hklt) (ih (le_of_lt hklt))

end ProximityGap.Frontier.CharZeroOpenCoreSmallR

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharZeroOpenCoreSmallR.rhoC_antitone_iff_T_increasing
#print axioms ProximityGap.Frontier.CharZeroOpenCoreSmallR.charZero_open_core_le_one_smallR
