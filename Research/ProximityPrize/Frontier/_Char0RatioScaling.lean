/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The char-0 moment ratio R_r: exact anchor and the prize-scale scaling correction (#444)

Fresh angle (i): the asymptotics of `R_r = E_char0(μ_n, r) / Wick`, `Wick = (2r−1)‼·n^r`.  This brick records
the rigorous anchor and an **honesty correction to an earlier framing** (§7.6(iv) / `_RhoDecomposition`).

**The exact anchor.**  The char-0 second-moment energy is the Sidon-floor value `E_2 = 3n² − 3n` (`μ_n` is Sidon
except for the single antipodal coincidence `x + (−x) = 0`), and `Wick_2 = (2·2−1)‼·n² = 3n²`.  Hence
`R_2 = (3n² − 3n)/(3n²) = 1 − 1/n` **exactly** (`R2_eq_one_sub_inv`), so the char-0 slack *fraction*
`1 − R_2 = 1/n` (`char0_slack_fraction_at_r2`).  Measured (`probe_Rr_scaling`) this extends to the leading law
`1 − R_r ≈ r(r−1)/(2n)` for `r ≪ √n` (each of the `C(r,2)` pairs contributes one `1/n` antipodal coincidence).

**The correction (this matters for the prize).**  An earlier draft (§7.6(iv)) said `R_r → 0` super-geometrically
with a char-0 slack "*growing with depth*, on the data's side".  That holds **only** in the computable regime
`r ≳ √n` (reached only because `n` is small there).  At **prize scale** `n = 2^{30}`, the saddle `r ≈ log p ≈ 110`
satisfies `r ≪ √n = 2^{15} = 32768`, so `1 − R_r ≈ r²/(2n) ≈ 5.6·10⁻⁶` and **`R_r ≈ 1`, not `→ 0`**.  The char-0
slack component `(1 − R_r)·Wick ≈ (r²/2n)·Wick` is therefore a *small* `r²/n` fraction of `Wick`, **not** a widening
budget; at prize scale the slack of `_RhoDecomposition` is dominated by the DC term `(n^{2r} − Wick)/p`, not by the
char-0 component.  The "margin widening with depth" reading was a finite-size artifact, and is corrected in the
thesis accordingly.  (The DC-subtracted moment `ρ_r` decreasing in the computable data is real *there*; it does not
license the prize-scale extrapolation, which this brick blocks.)

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace ProximityGap.Char0RatioScaling

/-- **Exact anchor `R_2 = 1 − 1/n`.**  From the Sidon-floor `E_2 = 3n² − 3n` and `Wick_2 = 3n²`. -/
theorem R2_eq_one_sub_inv (n : ℝ) (hn : 0 < n) :
    (3 * n ^ 2 - 3 * n) / (3 * n ^ 2) = 1 - 1 / n := by
  have hn2 : n ^ 2 ≠ 0 := by positivity
  field_simp

/-- **The char-0 slack fraction at `r = 2` is `1/n`.**  So it *shrinks* with `n` (→ 0), the opposite of a
"widening budget"; at large `n` (prize scale) the char-0 slack is a small fraction of `Wick`. -/
theorem char0_slack_fraction_at_r2 (n : ℝ) (hn : 0 < n) :
    1 - (3 * n ^ 2 - 3 * n) / (3 * n ^ 2) = 1 / n := by
  rw [R2_eq_one_sub_inv n hn]; ring

/-- **Monotone anchor: `R_2` increases toward 1 as `n` grows.**  At fixed depth `r = 2`, `R_2(n) = 1 − 1/n` is
increasing in `n` and `< 1`, so `R_2 → 1` (not `→ 0`).  This is the rigorous seed of the prize-scale statement
`R_r ≈ 1` for `r ≪ √n`: the char-0 ratio is *close to* the Gaussian/Wick value in the thin-saddle regime, and the
super-geometric decay seen in small-`n` data lives only at `r ≳ √n`. -/
theorem R2_lt_one_and_increasing {n m : ℝ} (hn : 0 < n) (hnm : n ≤ m) :
    (1 - 1 / n ≤ 1 - 1 / m) ∧ (1 - 1 / n < 1) := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  refine ⟨?_, by simpa using (by positivity : (0:ℝ) < 1 / n)⟩
  have : 1 / m ≤ 1 / n := by
    apply one_div_le_one_div_of_le hn hnm
  linarith

end ProximityGap.Char0RatioScaling
