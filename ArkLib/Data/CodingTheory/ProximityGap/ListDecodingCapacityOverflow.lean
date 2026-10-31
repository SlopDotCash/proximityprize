/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeListSize

/-!
# End-to-end: capacity-exponent overflow ⇒ the up-to-capacity list-decoding bound fails (#232)

Chains the axiom-clean entropy-volume list lower bound
`CodingTheory.rs_lambda_ge_capacity_exponent` (`|Λ(RS,δ)| ≥ q^{E}/(n+1)`, `E` the capacity
exponent `n·H_q(⌊δn⌋/n) − (n−k)`) with an `rpow`/`logb` overflow bridge to conclude that whenever
the capacity exponent exceeds `logb q ((n+1)·ε*·q)`, the RS list size strictly exceeds `ε*·|F|`.

Combined with `CodingTheory.capacityExponent_pos` (the capacity exponent is *positive* at the
Singleton radius — `QEntropySelfBound.lean`), this gives a **conditional** route to the negative
side of the Grand List Decoding Challenge: wherever the overflow hypothesis holds, the
*up-to-capacity* list-decoding bound fails.  Positivity of `E` alone does **not** supply the
overflow.  The slack `E/n = H_q(δ) − (1 − ρ)` depends on `q` (at `δ = 1 − ρ` it is about
`h(δ)/ln q`, `h` the natural-log binary entropy), while the budget `logb q ((n+1)·ε*·q)` tends to
`1` as `q → ∞`.  Since an injective RS domain only forces `n ≤ q`, `q` may grow much faster than
`n`: e.g. at rate `1/2`, even `n`, `δ = 1/2`, `E ≈ n·ln 2/ln q`, and taking `q > 2^{n²}` makes
`E < 1/n` (roughly) while the budget is close to `1`, so overflow fails for arbitrarily large `n`.
Overflow therefore needs a **joint `(n, q)` regime** in which `ln q` is controlled by `n`
(heuristically `ln q ≲ n·h(δ) − ln(n+1) − ln ε*`); such a regime and its budget inequality are
**not** proved in this file.  The in-tree concrete instance
`rs_uptoCapacity_false_rate12_n256` discharges the overflow numerically for `n = 256`, rate `1/2`,
under the explicit field-size window `2^128 ≤ q ≤ 2^256`.

## Main results
- `threshold_lt_pow_div` — `rpow` overflow: `logb q ((n+1)·εq) < E → εq < q^E/(n+1)`.
- `rs_lambda_gt_threshold_of_capExp_overflow` — the end-to-end conditional refutation.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

namespace CodingTheory

open Real ListDecodable
open scoped NNReal ENNReal

/-- **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, if `logb q (n1·εq) < E` then
`εq < q^E / n1`. -/
theorem threshold_lt_pow_div (q : ℝ) (hq : 1 < q) (n1 : ℝ) (hn1 : 0 < n1)
    (εq : ℝ) (hεq : 0 < εq) (E : ℝ) (hE : Real.logb q (n1 * εq) < E) :
    εq < q ^ E / n1 := by
  have hA : 0 < n1 * εq := mul_pos hn1 hεq
  have hlt : n1 * εq < q ^ E := (Real.logb_lt_iff_lt_rpow hq hA).mp hE
  rw [lt_div_iff₀ hn1]; nlinarith [hlt]

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **End-to-end refutation (capacity-exponent overflow form).** For a Reed–Solomon code with
`q = |F| ≥ 2`, mode `⌊δn⌋ ∈ (0,n)`, if the capacity exponent
`E = n·H_q(⌊δn⌋/n) − (n−k)` exceeds `logb q ((n+1)·ε*·q)`, then `|Λ(RS[α,k], δ)| > ε*·|F|`: the
up-to-capacity list-decoding bound fails at `δ`. -/
theorem rs_lambda_gt_threshold_of_capExp_overflow
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (ε_star : ℝ≥0)
    (hover : Real.logb (Fintype.card F)
          (((Fintype.card ι : ℝ) + 1) * ((ε_star : ℝ) * (Fintype.card F)))
        < (Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
            - ((Fintype.card ι : ℝ) - (k : ℝ))) :
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda (ReedSolomon.code α k : Set (ι → F)) δ : ENNReal) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n1 : ℝ := (Fintype.card ι : ℝ) + 1 with hn1def
  set E : ℝ := (Fintype.card ι : ℝ)
        * qEntropy (Fintype.card F)
            ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
      - ((Fintype.card ι : ℝ) - (k : ℝ)) with hEdef
  have hqR : (1 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  have hn1 : (0 : ℝ) < n1 := by rw [hn1def]; positivity
  have hq0 : (0 : ℝ) < q := by linarith
  have hLB := rs_lambda_ge_capacity_exponent α k δ hδ_pos hδ_lt hq hkcard hk0 hkn
  -- hLB : ENNReal.ofReal (q ^ E / n1) ≤ Lambda
  have hεq0 : (0 : ℝ) ≤ (ε_star : ℝ) * q := by positivity
  rcases eq_or_lt_of_le hεq0 with hz | hpos
  · have hpow : (0 : ℝ) < q ^ E / n1 := by positivity
    have hLHS : (ε_star : ENNReal) * (Fintype.card F : ENNReal) = 0 := by
      rcases mul_eq_zero.mp hz.symm with h | h
      · simp [show ε_star = 0 by exact_mod_cast h]
      · exact absurd h hq0.ne'
    rw [hLHS]
    exact lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hpow) hLB
  · have hreal : (ε_star : ℝ) * q < q ^ E / n1 := threshold_lt_pow_div q hqR n1 hn1 _ hpos E hover
    have hconv : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        = ENNReal.ofReal ((ε_star : ℝ) * q) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      · simp [ENNReal.ofReal_coe_nnreal]
      · rw [hqdef, ENNReal.ofReal_natCast]
    rw [hconv]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal) hLB

#print axioms threshold_lt_pow_div
#print axioms rs_lambda_gt_threshold_of_capExp_overflow

end CodingTheory
