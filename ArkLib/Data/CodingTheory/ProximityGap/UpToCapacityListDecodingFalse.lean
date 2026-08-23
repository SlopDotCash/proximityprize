/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeListSize

/-!
# The up-to-capacity list-decoding bound is FALSE in the prize regime (#232, negative side)

Capstone of the negative side of the ABF26 Proximity Prize: an **unconditional** counterexample
(no admit, no open hypothesis) to the *up-to-capacity* list-decoding bound, for a prize-regime
Reed–Solomon code.

> For a rate-`1/2` Reed–Solomon code `RS[F, α, 128]` on a domain of size `256`, over any field with
> `2^128 ≤ |F| ≤ 2^256`, at the Singleton/capacity radius `δ = 1/2`:
>
>   `|Λ(RS, 1/2)|  >  ε*·|F|`,    `ε* = 2^{-128}`     (`rs_uptoCapacity_false_rate12_n256`).

So the list-decoding threshold `δ*` is strictly below capacity `1 − ρ = 1/2`. This refutes the
up-to-capacity list-decoding conjecture in the deployed regime ([CS25], [KK25], arXiv 2604.09724),
fully formalized.

## Proof

Chains the axiom-clean entropy-volume lower bound `CodingTheory.rs_lambda_ge_capacity_exponent`
(`|Λ| ≥ q^{E}/(n+1)`, `E = n·H_q(⌊δn⌋/n) − (n−k)`) with: the closed form of the capacity exponent
at rate `1/2` (`binEntropy(1/2) = log 2`); the resulting overflow at `n = 256` for the prize field
range (`1 < 119·log 2`); and an `rpow`/`logb` bridge.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. ePrint 2025/2046.
-/

namespace CodingTheory

open Real ListDecodable
open scoped NNReal ENNReal

/-- **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, `logb q (n1·εq) < E → εq < q^E/n1`. -/
theorem threshold_lt_pow_div (q : ℝ) (hq : 1 < q) (n1 : ℝ) (hn1 : 0 < n1)
    (εq : ℝ) (hεq : 0 < εq) (E : ℝ) (hE : Real.logb q (n1 * εq) < E) :
    εq < q ^ E / n1 := by
  have hA : 0 < n1 * εq := mul_pos hn1 hεq
  have hlt : n1 * εq < q ^ E := (Real.logb_lt_iff_lt_rpow hq hA).mp hE
  rw [lt_div_iff₀ hn1]; nlinarith [hlt]

/-- **Closed form of the capacity exponent at rate `1/2`.** -/
theorem capExp_half_mul_log (q : ℕ) (hq : 2 ≤ q) (n : ℝ) :
    ((n : ℝ) * qEntropy q (1/2) - n/2) * Real.log q
      = n * Real.log 2 - (n/2) * Real.log ((q:ℝ)/((q:ℝ)-1)) := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hqne : Real.log q ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hlogdiv : Real.log ((q:ℝ)/((q:ℝ)-1)) = Real.log q - Real.log ((q:ℝ)-1) :=
    Real.log_div hq0.ne' hq1.ne'
  have hhalf : Real.log ((1:ℝ)/2) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one]; ring
  unfold qEntropy
  simp only [Real.logb, show (1:ℝ) - 1/2 = 1/2 from by ring, hhalf, hlogdiv]
  field_simp
  ring

/-- **The overflow holds at `n = 256`, rate `1/2`, for the prize field range.** -/
theorem hover_core_n256 (q : ℝ) (hq1 : (2:ℝ)^128 ≤ q) (hq2 : q ≤ (2:ℝ)^256) :
    Real.log (257 * (q / 2^128)) < 256 * Real.log 2 - 128 * Real.log (q / (q - 1)) := by
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hq1
  have h2le : (2:ℝ) ≤ 2^128 := by
    have := pow_le_pow_right₀ (one_le_two : (1:ℝ) ≤ 2) (by norm_num : 1 ≤ 128); simpa using this
  have hq1' : (1:ℝ) < q := by linarith
  have hqm1 : (0:ℝ) < q - 1 := by linarith
  have hlog2 : (0.6931:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog257 : Real.log 257 ≤ 9 * Real.log 2 := by
    calc Real.log 257 ≤ Real.log (2^9) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 9 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hlogq : Real.log q ≤ 256 * Real.log 2 := by
    calc Real.log q ≤ Real.log (2^256) := Real.log_le_log hqpos hq2
      _ = 256 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hcorr : 128 * Real.log (q / (q - 1)) ≤ 1 := by
    have hle : Real.log (q / (q - 1)) ≤ q / (q - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsimp : q / (q - 1) - 1 = 1 / (q - 1) := by field_simp; ring
    have hfrac : 1 / (q - 1) ≤ 1 / 128 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith [hq1]
    calc 128 * Real.log (q / (q - 1)) ≤ 128 * (1 / (q - 1)) := by
            rw [hsimp] at hle; linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 128)]
      _ ≤ 128 * (1 / 128) := by linarith [mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ) ≤ 128)]
      _ = 1 := by norm_num
  have hsplit : Real.log (257 * (q / 2^128)) = Real.log 257 + Real.log q - 128 * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  rw [hsplit]
  nlinarith [hlog257, hlogq, hcorr, hlog2]

/-- **The up-to-capacity list-decoding bound is false (prize regime).** A rate-`1/2`
Reed–Solomon code on a size-`256` domain over a field with `2^128 ≤ |F| ≤ 2^256` has, at the
Singleton radius `δ = 1/2`, list size strictly exceeding `ε*·|F|` (`ε* = 2^{-128}`). Hence
`δ* < 1 − ρ`: the list-decoding threshold cannot reach capacity. -/
theorem rs_uptoCapacity_false_rate12_n256
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (α : Fin 256 ↪ F)
    (hq1 : (2:ℝ)^128 ≤ (Fintype.card F : ℝ)) (hq2 : (Fintype.card F : ℝ) ≤ 2^256) :
    ENNReal.ofReal ((1 / 2 ^ 128) * (Fintype.card F : ℝ))
      < (Lambda (ReedSolomon.code α 128 : Set (Fin 256 → F)) (1/2) : ENNReal) := by
  have hcard : Fintype.card (Fin 256) = 256 := Fintype.card_fin 256
  have h2le : (2:ℝ) ≤ 2^128 := by
    have := pow_le_pow_right₀ (one_le_two : (1:ℝ) ≤ 2) (by norm_num : 1 ≤ 128); simpa using this
  have hq2N : 2 ≤ Fintype.card F := by
    have : (2:ℝ) ≤ (Fintype.card F : ℝ) := le_trans h2le hq1
    exact_mod_cast this
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hqR1 : (1:ℝ) < q := lt_of_lt_of_le one_lt_two (le_trans h2le hq1)
  have hlogq : (0:ℝ) < Real.log q := Real.log_pos hqR1
  have hfloor : ⌊(1/2 : ℝ) * (Fintype.card (Fin 256) : ℝ)⌋₊ = 128 := by rw [hcard]; norm_num
  have hLB := rs_lambda_ge_capacity_exponent (F := F) α 128 (1/2)
    (by norm_num) (by norm_num) hq2N (by rw [hcard]; norm_num)
    (by rw [hfloor]; norm_num) (by rw [hfloor, hcard]; norm_num)
  rw [hfloor, hcard] at hLB
  norm_num at hLB
  -- hLB : ENNReal.ofReal (q ^ (256 * qEntropy (card F) (1/2) - 128) / 257) ≤ Lambda
  set E : ℝ := 256 * qEntropy (Fintype.card F) (1 / 2) - 128 with hEdef
  have hclosed : E * Real.log q = 256 * Real.log 2 - 128 * Real.log (q / (q - 1)) := by
    have h := capExp_half_mul_log (Fintype.card F) hq2N 256
    rw [hEdef, hqdef]; linear_combination h
  have hover : Real.log (257 * (q / 2 ^ 128)) < E * Real.log q := by
    rw [hclosed]; exact hover_core_n256 q (by rw [hqdef]; exact hq1) (by rw [hqdef]; exact hq2)
  have hlogb : Real.logb q (257 * (q / 2 ^ 128)) < E := by
    rw [Real.logb, div_lt_iff₀ hlogq]; exact hover
  have hεpos : (0:ℝ) < (1 / 2 ^ 128) * q := by positivity
  rw [show (257 : ℝ) * (q / 2 ^ 128) = 257 * ((1 / 2 ^ 128) * q) from by ring] at hlogb
  have hreal : (1 / 2 ^ 128) * q < q ^ E / 257 :=
    threshold_lt_pow_div q hqR1 257 (by norm_num) _ hεpos E hlogb
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal) hLB

#print axioms rs_uptoCapacity_false_rate12_n256

end CodingTheory
