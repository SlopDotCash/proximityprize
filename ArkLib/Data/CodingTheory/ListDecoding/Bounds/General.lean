/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ProximityPrize.Compatibility.ListSize
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Linear
import ArkLib.Data.CodingTheory.Basic.Entropy
import ProximityPrize.Extensions.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ListDecoding.JH01
import ArkLib.Data.CodingTheory.ListDecoding.AGL23Barrier
import ArkLib.Data.CodingTheory.ListDecoding.CZ25CapacityReduction
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.BKR06FiberCount
import ArkLib.ToMathlib.BKR06Injection
import ProximityPrize.Extensions.Data.CodingTheory.SubspaceDesign
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.Probability.Combinatorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# List-decoding bounds from ABF26 §3 — random RS domains & general lower bounds

Random Reed-Solomon domains (ABF26 §3.1, [AGL24]) and the general §3.2 lower-bound
statements, including the MS77 Hamming-ball-volume ingredient and the `ABF26C38`
development. Part 1 of the `Bounds` split; see the `Bounds.lean` umbrella for the
full overview and quantification conventions.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ListDecodable

/-! ## Random Reed-Solomon domains — ABF26 §3.1 ([AGL24]) -/

section RandomReedSolomon

/-- **ABF26 Theorem 3.6 [AGL24 Thm 1.1], statement front door.**

For a finite field `F`, a positive length `n ≤ |F|`, and a uniformly sampled size-`n`
evaluation domain `L ⊆ F`, the random Reed-Solomon code `RS[F,L,k]` is list-decodable at the
capacity-near radius `1 - k/n - η` with failure probability at most `failure`.

The theorem's quantitative choices for `listBound` and `failure` are intentionally explicit
parameters here: this definition records the faithful probability space and RS-family target,
while the AGL24 first-moment/probabilistic proof remains external. -/
noncomputable def random_rs_list_decoding
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal)
    (_hn_pos : 0 < n) (hn : n ≤ Fintype.card F) : Prop := by
  classical
  exact
    Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
      ¬ (Lambda
          ((ReedSolomon.code (Probability.SizeSubset.toEmbedding L) k : Set (L → F)))
          (1 - (k : ℝ) / (n : ℝ) - η) ≤ (listBound : ℕ∞))] ≤ failure
  -- Missing ingredient: AGL24's random-RS near-capacity list-decoding theorem.  The
  -- probability space is now in-tree (`uniformSizeSubsetOfLe`), but the proof bounding the
  -- bad-domain probability and instantiating the paper's concrete `listBound`/`failure`
  -- parameters is still external.

end RandomReedSolomon

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/- The canonical ListDecodability.Bounds.Linear owner provides the volume bounds.
The wrappers below retain the downstream list-size API through the finite-alphabet bridge. -/

/-- **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size for an arbitrary
finite-alphabet code:

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |A|`, `n = |ι|`, and the explicit cardinality hypothesis gives `|C| = q^k`.
**Proven** by the paper's averaging argument (fulltext §3, [Eli57]):
the maximised list size dominates the mean over received words, and double counting gives
`∑_f |Λ(C,δ,f)| = ∑_{c∈C} Vol_q(δ,n) = q^k · Vol_q(δ,n)`, so the max is `≥ Vol/q^{n-k}`.
Uses `hammingBallVolume` (ABF26 D2.4) and `hammingBallVolume_eq_ncard_hammingBall` from
`HammingBallVolume.lean`. Linearity is not used; the field-linear specialization below supplies
the cardinality hypothesis using `Module.card_eq_pow_finrank`. -/
theorem lambda_ge_elias_volume_eli57
    {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℝ)
          / (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - k))
      ≤ (Lambda C δ : ENNReal) := by
  rw [ProximityPrize.Compatibility.legacyLambda_eq_canonical]
  exact lambda_ge_elias_volume C k hcard δ _hδ_pos

/-- **ABF26 Lemma 3.7 [Eli57] for a field-linear code**, using the canonical
`linear_lambda_ge_elias_volume`. -/
theorem linear_lambda_ge_elias_volume_eli57
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  rw [ProximityPrize.Compatibility.legacyLambda_eq_canonical]
  exact linear_lambda_ge_elias_volume C δ _hδ_pos

/-! ### MS77 Hamming-ball volume bound (ingredient (★) for C3.8 below).

The classical MacWilliams–Sloane volume estimate is stated for an *integer* radius
`δ·n`. Off the lattice `δ·n ∈ ℕ` the inequality `q^{n·H_q(δ)}/√(8nδ(1−δ)) ≤ Vol_q(δ,n)`
is genuinely **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at
`δ = k/n`, via `⌊δn⌋`), while the LHS is strictly increasing in `δ`. Concretely with
`q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. (Cf. the `subspaceDesign_tau_lower`
countermodel-documented style.) So the faithful MS77 statement carries the lattice
hypothesis `δ·n = ⌊δ·n⌋₊` — the minimal correct reading of [MS77, Ch.10 Lem 7].

The lattice volume bound uses the canonical `qary_shell_entropy_lower` and includes the shell at
`⌊δ·n⌋` in the Hamming-ball volume. The auxiliary Stirling and binomial identities remain available
under their historical names. -/

namespace ABF26C38

open scoped Real Nat Topology
open Real Stirling Filter

-- ===== Robbins upper bound (proven) =====
theorem robbins_upper {m : ℕ} (hm : m ≠ 0) :
    stirlingSeq m ≤ √π * Real.exp (1 / (12 * m)) := by
  set H : ℕ → ℝ := fun n =>
      Real.log (stirlingSeq (n + 1)) - Real.log (√π) -
        1 / (12 * ((n : ℝ) + 1))
    with hH
  have hsqrtπ_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hmono : Monotone H := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [hH]
    have hdiff := log_stirlingSeq_diff_le (n + 1)
    have htel : (1 : ℝ) / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp; ring
    have hdiff' : Real.log (stirlingSeq (n + 1)) - Real.log (stirlingSeq (n + 2)) ≤
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      rw [← htel]; convert hdiff using 2; push_cast; ring
    change Real.log (stirlingSeq (n + 1)) - Real.log (√π) -
          1 / (12 * ((n : ℝ) + 1)) ≤
        Real.log (stirlingSeq (n + 1 + 1)) - Real.log (√π) -
          1 / (12 * (((n + 1 : ℕ) : ℝ) + 1))
    have hidx : (n + 1 + 1) = (n + 2) := by ring
    rw [hidx]
    have hpush : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hpush]; linarith [hdiff']
  have htend : Tendsto H atTop (𝓝 (0 : ℝ)) := by
    have hss : Tendsto (fun n : ℕ => stirlingSeq (n + 1)) atTop (𝓝 (√π)) :=
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
    have hlog : Tendsto (fun n : ℕ => Real.log (stirlingSeq (n + 1))) atTop (𝓝 (Real.log (√π))) :=
      (Real.continuousAt_log hsqrtπ_pos.ne').tendsto.comp hss
    have hrec : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have : Tendsto (fun n : ℕ => (1 / 12) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((1/12) * 0)) :=
        hbase.const_mul (1/12)
      simp only [mul_zero] at this
      refine this.congr (fun n => ?_)
      rw [mul_one_div, one_div, one_div, mul_inv]; ring
    have hcomb : Tendsto (fun n : ℕ =>
        Real.log (stirlingSeq (n + 1)) - Real.log (√π) - 1 / (12 * ((n : ℝ) + 1)))
        atTop (𝓝 (Real.log (√π) - Real.log (√π) - 0)) :=
      (hlog.sub_const _).sub hrec
    have hz : Real.log (√π) - Real.log (√π) - 0 = 0 := by ring
    rw [hz] at hcomb; exact hcomb
  have hle := hmono.ge_of_tendsto htend
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj := hle j
  simp only [hH] at hj
  have hlog_le : Real.log (stirlingSeq (j + 1)) ≤ Real.log (√π) + 1 / (12 * ((j : ℝ) + 1)) := by
    linarith
  have hss_pos : 0 < stirlingSeq (j + 1) := stirlingSeq'_pos j
  have hrhs_pos : 0 < √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by positivity
  have hgoal : stirlingSeq (j + 1) ≤ √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by
    rw [← Real.log_le_log_iff hss_pos hrhs_pos]
    rw [Real.log_mul hsqrtπ_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [hlog_le]
  have hcast_m : ((((j : ℕ) + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) := by push_cast; ring
  rw [hcast_m]; exact hgoal

-- ===== closed forms =====
theorem ss2_eq : stirlingSeq 2 = Real.exp 1 ^ 2 / 4 := by
  have h : stirlingSeq 2 = 2 / (√4 * (2 / Real.exp 1) ^ 2) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have h4 : √(4 : ℝ) = 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp; ring

theorem ss3_eq : stirlingSeq 3 = 2 * Real.exp 1 ^ 3 / (9 * √6) := by
  have h : stirlingSeq 3 = 6 / (√6 * (3 / Real.exp 1) ^ 3) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have h6 : √(6:ℝ) ≠ 0 := by positivity
  field_simp; ring

-- ===== generic numeric =====
theorem sqrtpi_exp_le_two : √π * Real.exp (1/9) ≤ 2 := by
  have he : Real.exp (1/9) ≤ 9/8 := by
    have h : (1 : ℝ) - (1/9) ≤ Real.exp (-(1/9)) := by
      have := Real.add_one_le_exp (-(1/9 : ℝ)); linarith
    rw [Real.exp_neg] at h
    have hexp_pos : 0 < Real.exp (1/9) := Real.exp_pos _
    have hmul : (1 - 1/9) * Real.exp (1/9) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hexp_pos.le
      rwa [inv_mul_cancel₀ hexp_pos.ne'] at this
    nlinarith [hexp_pos, hmul]
  have hs : √π ≤ 16/9 := by
    have hπ : π < 3.15 := Real.pi_lt_d2
    have : π ≤ (16/9 : ℝ)^2 := by rw [show ((16:ℝ)/9)^2 = 256/81 by norm_num]; nlinarith
    calc √π ≤ √((16/9:ℝ)^2) := Real.sqrt_le_sqrt this
      _ = 16/9 := by rw [Real.sqrt_sq (by norm_num)]
  have he_nonneg : 0 ≤ Real.exp (1/9) := (Real.exp_pos _).le
  calc √π * Real.exp (1/9) ≤ (16/9) * (9/8) := by
        apply mul_le_mul hs he he_nonneg (by norm_num)
    _ = 2 := by norm_num

-- ===== CORE LEMMA =====
-- For k ≥ 1, j ≥ 1: stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k+j)
theorem core_stirling_add {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k + j) :=
  stirlingSeq_mul_le_two_mul_add k j

-- ===== Stirling/binomial collapse for the MS77 reduction =====

-- factorial in terms of stirlingSeq, for m ≥ 1
theorem fact_eq_ss {m : ℕ} (hm : 1 ≤ m) :
    (m ! : ℝ) = stirlingSeq m * (√(2 * m) * (m / Real.exp 1) ^ m) := by
  rw [stirlingSeq]
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < √(2 * (m:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hden : √(2 * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  field_simp

-- radical collapse: √(8Kj/(K+j)) * √(2(K+j)) = 2 * (√(2K) * √(2j))
theorem radical_collapse (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j))
      = 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hKjmul : (0:ℝ) ≤ (K:ℝ) * j := by positivity
  -- LHS = √(8Kj/(K+j) · 2(K+j)) = √(16Kj) = 4 √(Kj)
  have hL : √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j)) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (8 * (K:ℝ) * j / (K + j) * (2 * (K + j))) = 16 * (K * j) by field_simp; ring]
    rw [show (16 : ℝ) * ((K:ℝ) * j) = (4:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  -- RHS = 2 √(2K·2j) = 2 √(4Kj) = 4 √(Kj)
  have hR : 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 * (K:ℝ) * (2 * j)) = (2:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  rw [hL, hR]

-- Power identity splitting `((K+j)/e)^(K+j)` into binomial and Stirling-scale factors.
theorem power_identity (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    (((K:ℝ) + j) / Real.exp 1) ^ (K + j)
      = ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j)
        * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [pow_add]
  rw [show ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j)
        * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j)
      = ((((K:ℝ)+j)/K) * ((K:ℝ) / Real.exp 1))^K
        * ((((K:ℝ)+j)/j) * ((j:ℝ) / Real.exp 1))^j by
        rw [mul_pow, mul_pow]; ring]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

-- choose as a real ratio of factorials
theorem choose_real (K j : ℕ) :
    (Nat.choose (K + j) K : ℝ) = ((K + j)! : ℝ) / ((K ! : ℝ) * (j ! : ℝ)) := by
  have h : Nat.choose (K + j) K * K ! * j ! = (K + j)! := by
    have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right K j)
    rwa [Nat.add_sub_cancel_left] at h0
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hcast : ((Nat.choose (K + j) K : ℝ) * (K ! : ℝ)) * (j ! : ℝ) = ((K + j)! : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this
    linarith [this]
  field_simp
  linarith [hcast]

-- master equation
theorem master_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose (K + j) K : ℝ)
      = (2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j))
        * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hssK : 0 < stirlingSeq K := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    exact stirlingSeq'_pos K'
  have hssj : 0 < stirlingSeq j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact stirlingSeq'_pos j'
  -- expand choose and factorials
  rw [choose_real]
  rw [fact_eq_ss (m := K + j) (by omega), fact_eq_ss (m := K) hK, fact_eq_ss (m := j) hj]
  -- handle radical and power separately.  Push casts on (K+j).
  have hcast_add : (((K + j : ℕ)) : ℝ) = (K:ℝ) + j := by push_cast; ring
  rw [hcast_add]
  -- Now substitute the power identity for ((K+j)/e)^(K+j).
  rw [power_identity K j hK hj]
  -- And the radical collapse.
  -- LHS is reduced by splitting the power term and collapsing the radical factor.
  -- Goal is an equality of reals; field_simp + the radical_collapse relation + ring.
  have hrad := radical_collapse K j hK hj
  -- denominators nonzero
  have hpowK : ((K:ℝ) / Real.exp 1) ^ K ≠ 0 := by positivity
  have hpowj : ((j:ℝ) / Real.exp 1) ^ j ≠ 0 := by positivity
  have hsqK : √(2 * (K:ℝ)) ≠ 0 := by positivity
  have hsqj : √(2 * (j:ℝ)) ≠ 0 := by positivity
  -- generalize the radicals AND the power terms so field_simp can't distribute inside them
  set a := √(2 * (K:ℝ)) with ha
  set b := √(2 * (j:ℝ)) with hb
  set c := √(2 * ((K:ℝ) + j)) with hc
  set d := √(8 * (K:ℝ) * j / (K + j)) with hd
  set P : ℝ := (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j with hP
  set eK : ℝ := ((K:ℝ) / Real.exp 1) ^ K with heK
  set ej : ℝ := ((j:ℝ) / Real.exp 1) ^ j with hej
  -- now LHS = d * (ss(K+j) * (c * (P * (eK * ej))) / (ss K * (a * eK) * (ss j * (b * ej))))
  -- RHS = 2 ss(K+j)/(ss K ss j) * P; hrad : d * c = 2*(a*b)
  have heK_ne : eK ≠ 0 := by rw [heK]; positivity
  have hej_ne : ej ≠ 0 := by rw [hej]; positivity
  -- field_simp clears the (now-opaque) factors; relation hrad : d*c = 2*(a*b)
  field_simp
  linear_combination (stirlingSeq (K + j) * P) * hrad

-- B_eq: exp((K+j)·(-δ log δ - (1-δ) log(1-δ))) = ((K+j)/K)^K · ((K+j)/j)^j, δ = K/(K+j)
theorem B_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    Real.exp (((K + j : ℕ) : ℝ) * (-( (K:ℝ)/(K+j)) * Real.log ((K:ℝ)/(K+j))
        - (1 - (K:ℝ)/(K+j)) * Real.log (1 - (K:ℝ)/(K+j))))
      = (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hcast : (((K + j : ℕ) : ℝ)) = (K:ℝ) + j := by push_cast; ring
  rw [hcast]
  -- 1 - K/(K+j) = j/(K+j)
  have h1d : (1 : ℝ) - (K:ℝ)/(K+j) = (j:ℝ)/(K+j) := by field_simp; ring
  rw [h1d]
  -- the exponent = K·log((K+j)/K) + j·log((K+j)/j)
  have hlogK : Real.log ((K:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/K) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hlogj : Real.log ((j:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/j) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [hlogK, hlogj]
  -- exponent: (K+j)·(-(K/(K+j))·(-log((K+j)/K)) - (j/(K+j))·(-log((K+j)/j)))
  --         = K·log((K+j)/K) + j·log((K+j)/j)
  have hexp_simp : ((K:ℝ) + j) * (-((K:ℝ)/(K+j)) * (-Real.log (((K:ℝ)+j)/K))
      - (j:ℝ)/(K+j) * (-Real.log (((K:ℝ)+j)/j)))
      = (K:ℝ) * Real.log (((K:ℝ)+j)/K) + (j:ℝ) * Real.log (((K:ℝ)+j)/j) := by
    field_simp; ring
  rw [hexp_simp, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]

-- ===== core lemma (proven separately, restate signature for use) =====

-- ===== entropy identity =====

-- ===== entropy/power identity =====
theorem qpow_eq_exp (q : ℕ) (n : ℕ) (δ : ℝ) (hq : 2 ≤ q) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ)
      = Real.exp ((n:ℝ) * (δ * Real.log ((q:ℝ)-1) - δ * Real.log δ - (1-δ) * Real.log (1-δ))) := by
  have hqpos : (0:ℝ) < q := by positivity
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log q ≠ 0 := by have := Real.log_pos hq1; linarith
  rw [Real.rpow_def_of_pos hqpos]
  congr 1
  rw [qEntropy_eq_logb_form]
  simp only [Real.logb]
  field_simp

-- ===== FINAL: MS77 lattice bound (★) =====
-- For q ≥ 2, 0 < δ < 1, n ≥ 1, lattice δ*n = ⌊δ*n⌋₊:
--   q^{n·qEntropy q δ} / √(8nδ(1-δ)) ≤ hammingBallVolume q δ n
theorem ms77_lattice (q n : ℕ) (δ : ℝ)
    (hq : 2 ≤ q) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hlat : δ * n = (⌊δ * n⌋₊ : ℝ)) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ) / (8 * (n:ℝ) * δ * (1 - δ)) ^ ((1:ℝ)/2)
      ≤ (hammingBallVolume q δ n : ℝ) := by
  let d := ⌊δ * (n : ℝ)⌋₊
  have hshell : Nat.choose n d * (q - 1) ^ d ≤ hammingBallVolume q δ n := by
    unfold hammingBallVolume
    exact Finset.single_le_sum
      (s := Finset.range (d + 1)) (f := fun i => Nat.choose n i * (q - 1) ^ i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self d))
  exact (qary_shell_entropy_lower q n d δ hq hlat.symm).trans (by exact_mod_cast hshell)

end ABF26C38


/-- **ABF26 Corollary 3.8.** Volume-based lower bound on list size for an arbitrary code over a
nontrivial finite alphabet, using the MS77 volume estimate
`Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2). **FULLY PROVEN** (axioms ⊆ {propext, Classical.choice,
Quot.sound}); no `sorry`, under the lattice hypothesis `hlat` documented next.
The stronger `[Nontrivial A]` assumption is load-bearing here because `qEntropy` divides by
`Real.log q`; the Elias core above needs only `[Nonempty A]` and therefore permits `q = 1`.

**Lattice hypothesis (documented statement repair).** The MS77 estimate `(★)` below is a
classical lemma for an **integer** radius `δ·n`. As literally stated for arbitrary
`0 < δ < 1` it is **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at the
lattice points `δ = k/n`, via the floor `⌊δn⌋`), while the LHS `q^{n·H_q(δ)}/√(8nδ(1-δ))` is
strictly increasing in `δ`; between lattice points the LHS overtakes the frozen volume.
Countermodel `q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, so `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. The faithful reading of
[MS77, Ch.10 Lem 7] therefore carries the minimal hypothesis `hlat : δ·n = ⌊δ·n⌋₊`
(equivalently `δ = ⌊δn⌋/n`). This mirrors the documented-countermodel house style of
`subspaceDesign_tau_lower` / the `RationalFunctions` statement-bug class. At lattice points
the bound is TRUE (numerically verified, zero failures over `q ∈ {2,7,101,1009,65537}`,
`n ≤ 160`) and is proven below.

**Proof architecture.** Since L3.7 (`lambda_ge_elias_volume_eli57`, PROVEN in-tree)
gives `Vol_q(δ,n) / q^{n-k} ≤ |Λ(C,δ)|`, this corollary follows by transitivity from the
single real inequality

  `q^{n·H_q(δ)} / √(8·n·δ·(1-δ)) ≤ Vol_q(δ, n)`         (★)

The reduction `(★) ⟹ C3.8` (with `n ≠ 0`): `ρ = k/n ⟹ n·ρ = k`, so the C3.8 numerator
exponent `n·(ρ-1+H_q) = k - n + n·H_q`, giving `q^{n(ρ-1+H_q)} = q^{n·H_q} / q^{n-k}`; hence
the C3.8 real RHS `= (q^{n·H_q}/√(8nδ(1-δ))) / q^{n-k} ≤ Vol / q^{n-k}` by (★), which is
exactly the L3.7 real bound, and `ENNReal.ofReal` is monotone.

At the lattice point `K = ⌊δn⌋ = δn`, `ABF26C38.ms77_lattice` obtains (★) from
`qary_shell_entropy_lower` for the shell `C(n,K)(q-1)^K`, which is at most the full volume.
The canonical shell estimate uses `stirlingSeq_mul_le_two_mul_add` for its factor of two.
[MS77, MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 10, Lemma 7]. -/
theorem lambda_ge_entropy_volume_of_floor_eq
    {A : Type} [Fintype A] [Nontrivial A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ)) :
    let q : ℕ := Fintype.card A
    let n : ℕ := Fintype.card ι
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda C δ : ENNReal) := by
  rw [ProximityPrize.Compatibility.legacyLambda_eq_canonical]
  exact lambda_ge_entropy_volume C k hcard δ _hδ_pos _hδ_lt
    ⟨⌊δ * (Fintype.card ι : ℝ)⌋₊, hlat.symm⟩

/-- **ABF26 Corollary 3.8 for a field-linear code.** This preserves the original API as a
specialization of `lambda_ge_entropy_volume`, with the code cardinality supplied by
`Module.card_eq_pow_finrank`. -/
theorem linear_lambda_ge_entropy_volume_of_floor_eq
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ)) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  rw [ProximityPrize.Compatibility.legacyLambda_eq_canonical]
  exact linear_lambda_ge_entropy_volume C δ
    ⟨⌊δ * (Fintype.card ι : ℝ)⌋₊, hlat.symm⟩

/- **ST20 plurality-center averaging core (in-tree, fully proven).**
Given `ℓ + 1` words `c₀, …, c_ℓ : ι → F`, the *plurality center* `z`, obtained by choosing at
each coordinate a value attained by at least one of the `cⱼ` (e.g. the most frequent one),
satisfies the aggregate-distance bound

  `∑ⱼ d_H(z, cⱼ) ≤ ℓ · n`,    where `n = |ι|`.

This is the genuinely-combinatorial half of [ST20 Thm 1.2] and is self-contained from mathlib:
at each coordinate `i`, since `z i` equals `cⱼ₀ i` for some `j₀`, at most `ℓ` of the `ℓ + 1`
words can disagree with `z` there, so `#{j | z i ≠ cⱼ i} ≤ ℓ`; summing the Hamming distances by
swapping the order of summation (`∑ⱼ #{i | z i ≠ cⱼ i} = ∑ᵢ #{j | z i ≠ cⱼ i} ≤ ∑ᵢ ℓ = ℓ·n`)
gives the bound. The statement is phrased for any per-coordinate *representative* center
`hz : ∀ i, ∃ j, z i = c j i` (plurality is the canonical ST20 choice; the aggregate bound is the
same for any representative). The existence of such a `z` (take `z = c 0`) is immediate.

This proves the *averaging* ingredient (b) of T3.9's reduction. By itself it does not close T3.9:
the ST20 list-decoding bound additionally needs the ℓ-fold-agreement pigeonhole (ingredient (a))
that selects `ℓ + 1` codewords pairwise agreeing on a *common* `≥ n − s` coordinate set, so that
the center is within relative distance `δ` of ALL of them simultaneously. When this note was
written that kernel/partition ingredient was described as an external wall absent in tree. **It
is no longer absent:** the helpers below (range-fiber and kernel extraction, the block partition
and the distance bound) and `linear_C_le_generalized_singleton_st20` give the full proof of the
linear T3.9 bound (under its lattice and meaningful-radius hypotheses `hlat`, `ha_le`). -/
/-- **ST20 plurality-center averaging core, alphabet-generic.**
Given `ℓ + 1` words `c₀, …, c_ℓ : ι → A` over any finite alphabet `A`, the
*representative* centre `z` (here `z = c₀`) satisfies the aggregate-distance bound

  `∑ⱼ d_H(z, cⱼ) ≤ ℓ · n`,    where `n = |ι|`.

The argument is purely combinatorial: at each coordinate `i`, `z i = c₀ i` matches at
least one of the `ℓ + 1` words, so at most `ℓ` can disagree there; summing over `i`
and swapping `∑ⱼ∑ᵢ = ∑ᵢ∑ⱼ` gives the bound. This is the ST20 averaging ingredient (b)
stated for an arbitrary alphabet; `exists_representative_center_sum_hammingDist_le` below
is its field-linear specialization (no new mathematics — same witness `z = c₀`). -/
theorem exists_representative_center_sum_hammingDist_le_generic {A : Type} [Fintype A]
    [DecidableEq A] (ℓ : ℕ) (c : Fin (ℓ + 1) → (ι → A)) :
    ∃ z : ι → A, (∑ j, hammingDist z (c j)) ≤ ℓ * Fintype.card ι := by
  refine ⟨c 0, ?_⟩
  have hdist : ∀ j, hammingDist (c 0) (c j)
      = ∑ i : ι, ite ((c 0) i ≠ c j i) 1 0 := by
    intro j
    rw [hammingDist]
    exact Finset.card_filter (fun i => (c 0) i ≠ c j i) Finset.univ
  rw [Finset.sum_congr rfl (fun j _ => hdist j)]
  rw [Finset.sum_comm]
  have hinner : ∀ i : ι, (∑ j, ite ((c 0) i ≠ c j i) 1 0) ≤ ℓ := by
    intro i
    rw [← Finset.card_filter (fun j => (c 0) i ≠ c j i) Finset.univ]
    have hsub : {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}
        ⊆ (Finset.univ : Finset (Fin (ℓ + 1))).erase 0 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hj.2 rfl
    calc {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}.card
        ≤ ((Finset.univ : Finset (Fin (ℓ + 1))).erase 0).card := Finset.card_le_card hsub
      _ = Fintype.card (Fin (ℓ + 1)) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      _ = ℓ := by rw [Fintype.card_fin]; omega
  calc (∑ i : ι, ∑ j, ite ((c 0) i ≠ c j i) 1 0)
      ≤ ∑ _i : ι, ℓ := Finset.sum_le_sum (fun i _ => hinner i)
    _ = ℓ * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- **ST20 plurality-center averaging core, field-linear specialization.**
Wrapper of `exists_representative_center_sum_hammingDist_le_generic` at `A = F`. -/
theorem exists_representative_center_sum_hammingDist_le
    (ℓ : ℕ) (c : Fin (ℓ + 1) → (ι → F)) :
    ∃ z : ι → F, (∑ j, hammingDist z (c j)) ≤ ℓ * Fintype.card ι :=
  exists_representative_center_sum_hammingDist_le_generic (A := F) ℓ c

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2], linear refinement.** Generalized Singleton bound
for list decoding. For a linear code `C ⊆ F^n` with `0 < ℓ < |F|`, `δ ∈ (0,1)` and
`|Λ(C, δ)| ≤ ℓ`:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`.

The canonical `linear_card_le_generalized_singleton` formalizes Shangguan–Tamo's pigeonhole and
partition argument (SIAM J. Comput. 52(3), eq. (2)). The finite-alphabet list-size bridge supplies
its list-size hypothesis for this API.

**SIGFIX (two hypotheses added vs. the bare ABF26 statement — both are faithful to ST20
and necessary).** The unparameterised statement is *false*: e.g. `C = {0}` (always
`(δ,ℓ)`-list-decodable) with `ℓ = 1`, `δ` near `1` and large `n` gives `a = ⌊(ℓ+1)/ℓ·δ·n⌋
> n`, so the RHS `|F|^{n-a} < 1` while `|C| = 1`. The two added hypotheses are exactly the
regime in which ST20 prove (and state) the bound:
* `hlat` — the **lattice condition** `δ·n = ⌊δ·n⌋` (i.e. `δ·n ∈ ℤ`). ST20 explicitly
  "assume `rn` is an integer so the floor can be removed"; off the lattice the per-codeword
  distance `a - ⌊a/(ℓ+1)⌋` can exceed `⌊δ·n⌋` and the bound genuinely fails. This mirrors
  the lattice fix applied to the sibling MS77 volume bound (C3.8) in this file.
* `ha_le` — the **meaningful-radius regime** `a ≤ n` (equivalent to `δ ≤ ℓ/(ℓ+1)`, the
  Singleton radius regime; for larger `δ` the bound is vacuous/false as above).
Sound and `sorryAx`-free (`#print axioms`: only `propext, Classical.choice, Quot.sound`). -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ))
    (ha_le : ⌊((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι⌋₊ ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  rw [ProximityPrize.Compatibility.legacyLambda_eq_canonical] at _hΛ
  exact linear_card_le_generalized_singleton C ℓ δ _hℓ_lt
    ⟨⌊δ * (Fintype.card ι : ℝ)⌋₊, hlat.symm⟩ ha_le _hΛ

end LowerBounds_General

end CodingTheory
