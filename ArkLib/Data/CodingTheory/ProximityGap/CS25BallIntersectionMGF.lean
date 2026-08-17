/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionBound

/-!
# CS25 #82, deliverable 2: the moment generating function (Chernoff) ball-intersection bound

The combinatorial ball-intersection decay (`CS25BallIntersectionBudget`) loses a factor of `q^{wt e}`
on the support of `e`, so it is tight only over `𝔽₂`.  This file gives the **tight** bound for every
field, by importing the *moment generating function / Chernoff* method from probability theory:

  `θ^{2r} · I(e) ≤ (1 + (q−1)θ²)^{n−wt(e)} · (2θ + (q−2)θ²)^{wt(e)}`   for all `θ ∈ [0,1]`,

with `I(e) = jointCoverCount δ 0 e = |B(0,δ) ∩ B(e,δ)|`, `r = ⌊δ·n⌋`, `q = |F|`, `n = |ι|`.

The proof is the standard Chernoff argument, which crucially **factors over coordinates** and so
sidesteps the intractable multinomial entirely:

* indicator bound `θ^{2r}·1[wt w ≤ r ∧ wt(w−e) ≤ r] ≤ θ^{wt w}·θ^{wt(w−e)}` (since `θ ≤ 1`);
* `∑_w θ^{wt w + wt(w−e)} = ∏_i ∑_{x∈F} θ^{[x≠0]}θ^{[x≠eᵢ]}` (the generating function factorizes
  by `Finset.prod_univ_sum`);
* each coordinate sum is `1 + (q−1)θ²` (off `supp e`) or `2θ + (q−2)θ²` (on `supp e`).

Optimizing `θ` in `[0,1]` recovers the exact CS25 large-deviation exponent for the ball intersection
— the input to the second-moment band, now with the correct `q`-dependence.

## Main results

* `per_coord_zero` / `per_coord_ne` — the per-coordinate generating-function sums.
* `mgf_factor` — the coordinate factorization `∑_w θ^{wt w + wt(w−e)} = ∏_i ∑_x …`.
* `jointCoverCount_mgf_le` — the Chernoff ball-intersection bound, valid for every `θ ∈ [0,1]`.
-/

set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false


open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section PerCoord

variable {F : Type*} [Fintype F] [DecidableEq F] [Zero F]

/-- `θ^{[P]} = if P then θ else 1`, the indicator-power identity. -/
theorem coord_summand (θ : ℝ) (c x : F) :
    θ ^ (if x ≠ 0 then 1 else 0) * θ ^ (if x ≠ c then 1 else 0)
      = (if x ≠ 0 then θ else 1) * (if x ≠ c then θ else 1) := by
  by_cases h0 : x ≠ 0 <;> by_cases hc : x ≠ c <;> simp [h0, hc]

/-- Linearization of an indicator power: `if P then θ else 1 = 1 + (θ−1)·[P]`. -/
theorem factor_id (θ : ℝ) (P : Prop) [Decidable P] :
    (if P then θ else 1) = 1 + (θ - 1) * (if P then (1 : ℝ) else 0) := by
  by_cases h : P <;> simp [h]

/-- `∑_x [x ≠ c]·θ = (q−1)·θ`. -/
theorem sum_ite_ne (θa : ℝ) (c : F) :
    ∑ x : F, (if x ≠ c then θa else 0) = ((Fintype.card F : ℝ) - 1) * θa := by
  classical
  haveI : Nonempty F := ⟨c⟩
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [← Finset.sum_filter, Finset.filter_ne', Finset.sum_const,
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, nsmul_eq_mul, Nat.cast_sub hpos]
  push_cast; ring

/-- `∑_x [x ≠ c] = q − 1`. -/
theorem sum_indic_ne (c : F) :
    ∑ x : F, (if x ≠ c then (1 : ℝ) else 0) = (Fintype.card F : ℝ) - 1 := by
  rw [sum_ite_ne 1 c]; ring

/-- `∑_x [x ≠ 0]·[x ≠ c] = q − 2` for `c ≠ 0`. -/
theorem sum_ite_pair (c : F) (hc : c ≠ 0) :
    ∑ x : F, (if x ≠ (0 : F) then (1 : ℝ) else 0) * (if x ≠ c then (1 : ℝ) else 0)
      = (Fintype.card F : ℝ) - 2 := by
  classical
  have hconv : ∀ x : F, (if x ≠ (0 : F) then (1 : ℝ) else 0) * (if x ≠ c then (1 : ℝ) else 0)
      = (if (x ≠ (0 : F) ∧ x ≠ c) then (1 : ℝ) else 0) := by
    intro x; by_cases h0 : x ≠ (0 : F) <;> by_cases hcx : x ≠ c <;> simp [h0, hcx]
  simp_rw [hconv]
  rw [Finset.sum_boole]
  have hcard2 : ({0, c} : Finset F).card = 2 := Finset.card_pair (Ne.symm hc)
  have h2le : 2 ≤ Fintype.card F := by
    rw [← hcard2, ← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have hset : (univ.filter (fun x : F => x ≠ 0 ∧ x ≠ c)) = ({0, c} : Finset F)ᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton, not_or]
  rw [hset, Finset.card_compl, hcard2, Nat.cast_sub h2le]; push_cast; ring

/-- **Off-support coordinate sum.** `∑_x θ^{[x≠0]}·θ^{[x≠0]} = 1 + (q−1)θ²`. -/
theorem per_coord_zero (θ : ℝ) :
    ∑ x : F, (if x ≠ (0 : F) then θ else 1) * (if x ≠ (0 : F) then θ else 1)
      = 1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2 := by
  classical
  have hpt : ∀ x : F, (if x ≠ (0 : F) then θ else 1) * (if x ≠ (0 : F) then θ else 1)
      = 1 + (2 * (θ - 1) + (θ - 1) ^ 2) * (if x ≠ (0 : F) then (1 : ℝ) else 0) := by
    intro x; by_cases h : x ≠ (0 : F) <;> simp [h] <;> ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, sum_indic_ne (0 : F)]
  ring

/-- **On-support coordinate sum.** `∑_x θ^{[x≠0]}·θ^{[x≠c]} = 2θ + (q−2)θ²` for `c ≠ 0`. -/
theorem per_coord_ne (θ : ℝ) (c : F) (hc : c ≠ 0) :
    ∑ x : F, (if x ≠ (0 : F) then θ else 1) * (if x ≠ c then θ else 1)
      = 2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2 := by
  classical
  have hpt : ∀ x : F, (if x ≠ (0 : F) then θ else 1) * (if x ≠ c then θ else 1)
      = 1 + (θ - 1) * (if x ≠ (0 : F) then (1 : ℝ) else 0)
        + (θ - 1) * (if x ≠ c then (1 : ℝ) else 0)
        + (θ - 1) ^ 2 * ((if x ≠ (0 : F) then (1 : ℝ) else 0) * (if x ≠ c then (1 : ℝ) else 0)) := by
    intro x; rw [factor_id θ (x ≠ (0 : F)), factor_id θ (x ≠ c)]; ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_indic_ne (0 : F), sum_indic_ne c, sum_ite_pair c hc]
  ring

end PerCoord

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Coordinate factorization (the generating function).**
`∑_{w} θ^{wt w + Δ₀(w,e)} = ∏_i ∑_{x∈F} θ^{[x≠0]}θ^{[x≠eᵢ]}`.  This is where the Chernoff method
beats the multinomial: the joint weight enumerator factorizes over coordinates. -/
theorem mgf_factor (θ : ℝ) (e : ι → F) :
    ∑ w : ι → F, θ ^ (hammingNorm w + hammingDist w e)
      = ∏ i : ι, ∑ x : F, (θ ^ (if x ≠ 0 then 1 else 0) * θ ^ (if x ≠ e i then 1 else 0)) := by
  classical
  have step4 : ∀ w : ι → F,
      θ ^ (hammingNorm w + hammingDist w e)
        = ∏ i : ι, (θ ^ (if w i ≠ 0 then 1 else 0) * θ ^ (if w i ≠ e i then 1 else 0)) := by
    intro w
    have hN : hammingNorm w = ∑ i : ι, (if w i ≠ 0 then 1 else 0) := by
      rw [hammingNorm, Finset.card_filter]
    have hD : hammingDist w e = ∑ i : ι, (if w i ≠ e i then 1 else 0) := by
      rw [hammingDist, Finset.card_filter]
    rw [hN, hD, ← Finset.sum_add_distrib, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [pow_add]
  simp_rw [step4]
  rw [Finset.prod_univ_sum (fun _ => (univ : Finset F))
    (fun i x => θ ^ (if x ≠ 0 then 1 else 0) * θ ^ (if x ≠ e i then 1 else 0)),
    Fintype.piFinset_univ]

/-- The factorized generating function in closed form:
`∏_i ∑_x θ^{[x≠0]}θ^{[x≠eᵢ]} = (1+(q−1)θ²)^{n−wt e} · (2θ+(q−2)θ²)^{wt e}`. -/
theorem prod_value (θ : ℝ) (e : ι → F) :
    ∏ i : ι, (∑ x : F, (θ ^ (if x ≠ 0 then 1 else 0) * θ ^ (if x ≠ e i then 1 else 0)))
      = (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι - hammingNorm e)
        * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2) ^ (hammingNorm e) := by
  classical
  have hfac : ∀ i : ι,
      (∑ x : F, (θ ^ (if x ≠ 0 then 1 else 0) * θ ^ (if x ≠ e i then 1 else 0)))
        = if e i = 0 then (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2)
            else (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2) := by
    intro i
    simp_rw [coord_summand θ (e i)]
    by_cases h : e i = 0
    · rw [if_pos h, h]; exact per_coord_zero θ
    · rw [if_neg h]; exact per_coord_ne θ (e i) h
  simp_rw [hfac]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hne : (univ.filter (fun i => ¬ (e i = 0))).card = hammingNorm e := by rw [hammingNorm]
  have hzero : (univ.filter (fun i : ι => e i = 0)).card = Fintype.card ι - hammingNorm e := by
    have hpart := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
      (p := fun i => e i = 0)
    rw [hne, Finset.card_univ] at hpart
    omega
  rw [hne, hzero]

/-- **Moment-generating-function (Chernoff) ball-intersection bound.** For every `θ ∈ [0,1]`,

  `θ^{2r} · I(e) ≤ (1 + (q−1)θ²)^{n−wt(e)} · (2θ + (q−2)θ²)^{wt(e)}`,    `r = ⌊δ·n⌋`.

This is the **tight** ball-intersection decay for every field `F` (optimizing `θ` recovers the exact
CS25 large-deviation exponent), the `q`-correct replacement for the `𝔽₂`-only combinatorial bound
`jointCoverCount_le_ballVolume_mul`. The proof factorizes the joint weight enumerator over
coordinates — the Chernoff method from probability theory — bypassing the intractable multinomial. -/
theorem jointCoverCount_mgf_le (δ : ℝ≥0) (e : ι → F) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ ^ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊) * (jointCoverCount δ 0 e : ℝ)
      ≤ (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι - hammingNorm e)
        * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2) ^ (hammingNorm e) := by
  classical
  set r := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ with hr
  rw [jointCoverCount_eq_hamming]
  -- (card filter : ℝ) as a sum of indicators
  have hsum : ((univ.filter (fun w : ι → F =>
        hammingDist w 0 ≤ r ∧ hammingDist w e ≤ r)).card : ℝ)
      = ∑ w : ι → F, (if (hammingDist w 0 ≤ r ∧ hammingDist w e ≤ r) then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hsum, Finset.mul_sum]
  -- pointwise Chernoff bound, then factorize
  refine le_trans (Finset.sum_le_sum (g := fun w => θ ^ (hammingNorm w) * θ ^ (hammingDist w e))
    (fun w _ => ?_)) ?_
  · -- θ^{2r}·1[both ≤ r] ≤ θ^{wt w}·θ^{Δ₀(w,e)}
    by_cases hP : hammingDist w 0 ≤ r ∧ hammingDist w e ≤ r
    · rw [if_pos hP, mul_one]
      have hN : hammingDist w 0 = hammingNorm w := hammingDist_zero_right w
      have hle : hammingNorm w + hammingDist w e ≤ 2 * r := by
        rw [hN] at hP; omega
      calc θ ^ (2 * r) ≤ θ ^ (hammingNorm w + hammingDist w e) :=
            pow_le_pow_of_le_one hθ0 hθ1 hle
        _ = θ ^ (hammingNorm w) * θ ^ (hammingDist w e) := by rw [pow_add]
    · rw [if_neg hP, mul_zero]
      exact mul_nonneg (pow_nonneg hθ0 _) (pow_nonneg hθ0 _)
  · -- ∑_w θ^{wt w}·θ^{Δ₀} = ∑_w θ^{wt w + Δ₀} = ∏_i ∑_x … = closed form
    have hpow : ∀ w : ι → F,
        θ ^ (hammingNorm w) * θ ^ (hammingDist w e) = θ ^ (hammingNorm w + hammingDist w e) := by
      intro w; rw [pow_add]
    simp_rw [hpow]
    rw [mgf_factor θ e, prod_value θ e]

/-- **Second-moment Chernoff bound.** Summing the per-`e` MGF bound over a code `C` gives

  `θ^{2r} · ∑_{e∈C} I(e) ≤ ∑_{e∈C} (1+(q−1)θ²)^{n−wt(e)}·(2θ+(q−2)θ²)^{wt(e)}`,    `∀ θ ∈ [0,1]`,

i.e. `θ^{2r}` times the CS25 second-moment off-diagonal is at most the code's **homogeneous weight
enumerator** `W_C(X,Y) = ∑_{e∈C} X^{wt(e)} Y^{n−wt(e)}` evaluated at `X = 2θ+(q−2)θ²`,
`Y = 1+(q−1)θ²`.  This reduces the (tight, all-field) second moment to the weight enumerator — a
classical, well-studied object (for RS/MDS codes given in closed form by MacWilliams) — and an
optimization over `θ ∈ [0,1]`. -/
theorem sum_jointCoverCount_mgf_le (C : Finset (ι → F)) (δ : ℝ≥0) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ ^ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊) * (∑ e ∈ C, (jointCoverCount δ 0 e : ℝ))
      ≤ ∑ e ∈ C, ((1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι - hammingNorm e)
          * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2) ^ (hammingNorm e)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ => jointCoverCount_mgf_le δ e θ hθ0 hθ1)

/-- **Weight-enumerator binomial bound (MDS input, diagonal-separated).** For any code `C` whose
*off-diagonal* weight distribution satisfies `A_d ≤ C(n,d)q^d/q^{n−k}` for `d ≥ 1`, and `X, Y ≥ 0`,

  `∑_{e∈C} Y^{n−wt(e)} X^{wt(e)} ≤ A_0·Y^n + (q·X + Y)^n / q^{n−k}`,

where `A_0 = #{e∈C : e = 0}` is the diagonal term.  The `d=0` term MUST be separated: the MDS bound
`C(n,0)q^0/q^{n−k} = q^{−(n−k)} < 1` is strictly below the true diagonal `A_0 = 1`, so a uniform
hypothesis over all `d` would be unsatisfiable for any code containing `0`. -/
theorem weightEnum_mds_le (C : Finset (ι → F)) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (k : ℕ)
    (hA : ∀ d : ℕ, 1 ≤ d → ((C.filter (fun e => hammingNorm e = d)).card : ℝ)
            ≤ (Nat.choose (Fintype.card ι) d : ℝ) * (Fintype.card F : ℝ) ^ d
                / (Fintype.card F : ℝ) ^ (Fintype.card ι - k)) :
    ∑ e ∈ C, Y ^ (Fintype.card ι - hammingNorm e) * X ^ (hammingNorm e)
      ≤ ((C.filter (fun e => hammingNorm e = 0)).card : ℝ) * Y ^ (Fintype.card ι)
        + ((Fintype.card F : ℝ) * X + Y) ^ (Fintype.card ι)
            / (Fintype.card F : ℝ) ^ (Fintype.card ι - k) := by
  classical
  set n := Fintype.card ι
  set q := (Fintype.card F : ℝ)
  set A0 := ((C.filter (fun e => hammingNorm e = 0)).card : ℝ)
  have hfib : ∑ e ∈ C, Y ^ (n - hammingNorm e) * X ^ (hammingNorm e)
      = ∑ d ∈ Finset.range (n + 1),
          ((C.filter (fun e => hammingNorm e = d)).card : ℝ) * (Y ^ (n - d) * X ^ d) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := hammingNorm) (t := Finset.range (n + 1))
      (fun e _ => Finset.mem_range.mpr (Nat.lt_succ_of_le hammingNorm_le_card_fintype))
      (f := fun e => Y ^ (n - hammingNorm e) * X ^ (hammingNorm e))]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hfib]
  have hpt : ∀ d ∈ Finset.range (n + 1),
      ((C.filter (fun e => hammingNorm e = d)).card : ℝ) * (Y ^ (n - d) * X ^ d)
        ≤ (if d = 0 then A0 * Y ^ n else 0)
          + (Nat.choose n d : ℝ) * q ^ d / q ^ (n - k) * (Y ^ (n - d) * X ^ d) := by
    intro d _
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [if_pos rfl]
      have hg0 : (0:ℝ) ≤ (Nat.choose n 0 : ℝ) * q ^ 0 / q ^ (n - k) * (Y ^ (n - 0) * X ^ 0) := by
        positivity
      have hL : ((C.filter (fun e => hammingNorm e = 0)).card : ℝ) * (Y ^ (n - 0) * X ^ 0)
          = A0 * Y ^ n := by simp [A0]
      rw [hL]; linarith
    · rw [if_neg (by omega), zero_add]
      exact mul_le_mul_of_nonneg_right (hA d hd) (by positivity)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib]
  have hdiag : ∑ d ∈ Finset.range (n + 1), (if d = 0 then A0 * Y ^ n else 0) = A0 * Y ^ n := by
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => A0 * Y ^ n)]
    simp [Finset.mem_range]
  rw [hdiag]
  gcongr
  rw [add_pow, Finset.sum_div]
  refine Finset.sum_le_sum (fun d _ => ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring_nf
  rfl

/-- **Full MDS second-moment Chernoff bound (diagonal-separated).** Combining
`sum_jointCoverCount_mgf_le` with `weightEnum_mds_le`: for every `θ ∈ [0,1]` and any code whose
off-diagonal weights obey the MDS bound `A_d ≤ C(n,d)q^{d}/q^{n−k}` (`d ≥ 1`),

  `θ^{2r} · ∑_{e∈C} I(e) ≤ A_0·(1+(q−1)θ²)^n + (q·(2θ+(q−2)θ²)+(1+(q−1)θ²))^n / q^{n−k}`,

`r = ⌊δ·n⌋`, `A_0 = #{e∈C : e=0}`.  The first summand is the diagonal `e=0` term (`= I(0) = V`
after optimization); the second is the off-diagonal, fully explicit in `(θ, q, n, k)`.  Minimizing
over `θ ∈ [0,1]` yields the CS25 second-moment exponent for Reed–Solomon (MDS) codes. -/
theorem sum_jointCoverCount_mgf_mds_le (C : Finset (ι → F)) (δ : ℝ≥0) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k : ℕ)
    (hA : ∀ d : ℕ, 1 ≤ d → ((C.filter (fun e => hammingNorm e = d)).card : ℝ)
            ≤ (Nat.choose (Fintype.card ι) d : ℝ) * (Fintype.card F : ℝ) ^ d
                / (Fintype.card F : ℝ) ^ (Fintype.card ι - k)) :
    θ ^ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊) * (∑ e ∈ C, (jointCoverCount δ 0 e : ℝ))
      ≤ ((C.filter (fun e => hammingNorm e = 0)).card : ℝ)
          * (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι)
        + ((Fintype.card F : ℝ) * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2)
            + (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2)) ^ (Fintype.card ι)
          / (Fintype.card F : ℝ) ^ (Fintype.card ι - k) := by
  haveI : Nonempty F := ⟨0⟩
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hX : 0 ≤ 2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ1),
      mul_nonneg (le_trans zero_le_one hq1) (sq_nonneg θ), sq_nonneg θ]
  have hY : 0 ≤ 1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (Fintype.card F : ℝ) - 1) (sq_nonneg θ)]
  exact le_trans (sum_jointCoverCount_mgf_le C δ θ hθ0 hθ1) (weightEnum_mds_le C _ _ hX hY k hA)

end ArkLib.CS25
