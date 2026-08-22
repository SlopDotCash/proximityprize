/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# SYZ4: the degenerate-channel ceiling, optimized over the agreement radius (issue #466 / #507)

This file sharpens the unconditional production rate-`1/2` ceiling from `31/64 ≈ 0.484` down to

  `mcaDeltaStar (evalCode g (2^30) (2^29 − 1)) epsStar ≤ 369098751 / 2^30 = 11/32 − 2^-30 ≈ 0.34375`,

still unconditional, over the first certified prize field `P = 2^30·(2^128 + 192) + 1`.  It is the
optimized-radius consumer of the SYZ degenerate-subset channel (SYZ1 probe, SYZ2 formalized channel
in `Frontier/_SYZ2PredecessorCapRefutationCore.lean`, SYZ3 over-budget stack in
`Frontier/_SYZ3OverBudgetStackWitness.lean`).

**Why SYZ3 sat at `31/64`, and how SYZ4 moves.**  SYZ3's stack agreed with each of its three
degenerate codewords on a `33`-block subset, whose complement (`31` blocks per subset) carried the
bad scalars — a radius of `predecessorRadius (2^30) (31·2^24) ≈ 31/64`.  There the `33` agreement
blocks were `31` *vanishing-core* blocks (`Z_N` kills them, so agreement is free) plus a `2`-block
distinguishing pair; the core is capped at `31` blocks because the codeword degree `|N|·2^24` must
stay below the RS dimension `2^29` (`32·2^24 = 2^29` is already too big).  To reach a *smaller*
radius one needs *larger* agreement subsets, which the vanishing core cannot supply.

SYZ4 instead grows agreement by *zero-multiplier* blocks: the codeword keeps degree `31·2^24 < 2^29`
(still `N = {0..30}` vanishing core), but the `33` non-core blocks are partitioned into three
`11`-block **agreement regions** `A₀ = {31..41}`, `A₁ = {42..52}`, `A₂ = {53..63}`, where subset `j`
carries the constant multiplier pair `(c₁ j, c₀ j)` on `Aⱼ` and *the stack matches it there*
(both rows equal, so agreement, though `Z_N ≠ 0`).  Each subset then agrees on `N ∪ Aⱼ` — `42`
blocks, `t = 42·2^24 = 704643072 ≥ 2^29` — and its `22`-block complement `A_{j'} ∪ A_{j''}` carries
the bad scalars.  Three subsets give

  `3 · 22 · 2^24 = 1107296256 > 2^30`

distinct `mcaEvent`-bad scalars at radius `predecessorRadius (2^30) (22·2^24) = 369098751/2^30`.
Since `2^30 < 1107296256 < 1107296256·2^128 / ... ` the mass `1107296256 / P` strictly exceeds
`epsStar = 2^-128` (equivalently `P < 1107296256·2^128`), so the radius is *bad*, and
`mcaDeltaStar_le_of_bad` pins the ceiling.

**The optimum, and why `1/3` is the (unattained) infimum.**  With block granularity `2^24`
(`64` blocks) and `D = 3` subsets, minimizing the radius over feasible agreement sizes gives exactly
`42` agreement blocks: `43` blocks would leave only `3·21·2^24 = 63·2^24 < 2^30` bad scalars.  As the
block granularity is refined the optimum `radius → 1/3⁺`: the general `D = 3` bound is
`(1−ρ)/(2−ρ) = 1/3` at `ρ = 1/2`, approached but **not attained**, the obstruction being precisely
the degree cap `ρ_core < 1/2` on the vanishing core.  `11/32 ≈ 0.34375` is the concrete rung landed
here; Johnson `1 − √(1/2) ≈ 0.2929` remains strictly below — no contradiction.

**Untouched.**  The unconditional good-side floor `178956971/2^30 ≈ 0.1667` is unchanged, and the
CORE (pinning `δ*` exactly) remains OPEN: sharpening the *ceiling* says nothing about `δ*` itself.

**Provenance.**  The channel theorems (`pencilScalar`, `mcaEvent_pencil`,
`rsCode_eq_of_agree_on_card_le`) are restated verbatim (with attribution) from
`Frontier/_SYZ2PredecessorCapRefutationCore.lean` (SYZ2) via
`Frontier/_SYZ3OverBudgetStackWitness.lean` (SYZ3), and the kernel-cheap `binaryPow` from
`Frontier/_PrizeShapePrimeP30.lean`, because those originals are `private` or not in the shared
olean cache.  The block scaffold (`ω`, `zval`, `ZNX`, `card_fiber`, `card_filter_label`) is likewise
adapted from SYZ3; only the label layer (`m0`, `m1`, `nd`, `SLab`) and the counts change, plus the
new ceiling consumer.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Finset Polynomial
open scoped NNReal ENNReal
open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership Code
open ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling

/-! ## The SYZ2 channel, restated (verbatim from SYZ2 via SYZ3, with attribution) -/

section Channel

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The pencil scalar attached to an off-`S` point `x` of a degenerate subset
(SYZ2 `pencilScalar`). -/
noncomputable def pencilScalar (u₀ u₁ v₀ v₁ : ι → F) (x : ι) : F :=
  -((u₀ x - v₀ x) / (u₁ x - v₁ x))

/-- SYZ2 channel theorem (a): the codeword pencil agrees with the line on `S ∪ {x}`. -/
theorem pencil_line_agrees {S : Finset ι} {u₀ u₁ v₀ v₁ : ι → F}
    (h₀ : ∀ i ∈ S, v₀ i = u₀ i) (h₁ : ∀ i ∈ S, v₁ i = u₁ i)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x) :
    ∀ i ∈ insert x S,
      (v₀ + pencilScalar u₀ u₁ v₀ v₁ x • v₁) i
        = u₀ i + pencilScalar u₀ u₁ v₀ v₁ x • u₁ i := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hiS
  · have hne : u₁ i - v₁ i ≠ 0 := sub_ne_zero.mpr hd₁
    have key : pencilScalar u₀ u₁ v₀ v₁ i * (u₁ i - v₁ i) = -(u₀ i - v₀ i) := by
      rw [pencilScalar, neg_mul, div_mul_cancel₀ _ hne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -key
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h₀ i hiS, h₁ i hiS]

/-- SYZ2 channel theorem (b): the pair-joint clause fails on the enlarged witness set. -/
theorem not_pairJointAgreesOn_insert (C : Submodule F (ι → F))
    {S : Finset ι} {u₀ u₁ v₁ : ι → F}
    (huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x) :
    ¬ pairJointAgreesOn (C : Set (ι → F)) (insert x S) u₀ u₁ := by
  rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
  have hw₁v : w₁ = v₁ :=
    huniq₁ w₁ hw₁ fun i hi => (h i (Finset.mem_insert_of_mem hi)).2
  have hx : w₁ x = u₁ x := (h x (Finset.mem_insert_self x S)).2
  rw [hw₁v] at hx
  exact hd₁ hx.symm

/-- SYZ2 per-point channel: every eligible off-`S` point produces a literal
`mcaEvent`-bad scalar. -/
theorem mcaEvent_pencil (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {S : Finset ι} {u₀ u₁ v₀ v₁ : ι → F}
    (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C)
    (h₀ : ∀ i ∈ S, v₀ i = u₀ i) (h₁ : ∀ i ∈ S, v₁ i = u₁ i)
    (huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x)
    (hcard : (((insert x S).card : ℝ≥0)) ≥ (1 - δ) * Fintype.card ι) :
    mcaEvent (C : Set (ι → F)) δ u₀ u₁ (pencilScalar u₀ u₁ v₀ v₁ x) :=
  ⟨insert x S, hcard,
    ⟨v₀ + pencilScalar u₀ u₁ v₀ v₁ x • v₁,
      C.add_mem hv₀ (C.smul_mem _ hv₁),
      pencil_line_agrees h₀ h₁ hd₁⟩,
    not_pairJointAgreesOn_insert C huniq₁ hd₁⟩

/-- SYZ2 Reed–Solomon interpolation uniqueness on any subset of at least `k` points. -/
theorem rsCode_eq_of_agree_on_card_le {n : ℕ} [NeZero n]
    (dom : Fin n ↪ F) {k : ℕ} {S : Finset (Fin n)} (hk : k ≤ S.card)
    {w w' : Fin n → F} (hw : w ∈ rsCode dom k) (hw' : w' ∈ rsCode dom k)
    (hagree : ∀ i ∈ S, w i = w' i) : w = w' := by
  obtain ⟨p, hP, rfl⟩ := hw
  obtain ⟨Q, hQ, rfl⟩ := hw'
  have hPQ : p - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := p - Q) (s := S.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ dom.injective]
      calc (p - Q).degree ≤ max p.degree Q.degree := Polynomial.degree_sub_le p Q
        _ < (k : WithBot ℕ) := max_lt hP hQ
        _ ≤ (S.card : WithBot ℕ) := by exact_mod_cast hk
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.eval_sub, sub_eq_zero]
      exact hagree i hi
  have hPQ' : p = Q := sub_eq_zero.mp hPQ
  rw [hPQ']

end Channel

/-! ## Kernel-cheap exponentiation (restated from `_PrizeShapePrimeP30.lean`) -/

section BinaryPow

private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

end BinaryPow

/-! ## Production construction at the first certified prize field -/

section Production

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

local instance localInstance_SYZ4DegenerateChannelCeiling_1 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨prime_P⟩

local instance localInstance_SYZ4DegenerateChannelCeiling_2 : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

local instance localInstance_SYZ4DegenerateChannelCeiling_3 : NeZero (64 : ℕ) := ⟨by norm_num⟩

/-- Small naturals are below the 158-bit modulus. -/
private theorem lt_P_small {a : ℕ} (h : a ≤ 12) : a < P := by
  show a < 365375409332725729550921208179070755120141565953
  omega

private theorem natCast_inj_small {a b : ℕ} (ha : a < P) (hb : b < P)
    (h : (a : ZMod P) = (b : ZMod P)) : a = b := by
  have hva : ((a : ℕ) : ZMod P).val = a := ZMod.val_natCast_of_lt ha
  have hvb : ((b : ℕ) : ZMod P).val = b := ZMod.val_natCast_of_lt hb
  rw [← hva, ← hvb, h]

private theorem natCast_ne_zero_small {a : ℕ} (h0 : 0 < a) (ha : a < P) :
    (a : ZMod P) ≠ 0 := by
  intro h
  have h0P : (0 : ℕ) < P := lt_P_small (by norm_num)
  have := natCast_inj_small ha h0P (by simpa using h)
  omega

/-! ### Domain block structure (adapted from SYZ3) -/

/-- The label of a domain index: its block `i mod 64`. -/
def lb (i : Fin (2 ^ 30)) : ℕ := (i : ℕ) % 64

theorem lb_lt (i : Fin (2 ^ 30)) : lb i < 64 := Nat.mod_lt _ (by norm_num)

theorem g_pow_full : g ^ (1073741824 : ℕ) = 1 := by
  have he : (1073741824 : ℕ) = 2 ^ 30 := by norm_num
  rw [he, ← orderOf_g]
  exact pow_orderOf_eq_one g

/-- The order-64 block character `ω = g^{2^24}`. -/
noncomputable def ω : ZMod P := g ^ (16777216 : ℕ)

theorem ω_pow_64 : ω ^ (64 : ℕ) = 1 := by
  rw [ω, ← pow_mul]
  have he : (16777216 * 64 : ℕ) = 1073741824 := by norm_num
  rw [he]
  exact g_pow_full

theorem orderOf_ω : orderOf ω = 64 := by
  have h32 : ω ^ (32 : ℕ) ≠ 1 := by
    rw [ω, ← pow_mul]
    have he : (16777216 * 32 : ℕ) = 536870912 := by norm_num
    rw [he]
    intro hone
    have hle := orderOf_le_of_pow_eq_one (n := 536870912) (by norm_num) hone
    rw [orderOf_g] at hle
    norm_num at hle
  have h2_5 : ω ^ ((2 : ℕ) ^ 5) ≠ 1 := by
    have he : ((2 : ℕ) ^ 5) = 32 := by norm_num
    rwa [he]
  have h2_6 : ω ^ ((2 : ℕ) ^ (5 + 1)) = 1 := by
    have he : ((2 : ℕ) ^ (5 + 1)) = 64 := by norm_num
    rw [he]
    exact ω_pow_64
  have h := orderOf_eq_prime_pow (x := ω) (p := 2) (n := 5) h2_5 h2_6
  rw [h]
  norm_num

/-- Powers of `ω` reduce mod 64. -/
theorem ω_pow_mod (m : ℕ) : ω ^ m = ω ^ (m % 64) := by
  conv_lhs => rw [← Nat.div_add_mod m 64]
  rw [pow_add, pow_mul, ω_pow_64, one_pow, one_mul]

/-- Powers of `ω` are injective on labels `< 64`. -/
theorem ω_pow_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : ω ^ a = ω ^ b) :
    a = b := by
  have hinj := (smoothDom ω 64 orderOf_ω).injective
  have hfin : (⟨a, ha⟩ : Fin 64) = ⟨b, hb⟩ := hinj h
  exact congrArg Fin.val hfin

/-- The `2^24`-th power of `g^i` sees only the label of `i`. -/
theorem g_pow_block (i : ℕ) : (g ^ i) ^ (16777216 : ℕ) = ω ^ (i % 64) := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  show ω ^ i = ω ^ (i % 64)
  exact ω_pow_mod i

/-! ### The vanishing product and the codeword scaffold (unchanged core `N = {0..30}`) -/

/-- `zval b = Z_N(ω^b)`: value at label `b` of the vanishing product of the core labels
`N = {0..30}`. Zero exactly on `N` (among labels `< 64`). -/
noncomputable def zval (b : ℕ) : ZMod P :=
  ∏ a ∈ Finset.range 31, (ω ^ b - ω ^ a)

theorem zval_eq_zero {b : ℕ} (hb : b ≤ 30) : zval b = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) (sub_self _)

theorem zval_ne_zero {b : ℕ} (hb31 : 31 ≤ b) (hb : b < 64) : zval b ≠ 0 := by
  rw [zval, Finset.prod_ne_zero_iff]
  intro a ha
  have ha31 : a < 31 := Finset.mem_range.mp ha
  refine sub_ne_zero.mpr fun h => ?_
  have := ω_pow_inj hb (by omega) h
  omega

/-- The vanishing polynomial `Z_N(X^{2^24})` of the 31 core blocks. -/
noncomputable def ZNX : Polynomial (ZMod P) :=
  ∏ a ∈ Finset.range 31, (Polynomial.X ^ (16777216 : ℕ) - Polynomial.C (ω ^ a))

theorem ZNX_natDegree_le : ZNX.natDegree ≤ 520093696 := by
  rw [ZNX]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 16777216) ?_) ?_
  · intro a _
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp [Polynomial.natDegree_C]
  · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem ZNX_eval (i : ℕ) : ZNX.eval (g ^ i) = zval (i % 64) := by
  rw [ZNX, Polynomial.eval_prod, zval]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    g_pow_block]

/-! ### Label combinatorics (SYZ4 agreement-region design)

`N = {0..30}` (core), `A₀ = {31..41}`, `A₁ = {42..52}`, `A₂ = {53..63}` (11 blocks each).
The stack multiplier of a block is the codeword multiplier of the region owning it:
`m₁ = c₁(region) = region-index`, `m₀ = c₀(region)`. -/

/-- Row-1 multiplier per block: `0` on `N ∪ A₀`, `1` on `A₁`, `2` on `A₂`. -/
def m1 (b : ℕ) : ℕ := if b ≤ 41 then 0 else if b ≤ 52 then 1 else 2

/-- Row-0 multiplier per block: `0` on `N ∪ A₀`, `1` on `A₁`, `3` on `A₂`. -/
def m0 (b : ℕ) : ℕ := if b ≤ 41 then 0 else if b ≤ 52 then 1 else 3

/-- Row-1 codeword multiplier of subset `j`: `(0,1,2)`. -/
def c1 (j : Fin 3) : ℕ := if j = 0 then 0 else if j = 1 then 1 else 2

/-- Row-0 codeword multiplier of subset `j`: `(0,1,3)`. -/
def c0 (j : Fin 3) : ℕ := if j = 0 then 0 else if j = 1 then 1 else 3

/-- The agreement region owned by subset `j`. -/
def ARegion (j : Fin 3) : Finset ℕ :=
  if j = 0 then Finset.Icc 31 41 else if j = 1 then Finset.Icc 42 52 else Finset.Icc 53 63

/-- The label set of degenerate subset `j`: the core `N` plus its agreement region `Aⱼ`. -/
def SLab (j : Fin 3) : Finset ℕ := Finset.range 31 ∪ ARegion j

/-- The pencil coefficient pair `(num, den)` of an eligible (label, subset) slot:
the pencil scalar there is `−(num/den)·g^i`. Dummy on ineligible branches. -/
def nd (j : Fin 3) (b : ℕ) : ℕ × ℕ :=
  if b ≤ 30 then (0, 0) else
  if b ≤ 41 then (if j = 1 then (1, 1) else (3, 2)) else
  if b ≤ 52 then (if j = 0 then (1, 1) else (2, 1)) else
  (if j = 0 then (3, 2) else (2, 1))

/-- Consistency on the degenerate subsets: on `SLab j` (off the core) the stack multipliers
match the codeword multipliers. -/
private theorem fact_S : ∀ j : Fin 3, ∀ b ∈ Finset.range 64, b ∈ SLab j →
    30 < b → m1 b = c1 j ∧ m0 b = c0 j := by decide

/-- Eligibility data off the degenerate subsets: label bounds, row-1 separation, the
coefficient-pair inventory, and the exact integer pencil identity
`den·(m₀ − c₀) = num·(m₁ − c₁)`. -/
private theorem fact_A : ∀ j : Fin 3, ∀ b ∈ Finset.range 64, b ∉ SLab j →
    31 ≤ b ∧ m1 b ≠ c1 j ∧ m1 b ≤ 2 ∧ c1 j ≤ 2 ∧
      (nd j b = (1, 1) ∨ nd j b = (2, 1) ∨ nd j b = (3, 2)) ∧
      ((nd j b).2 : ℤ) * ((m0 b : ℤ) - (c0 j : ℤ))
        = ((nd j b).1 : ℤ) * ((m1 b : ℤ) - (c1 j : ℤ)) := by decide

/-- Within one label, distinct subsets carry distinct coefficient pairs. -/
private theorem fact_nd_inj : ∀ j j' : Fin 3, ∀ b ∈ Finset.range 64,
    b ∉ SLab j → b ∉ SLab j' → nd j b = nd j' b → j = j' := by decide

/-! ### The stack and the codewords -/

/-- The row-1 word: label multiplier times the core vanishing value. -/
noncomputable def u1 : Fin (2 ^ 30) → ZMod P := fun i =>
  (m1 (lb i) : ZMod P) * zval (lb i)

/-- The row-0 word: label multiplier times the core vanishing value times `g^i`. -/
noncomputable def u0 : Fin (2 ^ 30) → ZMod P := fun i =>
  (m0 (lb i) : ZMod P) * zval (lb i) * g ^ (i : ℕ)

/-- The row-1 codeword of subset `j`. -/
noncomputable def v1 (j : Fin 3) : Fin (2 ^ 30) → ZMod P := fun i =>
  (c1 j : ZMod P) * zval (lb i)

/-- The row-0 codeword of subset `j`. -/
noncomputable def v0 (j : Fin 3) : Fin (2 ^ 30) → ZMod P := fun i =>
  (c0 j : ZMod P) * zval (lb i) * g ^ (i : ℕ)

/-- The production code, in generic Reed–Solomon form. -/
noncomputable def prodCode : Submodule (ZMod P) (Fin (2 ^ 30) → ZMod P) :=
  rsCode (smoothDom g (2 ^ 30) orderOf_g) (2 ^ 29)

theorem dom_apply (i : Fin (2 ^ 30)) :
    (smoothDom g (2 ^ 30) orderOf_g) i = g ^ (i : ℕ) := rfl

theorem znx_degree_lt : ZNX.degree < 2 ^ 29 := by
  have h2 : ZNX.natDegree < 2 ^ 29 := lt_of_le_of_lt ZNX_natDegree_le (by norm_num)
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h2)

theorem znxX_degree_lt : (ZNX * Polynomial.X).degree < 2 ^ 29 := by
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have hz : ZNX.degree ≤ (520093696 : ℕ) :=
    le_trans Polynomial.degree_le_natDegree (by exact_mod_cast ZNX_natDegree_le)
  have hx : (Polynomial.X : Polynomial (ZMod P)).degree ≤ (1 : ℕ) := Polynomial.degree_X_le
  calc ZNX.degree + (Polynomial.X : Polynomial (ZMod P)).degree
      ≤ (520093696 : ℕ) + (1 : ℕ) := add_le_add hz hx
    _ < 2 ^ 29 := by norm_num

noncomputable def znxWord : Fin (2 ^ 30) → ZMod P := fun i => ZNX.eval (g ^ (i : ℕ))

noncomputable def xznxWord : Fin (2 ^ 30) → ZMod P :=
  fun i => (ZNX * Polynomial.X).eval (g ^ (i : ℕ))

theorem znxWord_apply (i : Fin (2 ^ 30)) : znxWord i = zval (lb i) :=
  ZNX_eval (i : ℕ)

theorem xznxWord_apply (i : Fin (2 ^ 30)) : xznxWord i = zval (lb i) * g ^ (i : ℕ) := by
  show (ZNX * Polynomial.X).eval (g ^ (i : ℕ)) = zval (lb i) * g ^ (i : ℕ)
  rw [Polynomial.eval_mul, Polynomial.eval_X, ZNX_eval]
  rfl

theorem znxWord_mem : znxWord ∈ prodCode :=
  ⟨ZNX, znx_degree_lt, by funext i; rw [dom_apply]; rfl⟩

theorem xznxWord_mem : xznxWord ∈ prodCode :=
  ⟨ZNX * Polynomial.X, znxX_degree_lt, by funext i; rw [dom_apply]; rfl⟩

theorem v1_mem (j : Fin 3) : v1 j ∈ prodCode := by
  have h : v1 j = (c1 j : ZMod P) • znxWord := by
    funext i
    simp only [v1, Pi.smul_apply, smul_eq_mul, znxWord_apply]
  rw [h]; exact prodCode.smul_mem _ znxWord_mem

theorem v0_mem (j : Fin 3) : v0 j ∈ prodCode := by
  have h : v0 j = (c0 j : ZMod P) • xznxWord := by
    funext i
    simp only [v0, Pi.smul_apply, smul_eq_mul, xznxWord_apply, mul_assoc]
  rw [h]; exact prodCode.smul_mem _ xznxWord_mem

/-! ### The degenerate subsets and agreement -/

/-- Degenerate subset `j`: the union of its 42 label blocks. -/
def S (j : Fin 3) : Finset (Fin (2 ^ 30)) :=
  Finset.univ.filter fun i => lb i ∈ SLab j

/-- Eligible (off-subset) indices of subset `j`: its 22 complementary blocks. -/
def E (j : Fin 3) : Finset (Fin (2 ^ 30)) :=
  Finset.univ.filter fun i => lb i ∉ SLab j

theorem mem_S {j : Fin 3} {i : Fin (2 ^ 30)} : i ∈ S j ↔ lb i ∈ SLab j := by
  simp [S]

theorem mem_E {j : Fin 3} {i : Fin (2 ^ 30)} : i ∈ E j ↔ lb i ∉ SLab j := by
  simp [E]

theorem agree_v1 (j : Fin 3) : ∀ i ∈ S j, v1 j i = u1 i := by
  intro i hi
  have hb : lb i ∈ SLab j := mem_S.mp hi
  by_cases h30 : lb i ≤ 30
  · simp only [v1, u1, zval_eq_zero h30, mul_zero]
  · obtain ⟨hm1, -⟩ := fact_S j (lb i) (Finset.mem_range.mpr (lb_lt i)) hb (by omega)
    simp only [v1, u1, hm1]

theorem agree_v0 (j : Fin 3) : ∀ i ∈ S j, v0 j i = u0 i := by
  intro i hi
  have hb : lb i ∈ SLab j := mem_S.mp hi
  by_cases h30 : lb i ≤ 30
  · simp only [v0, u0, zval_eq_zero h30, mul_zero, zero_mul]
  · obtain ⟨-, hm0⟩ := fact_S j (lb i) (Finset.mem_range.mpr (lb_lt i)) hb (by omega)
    simp only [v0, u0, hm0]

/-! ### Block-counting -/

theorem card_fiber (b : ℕ) (hb : b < 64) :
    (Finset.univ.filter fun i : Fin (2 ^ 30) => lb i = b).card = 2 ^ 24 := by
  rw [← Finset.card_range (2 ^ 24)]
  refine Finset.card_bij' (fun i _ => (i : ℕ) / 64)
    (fun t ht => (⟨b + 64 * t, by
      have := Finset.mem_range.mp ht; omega⟩ : Fin (2 ^ 30))) ?_ ?_ ?_ ?_
  · intro i hi
    have h1 : (i : ℕ) < 2 ^ 30 := i.isLt
    have h2 : lb i = b := (Finset.mem_filter.mp hi).2
    rw [lb] at h2
    refine Finset.mem_range.mpr ?_
    show (i : ℕ) / 64 < 2 ^ 24
    omega
  · intro t ht
    have ht' : t < 2 ^ 24 := Finset.mem_range.mp ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show (b + 64 * t) % 64 = b
    omega
  · intro i hi
    have h2 : lb i = b := (Finset.mem_filter.mp hi).2
    rw [lb] at h2
    refine Fin.ext ?_
    show b + 64 * ((i : ℕ) / 64) = (i : ℕ)
    omega
  · intro t ht
    have ht' : t < 2 ^ 24 := Finset.mem_range.mp ht
    show (b + 64 * t) / 64 = t
    omega

theorem card_filter_label (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun i : Fin (2 ^ 30) => Q (lb i)).card
      = ((Finset.range 64).filter Q).card * 2 ^ 24 := by
  have hsplit : (Finset.univ.filter fun i : Fin (2 ^ 30) => Q (lb i))
      = ((Finset.range 64).filter Q).biUnion
          (fun b => Finset.univ.filter fun i : Fin (2 ^ 30) => lb i = b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · intro hQ
      exact ⟨lb i, ⟨lb_lt i, hQ⟩, rfl⟩
    · rintro ⟨b, ⟨_, hQ⟩, rfl⟩
      exact hQ
  rw [hsplit, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun b hb =>
      card_fiber b (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)]
    rw [Finset.sum_const, smul_eq_mul]
  · intro b hb b' hb' hbb'
    refine Finset.disjoint_left.mpr fun i hi hi' => ?_
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hi').2
    exact hbb' (by omega)

theorem card_S (j : Fin 3) : (S j).card = 704643072 := by
  have hcount : ((Finset.range 64).filter fun b => b ∈ SLab j).card = 42 := by
    fin_cases j <;> decide
  have h := card_filter_label (fun b => b ∈ SLab j)
  rw [S, h, hcount]
  norm_num

theorem card_E (j : Fin 3) : (E j).card = 369098752 := by
  have hcount : ((Finset.range 64).filter fun b => b ∉ SLab j).card = 22 := by
    fin_cases j <;> decide
  have h := card_filter_label (fun b => b ∉ SLab j)
  rw [E, h, hcount]
  norm_num

/-! ### Interpolation uniqueness and the radius threshold -/

theorem uniq_v1 (j : Fin 3) : ∀ w ∈ (prodCode : Set (Fin (2 ^ 30) → ZMod P)),
    (∀ i ∈ S j, w i = u1 i) → w = v1 j := by
  intro w hw hagree
  refine rsCode_eq_of_agree_on_card_le (smoothDom g (2 ^ 30) orderOf_g)
    (k := 2 ^ 29) (S := S j) (by rw [card_S]; norm_num) hw (v1_mem j) ?_
  intro i hi
  rw [hagree i hi, ← agree_v1 j i hi]

/-- The radius-threshold arithmetic: at `δ = predecessorRadius (2^30) (22·2^24)`
the required witness size `(1 − δ)·n` is exactly `704643073 = |S j| + 1`. -/
theorem card_threshold (j : Fin 3) {i : Fin (2 ^ 30)} (hi : i ∉ S j) :
    (((insert i (S j)).card : ℝ≥0))
      ≥ (1 - predecessorRadius (2 ^ 30) (22 * 2 ^ 24))
          * Fintype.card (Fin (2 ^ 30)) := by
  rw [Finset.card_insert_of_notMem hi, card_S, Fintype.card_fin]
  have hδ : predecessorRadius (2 ^ 30) (22 * 2 ^ 24)
      = (369098751 : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
    rw [predecessorRadius]
    norm_num
  have hle : (1 : ℝ≥0) - predecessorRadius (2 ^ 30) (22 * 2 ^ 24)
      ≤ (704643073 : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
    rw [tsub_le_iff_right, hδ, ← add_div,
      show (704643073 : ℝ≥0) + 369098751 = 2 ^ 30 by norm_num,
      div_self (by norm_num : (2 ^ 30 : ℝ≥0) ≠ 0)]
  calc (1 - predecessorRadius (2 ^ 30) (22 * 2 ^ 24)) * ((2 ^ 30 : ℕ) : ℝ≥0)
      ≤ ((704643073 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) * ((2 ^ 30 : ℕ) : ℝ≥0) := by
        gcongr
    _ = (704643073 : ℝ≥0) := by
        rw [div_mul_eq_mul_div]
        norm_num
    _ = ((704643072 + 1 : ℕ) : ℝ≥0) := by norm_num

/-! ### The pencil normal form and slot injectivity -/

theorem row1_ne (j : Fin 3) {i : Fin (2 ^ 30)} (h : lb i ∉ SLab j) :
    u1 i ≠ v1 j i := by
  obtain ⟨hb31, hne, hm1le, hc1le, -, -⟩ :=
    fact_A j (lb i) (Finset.mem_range.mpr (lb_lt i)) h
  have hz : zval (lb i) ≠ 0 := zval_ne_zero hb31 (lb_lt i)
  simp only [u1, v1]
  intro heq
  have hcast : ((m1 (lb i) : ℕ) : ZMod P) = ((c1 j : ℕ) : ZMod P) :=
    mul_right_cancel₀ hz heq
  exact hne (natCast_inj_small (lt_P_small (by omega)) (lt_P_small (by omega)) hcast)

/-- **The pencil normal form.** On an eligible slot the pencil scalar satisfies
`den · γ = −num · g^i`. -/
theorem pencil_mul_den (j : Fin 3) {i : Fin (2 ^ 30)} (h : lb i ∉ SLab j) :
    ((nd j (lb i)).2 : ZMod P) * pencilScalar u0 u1 (v0 j) (v1 j) i
      = -(((nd j (lb i)).1 : ZMod P) * g ^ (i : ℕ)) := by
  obtain ⟨hb31, hne, hm1le, hc1le, -, hid⟩ :=
    fact_A j (lb i) (Finset.mem_range.mpr (lb_lt i)) h
  have hz : zval (lb i) ≠ 0 := zval_ne_zero hb31 (lb_lt i)
  have he1 : ((m1 (lb i) : ZMod P) - ((c1 j : ℕ) : ZMod P)) ≠ 0 := by
    refine sub_ne_zero.mpr fun hcast => ?_
    exact hne (natCast_inj_small (lt_P_small (by omega)) (lt_P_small (by omega)) hcast)
  have h1 : u1 i - v1 j i
      = ((m1 (lb i) : ZMod P) - ((c1 j : ℕ) : ZMod P)) * zval (lb i) := by
    simp only [u1, v1]
    ring
  have h0 : u0 i - v0 j i
      = ((m0 (lb i) : ZMod P) - ((c0 j : ℕ) : ZMod P)) * zval (lb i)
          * g ^ (i : ℕ) := by
    simp only [u0, v0]
    ring
  have hkey : ((nd j (lb i)).2 : ZMod P)
        * ((m0 (lb i) : ZMod P) - ((c0 j : ℕ) : ZMod P))
      = ((nd j (lb i)).1 : ZMod P)
        * ((m1 (lb i) : ZMod P) - ((c1 j : ℕ) : ZMod P)) := by
    have hcast := congrArg (fun z : ℤ => ((z : ℤ) : ZMod P)) hid
    push_cast at hcast
    exact hcast
  have hden : (u1 i - v1 j i) ≠ 0 := by
    rw [h1]
    exact mul_ne_zero he1 hz
  rw [pencilScalar, mul_neg, neg_inj, ← mul_div_assoc, div_eq_iff hden, h0, h1]
  generalize g ^ (i : ℕ) = G
  linear_combination (zval (lb i) * G) * hkey

/-- **Slot injectivity.** Two eligible slots with equal pencil scalars coincide. -/
theorem slot_injective {j j' : Fin 3} {i i' : Fin (2 ^ 30)}
    (h : lb i ∉ SLab j) (h' : lb i' ∉ SLab j')
    (heq : pencilScalar u0 u1 (v0 j) (v1 j) i
      = pencilScalar u0 u1 (v0 j') (v1 j') i') :
    j = j' ∧ i = i' := by
  obtain ⟨-, -, -, -, hmem, -⟩ := fact_A j (lb i) (Finset.mem_range.mpr (lb_lt i)) h
  obtain ⟨-, -, -, -, hmem', -⟩ :=
    fact_A j' (lb i') (Finset.mem_range.mpr (lb_lt i')) h'
  have hden := pencil_mul_den j h
  have hden' := pencil_mul_den j' h'
  rw [heq] at hden
  have hcross : ((nd j (lb i)).1 : ZMod P) * ((nd j' (lb i')).2 : ZMod P)
        * g ^ (i : ℕ)
      = ((nd j' (lb i')).1 : ZMod P) * ((nd j (lb i)).2 : ZMod P)
        * g ^ (i' : ℕ) := by
    have e1 := congrArg (fun z => ((nd j' (lb i')).2 : ZMod P) * z) hden
    have e2 := congrArg (fun z => ((nd j (lb i)).2 : ZMod P) * z) hden'
    simp only at e1 e2
    have e3 : ((nd j' (lb i')).2 : ZMod P)
          * -(((nd j (lb i)).1 : ZMod P) * g ^ (i : ℕ))
        = ((nd j (lb i)).2 : ZMod P)
          * -(((nd j' (lb i')).1 : ZMod P) * g ^ (i' : ℕ)) := by
      rw [← e1, ← e2]
      ring
    linear_combination -e3
  have hgN : ∀ m : ℕ, (g ^ m) ^ (1073741824 : ℕ) = 1 := by
    intro m
    rw [← pow_mul, Nat.mul_comm, pow_mul, g_pow_full, one_pow]
  have hpow : (((nd j (lb i)).1 * (nd j' (lb i')).2 : ℕ) : ZMod P)
        ^ (1073741824 : ℕ)
      = (((nd j' (lb i')).1 * (nd j (lb i)).2 : ℕ) : ZMod P)
        ^ (1073741824 : ℕ) := by
    have hc := congrArg (fun z : ZMod P => z ^ (1073741824 : ℕ)) hcross
    simp only [mul_pow, hgN, mul_one] at hc
    push_cast
    rw [mul_pow, mul_pow]
    exact hc
  have hsame : nd j (lb i) = nd j' (lb i') := by
    rcases hmem with hp | hp | hp <;> rcases hmem' with hp' | hp' | hp' <;>
      rw [hp, hp'] at hpow ⊢ <;>
      first
        | rfl
        | (rw [← binaryPow_eq_pow, ← binaryPow_eq_pow] at hpow
           revert hpow
           decide)
  have hconst : (((nd j (lb i)).1 * (nd j (lb i)).2 : ℕ) : ZMod P) ≠ 0 := by
    rcases hmem with hp | hp | hp <;> rw [hp] <;>
      exact natCast_ne_zero_small (by norm_num) (lt_P_small (by norm_num))
  have hgi : g ^ (i : ℕ) = g ^ ((i' : ℕ)) := by
    have hc : (((nd j (lb i)).1 * (nd j (lb i)).2 : ℕ) : ZMod P) * g ^ (i : ℕ)
        = (((nd j (lb i)).1 * (nd j (lb i)).2 : ℕ) : ZMod P) * g ^ (i' : ℕ) := by
      push_cast
      calc ((nd j (lb i)).1 : ZMod P) * ((nd j (lb i)).2 : ZMod P) * g ^ (i : ℕ)
          = ((nd j (lb i)).1 : ZMod P) * ((nd j' (lb i')).2 : ZMod P)
              * g ^ (i : ℕ) := by rw [hsame]
        _ = ((nd j' (lb i')).1 : ZMod P) * ((nd j (lb i)).2 : ZMod P)
              * g ^ (i' : ℕ) := hcross
        _ = ((nd j (lb i)).1 : ZMod P) * ((nd j (lb i)).2 : ZMod P)
              * g ^ (i' : ℕ) := by rw [hsame]
    exact mul_left_cancel₀ hconst hc
  have hii : i = i' := (smoothDom g (2 ^ 30) orderOf_g).injective hgi
  subst hii
  exact ⟨fact_nd_inj j j' (lb i) (Finset.mem_range.mpr (lb_lt i)) h h' hsame, rfl⟩

/-! ### The over-budget count -/

/-- The pencil image of subset `j` over its eligible blocks. -/
noncomputable def Im (j : Fin 3) : Finset (ZMod P) :=
  (E j).image fun i => pencilScalar u0 u1 (v0 j) (v1 j) i

theorem card_Im (j : Fin 3) : (Im j).card = 369098752 := by
  rw [Im, Finset.card_image_of_injOn, card_E]
  intro i hi i' hi' heq
  exact (slot_injective (mem_E.mp hi) (mem_E.mp hi') heq).2

theorem disjoint_Im {j j' : Fin 3} (hjj' : j ≠ j') : Disjoint (Im j) (Im j') := by
  refine Finset.disjoint_left.mpr fun γ hγ hγ' => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp hγ'
  exact hjj' (slot_injective (mem_E.mp hi) (mem_E.mp hi') heq.symm).1

section CountAssembly

attribute [local instance] Classical.propDecidable

/-- The radius of the SYZ4 ceiling. -/
noncomputable def δnew : ℝ≥0 := predecessorRadius (2 ^ 30) (22 * 2 ^ 24)

/-- Every pencil value of every eligible slot is a literal `mcaEvent`-bad scalar. -/
theorem Im_subset_bad (j : Fin 3) :
    Im j ⊆ Finset.univ.filter fun γ : ZMod P =>
      mcaEvent (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew u0 u1 γ := by
  intro γ hγ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hγ
  have helig : lb i ∉ SLab j := mem_E.mp hi
  have hiS : i ∉ S j := fun hmem => helig (mem_S.mp hmem)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact mcaEvent_pencil prodCode (v0_mem j) (v1_mem j) (agree_v0 j) (agree_v1 j)
    (uniq_v1 j) (row1_ne j helig) (card_threshold j hiS)

/-- The full bad set: the three disjoint eligible images. -/
noncomputable def badSet : Finset (ZMod P) := Im 0 ∪ Im 1 ∪ Im 2

theorem card_badSet : badSet.card = 1107296256 := by
  have h01 : Disjoint (Im 0) (Im 1) := disjoint_Im (by decide)
  have h012 : Disjoint (Im 0 ∪ Im 1) (Im 2) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_Im (by decide), disjoint_Im (by decide)⟩
  rw [badSet, Finset.card_union_of_disjoint h012, Finset.card_union_of_disjoint h01,
    card_Im, card_Im, card_Im]

theorem badSet_subset_bad :
    badSet ⊆ Finset.univ.filter fun γ : ZMod P =>
      mcaEvent (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew u0 u1 γ :=
  Finset.union_subset (Finset.union_subset (Im_subset_bad 0) (Im_subset_bad 1))
    (Im_subset_bad 2)

/-- **The over-budget bad-scalar count**: `> 2^30` distinct `mcaEvent`-bad scalars at the
`11/32`-predecessor radius. -/
theorem badScalar_count_over_budget :
    2 ^ 30 < (Finset.univ.filter fun γ : ZMod P =>
      mcaEvent (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew u0 u1 γ).card := by
  calc (2 ^ 30 : ℕ) < 1107296256 := by norm_num
    _ = badSet.card := card_badSet.symm
    _ ≤ _ := Finset.card_le_card badSet_subset_bad

/-! ### The ceiling: feeding the over-budget mass through the in-tree engine -/

/-- The two-row stack, as a `WordStack`. -/
noncomputable def ustack : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)) :=
  fun r => if r = 0 then u0 else u1

theorem ustack_zero : ustack 0 = u0 := rfl

theorem ustack_one : ustack 1 = u1 := by
  simp only [ustack, if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The bad mass strictly exceeds `epsStar`: from `P < 1107296256 · 2^128`. -/
theorem epsStar_lt_badMass :
    (ProximityGap.epsStar : ℝ≥0∞) <
      ((1107296256 : ℕ) : ℝ≥0∞) / ((P : ℕ) : ℝ≥0∞) := by
  have hP0 : ((P : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact prime_P.pos.ne'
  have hPtop : ((P : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top P
  have h2t0 : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; norm_num
  have h2ttop : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : ((P : ℕ) : ℝ≥0∞) < ((1107296256 : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul]
    exact_mod_cast
      (show (P : ℕ) < 1107296256 * 2 ^ 128 by
        show (365375409332725729550921208179070755120141565953 : ℕ) < 1107296256 * 2 ^ 128
        norm_num)
  rw [epsStar_coe_eq_natCast_inv,
    ENNReal.lt_div_iff_mul_lt (Or.inl hP0) (Or.inl hPtop),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl h2t0) (Or.inl h2ttop)]
  exact key

/-- **The SYZ4 ceiling (production rate `1/2`, first certified field):**
`mcaDeltaStar (evalCode g (2^30) (2^29 − 1)) epsStar ≤ predecessorRadius (2^30) (22·2^24)`,
i.e. `δ* ≤ 369098751/2^30 = 11/32 − 2^-30 ≈ 0.34375`, unconditional — sharpening the previous
`31/64 ≈ 0.484` ceiling. -/
theorem firstPrime_rateHalf_mcaDeltaStar_le_syz4 :
    mcaDeltaStar
      (F := ZMod P) (A := ZMod P)
      (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ℝ≥0∞)
      ≤ predecessorRadius (2 ^ 30) (22 * 2 ^ 24) := by
  have hbridge : evalCode g (2 ^ 30) (2 ^ 29 - 1)
      = ((prodCode : Submodule (ZMod P) (Fin (2 ^ 30) → ZMod P)) :
          Set (Fin (2 ^ 30) → ZMod P)) := by
    simpa only [prodCode, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 29)] using
      (evalCode_eq_rsCode orderOf_g (2 ^ 29 - 1))
  rw [hbridge]
  -- bad mass lower bound from the explicit over-budget set
  have hbad : ∀ γ ∈ badSet,
      mcaEvent (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew (ustack 0) (ustack 1) γ := by
    intro γ hγ
    rw [ustack_zero, ustack_one]
    have := badSet_subset_bad hγ
    exact (Finset.mem_filter.mp this).2
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod P) (A := ZMod P)
    (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew ustack badSet hbad
  rw [card_badSet, ZMod.card] at hengine
  have hlt : (ProximityGap.epsStar : ℝ≥0∞)
      < epsMCA (F := ZMod P) (A := ZMod P)
          (prodCode : Set (Fin (2 ^ 30) → ZMod P)) δnew :=
    lt_of_lt_of_le epsStar_lt_badMass hengine
  have := ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad
    (F := ZMod P) (A := ZMod P)
    (prodCode : Set (Fin (2 ^ 30) → ZMod P)) (ProximityGap.epsStar : ℝ≥0∞) hlt
  simpa only [δnew] using this

/-- The achieved ceiling in explicit rational form: `δ* ≤ 369098751 / 2^30`. -/
theorem firstPrime_rateHalf_mcaDeltaStar_le_exact :
    mcaDeltaStar
      (F := ZMod P) (A := ZMod P)
      (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ℝ≥0∞)
      ≤ (369098751 : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
  refine le_trans firstPrime_rateHalf_mcaDeltaStar_le_syz4 ?_
  rw [predecessorRadius]
  norm_num

/-- The achieved ceiling is strictly below `11/32` (and, a fortiori, below the previous
`31/64`), while remaining above Johnson `1 − √(1/2)`. -/
theorem syz4_radius_lt_elevenThirtyTwo :
    predecessorRadius (2 ^ 30) (22 * 2 ^ 24) < (11 / 32 : ℝ≥0) := by
  rw [predecessorRadius]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num

end CountAssembly

end Production

end ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling.slot_injective
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling.badScalar_count_over_budget
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling.firstPrime_rateHalf_mcaDeltaStar_le_syz4
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ4DegenerateChannelCeiling.firstPrime_rateHalf_mcaDeltaStar_le_exact
