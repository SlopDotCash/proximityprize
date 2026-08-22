/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket

/-!
# SYZ2: the degenerate-subset pencil channel, formalized (issue #466 / #507)

This file formalizes the SYZ1 channel
(`docs/kb/deltastar-466-syz1-predecessor-cap-refuted-2026-07-10.md`, probe
`scripts/probes/probe_syzygy_configuration_bad_counts.py`, functions
`degenerate_gamma_candidates` / `verify_bad`) against the literal `mcaEvent`
of `Errors.lean`.

**The channel.** Call a subset `S` *degenerate* for a stack `(u₀, u₁)` over a linear
code `C` when both restrictions `uᵢ|S` are restrictions of codewords `vᵢ`. Then for
every off-`S` point `x` where `u₁ x ≠ v₁ x`, the *pencil scalar*
`γₓ = −(u₀ x − v₀ x)/(u₁ x − v₁ x)` is genuinely `mcaEvent`-bad: the line
`u₀ + γₓ • u₁` agrees with the codeword `v₀ + γₓ • v₁` on `S ∪ {x}`
(`pencil_line_agrees`), while `pairJointAgreesOn` fails on that same witness set
because the unique `S`-interpolant of `u₁` misses `u₁` at `x`
(`not_pairJointAgreesOn_insert`). Distinct pencil values give distinct bad scalars,
so one degenerate subset donates the whole image of the pencil map
(`badScalar_count_ge_of_degenerate_subset`), and a family of degenerate subsets
donates the union of the images (`badScalar_count_ge_of_degenerate_family`).

**Constructive supply.** Degenerate stacks are free to build: for any codewords
`v₀, v₁`, any `S` with the interpolation-uniqueness property, any `d₁` vanishing on
`S` and nonvanishing off `S`, and any `f` injective off `S`, the stack
`(v₀ + f·d₁, v₁ + d₁)` has pencil `γₓ = −f x` off `S`, hence at least
`n − |S|` distinct bad scalars (`badScalar_count_ge_of_constructed_stack`).

**Production instantiation (single subset).** At the first certified prize field
(`P = 2^30·(2^128+192)+1`, code `evalCode g (2^30) (2^29−1)`, i.e. RS of dimension
`2^29` on the smooth domain), with `S` the initial segment of size
`t = 553648129 ≥ 2^29` (so uniqueness is RS interpolation,
`rsCode_eq_of_agree_on_card_le`) and radius `predecessorRadius (2^30) (31·2^24)`,
the explicit stack `(f·d₁, d₁)` — `d₁` the indicator of the tail, `f` the
enumeration embedding into `ZMod P` — carries at least

  `n − t = 31·2^24 − 1 = 520093695`

`mcaEvent`-bad scalars (`firstPrime_production_singleSubset_badScalar_lower`).
This is a machine-checked production-scale lower bound of ≈ 48% of the `2^30`
budget of the `hcount` hypothesis of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`
(`Frontier/_PrizeShapeRateHalfBracket.lean`), from a **single** degenerate subset.

**Honest scope.** The full refutation `¬hcount` needs a stack that is degenerate for
`D = 3` subsets simultaneously with essentially disjoint pencil images
(`3·(n−t) ≈ 1.56·10^9 > 2^30`); the probe verifies this channel is exactly additive
at analogue scales (n = 32 with D = 3/7, n = 64 with D = 7/15, all over budget,
field-size-free). The remaining Lean step is precisely named here:
`OverBudgetDegenerateStackExists`, and
`firstPrime_predecessor_cap_refuted_of_overBudget_stack` reduces `¬hcount` to it.
This file does **not** claim `¬hcount`; it lands the channel plus the
single-subset production instantiation.

**Untouched:** the unconditional bracket `178956971/2^30 ≤ δ* ≤ 31/64` and the CORE.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Finset Polynomial
open scoped NNReal ENNReal
open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership Code
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore

attribute [local instance] Classical.propDecidable

/-! ## The general channel -/

section Channel

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The pencil scalar attached to an off-`S` point `x` of a degenerate subset:
the unique `γ` for which the line `u₀ + γ • u₁` picks up the extra agreement
point `x` against the codeword pencil `v₀ + γ • v₁`. -/
noncomputable def pencilScalar (u₀ u₁ v₀ v₁ : ι → F) (x : ι) : F :=
  -((u₀ x - v₀ x) / (u₁ x - v₁ x))

/-- **(a) Pure algebra of the pencil.** If `v₀, v₁` agree with `u₀, u₁` on `S` and
`u₁ x ≠ v₁ x`, then the codeword combination `v₀ + γₓ • v₁` agrees with the line
`u₀ + γₓ • u₁` on all of `S ∪ {x}`. -/
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

/-- **(b) The pair-joint clause fails on the enlarged witness set.** If every
codeword agreeing with `u₁` on `S` equals `v₁` (interpolation uniqueness on `S`),
and `u₁ x ≠ v₁ x`, then no codeword pair jointly agrees with `(u₀, u₁)` on
`S ∪ {x}`: the `u₁`-side codeword is forced to be `v₁`, which misses `x`. -/
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

/-- **The per-point channel.** On a degenerate subset `S` (with interpolation
uniqueness for the `u₁` side), every off-pencil point `x` with `u₁ x ≠ v₁ x`
produces a literal `mcaEvent`-bad scalar, provided the enlarged witness set
`S ∪ {x}` clears the radius threshold. -/
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

/-- **(c) The per-subset counting form.** One degenerate subset donates at least
the image of its pencil map over the eligible off-`S` points to the bad-scalar
count at radius `δ`. -/
theorem badScalar_count_ge_of_degenerate_subset (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {S : Finset ι} {u₀ u₁ v₀ v₁ : ι → F}
    (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C)
    (h₀ : ∀ i ∈ S, v₀ i = u₀ i) (h₁ : ∀ i ∈ S, v₁ i = u₁ i)
    (huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁)
    (hcard : ((S.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    ((Finset.univ.filter fun x : ι => x ∉ S ∧ u₁ x ≠ v₁ x).image
        (pencilScalar u₀ u₁ v₀ v₁)).card
      ≤ (Finset.univ.filter fun γ : F =>
          mcaEvent (C : Set (ι → F)) δ u₀ u₁ γ).card := by
  apply Finset.card_le_card
  intro γ hγ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨hxS, hd₁⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  refine mcaEvent_pencil C hv₀ hv₁ h₀ h₁ huniq₁ hd₁ ?_
  rw [Finset.card_insert_of_notMem hxS]
  exact_mod_cast hcard

/-- **The `D`-subset counting scaffold.** A family of degenerate subsets donates
the *union* of its pencil images. This is the additive stacking used by the SYZ1
probe (`D·(n−t)` bad scalars when the images are disjoint); the construction of a
production `D = 3` family is the named residual below. -/
theorem badScalar_count_ge_of_degenerate_family {κ : Type} [DecidableEq κ]
    (C : Submodule F (ι → F)) {δ : ℝ≥0} {u₀ u₁ : ι → F}
    (I : Finset κ) (S : κ → Finset ι) (v₀ v₁ : κ → ι → F)
    (hv₀ : ∀ j ∈ I, v₀ j ∈ C) (hv₁ : ∀ j ∈ I, v₁ j ∈ C)
    (h₀ : ∀ j ∈ I, ∀ i ∈ S j, v₀ j i = u₀ i)
    (h₁ : ∀ j ∈ I, ∀ i ∈ S j, v₁ j i = u₁ i)
    (huniq₁ : ∀ j ∈ I, ∀ w ∈ (C : Set (ι → F)),
      (∀ i ∈ S j, w i = u₁ i) → w = v₁ j)
    (hcard : ∀ j ∈ I, (((S j).card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    (I.biUnion fun j =>
        (Finset.univ.filter fun x : ι => x ∉ S j ∧ u₁ x ≠ v₁ j x).image
          (pencilScalar u₀ u₁ (v₀ j) (v₁ j))).card
      ≤ (Finset.univ.filter fun γ : F =>
          mcaEvent (C : Set (ι → F)) δ u₀ u₁ γ).card := by
  apply Finset.card_le_card
  intro γ hγ
  obtain ⟨j, hj, hγj⟩ := Finset.mem_biUnion.mp hγ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγj
  obtain ⟨hxS, hd₁⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  refine mcaEvent_pencil C (hv₀ j hj) (hv₁ j hj) (h₀ j hj) (h₁ j hj)
    (huniq₁ j hj) hd₁ ?_
  rw [Finset.card_insert_of_notMem hxS]
  exact_mod_cast hcard j hj

/-- **(d) The constructive stack.** For any codewords `v₀, v₁`, any subset `S`
with the two-sided interpolation-uniqueness property, any `d₁` vanishing on `S`
and nonvanishing off `S`, and any `f` injective off `S`, the explicitly
constructed stack `(v₀ + f·d₁, v₁ + d₁)` has at least `n − |S|` distinct
`mcaEvent`-bad scalars (its pencil is `γₓ = −f x`). -/
theorem badScalar_count_ge_of_constructed_stack (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {S : Finset ι} {v₀ v₁ : ι → F} (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C)
    (hSuniq : ∀ w ∈ (C : Set (ι → F)), ∀ w' ∈ (C : Set (ι → F)),
      (∀ i ∈ S, w i = w' i) → w = w')
    (d₁ f : ι → F)
    (hd₁S : ∀ i ∈ S, d₁ i = 0)
    (hd₁off : ∀ x, x ∉ S → d₁ x ≠ 0)
    (hf : ∀ x, x ∉ S → ∀ y, y ∉ S → f x = f y → x = y)
    (hcard : ((S.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    Fintype.card ι - S.card
      ≤ (Finset.univ.filter fun γ : F =>
          mcaEvent (C : Set (ι → F)) δ
            (v₀ + fun x => f x * d₁ x) (v₁ + d₁) γ).card := by
  set u₀ : ι → F := v₀ + fun x => f x * d₁ x with hu₀
  set u₁ : ι → F := v₁ + d₁ with hu₁
  have h₀ : ∀ i ∈ S, v₀ i = u₀ i := by
    intro i hi
    simp [hu₀, hd₁S i hi]
  have h₁ : ∀ i ∈ S, v₁ i = u₁ i := by
    intro i hi
    simp [hu₁, hd₁S i hi]
  have huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁ := by
    intro w hw hagree
    refine hSuniq w hw v₁ hv₁ fun i hi => ?_
    rw [hagree i hi, ← h₁ i hi]
  have hXeq : (Finset.univ.filter fun x : ι => x ∉ S ∧ u₁ x ≠ v₁ x)
      = Finset.univ.filter fun x : ι => x ∉ S := by
    refine Finset.filter_congr fun x _ => ?_
    refine and_iff_left_iff_imp.mpr fun hxS heq => hd₁off x hxS ?_
    have hsum : v₁ x + d₁ x = v₁ x := by simpa [hu₁] using heq
    have := congrArg (fun z => z - v₁ x) hsum
    simpa using this
  have hpencil : ∀ x, x ∉ S → pencilScalar u₀ u₁ v₀ v₁ x = -f x := by
    intro x hxS
    have hne := hd₁off x hxS
    have e0 : u₀ x - v₀ x = f x * d₁ x := by simp [hu₀]
    have e1 : u₁ x - v₁ x = d₁ x := by simp [hu₁]
    rw [pencilScalar, e0, e1, mul_div_assoc, div_self hne, mul_one]
  have himg : ((Finset.univ.filter fun x : ι => x ∉ S ∧ u₁ x ≠ v₁ x).image
      (pencilScalar u₀ u₁ v₀ v₁)).card = Fintype.card ι - S.card := by
    rw [hXeq, Finset.card_image_of_injOn, show
        (Finset.univ.filter fun x : ι => x ∉ S) = Sᶜ from by
          ext x; simp, Finset.card_compl]
    intro x hx y hy hxy
    have hxS := (Finset.mem_filter.mp hx).2
    have hyS := (Finset.mem_filter.mp hy).2
    rw [hpencil x hxS, hpencil y hyS] at hxy
    exact hf x hxS y hyS (neg_injective hxy)
  calc Fintype.card ι - S.card
      = ((Finset.univ.filter fun x : ι => x ∉ S ∧ u₁ x ≠ v₁ x).image
          (pencilScalar u₀ u₁ v₀ v₁)).card := himg.symm
    _ ≤ _ := badScalar_count_ge_of_degenerate_subset C hv₀ hv₁ h₀ h₁ huniq₁ hcard

end Channel

/-! ## Reed–Solomon interpolation uniqueness -/

section RSUniqueness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **RS interpolation uniqueness.** Two codewords of `rsCode dom k` agreeing on a
subset of at least `k` points are equal: their difference comes from a polynomial of
degree `< k` vanishing at `≥ k` distinct domain points. This is the `huniq` /
`hSuniq` input of the channel, discharged at any `|S| ≥ k`. -/
theorem rsCode_eq_of_agree_on_card_le {n : ℕ} [NeZero n]
    (dom : Fin n ↪ F) {k : ℕ} {S : Finset (Fin n)} (hk : k ≤ S.card)
    {w w' : Fin n → F} (hw : w ∈ rsCode dom k) (hw' : w' ∈ rsCode dom k)
    (hagree : ∀ i ∈ S, w i = w' i) : w = w' := by
  obtain ⟨P, hP, rfl⟩ := hw
  obtain ⟨Q, hQ, rfl⟩ := hw'
  have hPQ : P - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := P - Q) (s := S.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ dom.injective]
      calc (P - Q).degree ≤ max P.degree Q.degree := Polynomial.degree_sub_le P Q
        _ < (k : WithBot ℕ) := max_lt hP hQ
        _ ≤ (S.card : WithBot ℕ) := by exact_mod_cast hk
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.eval_sub, sub_eq_zero]
      exact hagree i hi
  have hPQ' : P = Q := sub_eq_zero.mp hPQ
  rw [hPQ']

end RSUniqueness

/-! ## Production instantiation at the first certified prize field -/

section Production

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

local instance localInstance_SYZ2PredecessorCapRefutationCore_1 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨prime_P⟩

local instance localInstance_SYZ2PredecessorCapRefutationCore_2 : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

/-- The degenerate subset: the initial segment of size `t = 553648129 = 2^30 − (31·2^24 − 1)`,
which is `≥ k = 2^29`, so RS interpolation uniqueness holds on it. -/
noncomputable def prodS : Finset (Fin (2 ^ 30)) :=
  Finset.univ.map (Fin.castLEEmb (show (553648129 : ℕ) ≤ 2 ^ 30 by norm_num))

theorem mem_prodS_iff {x : Fin (2 ^ 30)} : x ∈ prodS ↔ (x : ℕ) < 553648129 := by
  constructor
  · rintro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact i.isLt
  · intro hx
    exact Finset.mem_map.mpr ⟨⟨(x : ℕ), hx⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem card_prodS : prodS.card = 553648129 := by
  rw [prodS, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The second-row perturbation: the indicator of the off-`S` tail. -/
noncomputable def prodD₁ : Fin (2 ^ 30) → ZMod P := fun x =>
  if (x : ℕ) < 553648129 then 0 else 1

/-- The pencil-labelling function: the enumeration embedding `Fin (2^30) ↪ ZMod P`
(injective since `2^30 < P`). -/
noncomputable def prodF : Fin (2 ^ 30) → ZMod P := fun x => ((x : ℕ) : ZMod P)

theorem prodF_injective : Function.Injective prodF := by
  intro x y hxy
  have hx : ((x : ℕ) : ZMod P).val = (x : ℕ) :=
    ZMod.val_natCast_of_lt (lt_trans x.isLt (by norm_num))
  have hy : ((y : ℕ) : ZMod P).val = (y : ℕ) :=
    ZMod.val_natCast_of_lt (lt_trans y.isLt (by norm_num))
  have := congrArg ZMod.val hxy
  rw [prodF, prodF] at this
  exact Fin.ext (by rw [← hx, ← hy]; exact this)

/-- The radius-threshold arithmetic: at `δ = predecessorRadius (2^30) (31·2^24)`
the required witness size `(1 − δ)·n` is exactly `t = 553648129 = |S| < |S| + 1`. -/
theorem prod_card_threshold :
    ((prodS.card + 1 : ℕ) : ℝ≥0)
      ≥ (1 - predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
          * Fintype.card (Fin (2 ^ 30)) := by
  rw [card_prodS, Fintype.card_fin]
  have hδ : predecessorRadius (2 ^ 30) (31 * 2 ^ 24)
      = (520093695 : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
    rw [predecessorRadius]
    norm_num
  have hle : (1 : ℝ≥0) - predecessorRadius (2 ^ 30) (31 * 2 ^ 24)
      ≤ (553648129 : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
    rw [tsub_le_iff_right, hδ, ← add_div,
      show (553648129 : ℝ≥0) + 520093695 = 2 ^ 30 by norm_num,
      div_self (by norm_num : (2 ^ 30 : ℝ≥0) ≠ 0)]
  calc (1 - predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) * ((2 ^ 30 : ℕ) : ℝ≥0)
      ≤ ((553648129 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) * ((2 ^ 30 : ℕ) : ℝ≥0) := by
        gcongr
    _ = (553648129 : ℝ≥0) := by
        rw [div_mul_eq_mul_div]
        norm_num
    _ ≤ ((553648130 : ℕ) : ℝ≥0) := by norm_num

/-- **The production single-subset lower bound.** At the first certified prize
field and the production code `evalCode g (2^30) (2^29 − 1)`, the explicit stack
`(prodF · prodD₁, prodD₁)` carries at least `31·2^24 − 1 = 520093695` literal
`mcaEvent`-bad scalars at the `31/64`-predecessor radius — about 48% of the `2^30`
budget of the `hcount` cap, from a **single** degenerate subset. -/
theorem firstPrime_production_singleSubset_badScalar_lower :
    (520093695 : ℕ)
      ≤ (Finset.univ.filter fun γ : ZMod P =>
          mcaEvent (evalCode g (2 ^ 30) (2 ^ 29 - 1))
            (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
            ((0 : Fin (2 ^ 30) → ZMod P) + fun x => prodF x * prodD₁ x)
            ((0 : Fin (2 ^ 30) → ZMod P) + prodD₁) γ).card := by
  have hbridge : evalCode g (2 ^ 30) (2 ^ 29 - 1)
      = ((rsCode (smoothDom g (2 ^ 30) orderOf_g) (2 ^ 29) :
          Submodule (ZMod P) (Fin (2 ^ 30) → ZMod P)) :
          Set (Fin (2 ^ 30) → ZMod P)) := by
    simpa only [Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 29)] using
      (evalCode_eq_rsCode orderOf_g (2 ^ 29 - 1))
  simp only [hbridge]
  have hmain := badScalar_count_ge_of_constructed_stack
    (rsCode (smoothDom g (2 ^ 30) orderOf_g) (2 ^ 29))
    (δ := predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
    (S := prodS) (v₀ := 0) (v₁ := 0)
    (Submodule.zero_mem _) (Submodule.zero_mem _)
    (fun w hw w' hw' hagree =>
      rsCode_eq_of_agree_on_card_le (smoothDom g (2 ^ 30) orderOf_g)
        (by rw [card_prodS]; norm_num) hw hw' hagree)
    prodD₁ prodF
    (fun i hi => by rw [prodD₁, if_pos (mem_prodS_iff.mp hi)])
    (fun x hx => by
      rw [prodD₁, if_neg (fun hlt => hx (mem_prodS_iff.mpr hlt))]
      exact one_ne_zero)
    (fun x _ y _ hxy => prodF_injective hxy)
    prod_card_threshold
  refine le_trans ?_ hmain
  have h1 : Fintype.card (Fin (2 ^ 30)) = 1073741824 := by
    rw [Fintype.card_fin]
    norm_num
  have h2 := card_prodS
  omega

/-! ## The precisely named residual and the refutation reduction -/

/-- **The SYZ2 residual (open).** There exists a stack whose `mcaEvent`-bad-scalar
count at the `31/64`-predecessor radius strictly exceeds the `2^30` budget.

The SYZ1 probe evidence: a `D = 3` simultaneous degenerate stack yields
`3·(31·2^24 − 1) ≈ 1.56·10^9 > 2^30` with exact additivity at both probed analogue
scales; the syndrome rank budget `2(t−k)·D < 2(n−k)` admits `D ≤ 30`. What remains
in Lean is constructing a stack simultaneously degenerate for three subsets with
essentially disjoint pencil images. -/
def OverBudgetDegenerateStackExists : Prop :=
  ∃ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    2 ^ 30 < (Finset.univ.filter fun γ : ZMod P =>
      mcaEvent (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) (u 0) (u 1) γ).card

/-- **The refutation reduction.** An over-budget stack refutes the literal `hcount`
hypothesis of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`. -/
theorem firstPrime_predecessor_cap_refuted_of_overBudget_stack
    (hover : OverBudgetDegenerateStackExists) :
    ¬ (∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun γ : ZMod P =>
        mcaEvent (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
          (u 0) (u 1) γ).card ≤ 2 ^ 30) := by
  intro hcount
  obtain ⟨u, hu⟩ := hover
  exact absurd (hcount u) (not_le.mpr hu)

end Production

end ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.pencil_line_agrees
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.not_pairJointAgreesOn_insert
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.mcaEvent_pencil
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.badScalar_count_ge_of_degenerate_subset
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.badScalar_count_ge_of_degenerate_family
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.badScalar_count_ge_of_constructed_stack
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.rsCode_eq_of_agree_on_card_le
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.firstPrime_production_singleSubset_badScalar_lower
#print axioms ArkLib.ProximityGap.Frontier.SYZ2PredecessorCapRefutationCore.firstPrime_predecessor_cap_refuted_of_overBudget_stack
