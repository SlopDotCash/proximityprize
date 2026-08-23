/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2GCXK25

/-!
# GKL24 first-moment bad-witness cardinality bound (#67)

The genuine first-moment content behind `GKL24FirstMomentResidual`: for a *fixed* candidate
codeword `w`, the set of "bad" combining scalars `γ` (those for which `w` witnesses the MCA event
on some large agreement set) is bounded in cardinality by the Hamming weight of `u₁`.

## The mathematics (coordinate-injectivity / first moment)

For each bad scalar `γ` there is a set `S_γ` with `|S_γ| ≥ (1-δ)n` on which `w = u₀ + γ • u₁`.
At any coordinate `i` with `u₁ i ≠ 0`, the equation `w i = u₀ i + γ • u₁ i` determines `γ` **uniquely**
(`γ • u₁ i = γ' • u₁ i ∧ u₁ i ≠ 0 ⟹ γ = γ'`, by `NoZeroSMulDivisors`).  Hence each weight-coordinate
of `u₁` lies in `S_γ` for **at most one** bad `γ`: the sets `{S_γ ∩ supp(u₁)}` are pairwise disjoint.

Counting: their disjoint union sits inside `supp(u₁)`, so
`∑_γ |S_γ ∩ supp(u₁)| ≤ |supp(u₁)|`.  Each term is `≥ |S_γ| - |supp(u₁)ᶜ| ≥ wt(u₁) - δ·n`.  Therefore

  **`|mcaBadWitness| · (wt(u₁) - δ·n) ≤ wt(u₁)`**     (`mcaBadWitness_card_mul_le`)

the first-moment bound: when `u₁` is far from `0` (`wt(u₁) > δ·n`) the bad-scalar count is small,
`|mcaBadWitness| ≤ wt(u₁) / (wt(u₁) - δ·n)`.

This is the reconstructed GKL24/GCXK25 first-moment count, the analogue of the radius-`1/n` J1 cap
(`GrandChallengeJ1Cap.not_three_j1_ratioConstraints`), here at a general agreement radius `δ`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open Finset
open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Coordinate-injectivity of the combining scalar.**  At a coordinate where `u₁` is nonzero, the
line value `u₀ + γ • u₁` determines `γ` uniquely. -/
theorem scalar_unique_of_smul_eq [NoZeroSMulDivisors F A]
    {a : A} (ha : a ≠ 0) {γ γ' : F} (h : γ • a = γ' • a) : γ = γ' := by
  have hz : (γ - γ') • a = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 ha

/-- The support (weight coordinates) of `u₁`. -/
noncomputable def supp₁ (u₁ : ι → A) : Finset ι := Finset.univ.filter (fun i => u₁ i ≠ 0)

@[simp] theorem mem_supp₁ {u₁ : ι → A} {i : ι} : i ∈ supp₁ u₁ ↔ u₁ i ≠ 0 := by
  simp [supp₁]

open Classical in
/-- A witness agreement set for a bad combining scalar `γ`: chosen via `mcaBadWitness`'s defining
existential when `γ` is bad, and `∅` otherwise. -/
noncomputable def badWitnessSet (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ w : ι → A) (γ : F) :
    Finset ι :=
  if h : ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧ ¬ pairJointAgreesOn C S u₀ u₁
    then h.choose else ∅

open Classical in
/-- For a bad scalar, `badWitnessSet` is large and `w` agrees with the line on it. -/
theorem badWitnessSet_spec {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A} {γ : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ((badWitnessSet C δ u₀ u₁ w γ).card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ badWitnessSet C δ u₀ u₁ w γ, w i = u₀ i + γ • u₁ i) := by
  rw [mcaBadWitness, mem_filter] at hγ
  have hex := hγ.2
  unfold badWitnessSet
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1⟩

open Classical in
/-- **Pairwise disjointness on the support.**  Distinct bad scalars have witness sets that are
disjoint on `supp(u₁)`: a weight coordinate uniquely determines the combining scalar. -/
theorem badWitnessSet_inter_supp_disjoint [NoZeroSMulDivisors F A]
    {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A} {γ γ' : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w)
    (hγ' : γ' ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) (hne : γ ≠ γ') :
    Disjoint (badWitnessSet C δ u₀ u₁ w γ ∩ supp₁ u₁)
      (badWitnessSet C δ u₀ u₁ w γ' ∩ supp₁ u₁) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [Finset.mem_inter] at hi hi'
  have hu₁ : u₁ i ≠ 0 := mem_supp₁.mp hi.2
  have hw := (badWitnessSet_spec hγ).2 i hi.1
  have hw' := (badWitnessSet_spec hγ').2 i hi'.1
  -- u₀ i + γ • u₁ i = w i = u₀ i + γ' • u₁ i ⟹ γ • u₁ i = γ' • u₁ i ⟹ γ = γ'
  have hsmul : γ • u₁ i = γ' • u₁ i := by
    have : u₀ i + γ • u₁ i = u₀ i + γ' • u₁ i := by rw [← hw, ← hw']
    exact add_left_cancel this
  exact hne (scalar_unique_of_smul_eq hu₁ hsmul)

/-- Each bad witness set, intersected with `supp(u₁)`, has at least `wt(u₁) - δ·n` coordinates
(inclusion–exclusion against the `≥ (1-δ)n` size bound). -/
theorem card_badWitnessSet_inter_supp_ge {C : Set (ι → A)} {δ : ℝ≥0} (hδ : δ ≤ 1)
    {u₀ u₁ w : ι → A} {γ : F} (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ((supp₁ u₁).card : ℝ) - δ * Fintype.card ι ≤
      ((badWitnessSet C δ u₀ u₁ w γ ∩ supp₁ u₁).card : ℝ) := by
  set S := badWitnessSet C δ u₀ u₁ w γ
  set T := supp₁ u₁
  -- |S ∩ T| + |S ∪ T| = |S| + |T|, and |S ∪ T| ≤ n
  have hie : (S ∩ T).card + (S ∪ T).card = S.card + T.card :=
    Finset.card_inter_add_card_union S T
  have hunion : (S ∪ T).card ≤ Fintype.card ι := Finset.card_le_univ _
  -- |S| ≥ (1-δ)n in ℝ
  have hScardNN : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := (badWitnessSet_spec hγ).1
  have hScardR : (1 - (δ : ℝ)) * Fintype.card ι ≤ (S.card : ℝ) := by
    have := (NNReal.coe_le_coe).mpr hScardNN
    push_cast [NNReal.coe_sub hδ] at this
    linarith [this]
  -- combine: |S ∩ T| = |S| + |T| - |S ∪ T| ≥ (1-δ)n + |T| - n = |T| - δn
  have hieR : ((S ∩ T).card : ℝ) + (S ∪ T).card = S.card + T.card := by exact_mod_cast hie
  have hunionR : ((S ∪ T).card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hunion
  nlinarith [hieR, hunionR, hScardR]

open Classical in
/-- **GKL24 first-moment bad-witness cardinality bound (#67).**

For a fixed candidate codeword `w`, the bad combining scalars are capped by the Hamming weight of
`u₁`:
`|mcaBadWitness| · (wt(u₁) - δ·n) ≤ wt(u₁)`.  When `u₁` is far from `0` (`wt(u₁) > δ·n`) this
forces `|mcaBadWitness| ≤ wt(u₁) / (wt(u₁) - δ·n)`.  Proven by the coordinate-injectivity / first
moment argument: the bad witness sets are pairwise disjoint on `supp(u₁)`, their disjoint union sits
in `supp(u₁)`, and each contributes `≥ wt(u₁) - δ·n` coordinates. -/
theorem mcaBadWitness_card_mul_le [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ w : ι → A) :
    ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) *
        ((supp₁ u₁).card - δ * Fintype.card ι) ≤ (supp₁ u₁).card := by
  set bad := mcaBadWitness (F := F) C δ u₀ u₁ w with hbad
  set T := supp₁ u₁ with hT
  -- disjoint union of the (witness ∩ supp) sets equals the sum of cards
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' →
      Disjoint (badWitnessSet C δ u₀ u₁ w γ ∩ T) (badWitnessSet C δ u₀ u₁ w γ' ∩ T) :=
    fun γ hγ γ' hγ' hne => badWitnessSet_inter_supp_disjoint hγ hγ' hne
  have hsum_eq : (bad.biUnion (fun γ => badWitnessSet C δ u₀ u₁ w γ ∩ T)).card =
      ∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card :=
    Finset.card_biUnion hdisj
  -- the union sits inside T
  have hsub : bad.biUnion (fun γ => badWitnessSet C δ u₀ u₁ w γ ∩ T) ⊆ T := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hγi⟩ := hi
    exact (Finset.mem_inter.mp hγi).2
  -- hence ∑ |witness ∩ T| ≤ |T|
  have hsum_le : (∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card) ≤ T.card := by
    rw [← hsum_eq]; exact Finset.card_le_card hsub
  have hsum_leR : (∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ)) ≤ (T.card : ℝ) := by
    have : ((∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℕ) : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast hsum_le
    push_cast at this; exact this
  -- each term ≥ |T| - δn
  have hterm : ∀ γ ∈ bad, ((T.card : ℝ) - δ * Fintype.card ι) ≤
      ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) :=
    fun γ hγ => card_badWitnessSet_inter_supp_ge hδ hγ
  -- sum the lower bounds: |bad|·(|T| - δn) ≤ ∑ ≤ |T|
  have hlb : (bad.card : ℝ) * ((T.card : ℝ) - δ * Fintype.card ι) ≤
      ∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) := by
    calc
      (bad.card : ℝ) * ((T.card : ℝ) - δ * Fintype.card ι)
          = ∑ _γ ∈ bad, ((T.card : ℝ) - δ * Fintype.card ι) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
      _ ≤ ∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) :=
            Finset.sum_le_sum hterm
  calc (bad.card : ℝ) * ((T.card : ℝ) - δ * Fintype.card ι)
      ≤ ∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) := hlb
    _ ≤ (T.card : ℝ) := hsum_leR

/-- **Per-codeword bad-witness cap (division form).**  When `u₁` is far from `0`
(`wt(u₁) > δ·n`), the bad-scalar count for a fixed `w` is `O(1)`:
`|mcaBadWitness| ≤ wt(u₁) / (wt(u₁) - δ·n)`. -/
theorem mcaBadWitness_card_le_of_weight [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ w : ι → A)
    (hwt : (δ : ℝ) * Fintype.card ι < (supp₁ u₁).card) :
    ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) ≤
      (supp₁ u₁).card / ((supp₁ u₁).card - δ * Fintype.card ι) := by
  have hpos : (0 : ℝ) < (supp₁ u₁).card - δ * Fintype.card ι := by linarith
  rw [le_div_iff₀ hpos]
  exact mcaBadWitness_card_mul_le C δ hδ u₀ u₁ w

/-- **First-moment MCA bad-scalar bound (the #67 assembly).**  Combining the per-codeword cap
above with the union-bound containment `mcaBad ⊆ ⋃_w mcaBadWitness w` over any codeword cover `T`:
for `u₁` far from `0`, the total MCA bad-scalar count is

  `|mcaBad| ≤ |T| · wt(u₁) / (wt(u₁) - δ·n)`.

This is the GKL24/GCXK25 first-moment list-size bound, with the genuinely-mathematical per-codeword
content (`mcaBadWitness_card_mul_le`) discharged in full; the only inputs are a codeword cover `T`
and the far-from-zero condition. -/
theorem mcaBad_card_le_of_weight [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T)
    (hwt : (δ : ℝ) * Fintype.card ι < (supp₁ u₁).card) :
    ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤
      (T.card : ℝ) * ((supp₁ u₁).card / ((supp₁ u₁).card - δ * Fintype.card ι)) := by
  have hpos : (0 : ℝ) < (supp₁ u₁).card - δ * Fintype.card ι := by linarith
  refine mcaBad_card_le_of_per_codeword C δ u₀ u₁ T hT
    (div_nonneg (by positivity) (le_of_lt hpos)) ?_
  intro w _
  exact mcaBadWitness_card_le_of_weight C δ hδ u₀ u₁ w hwt

/-! ### The complementary near-zero branch

The first-moment bound above is vacuous when `u₁` is *sparse* (`wt(u₁) ≤ δ·n`).  That regime is
exactly when `u₁` is itself `δ`-close to the zero codeword: on its zero set (size `≥ (1-δ)n`) it
agrees with `0 ∈ C`.  This is the second half of the MCA dichotomy. -/

/-- **Near-zero witness.**  A sparse `u₁` (`wt(u₁) ≤ δ·n`) agrees with the zero codeword on a set
of size `≥ (1-δ)·n` — its complement of support.  (For a `Submodule` code `0 ∈ C`, so this exhibits
`u₁` as `δ`-close to a codeword.) -/
theorem exists_large_agree_zero_of_small_weight
    (δ : ℝ≥0) (u₁ : ι → A)
    (hwt : ((supp₁ u₁).card : ℝ) ≤ δ * Fintype.card ι) :
    ∃ S : Finset ι, ((1 - δ) * Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
      ∀ i ∈ S, u₁ i = (0 : ι → A) i := by
  refine ⟨(supp₁ u₁)ᶜ, ?_, ?_⟩
  · -- |suppᶜ| = n - |supp| ≥ n - δn = (1-δ)n
    have hcompl : ((supp₁ u₁)ᶜ.card : ℝ) = (Fintype.card ι : ℝ) - (supp₁ u₁).card := by
      rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ _)]
    rw [hcompl]
    nlinarith [hwt]
  · intro i hi
    simp only [Pi.zero_apply]
    by_contra hne
    exact (Finset.mem_compl.mp hi) (mem_supp₁.mpr hne)

/-! ### The uniform bound `|mcaBadWitness| ≤ wt(u₁)`

A bound that holds for **every** stack (no far-from-zero condition), as long as the candidate `w`
and the zero word both lie in the code: each bad scalar's witness set must contain a
`supp(u₁)` coordinate (otherwise the line word agrees with `(w, 0)`, a joint codeword pair on the
whole witness set, contradicting non-joint-agreement), and that coordinate pins the scalar
uniquely.  Hence the bad scalars inject into `supp(u₁)`. -/

open Classical in
/-- The chosen witness set of a bad scalar is non-jointly-agreeing. -/
theorem badWitnessSet_not_joint {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A} {γ : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ¬ pairJointAgreesOn C (badWitnessSet C δ u₀ u₁ w γ) u₀ u₁ := by
  rw [mcaBadWitness, mem_filter] at hγ
  have hex := hγ.2
  unfold badWitnessSet
  rw [dif_pos hex]
  exact hex.choose_spec.2.2

/-- For a bad scalar, the witness set contains a coordinate where `u₁` is nonzero — otherwise the
line word `u₀ + γ • u₁ = u₀` agrees with the joint codeword pair `(w, 0)` on the whole witness set,
contradicting `¬ pairJointAgreesOn`. -/
theorem exists_supp_mem_badWitnessSet {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A}
    (hwC : w ∈ C) (h0C : (0 : ι → A) ∈ C) {γ : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ∃ i ∈ badWitnessSet C δ u₀ u₁ w γ, u₁ i ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply badWitnessSet_not_joint hγ
  refine ⟨w, hwC, 0, h0C, ?_⟩
  intro i hi
  have hu0 : u₁ i = 0 := hcon i hi
  have hwa := (badWitnessSet_spec hγ).2 i hi
  refine ⟨?_, ?_⟩
  · rw [hwa, hu0, smul_zero, add_zero]
  · simp [hu0]

open Classical in
/-- **Uniform bad-witness bound.**  For a candidate `w` in the code (with `0` also in the code),
the bad combining scalars inject into `supp(u₁)`, so `|mcaBadWitness| ≤ wt(u₁) ≤ n`.  Unlike
`mcaBadWitness_card_mul_le`, this holds for *every* stack — no far-from-zero hypothesis — and is the
uniform per-codeword bound that discharges the first-moment residual's `b` over all stacks. -/
theorem mcaBadWitness_card_le_weight [NoZeroSMulDivisors F A]
    {C : Set (ι → A)} (δ : ℝ≥0) {u₀ u₁ w : ι → A}
    (hwC : w ∈ C) (h0C : (0 : ι → A) ∈ C) :
    (mcaBadWitness (F := F) C δ u₀ u₁ w).card ≤ (supp₁ u₁).card := by
  set bad := mcaBadWitness (F := F) C δ u₀ u₁ w with hbad
  -- coordinate-choice function: bad γ ↦ a witnessing supp(u₁) coordinate
  let f : F → ι := fun γ =>
    if h : γ ∈ bad then (exists_supp_mem_badWitnessSet hwC h0C h).choose
    else Classical.arbitrary ι
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · -- f maps bad scalars into supp(u₁)
    intro γ hγ
    have hspec := (exists_supp_mem_badWitnessSet hwC h0C hγ).choose_spec
    have hf : f γ = (exists_supp_mem_badWitnessSet hwC h0C hγ).choose := dif_pos hγ
    rw [hf]
    exact mem_supp₁.mpr hspec.2
  · -- f is injective on bad scalars (the witnessing coordinate pins the scalar)
    intro γ hγ γ' hγ' hfeq
    simp only [Finset.coe_sort_coe, Finset.mem_coe] at hγ hγ'
    have hspec := (exists_supp_mem_badWitnessSet hwC h0C hγ).choose_spec
    have hspec' := (exists_supp_mem_badWitnessSet hwC h0C hγ').choose_spec
    have hf : f γ = (exists_supp_mem_badWitnessSet hwC h0C hγ).choose := dif_pos hγ
    have hf' : f γ' = (exists_supp_mem_badWitnessSet hwC h0C hγ').choose := dif_pos hγ'
    set i := (exists_supp_mem_badWitnessSet hwC h0C hγ).choose with hi
    set i' := (exists_supp_mem_badWitnessSet hwC h0C hγ').choose with hi'
    have hii' : i = i' := by rw [← hf, ← hf']; exact hfeq
    -- at the common coordinate i, w i = u₀ i + γ • u₁ i = u₀ i + γ' • u₁ i
    have hwa : w i = u₀ i + γ • u₁ i := (badWitnessSet_spec hγ).2 i hspec.1
    have hwa' : w i' = u₀ i' + γ' • u₁ i' := (badWitnessSet_spec hγ').2 i' hspec'.1
    rw [← hii'] at hwa'
    have hsmul : γ • u₁ i = γ' • u₁ i := by
      have : u₀ i + γ • u₁ i = u₀ i + γ' • u₁ i := by rw [← hwa, hwa']
      exact add_left_cancel this
    exact scalar_unique_of_smul_eq hspec.2 hsmul

end ProximityGap
