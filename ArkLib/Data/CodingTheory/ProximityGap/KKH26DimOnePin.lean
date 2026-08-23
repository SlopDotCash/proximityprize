/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction

/-!
# The first unconditional `δ*` pin at the KKH26 ceiling: the `r = 2` (dimension-one) slice (#357)

`kkh26_deltaStar_pin_of_interior_ceiling` pins `δ*(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`
conditional on the single named obligation `InteriorCeiling`.  At production dimension that
obligation is the 25-year beyond-Johnson wall.  **This file discharges it at the slice
`(r, m) = (2, 1)`**, where the code `evalCode g (2^μ) 0` has dimension one (constants), and
produces the **first unconditional instantiation of the pin**: for every `μ ≥ 2` and every
`ε*` in the (nonempty) band

  `[((n²−n)/4)/p , (2²·C(2^{μ−1},2))/p)`,   `n = 2^μ`,

we get `mcaDeltaStar(evalCode g (2^μ) 0, ε*) = 1 − 2/2^μ` — **exactly**, axiom-clean.  For
`μ ≥ 3` the pinned radius lies strictly *beyond the Johnson radius* `1 − √ρ` (`ρ = 2^{−μ}`
the rate, `dimOne_ceiling_beyond_johnson`) and strictly below capacity `1 − ρ`
(`dimOne_ceiling_below_capacity`): the first machine-checked exact `δ*` value strictly inside
the open window `(1 − √ρ, 1 − ρ)` for any explicit smooth-domain evaluation code.

**The mechanism (the pair-ownership count).**  For the dimension-one code, a scalar `γ` is
MCA-bad iff some level set `S` of `u₀ + γ·u₁` with `|S| ≥ ⌈(1−δ)n⌉ ≥ 3` is *not* contained
in a single fibre of `i ↦ (u₁ i, u₀ i)`.  On such an `S` the word `u₁` cannot be constant
(constancy of `u₁` plus constancy of `u₀ + γu₁` forces joint constancy, i.e.
`pairJointAgreesOn`), so `S` owns at least `2(|S|−1) ≥ 4` ordered pairs `(i, j)` with
`u₁ i ≠ u₁ j` — and **any such pair determines `γ`**, since
`u₀ i + γ u₁ i = u₀ j + γ u₁ j` solves uniquely for `γ`.  The pair sets of distinct bad
scalars are therefore disjoint subsets of the off-diagonal, giving

  `#bad · 4 ≤ n² − n`,  i.e.  `#bad ≤ (n²−n)/4 = 2^{2μ−2} − 2^{μ−2}`,

strictly below the in-tree KKH26 ceiling count `2^r·C(2^{μ−1}, r)|_{r=2} = 2^{2μ−1} − 2^μ`
(`dimOne_band_nonempty`).  Probe: `scripts/probes/probe_dim1_interior_ceiling.py`
(criterion ⟺ `mcaEvent` byte-exact on 520 stacks × 3 independent checkers, 0 mismatches;
hill-climbed maxima 10 ≤ 14 at `n = 8`, 43 ≤ 60 at `n = 16`).

**Honest scope.**  This pins `δ*` for the dimension-one member of the family only; the
production-dimension conjecture (`k ≥ 2`, the genuine prize core) remains open, and the
regime-split route (`hd1 : 1 ≤ (r−2)m`) correctly never covered this slice.  What is new:
the first unconditional `InteriorCeiling` discharge at any parameter point, the first exact
in-window `δ*`, and the incidence-counting lower-bracket device (the `u₁`-inhomogeneous
pair ownership), which is independent of the staircase/strip machinery and reaches radii
far above the `d ≥ 3b−2` ladder.

The concrete instantiation `deltaStar_pin_F12289` pins `δ* = 3/4` for the dimension-one code
on the 8-point smooth domain `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` (the NTT prime), `ε* = 14/12289`, rate
`ρ = 1/8` — a production rate — with Johnson radius `1 − 1/√8 ≈ 0.646 < 3/4 < 7/8` = capacity.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.KKH26DimOne

/-! ## The dimension-one code: membership characterization -/

/-- Membership in the degree-`0` evaluation code is exactly constancy. -/
theorem mem_evalCode_zero_iff {p : ℕ} {g : ZMod p} {n : ℕ} {w : Fin n → ZMod p} :
    w ∈ evalCode g n 0 ↔ ∃ c : ZMod p, ∀ i, w i = c := by
  constructor
  · rintro ⟨q, hq, hw⟩
    refine ⟨q.coeff 0, fun i => ?_⟩
    rw [hw i]
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_le_zero hq]
    rw [Polynomial.eval_C]
  · rintro ⟨c, hc⟩
    exact ⟨Polynomial.C c, le_of_eq (Polynomial.natDegree_C c), fun i => by
      rw [hc i, Polynomial.eval_C]⟩

/-- Constants belong to the dimension-one code. -/
theorem const_mem_evalCode_zero {p : ℕ} {g : ZMod p} {n : ℕ} (c : ZMod p) :
    (fun _ : Fin n => c) ∈ evalCode g n 0 :=
  mem_evalCode_zero_iff.mpr ⟨c, fun _ => rfl⟩

/-! ## The pair-ownership count -/

/-- `x + y − 1 ≤ x·y` for positive naturals (the cross-fibre block size bound). -/
private lemma add_sub_one_le_mul {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    x + y - 1 ≤ x * y := by
  obtain ⟨x', rfl⟩ := Nat.exists_eq_add_of_le hx
  obtain ⟨y', rfl⟩ := Nat.exists_eq_add_of_le hy
  have h : (1 + x') * (1 + y') = x' * y' + (x' + y' + 1) := by ring
  omega

open Classical in
/-- **The pair-ownership count.**  For the dimension-one code at agreement threshold `> 2`
(i.e. `(1−δ)·n > 2`), every stack `(u₀, u₁)` has at most `(n²−n)/4` bad scalars: each bad
scalar owns at least four ordered cross-fibre pairs `(i, j)` (`u₁ i ≠ u₁ j` inside its
witness level set), distinct bad scalars own disjoint pair sets, and only `n² − n`
off-diagonal pairs exist in total.  Stated multiplicatively to avoid `ℕ`-division. -/
theorem dimOne_badScalars_card_mul_four_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]
    {δ : ℝ≥0} (hδ : (2 : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 0) δ u₀ u₁ γ)
        Finset.univ).card * 4 ≤ n * n - n := by
  classical
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 0) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- Step 1: for every bad scalar, a witness set with the three working properties.
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), 3 ≤ S.card ∧
      (∀ i ∈ S, ∀ j ∈ S, u₀ i + γ * u₁ i = u₀ j + γ * u₁ j) ∧
      ∃ i ∈ S, ∃ j ∈ S, u₁ i ≠ u₁ j := by
    intro γ hγ
    obtain ⟨S, hScard, ⟨w, hwC, hagree⟩, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨c, hc⟩ := mem_evalCode_zero_iff.mp hwC
    have hlevel : ∀ i ∈ S, u₀ i + γ * u₁ i = c := by
      intro i hi
      have h := hagree i hi
      rw [hc i, smul_eq_mul] at h
      exact h.symm
    have hpair : ∀ i ∈ S, ∀ j ∈ S, u₀ i + γ * u₁ i = u₀ j + γ * u₁ j := by
      intro i hi j hj
      rw [hlevel i hi, hlevel j hj]
    have h3 : 3 ≤ S.card := by
      have h2 : (2 : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : (2 : ℕ) < S.card := by exact_mod_cast h2
      omega
    refine ⟨S, h3, hpair, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    refine hnojoint ⟨fun _ => u₀ i₀, const_mem_evalCode_zero _,
      fun _ => u₁ i₀, const_mem_evalCode_zero _, fun i hi => ⟨?_, ?_⟩⟩
    · have h1 : u₀ i + γ * u₁ i = u₀ i₀ + γ * u₁ i₀ := hpair i hi i₀ hi₀
      have h2 : u₁ i = u₁ i₀ := hcon i hi i₀ hi₀
      rw [h2] at h1
      exact (add_right_cancel h1).symm
    · exact (hcon i hi i₀ hi₀).symm
  choose Sf hS3 hSpair hSnc using hwit
  -- Step 2: each bad scalar owns ≥ 4 ordered cross-fibre pairs inside its witness set.
  have hP4 : ∀ γ : {x // x ∈ B}, 4 ≤ (((Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2)).filter
      (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2)).card := by
    intro γ
    obtain ⟨i₀, hi₀, j₀, hj₀, hne⟩ := hSnc γ.1 γ.2
    set Af := (Sf γ.1 γ.2).filter (fun i => u₁ i = u₁ i₀) with hAdef
    set Cf := (Sf γ.1 γ.2).filter (fun i => ¬ u₁ i = u₁ i₀) with hCdef
    have hiA : i₀ ∈ Af := Finset.mem_filter.mpr ⟨hi₀, rfl⟩
    have hjC : j₀ ∈ Cf := Finset.mem_filter.mpr ⟨hj₀, fun h => hne h.symm⟩
    have hA1 : 1 ≤ Af.card := Finset.card_pos.mpr ⟨i₀, hiA⟩
    have hC1 : 1 ≤ Cf.card := Finset.card_pos.mpr ⟨j₀, hjC⟩
    have hsum : Af.card + Cf.card = (Sf γ.1 γ.2).card := by
      rw [hAdef, hCdef]
      exact Finset.card_filter_add_card_filter_not _
    have hsub : (Af ×ˢ Cf) ∪ (Cf ×ˢ Af) ⊆ ((Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2)).filter
        (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2) := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1⟩, ?_⟩
        have e1 := (Finset.mem_filter.mp h1).2
        have e2 := (Finset.mem_filter.mp h2).2
        rw [e1]
        exact fun h => e2 h.symm
      · obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1⟩, ?_⟩
        have e1 := (Finset.mem_filter.mp h1).2
        have e2 := (Finset.mem_filter.mp h2).2
        rw [e2]
        exact e1
    have hdisjAC : Disjoint (Af ×ˢ Cf) (Cf ×ˢ Af) := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      have e1 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_product.mp hq').1).2
      exact e2 e1
    have hprod : 2 ≤ Af.card * Cf.card := by
      have h := add_sub_one_le_mul hA1 hC1
      have hSc := hS3 γ.1 γ.2
      omega
    have hcomm : Cf.card * Af.card = Af.card * Cf.card := Nat.mul_comm _ _
    calc 4 ≤ Af.card * Cf.card + Cf.card * Af.card := by omega
    _ = ((Af ×ˢ Cf) ∪ (Cf ×ˢ Af)).card := by
        rw [Finset.card_union_of_disjoint hdisjAC, Finset.card_product, Finset.card_product]
    _ ≤ _ := Finset.card_le_card hsub
  -- Step 3: the pair sets of distinct bad scalars are disjoint (any cross-fibre pair
  -- inside a common level set determines the scalar).
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (((Sf γ₁.1 γ₁.2) ×ˢ (Sf γ₁.1 γ₁.2)).filter
          (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2))
        (((Sf γ₂.1 γ₂.2) ×ˢ (Sf γ₂.1 γ₂.2)).filter
          (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2)) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨hmem1, hu1⟩ := Finset.mem_filter.mp hq1
    obtain ⟨hmem2, _⟩ := Finset.mem_filter.mp hq2
    obtain ⟨hi1, hj1⟩ := Finset.mem_product.mp hmem1
    obtain ⟨hi2, hj2⟩ := Finset.mem_product.mp hmem2
    have e1 := hSpair γ₁.1 γ₁.2 q.1 hi1 q.2 hj1
    have e2 := hSpair γ₂.1 γ₂.2 q.1 hi2 q.2 hj2
    have key : (γ₁.1 - γ₂.1) * (u₁ q.1 - u₁ q.2) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp key with h | h
    · exact hne (Subtype.ext (sub_eq_zero.mp h))
    · exact hu1 (sub_eq_zero.mp h)
  -- Step 4: assemble through the off-diagonal.
  have hbig : B.attach.card * 4 ≤ (B.attach.biUnion (fun γ =>
      ((Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2)).filter
        (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2))).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * 4 = ∑ _γ ∈ B.attach, 4 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP4 γ)
  have hsub : (B.attach.biUnion (fun γ =>
      ((Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2)).filter
        (fun q : Fin n × Fin n => u₁ q.1 ≠ u₁ q.2)))
      ⊆ (Finset.univ : Finset (Fin n)).offDiag := by
    intro q hq
    obtain ⟨γ, _, hqP⟩ := Finset.mem_biUnion.mp hq
    have hu := (Finset.mem_filter.mp hqP).2
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
      fun h => hu (by rw [h])⟩
  have hoff : ((Finset.univ : Finset (Fin n)).offDiag).card = n * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  calc B.card * 4 = B.attach.card * 4 := by rw [Finset.card_attach]
  _ ≤ _ := hbig
  _ ≤ ((Finset.univ : Finset (Fin n)).offDiag).card := Finset.card_le_card hsub
  _ = n * n - n := hoff

open Classical in
/-- **The dimension-one `ε_mca` bound:** at agreement threshold `> 2`, the MCA error of the
dimension-one code is at most `((n²−n)/4)/p` — uniformly in `δ`. -/
theorem dimOne_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]
    {δ : ℝ≥0} (hδ : (2 : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n 0) δ
      ≤ (((n * n - n) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h4 := dimOne_badScalars_card_mul_four_le (g := g) hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 0) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ (n * n - n) / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr h4
  exact_mod_cast hle

/-! ## The `InteriorCeiling` discharge at `(r, m) = (2, 1)` -/

/-- **The interior ceiling holds unconditionally at the dimension-one slice:** for every
`ε* ≥ ((n²−n)/4)/p` and every `δ` below the KKH26 ceiling `1 − 2/2^μ`, the agreement
threshold exceeds `2`, so the pair-ownership bound applies. -/
theorem interiorCeiling_dimOne
    {p : ℕ} [Fact p.Prime] {μ : ℕ} {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (εstar : ℝ≥0∞)
    (hband : (((n * n - n) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ 1 2 εstar := by
  intro δ hδ
  have hcode : ((2 : ℕ) - 2) * 1 = 0 := by norm_num
  rw [hcode]
  refine le_trans (dimOne_epsMCA_le (g := g) ?_) hband
  have hc2 : ((2 : ℕ) : ℝ≥0) = (2 : ℝ≥0) := by norm_num
  rw [hc2] at hδ
  have hsum : δ + (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 := lt_tsub_iff_right.mp hδ
  have hlt : (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ + δ = δ + (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by ring
    _ < 1 := hsum
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have hmul : (2 : ℝ≥0) < (1 - δ) * (2 : ℝ≥0) ^ μ := by
    have h := mul_lt_mul_of_pos_right hlt hpow0
    rwa [div_mul_cancel₀ _ (ne_of_gt hpow0)] at h
  have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ μ := by
    rw [Fintype.card_fin, hn]
    push_cast
    ring
  rw [hcard]
  exact hmul

/-! ## The `ε*` band is nonempty, and the pinned radius is in the open window -/

/-- **Band nonemptiness:** the incidence bound `(n²−n)/4` sits strictly below the KKH26
ceiling count `2²·C(2^{μ−1}, 2) = 2^{2μ−1} − 2^μ` for every `μ ≥ 2`. -/
theorem dimOne_band_nonempty {μ : ℕ} (hμ : 2 ≤ μ) :
    (2 ^ μ * 2 ^ μ - 2 ^ μ) / 4 < 2 ^ 2 * (2 ^ (μ - 1)).choose 2 := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 2 := ⟨μ - 2, (Nat.sub_add_cancel hμ).symm⟩
  set y := 2 ^ ν with hydef
  have hy : 1 ≤ y := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (ν + 2) = 4 * y := by rw [hydef, pow_add]; ring
  have hpow1 : (2 : ℕ) ^ (ν + 2 - 1) = 2 * y := by
    have h21 : ν + 2 - 1 = ν + 1 := by omega
    rw [h21, hydef, pow_add]; ring
  rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 4), hpow, hpow1, Nat.choose_two_right]
  have hch : 2 * y * (2 * y - 1) / 2 = y * (2 * y - 1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
  rw [hch]
  have h16 : 4 * y * (4 * y) = 16 * (y * y) := by ring
  have hgoal : 2 ^ 2 * (y * (2 * y - 1)) * 4 = 16 * (y * (2 * y - 1)) := by ring
  rw [h16, hgoal]
  have ha : y ≤ y * y := Nat.le_mul_of_pos_left y (by omega)
  have hb : y * y ≤ y * (2 * y - 1) := by
    refine Nat.mul_le_mul_left y ?_
    omega
  have key : ∀ a b z : ℕ, 1 ≤ z → z ≤ a → a ≤ b → 16 * a - 4 * z < 16 * b := by
    intro a b z h1 h2 h3
    omega
  exact key (y * y) (y * (2 * y - 1)) y hy ha hb

/-- **Beyond Johnson (squared form):** for `μ ≥ 3` the ceiling's distance to `1` is strictly
below the Johnson distance `√ρ` (`ρ = 2^{−μ}` the rate of the dimension-one code), stated
square-free as `(2/2^μ)² < ρ`.  Hence the pinned radius `1 − 2/2^μ` lies strictly beyond the
Johnson radius `1 − √ρ`. -/
theorem dimOne_ceiling_beyond_johnson_sq {μ : ℕ} (hμ : 3 ≤ μ) :
    ((2 : ℝ≥0) / (2 : ℝ≥0) ^ μ) ^ 2 < ((2 : ℝ≥0) ^ μ)⁻¹ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  rw [div_pow, inv_eq_one_div, div_lt_div_iff₀ (by positivity) hpow0, one_mul, ← pow_mul]
  calc (2 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ μ = (2 : ℝ≥0) ^ (2 + μ) := by rw [pow_add]
  _ < (2 : ℝ≥0) ^ (μ * 2) := by
      refine pow_lt_pow_right₀ one_lt_two ?_
      omega

/-- **Below capacity:** the pinned radius `1 − 2/2^μ` is strictly below capacity
`1 − ρ = 1 − (2^μ)⁻¹` for every `μ ≥ 1`. -/
theorem dimOne_ceiling_below_capacity {μ : ℕ} (hμ : 1 ≤ μ) :
    (1 : ℝ≥0) - (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - ((2 : ℝ≥0) ^ μ)⁻¹ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have h2le : (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ ≤ 1 := by
    rw [div_le_one hpow0]
    calc (2 : ℝ≥0) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ μ := pow_le_pow_right₀ one_le_two hμ
  have hlt : ((2 : ℝ≥0) ^ μ)⁻¹ < (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
    rw [inv_eq_one_div, div_lt_div_iff₀ hpow0 hpow0]
    have h12 : (1 : ℝ≥0) * (2 : ℝ≥0) ^ μ = (2 : ℝ≥0) ^ μ := one_mul _
    rw [h12]
    calc (2 : ℝ≥0) ^ μ = 1 * (2 : ℝ≥0) ^ μ := (one_mul _).symm
    _ < 2 * (2 : ℝ≥0) ^ μ := by
        refine mul_lt_mul_of_pos_right ?_ hpow0
        exact one_lt_two
  have hinv1 : ((2 : ℝ≥0) ^ μ)⁻¹ ≤ 1 := le_trans hlt.le h2le
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub h2le, NNReal.coe_sub hinv1, NNReal.coe_one]
  have hltR := NNReal.coe_lt_coe.mpr hlt
  linarith

/-! ## THE PIN -/

/-- **THE FIRST UNCONDITIONAL `δ*` PIN AT THE KKH26 CEILING.**  For the dimension-one code
on the smooth `2^μ`-point domain (`μ ≥ 2`) and every `ε*` in the band
`[((n²−n)/4)/p, (2²·C(2^{μ−1},2))/p)` — nonempty by `dimOne_band_nonempty` —

  `mcaDeltaStar(evalCode g (2^μ) 0, ε*) = 1 − 2/2^μ`

with **no open obligation**: the good side is the pair-ownership incidence bound, the bad
side is the in-tree KKH26 witness spread.  For `μ ≥ 3` the pinned value lies strictly inside
the open window (beyond Johnson, below capacity). -/
theorem kkh26_dimOne_deltaStar_pin
    {p : ℕ} [Fact p.Prime] {μ : ℕ} (hμ : 2 ≤ μ) {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (εstar : ℝ≥0∞)
    (hlo : (((n * n - n) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ 2 * (2 ^ (μ - 1)).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n 0) εstar
      = 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hr : (2 : ℕ) ≤ 2 ^ (μ - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (μ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcode : ((2 : ℕ) - 2) * 1 = 0 := by norm_num
  have h := kkh26_deltaStar_pin_of_interior_ceiling (p := p) (n := n) (μ := μ) (m := 1)
    (r := 2) (g := g) (hμ := by omega) (hm := le_rfl) (hn := by rw [hn, mul_one])
    (hg := by rw [mul_one]; exact hg) (hp := hp) (hr2 := le_rfl) (hr := hr)
    (εstar := εstar) (hεstar := hhi)
    (hceiling := interiorCeiling_dimOne hn εstar hlo)
  rw [hcode] at h
  have hc2 : ((2 : ℕ) : ℝ≥0) = (2 : ℝ≥0) := by norm_num
  rw [hc2] at h
  exact h

/-- **The canonical pin:** at `ε* = ((n²−n)/4)/p` itself the pin always fires — band
membership is definitional on the left and `dimOne_band_nonempty` on the right. -/
theorem kkh26_dimOne_deltaStar_pin_canonical
    {p : ℕ} [Fact p.Prime] {μ : ℕ} (hμ : 2 ≤ μ) {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n 0)
        ((((n * n - n) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      = 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  refine kkh26_dimOne_deltaStar_pin hμ hn hg hp _ le_rfl ?_
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hlt' : (((n * n - n) / 4 : ℕ) : ℝ≥0∞)
      < ((2 ^ 2 * (2 ^ (μ - 1)).choose 2 : ℕ) : ℝ≥0∞) := by
    rw [hn]
    exact_mod_cast dimOne_band_nonempty hμ
  exact ENNReal.div_lt_div_right hp0 hpt hlt'

end ArkLib.ProximityGap.KKH26DimOne

/-! ## The concrete instantiation: `δ* = 3/4` at the NTT prime `p = 12289` -/

namespace ArkLib.ProximityGap.KKH26DimOne

section Concrete

local instance fact_prime_12289 : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- `4043` has multiplicative order `8` in `F₁₂₂₈₉` (`4043⁴ = −1`). -/
theorem orderOf_4043 : orderOf (4043 : ZMod 12289) = 8 := by
  have h4 : ¬ (4043 : ZMod 12289) ^ (2 : ℕ) ^ 2 = 1 := by decide
  have h8 : (4043 : ZMod 12289) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (4043 : ZMod 12289)) h4 h8
  norm_num at h
  exact h

/-- **The concrete pin at the NTT prime:** `δ* = 3/4` exactly, for the dimension-one code on
the 8-point smooth domain `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 14/12289`.  The rate is `ρ = 1/8` (a
production rate), the Johnson radius is `1 − 1/√8 ≈ 0.6464 < 3/4`, capacity `7/8 > 3/4`:
an exact `δ*` value strictly inside the open window, machine-checked end to end. -/
theorem deltaStar_pin_F12289 :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 0) ((14 : ℝ≥0∞) / (12289 : ℝ≥0∞))
      = 3 / 4 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_dimOne_deltaStar_pin_canonical (p := 12289) (μ := 3)
    (g := (4043 : ZMod 12289)) (n := 8) (by norm_num) (by norm_num) orderOf_4043
    (by norm_num)
  have e1 : (((8 * 8 - 8) / 4 : ℕ) : ℝ≥0∞) = (14 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 3 / 4 := by
    have hd : (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 1 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

end Concrete

end ArkLib.ProximityGap.KKH26DimOne

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimOne.dimOne_badScalars_card_mul_four_le
#print axioms ArkLib.ProximityGap.KKH26DimOne.dimOne_epsMCA_le
#print axioms ArkLib.ProximityGap.KKH26DimOne.interiorCeiling_dimOne
#print axioms ArkLib.ProximityGap.KKH26DimOne.dimOne_band_nonempty
#print axioms ArkLib.ProximityGap.KKH26DimOne.kkh26_dimOne_deltaStar_pin
#print axioms ArkLib.ProximityGap.KKH26DimOne.kkh26_dimOne_deltaStar_pin_canonical
#print axioms ArkLib.ProximityGap.KKH26DimOne.deltaStar_pin_F12289
