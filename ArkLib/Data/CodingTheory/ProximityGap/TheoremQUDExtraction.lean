/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.TheoremQAssembly
import ArkLib.Data.CodingTheory.ProximityGap.TheoremQUpperReduction

/-!
# O77's affine-root extraction residual, discharged on the window `3(n−t) < d` (#232)

`TheoremQUpperReduction.epsMCA_le_of_affineRoot_extraction` (O77) reduced the upper half of
the Theorem-Q determination to one named residual: for every stack `u` an affine error pair
`(e₀ u, e₁ u)` with `weight(e₁ u) ≤ W` whose line `e₀ + γ·e₁` has a root at a support
coordinate of `e₁` for *every* `mcaEvent`-bad scalar `γ`.  Its docstring asserted the
residual is "provably true in the unique-decoding regime `δ < (d−1)/2n`".  This file proves
the extraction — but on the window **`3·(n − t) < d`** (`t = ⌈(1−δ)n⌉₊`; in δ-units
`δ < d/(3n)`), and records that the *mechanism* the docstring appealed to genuinely breaks
strictly between `d/(3n)` and `(d−1)/(2n)`.

## The construction (`exists_affine_pair`)

If a stack has two distinct bad scalars `γ₁ ≠ γ₂` with closeness codewords `w₁, w₂` on
witness sets `S₁, S₂` (each of size `≥ t`), the affine solve

  `c₁ := (γ₁−γ₂)⁻¹·(w₁ − w₂)`,  `c₀ := w₁ − γ₁·c₁`

produces codewords (linearity) with `e₀ := u₀ − c₀`, `e₁ := u₁ − c₁` vanishing on
`S₁ ∩ S₂` (size `≥ 2t − n`), so `weight(e₁) ≤ 2(n−t)`.  For *any* further bad `γ` with
witness `(S, w)`, the codeword `d_γ := w − (c₀ + γ·c₁)` vanishes on `S \ (supp e₀ ∪ supp e₁)`,
hence `weight(d_γ) ≤ (n−t) + 2(n−t) = 3(n−t) < d`, forcing `d_γ = 0` by the minimum
distance: the decoding law is affine in `γ`.  The `¬ pairJointAgreesOn` clause then hands a
coordinate `x ∈ S` where `(c₀, c₁)` fails to match `(u₀, u₁)`; since `e₀ x + γ·e₁ x = 0`
there, necessarily `e₁ x ≠ 0` — the affine root at a support coordinate.  Stacks with at
most one bad scalar take an indicator pair of weight `1`.  Total weight `W = 2(n−t) + 1`.

## Why `3(n−t)`, not `(d−1)/2`: the honest boundary

The probe (`scripts/probes/probe_ud_affine_extraction.py`, exit 0) validates the window
(80 stacks at `e = n−t ≤ 2` over GF(97), RS(16,8), 69 with ≥ 2 bad scalars, 0 violations
of the affine law, the root property, or the count `≤ 2(n−t)+1`) **and refutes the
docstring's mechanism beyond it**: at `e ∈ {3,4}` (between `d/(3n)` and `(d−1)/(2n)`), a
`g`-planting construction (error pair arranged so a third bad scalar decodes to
`line + g` for a weight-`d` codeword `g`) breaks the affine decoding law in 24/24 planted
stacks at each `e` — the unique nearest codewords are *not* affine in `γ` there.  The
bad-scalar *count* never exceeded `2(n−t)+1` in the hunt (max 3), so the extraction
*statement* remains open in `(d/(3n), (d−1)/(2n)]`; only the codeword-subtraction proof
route is closed off.

## The bracket, and where it is non-empty

`theoremQ_epsMCA_two_sided_uniqueDecoding` — the two-sided Theorem-Q bracket with **no
extraction hypothesis**: under the Theorem-Q hypotheses and the window
`3(n−t) < n − (r−1)m + 1` (the RHS is the minimum distance of `evalCode H ((r−1)m)`),

  `B/q ≤ ε_mca(evalCode H ((r−1)m), δ) ≤ (2(n−t)+1)/q`.

`window_forces_r_eq_s`: the lower-half window `(1−δ)n ≤ rm` and this upper window
intersect **only at `r = s`** (at `r < s` the bracket is vacuous — e.g. at the O68 point
`(n,m,s,r) = (16,2,8,5)` the lower half needs `t ≤ 10` while the window needs `t ≥ 14`).
At `r = s` the bracket is genuinely two-sided: `C(s,s) = 1` forces `B ≥ 1`, so
`1/q ≤ ε_mca ≤ (2(n−t)+1)/q` on the window — confirmed concretely by the probe at
`(q,n,s,m,r) = (97,12,4,3,4)`, `t = 11` (`δ = 1/12`): the deep-quotient line carries
exactly 1 bad scalar and 20 stress stacks stay `≤ 3`.

Versus O78 (`EpsMCAInterleavedUD`, unconditional window `δ < d/(4n)`, bound `(1+2δn)/q`):
this window is wider by a third (`d/(3n) > d/(4n)`) at the same `O(δn)/q` bound shape, and
it is the one that composes with the Theorem-Q lower half in a single statement.

Provenance: axiom-clean (`[propext, Classical.choice, Quot.sound]`), zero `sorry`, zero
warnings, built against warm oleans (`lake env lean`).  References: [ABF26] Def 4.3 /
Grand Challenge 1; [BCIKS20] §1 (unique-decoding correlated agreement); the engine
`TheoremQUpperReduction.lean` (O77); the lower half `TheoremQAssembly.lean` (O68).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.TheoremQUDExtraction

open _root_.ProximityGap _root_.Code Polynomial
open scoped NNReal ENNReal BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The extraction, per stack -/

open Classical in
/-- **The affine-root extraction in the `3(n−t) < d` window (per stack).**  For any code `C`
closed under `F`-linear combinations, of minimum distance `≥ d`, and any stack `(u₀, u₁)`:
if `3·(n − t) < d` with `t = ⌈(1−δ)n⌉₊`, there is an affine error pair `(e₀, e₁)` with
`weight(e₁) ≤ 2(n−t) + 1` such that every `mcaEvent`-bad scalar of the stack is a root of
`e₀ + γ·e₁` at a support coordinate of `e₁`.  This is exactly the hypothesis pair of
`TheoremQUpper.epsMCA_le_of_affineRoot_extraction` — O77's named residual wall, discharged
on this window.

Proof: with two distinct bad scalars, subtract the affine solve `(c₀, c₁)` of the two
closeness codewords; the minimum distance forces every further bad scalar's codeword onto
the same affine family (`d_γ = 0`), and `¬ pairJointAgreesOn` pins the root coordinate.
With at most one bad scalar, an indicator pair of weight `1` suffices. -/
theorem exists_affine_pair
    (C : Set (ι → F)) (δ : ℝ≥0) (d : ℕ)
    (hlin : ∀ (a b : F), ∀ x ∈ C, ∀ y ∈ C, a • x + b • y ∈ C)
    (hdist : ∀ c ∈ C, c ≠ 0 → d ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    (hwin : 3 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < d)
    (u₀ u₁ : ι → F) :
    ∃ e₀ e₁ : ι → F,
      (Finset.univ.filter (fun i => e₁ i ≠ 0)).card
          ≤ 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1 ∧
      ∀ γ : F, mcaEvent (F := F) (A := F) C δ u₀ u₁ γ →
        ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 := by
  classical
  set t := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with ht
  by_cases h2 : ∃ γ₁ γ₂ : F, γ₁ ≠ γ₂ ∧
      mcaEvent (F := F) (A := F) C δ u₀ u₁ γ₁ ∧ mcaEvent (F := F) (A := F) C δ u₀ u₁ γ₂
  · -- ## two distinct bad scalars: the codeword-subtraction pair
    obtain ⟨γ₁, γ₂, hγne, hev₁, hev₂⟩ := h2
    obtain ⟨S₁, hS₁card, ⟨w₁, hw₁C, hw₁⟩, -⟩ := hev₁
    obtain ⟨S₂, hS₂card, ⟨w₂, hw₂C, hw₂⟩, -⟩ := hev₂
    simp only [smul_eq_mul] at hw₁ hw₂
    have hγsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hγne
    have hinv : (γ₁ - γ₂)⁻¹ * (γ₁ - γ₂) = 1 := inv_mul_cancel₀ hγsub
    -- the affine solve
    obtain ⟨c₁, hc₁C, hc₁i⟩ :
        ∃ c₁ ∈ C, ∀ i, c₁ i = (γ₁ - γ₂)⁻¹ * w₁ i + (-(γ₁ - γ₂)⁻¹) * w₂ i :=
      ⟨(γ₁ - γ₂)⁻¹ • w₁ + (-(γ₁ - γ₂)⁻¹) • w₂, hlin _ _ _ hw₁C _ hw₂C, fun i => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]⟩
    obtain ⟨c₀, hc₀C, hc₀i⟩ : ∃ c₀ ∈ C, ∀ i, c₀ i = w₁ i + (-γ₁) * c₁ i :=
      ⟨(1 : F) • w₁ + (-γ₁) • c₁, hlin _ _ _ hw₁C _ hc₁C, fun i => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]⟩
    have hS₁t : t ≤ S₁.card := Nat.ceil_le.mpr hS₁card
    have hS₂t : t ≤ S₂.card := Nat.ceil_le.mpr hS₂card
    -- the error pair vanishes on the intersection of the two witness sets
    have hvan : ∀ i ∈ S₁ ∩ S₂, u₀ i = c₀ i ∧ u₁ i = c₁ i := by
      intro i hi
      obtain ⟨hi₁, hi₂⟩ := Finset.mem_inter.mp hi
      have h1 := hw₁ i hi₁
      have h2' := hw₂ i hi₂
      have hu₁ : c₁ i = u₁ i := by
        rw [hc₁i i]
        linear_combination ((γ₁ - γ₂)⁻¹) * h1 - ((γ₁ - γ₂)⁻¹) * h2' + (u₁ i) * hinv
      have hu₀ : c₀ i = u₀ i := by
        rw [hc₀i i]
        linear_combination h1 - γ₁ * hu₁
      exact ⟨hu₀.symm, hu₁.symm⟩
    have hS₁n : S₁.card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have hS₂n : S₂.card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have hiu : (S₁ ∩ S₂).card + (S₁ ∪ S₂).card = S₁.card + S₂.card :=
      Finset.card_inter_add_card_union S₁ S₂
    have hun : (S₁ ∪ S₂).card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    refine ⟨u₀ - c₀, u₁ - c₁, ?_, ?_⟩
    · -- weight of the direction: supported off `S₁ ∩ S₂`
      have hsub : Finset.univ.filter (fun i => (u₁ - c₁) i ≠ 0) ⊆ (S₁ ∩ S₂)ᶜ := by
        intro i hi
        rw [Finset.mem_compl]
        intro hmem
        exact (Finset.mem_filter.mp hi).2
          (by rw [Pi.sub_apply, (hvan i hmem).2, sub_self])
      have hcompl : ((S₁ ∩ S₂)ᶜ : Finset ι).card = Fintype.card ι - (S₁ ∩ S₂).card :=
        Finset.card_compl _
      have hle := Finset.card_le_card hsub
      omega
    · -- the root property for every bad scalar
      intro γ hγ
      obtain ⟨S, hScard, ⟨w, hwC, hw⟩, hno⟩ := hγ
      simp only [smul_eq_mul] at hw
      have hSt : t ≤ S.card := Nat.ceil_le.mpr hScard
      have hSn : S.card ≤ Fintype.card ι := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      -- the discrepancy codeword
      obtain ⟨dγ, hdγC, hdγi⟩ : ∃ dγ ∈ C, ∀ i, dγ i = w i - (c₀ i + γ * c₁ i) := by
        refine ⟨(1 : F) • w + (-1 : F) • ((1 : F) • c₀ + γ • c₁),
          hlin _ _ _ hwC _ (hlin _ _ _ hc₀C _ hc₁C), fun i => ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
        ring
      -- its support sits inside `Sᶜ ∪ (S₁ ∩ S₂)ᶜ`, so its weight is `< d`
      have hd_supp : Finset.univ.filter (fun i => dγ i ≠ 0) ⊆ Sᶜ ∪ (S₁ ∩ S₂)ᶜ := by
        intro i hi
        rw [Finset.mem_union, Finset.mem_compl, Finset.mem_compl]
        by_contra hcon
        push Not at hcon
        obtain ⟨hiS, hi12⟩ := hcon
        refine (Finset.mem_filter.mp hi).2 ?_
        rw [hdγi i, hw i hiS, (hvan i hi12).1, (hvan i hi12).2]
        ring
      have hd_card : (Finset.univ.filter (fun i => dγ i ≠ 0)).card < d := by
        have hle := Finset.card_le_card hd_supp
        have hcards : (Sᶜ ∪ (S₁ ∩ S₂)ᶜ : Finset ι).card ≤
            (Sᶜ : Finset ι).card + ((S₁ ∩ S₂)ᶜ : Finset ι).card :=
          Finset.card_union_le _ _
        have h1 : (Sᶜ : Finset ι).card = Fintype.card ι - S.card := Finset.card_compl _
        have h2 : ((S₁ ∩ S₂)ᶜ : Finset ι).card = Fintype.card ι - (S₁ ∩ S₂).card :=
          Finset.card_compl _
        omega
      -- minimum distance forces the affine decoding law
      have hdγ0 : dγ = 0 := by
        by_contra hne
        exact absurd (hdist dγ hdγC hne) (not_le.mpr hd_card)
      -- the no-joint-pair clause pins the root coordinate
      have hno2 : ¬ (∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i) := hno
      push Not at hno2
      obtain ⟨x, hxS, hxne⟩ := hno2 c₀ hc₀C c₁ hc₁C
      have hwx := hw x hxS
      have hdx : w x - (c₀ x + γ * c₁ x) = 0 := by
        rw [← hdγi x, hdγ0]; rfl
      have hlinex : (u₀ x - c₀ x) + γ * (u₁ x - c₁ x) = 0 := by
        linear_combination hdx - hwx
      by_cases he₁x : u₁ x - c₁ x = 0
      · exfalso
        have h0 : u₀ x - c₀ x = 0 := by
          rw [he₁x, mul_zero, add_zero] at hlinex
          exact hlinex
        exact hxne (sub_eq_zero.mp h0).symm (sub_eq_zero.mp he₁x).symm
      · exact ⟨x, by simpa using he₁x, by simpa using hlinex⟩
  · -- ## at most one bad scalar: an indicator pair of weight 1
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    by_cases h1 : ∃ γ : F, mcaEvent (F := F) (A := F) C δ u₀ u₁ γ
    · obtain ⟨γ₀, hγ₀⟩ := h1
      refine ⟨fun i => if i = i₀ then -γ₀ else 0, fun i => if i = i₀ then 1 else 0, ?_, ?_⟩
      · have hfe : (Finset.univ.filter (fun i => (if i = i₀ then (1 : F) else 0) ≠ 0))
            = {i₀} := by
          ext i
          by_cases h : i = i₀ <;> simp [h]
        rw [hfe, Finset.card_singleton]
        omega
      · intro γ hγ
        have hγeq : γ = γ₀ := by
          by_contra hne
          exact h2 ⟨γ, γ₀, hne, hγ, hγ₀⟩
        subst hγeq
        exact ⟨i₀, by simp, by simp⟩
    · push Not at h1
      exact ⟨0, 0, by simp, fun γ hγ => absurd hγ (h1 γ)⟩

/-! ### The `ε_mca` upper bound on the window (the extraction discharged) -/

open Classical in
/-- **The unconditional `ε_mca` upper bound on the window `3(n−t) < d`.**  For any
`F`-linearly closed code of minimum distance `≥ d`:

  `3·(n − ⌈(1−δ)n⌉₊) < d  ⟹  ε_mca(C, δ) ≤ (2(n−t)+1)/|F|`.

This is O77's engine `epsMCA_le_of_affineRoot_extraction` with the extraction hypothesis
*discharged* (`exists_affine_pair` + choice), not assumed.  In δ-units the window is
`δ < d/(3n)` — strictly wider than O78's unconditional `d/(4n)` interleaved window, at the
same `O(δn)/q` bound shape. -/
theorem epsMCA_le_of_uniqueDecoding
    (C : Set (ι → F)) (δ : ℝ≥0) (d : ℕ)
    (hlin : ∀ (a b : F), ∀ x ∈ C, ∀ y ∈ C, a • x + b • y ∈ C)
    (hdist : ∀ c ∈ C, c ≠ 0 → d ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    (hwin : 3 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < d) :
    epsMCA (F := F) (A := F) C δ
      ≤ ((2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1 : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  choose e₀ e₁ hweight hroot using fun u : WordStack F (Fin 2) ι =>
    exists_affine_pair C δ d hlin hdist hwin (u 0) (u 1)
  exact TheoremQUpper.epsMCA_le_of_affineRoot_extraction C δ _ e₀ e₁ hweight hroot

/-! ### Instantiation for the Theorem-Q code family -/

/-- `evalCode H k` is closed under `F`-linear combinations. -/
theorem evalCode_lin_closed (H : Finset F) (k : ℕ) :
    ∀ (a b : F), ∀ x ∈ TheoremQAssembly.evalCode H k,
      ∀ y ∈ TheoremQAssembly.evalCode H k,
        a • x + b • y ∈ TheoremQAssembly.evalCode H k := by
  rintro a b x ⟨p, hpdeg, hpx⟩ y ⟨q, hqdeg, hqy⟩
  refine ⟨Polynomial.C a * p + Polynomial.C b * q, ?_, fun i => ?_⟩
  · refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    rw [max_lt_iff]
    exact ⟨lt_of_le_of_lt (Polynomial.natDegree_C_mul_le a p) hpdeg,
      lt_of_le_of_lt (Polynomial.natDegree_C_mul_le b q) hqdeg⟩
  · simp [hpx i, hqy i]

/-- **Minimum weight of `evalCode H k`**: a nonzero codeword (the evaluation of a nonzero
polynomial of degree `< k` on the `|H|` distinct points of `H`) has weight at least
`|H| − (k − 1)`. -/
theorem evalCode_min_weight (H : Finset F) [Nonempty {x : F // x ∈ H}] (k : ℕ) :
    ∀ c ∈ TheoremQAssembly.evalCode H k, c ≠ 0 →
      Fintype.card {x : F // x ∈ H} - (k - 1)
        ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card := by
  classical
  rintro c ⟨p, hpdeg, hpc⟩ hc0
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hc0 (funext fun i => by simpa using hpc i)
  have hzero : (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).card ≤ k - 1 := by
    have hinj : ((Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).image
          (fun i => i.1)).card
        = (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hsub : (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).image
        (fun i => i.1) ⊆ p.roots.toFinset := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      have hci := (Finset.mem_filter.mp hi).2
      rw [hpc i] at hci
      exact hci
    calc (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).card
        = _ := hinj.symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := p.card_roots'
      _ ≤ k - 1 := by omega
  have htot : (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i = 0)).card
      + (Finset.univ.filter (fun i : {x : F // x ∈ H} => ¬ c i = 0)).card
      = Fintype.card {x : F // x ∈ H} := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hfeq : (Finset.univ.filter (fun i : {x : F // x ∈ H} => c i ≠ 0))
      = (Finset.univ.filter (fun i : {x : F // x ∈ H} => ¬ c i = 0)) := rfl
  rw [hfeq]
  omega

open Classical in
/-- The window bound for the Theorem-Q code family: `evalCode H k` has minimum distance
`≥ |H| − (k−1)`, so `3(n−t) < |H| − (k−1)` gives `ε_mca ≤ (2(n−t)+1)/q` unconditionally. -/
theorem evalCode_epsMCA_le_uniqueDecoding
    (H : Finset F) [Nonempty {x : F // x ∈ H}] (k : ℕ) (δ : ℝ≥0)
    (hwin : 3 * (Fintype.card {x : F // x ∈ H}
        - ⌈(1 - δ) * (Fintype.card {x : F // x ∈ H} : ℝ≥0)⌉₊)
      < Fintype.card {x : F // x ∈ H} - (k - 1)) :
    epsMCA (F := F) (A := F) (TheoremQAssembly.evalCode H k) δ
      ≤ ((2 * (Fintype.card {x : F // x ∈ H}
            - ⌈(1 - δ) * (Fintype.card {x : F // x ∈ H} : ℝ≥0)⌉₊) + 1 : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_uniqueDecoding (TheoremQAssembly.evalCode H k) δ
    (Fintype.card {x : F // x ∈ H} - (k - 1))
    (evalCode_lin_closed H k) (evalCode_min_weight H k) hwin

/-! ### Where the bracket lives: the window intersection forces `r = s` -/

/-- **The two windows intersect only at `r = s`.**  If the Theorem-Q lower-half window
holds at floor `t` (`t ≤ rm`, the ℕ-form of `(1−δ)n ≤ rm`) *and* the upper window
`3(n−t) < n − (r−1)m + 1` holds, then `r = s`.  At `r < s` the two-sided bracket is
vacuous — e.g. at the O68 parameters `(n,m,s,r) = (16,2,8,5)` the lower half needs
`t ≤ 10` while the window needs `t ≥ 14`. -/
theorem window_forces_r_eq_s
    (n s m r t : ℕ)
    (hnsm : n = s * m) (hm : 1 ≤ m) (hr : 2 ≤ r) (hrs : r ≤ s)
    (ht : t ≤ r * m)
    (hwin : 3 * (n - t) < n - (r - 1) * m + 1) :
    r = s := by
  by_contra hne
  have hlt : r < s := lt_of_le_of_ne hrs hne
  have hrm_m : (r - 1) * m + m = r * m := by
    have h : ((r - 1) + 1) * m = r * m := by
      congr 1
      omega
    calc (r - 1) * m + m = ((r - 1) + 1) * m := by ring
      _ = r * m := h
  have hA : r * m + m ≤ n := by
    rw [hnsm]
    have h : (r + 1) * m ≤ s * m := Nat.mul_le_mul_right m (by omega)
    calc r * m + m = (r + 1) * m := by ring
      _ ≤ s * m := h
  obtain ⟨K, hK⟩ : ∃ K, (r - 1) * m = K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, r * m = R := ⟨_, rfl⟩
  rw [hK] at hwin hrm_m
  rw [hR] at ht hrm_m hA
  omega

/-! ### The headline: the unconditional two-sided bracket -/

open Classical in
/-- **The two-sided Theorem-Q bracket with NO extraction hypothesis.**  Under the
Theorem-Q hypotheses (`H` a full `n`-th-root domain, `n = s·m`, `2 ≤ r ≤ s`,
`(1−δ)n ≤ rm`, `q > n + k` with `k = (r−1)m`) **and** the unique-decoding window
`3·(n − ⌈(1−δ)n⌉₊) < n − (r−1)m + 1` (the RHS is the minimum distance of `evalCode H k`):

  `B/q ≤ ε_mca(evalCode H k, δ) ≤ (2(n−t)+1)/q`,

with the lower `B` satisfying the Theorem-Q value-spread bound (O68, unconditional) and the
upper half now also *unconditional* — O77's affine-root extraction residual is discharged
by `exists_affine_pair` on this window.  By `window_forces_r_eq_s` the hypotheses are
jointly satisfiable **only at `r = s`** (where `C(s,s) = 1` still forces `B ≥ 1`, so the
bracket reads `1/q ≤ ε_mca ≤ (2(n−t)+1)/q`); at `r < s` — in particular throughout the
list-decoding regime of the O68 witness — the gap `(d/(3n), δ_wit]` remains the unpinned
core, now with all three of its known approaches (O77 conditional `d/(2n)`, O78
unconditional `d/(4n)`, this unconditional `d/(3n)`) recorded on one surface. -/
theorem theoremQ_epsMCA_two_sided_uniqueDecoding
    (H : Finset F) [Nonempty {x : F // x ∈ H}] (n s m r : ℕ)
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hm : 1 ≤ m) (hr : 2 ≤ r) (hrs : r ≤ s)
    (hbig : n + (r - 1) * m < Fintype.card F)
    (δ : ℝ≥0)
    (hδ₁ : (1 - δ) * ((Fintype.card {x : F // x ∈ H} : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0))
    (hwin : 3 * (n - ⌈(1 - δ) * ((n : ℕ) : ℝ≥0)⌉₊) < n - (r - 1) * m + 1) :
    ∃ B : ℕ,
      Nat.choose s r * (Fintype.card F - n)
          ≤ B * ((Fintype.card F - n) + Nat.choose s r * ((r - 1) * m)) ∧
      (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
          ≤ epsMCA (F := F) (A := F) (TheoremQAssembly.evalCode H ((r - 1) * m)) δ ∧
      epsMCA (F := F) (A := F) (TheoremQAssembly.evalCode H ((r - 1) * m)) δ
          ≤ ((2 * (n - ⌈(1 - δ) * ((n : ℕ) : ℝ≥0)⌉₊) + 1 : ℕ) : ℝ≥0∞)
              / (Fintype.card F : ℝ≥0∞) := by
  have hci : Fintype.card {x : F // x ∈ H} = n := by
    rw [Fintype.card_coe, hcard]
  obtain ⟨B, hB1, hB2⟩ :=
    TheoremQAssembly.theoremQ_epsMCA_lower H n s m r hroots hcard hnsm hm hr hrs hbig δ hδ₁
  have hk1 : 1 ≤ (r - 1) * m := by
    have h1 : 1 ≤ r - 1 := by omega
    calc 1 = 1 * 1 := rfl
      _ ≤ (r - 1) * m := Nat.mul_le_mul h1 hm
  have hkn : (r - 1) * m < n := by
    rw [hnsm]
    have h1 : ((r - 1) + 1) * m ≤ s * m := Nat.mul_le_mul_right m (by omega)
    have h2 : (r - 1) * m + m = ((r - 1) + 1) * m := by ring
    omega
  have hwin' : 3 * (Fintype.card {x : F // x ∈ H}
      - ⌈(1 - δ) * (Fintype.card {x : F // x ∈ H} : ℝ≥0)⌉₊)
      < Fintype.card {x : F // x ∈ H} - ((r - 1) * m - 1) := by
    rw [hci]
    obtain ⟨K, hK⟩ : ∃ K, (r - 1) * m = K := ⟨_, rfl⟩
    rw [hK] at hwin hk1 hkn ⊢
    omega
  have hupper := evalCode_epsMCA_le_uniqueDecoding H ((r - 1) * m) δ hwin'
  rw [hci] at hupper
  exact ⟨B, hB1, hB2, hupper⟩

/-! ### Non-vacuity: the hypothesis spine is satisfiable (at `r = s`, as forced) -/

/-- **The headline's hypothesis spine is satisfiable** — concretely at `F = ZMod 13`,
`H = {1, 5, 8, 12}` (the fourth roots of unity), `(n, s, m, r) = (4, 2, 2, 2)` (the
`r = s` family forced by `window_forces_r_eq_s`), `δ = 0`: every hypothesis of
`theoremQ_epsMCA_two_sided_uniqueDecoding` holds.  No leaf of this file hides behind an
unsatisfiable hypothesis. -/
theorem theoremQ_ud_window_satisfiable :
    ∃ (H : Finset (ZMod 13)) (n s m r : ℕ) (δ : ℝ≥0),
      Nonempty {x : ZMod 13 // x ∈ H} ∧
      (∀ x ∈ H, x ^ n = 1) ∧ H.card = n ∧ n = s * m ∧ 1 ≤ m ∧ 2 ≤ r ∧ r ≤ s ∧
      n + (r - 1) * m < Fintype.card (ZMod 13) ∧
      (1 - δ) * ((Fintype.card {x : ZMod 13 // x ∈ H} : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0) ∧
      3 * (n - ⌈(1 - δ) * ((n : ℕ) : ℝ≥0)⌉₊) < n - (r - 1) * m + 1 := by
  refine ⟨{1, 5, 8, 12}, 4, 2, 2, 2, 0, ⟨⟨1, by decide⟩⟩, by decide, by decide, by norm_num,
    by norm_num, le_refl 2, le_refl 2, by decide, ?_, ?_⟩
  · rw [Fintype.card_coe]
    have hcard4 : ({1, 5, 8, 12} : Finset (ZMod 13)).card = 4 := by decide
    rw [hcard4]
    norm_num
  · have hceil : ⌈(1 - (0 : ℝ≥0)) * ((4 : ℕ) : ℝ≥0)⌉₊ = 4 := by
      rw [tsub_zero, one_mul]
      exact_mod_cast Nat.ceil_natCast 4
    rw [hceil]
    norm_num

local instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The headline theorem *fires* at the satisfiable instance (certifying the hypotheses
are jointly consistent, not merely individually satisfiable). -/
example :
    ∃ B : ℕ,
      Nat.choose 2 2 * (Fintype.card (ZMod 13) - 4)
          ≤ B * ((Fintype.card (ZMod 13) - 4) + Nat.choose 2 2 * ((2 - 1) * 2)) ∧
      (B : ℝ≥0∞) / (Fintype.card (ZMod 13) : ℝ≥0∞)
          ≤ epsMCA (F := ZMod 13) (A := ZMod 13)
              (TheoremQAssembly.evalCode ({1, 5, 8, 12} : Finset (ZMod 13))
                ((2 - 1) * 2)) 0 ∧
      epsMCA (F := ZMod 13) (A := ZMod 13)
          (TheoremQAssembly.evalCode ({1, 5, 8, 12} : Finset (ZMod 13)) ((2 - 1) * 2)) 0
        ≤ ((2 * (4 - ⌈(1 - (0 : ℝ≥0)) * ((4 : ℕ) : ℝ≥0)⌉₊) + 1 : ℕ) : ℝ≥0∞)
            / (Fintype.card (ZMod 13) : ℝ≥0∞) := by
  have hmem : (1 : ZMod 13) ∈ ({1, 5, 8, 12} : Finset (ZMod 13)) := by decide
  haveI hne : Nonempty {x : ZMod 13 // x ∈ ({1, 5, 8, 12} : Finset (ZMod 13))} :=
    ⟨⟨1, hmem⟩⟩
  have hroots : ∀ x ∈ ({1, 5, 8, 12} : Finset (ZMod 13)), x ^ 4 = 1 := by decide
  have hcard : ({1, 5, 8, 12} : Finset (ZMod 13)).card = 4 := by decide
  have hbig : 4 + (2 - 1) * 2 < Fintype.card (ZMod 13) := by decide
  have h := theoremQ_epsMCA_two_sided_uniqueDecoding (F := ZMod 13)
    ({1, 5, 8, 12} : Finset (ZMod 13)) 4 2 2 2 hroots hcard (by norm_num)
    (by norm_num) (le_refl 2) (le_refl 2) hbig 0
    (by
      rw [Fintype.card_coe]
      rw [hcard]
      norm_num)
    (by
      have hceil : ⌈(1 - (0 : ℝ≥0)) * ((4 : ℕ) : ℝ≥0)⌉₊ = 4 := by
        rw [tsub_zero, one_mul]
        exact_mod_cast Nat.ceil_natCast 4
      rw [hceil]
      norm_num)
  exact h

end ArkLib.ProximityGap.TheoremQUDExtraction

#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.exists_affine_pair
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.epsMCA_le_of_uniqueDecoding
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.evalCode_lin_closed
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.evalCode_min_weight
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.evalCode_epsMCA_le_uniqueDecoding
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.window_forces_r_eq_s
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.theoremQ_epsMCA_two_sided_uniqueDecoding
#print axioms ArkLib.ProximityGap.TheoremQUDExtraction.theoremQ_ud_window_satisfiable
