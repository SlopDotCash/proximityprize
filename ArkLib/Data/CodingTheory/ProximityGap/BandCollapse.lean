/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The band collapse theorem: at most `j + 1` bad scalars on band `j`

DISPROOF_LOG O153 proved (on paper) the first general sup-side result of the census
programme; this file formalizes it, with the distance condition *sharpened* from `4j` to
`3j` by the unified proof:

  **For a linear code in which every nonzero codeword has weight `> 3j`, every stack has at
  most `j + 1` bad scalars at any radius whose witness sets have size `≥ n − j`.**

Combined with the in-tree `(j+1)`-spike lower bound this pins the staircase law
`ε_mca·q = j + 1` on band `j` exactly for high-distance codes — the staircase side of the
two-family profile law (O147), now theorem-grade at every band.

## The unified proof

Badness of `γ` (with the event's own witness set `S_γ` and codeword `c_γ`) yields an error
word `w_γ = (u₀ + γ·u₁) − c_γ` of weight `≤ j`, vanishing on `S_γ`. Fix bad `γ₁ ≠ γ₂`. For
every bad `γ` the **bracket** `(γ₂−γ₁)·(w_γ − w_{γ₁}) − (γ−γ₁)·(w_{γ₂} − w_{γ₁})` lies in
`C` (the `u₁` terms cancel) and is supported on `supp w_γ ∪ supp w_{γ₁} ∪ supp w_{γ₂}`
(≤ `3j` points), hence is **zero**: the rigid relation
`w_γ = w_{γ₁} + (γ−γ₁)·v`, `v := (γ₂−γ₁)⁻¹·(w_{γ₂} − w_{γ₁})`. Then:

* **the injection**: if `S_γ` misses `supp v`, the explicit pair `(c_γ − γ·c*, c*)` (where
  `u₁ = c* + v` with `c* := (γ₂−γ₁)⁻¹·(c_{γ₂} − c_{γ₁}) ∈ C`) explains the stack on `S_γ`,
  contradicting the event. So each bad `γ` owns `x_γ ∈ S_γ ∩ supp v` with `w_γ(x_γ) = 0`;
  affine injectivity of `γ ↦ w_γ(x)` at each `x ∈ supp v` makes `γ ↦ x_γ` injective:
  `t ≤ |supp v|`.
* **the pinch**: at each `x ∈ supp v` at most one bad `γ` has `w_γ(x) = 0`, so
  `t·j ≥ ∑_γ wt(w_γ) ≥ |supp v|·(t−1) ≥ t·(t−1)`, giving `t ≤ j + 1`.

No case split, no short-word uniqueness, no analytic input. The `3j` condition is
consistent with every exact data point (e.g. `(13,12,6)` band 2: `d = 7 > 6`).

## References
* Issue #357 (surface (i)); DISPROOF_LOG O153; `GeneralSpikeLowerBound.lean` (the matching
  lower bound).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.BandCollapse

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Hamming weight (local, `Finset`-flavoured). -/
def wt (w : ι → F) : ℕ := (Finset.univ.filter (fun i => w i ≠ 0)).card

theorem wt_le_of_subset_zero {w : ι → F} {S : Finset ι}
    (h : ∀ i ∈ S, w i = 0) : wt w ≤ Fintype.card ι - S.card := by
  classical
  have hsub : Finset.univ.filter (fun i => w i ≠ 0) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiS
    exact (Finset.mem_filter.mp hi).2 (h i hiS)
  calc wt w ≤ Sᶜ.card := Finset.card_le_card hsub
    _ = Fintype.card ι - S.card := by rw [Finset.card_compl]

open Classical in
/-- **The band collapse.** If every nonzero codeword has weight `> 3j` and the radius
forces witness sets of size `≥ n − j`, then every stack has at most `j + 1` bad scalars. -/
theorem badScalar_card_le_band
    (C : Submodule F (ι → F)) {j : ℕ} (δ : ℝ≥0)
    (hforce : ∀ S : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) →
        Fintype.card ι - j ≤ S.card)
    (hdist : ∀ c ∈ C, c ≠ (0 : ι → F) → 3 * j < wt c)
    (u : WordStack F (Fin 2) ι) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ)).card ≤ j + 1 := by
  classical
  set B : Finset F := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ) with hB
  by_contra hbig
  push Not at hbig
  have htB : j + 2 ≤ B.card := hbig
  have hev : ∀ γ ∈ B, mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ :=
    fun γ hγ => (Finset.mem_filter.mp hγ).2
  -- choice data: witness set, codeword
  let Sγ : F → Finset ι := fun γ =>
    if h : mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ then h.choose else ∅
  have hSspec : ∀ γ ∈ B,
      ((Sγ γ).card : ℝ≥0) ≥ ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ∧
      (∃ c ∈ (C : Set (ι → F)), ∀ i ∈ Sγ γ, c i = (u 0) i + γ • (u 1) i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → F)) (Sγ γ) (u 0) (u 1) := by
    intro γ hγ
    have h := hev γ hγ
    simp only [Sγ, dif_pos h]
    exact h.choose_spec
  let cγ : F → (ι → F) := fun γ =>
    if h : ∃ c ∈ (C : Set (ι → F)), ∀ i ∈ Sγ γ, c i = (u 0) i + γ • (u 1) i
    then h.choose else 0
  have hcspec : ∀ γ ∈ B, cγ γ ∈ C ∧ ∀ i ∈ Sγ γ, cγ γ i = (u 0) i + γ * (u 1) i := by
    intro γ hγ
    have h := (hSspec γ hγ).2.1
    simp only [cγ, dif_pos h]
    exact ⟨h.choose_spec.1, fun i hi => by
      have := h.choose_spec.2 i hi
      simpa [smul_eq_mul] using this⟩
  -- error words
  let w : F → (ι → F) := fun γ i => ((u 0) i + γ * (u 1) i) - cγ γ i
  have hwvanish : ∀ γ ∈ B, ∀ i ∈ Sγ γ, w γ i = 0 := by
    intro γ hγ i hi
    simp only [w]
    rw [(hcspec γ hγ).2 i hi]
    ring
  have hwwt : ∀ γ ∈ B, wt (w γ) ≤ j := by
    intro γ hγ
    have h1 := wt_le_of_subset_zero (hwvanish γ hγ)
    have h2 := hforce (Sγ γ) (hSspec γ hγ).1
    omega
  -- two distinguished bad scalars
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨γ₁, hγ₁⟩ := hBne
  have hB2 : 1 < B.card := by omega
  obtain ⟨γ₂, hγ₂, hγ₂ne⟩ := Finset.exists_mem_ne hB2 γ₁
  set lam2 : F := γ₂ - γ₁ with hlam2
  have hlam2ne : lam2 ≠ 0 := sub_ne_zero.mpr hγ₂ne
  set v : ι → F := fun i => lam2⁻¹ * (w γ₂ i - w γ₁ i) with hv
  -- coset bookkeeping, pointwise: `w γ i − w γ₁ i = (γ−γ₁)·u₁ i − (c_γ i − c_{γ₁} i)`
  have hwdiff : ∀ γ, ∀ i,
      w γ i - w γ₁ i = (γ - γ₁) * (u 1) i - (cγ γ i - cγ γ₁ i) := by
    intro γ i
    simp only [w]
    ring
  -- THE RIGID RELATION
  have hrigid : ∀ γ ∈ B, ∀ i, w γ i = w γ₁ i + (γ - γ₁) * v i := by
    intro γ hγ
    set br : ι → F := fun i =>
      lam2 * (w γ i - w γ₁ i) - (γ - γ₁) * (w γ₂ i - w γ₁ i) with hbr
    have hbrC : br ∈ C := by
      have hfun : br = (γ - γ₁) • (cγ γ₂ - cγ γ₁) - lam2 • (cγ γ - cγ γ₁) := by
        funext i
        simp only [br, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hwdiff γ i, hwdiff γ₂ i, hlam2]
        ring
      rw [hfun]
      exact Submodule.sub_mem C
        (Submodule.smul_mem C _ (Submodule.sub_mem C (hcspec γ₂ hγ₂).1 (hcspec γ₁ hγ₁).1))
        (Submodule.smul_mem C _ (Submodule.sub_mem C (hcspec γ hγ).1 (hcspec γ₁ hγ₁).1))
    have hbrwt : wt br ≤ 3 * j := by
      have hsupp : Finset.univ.filter (fun i => br i ≠ 0)
          ⊆ ((Finset.univ.filter (fun i => w γ i ≠ 0))
            ∪ (Finset.univ.filter (fun i => w γ₁ i ≠ 0)))
            ∪ (Finset.univ.filter (fun i => w γ₂ i ≠ 0)) := by
        intro i hi
        have hbrne := (Finset.mem_filter.mp hi).2
        by_contra hnot
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          not_or, not_not] at hnot
        obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
        apply hbrne
        simp only [br, h1, h2, h3]
        ring
      have hle := Finset.card_le_card hsupp
      have hu1 := Finset.card_union_le
        ((Finset.univ.filter (fun i => w γ i ≠ 0))
          ∪ (Finset.univ.filter (fun i => w γ₁ i ≠ 0)))
        (Finset.univ.filter (fun i => w γ₂ i ≠ 0))
      have hu2 := Finset.card_union_le
        (Finset.univ.filter (fun i => w γ i ≠ 0))
        (Finset.univ.filter (fun i => w γ₁ i ≠ 0))
      have h1 := hwwt γ hγ
      have h2 := hwwt γ₁ hγ₁
      have h3 := hwwt γ₂ hγ₂
      unfold wt at *
      omega
    have hbr0 : br = 0 := by
      by_contra hne
      have := hdist br hbrC hne
      omega
    intro i
    have hzero : br i = 0 := by rw [hbr0]; rfl
    simp only [br] at hzero
    have hsolve : w γ i - w γ₁ i = (γ - γ₁) * (lam2⁻¹ * (w γ₂ i - w γ₁ i)) := by
      field_simp at hzero ⊢
      linear_combination hzero
    simp only [hv]
    linear_combination hsolve
  -- affine injectivity of zeros at points of `supp v`
  have hinjzero : ∀ i, v i ≠ 0 → ∀ γ ∈ B, ∀ γ' ∈ B,
      w γ i = 0 → w γ' i = 0 → γ = γ' := by
    intro i hvi γ hγ γ' hγ' h h'
    have e := hrigid γ hγ i
    have e' := hrigid γ' hγ' i
    rw [h] at e
    rw [h'] at e'
    have hdiff : (γ - γ') * v i = 0 := by linear_combination e' - e
    rcases mul_eq_zero.mp hdiff with hc | hc
    · exact sub_eq_zero.mp hc
    · exact absurd hc hvi
  set sv : Finset ι := Finset.univ.filter (fun i => v i ≠ 0) with hsv
  -- THE INJECTION: every bad `γ` owns a point of `S_γ ∩ supp v`.
  have hhit : ∀ γ ∈ B, ∃ x, x ∈ sv ∧ x ∈ Sγ γ := by
    intro γ hγ
    by_contra hnone
    push Not at hnone
    have hvzero : ∀ i ∈ Sγ γ, v i = 0 := by
      intro i hi
      by_contra hvi
      exact hnone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi⟩) hi
    -- the explaining pair
    set cstar : ι → F := fun i => lam2⁻¹ * (cγ γ₂ i - cγ γ₁ i) with hcstar
    have hcstarC : cstar ∈ C := by
      have hfun : cstar = lam2⁻¹ • (cγ γ₂ - cγ γ₁) := by
        funext i
        simp [cstar, smul_eq_mul]
      rw [hfun]
      exact Submodule.smul_mem C _
        (Submodule.sub_mem C (hcspec γ₂ hγ₂).1 (hcspec γ₁ hγ₁).1)
    -- `u₁ = cstar + v` pointwise
    have hu1 : ∀ i, (u 1) i = cstar i + v i := by
      intro i
      have hd := hwdiff γ₂ i
      simp only [hv, cstar, hlam2] at *
      field_simp
      linear_combination -hd
    apply (hSspec γ hγ).2.2
    refine ⟨(fun i => cγ γ i - γ * cstar i), ?_, cstar, hcstarC, ?_⟩
    · have hfun : (fun i => cγ γ i - γ * cstar i) = cγ γ - γ • cstar := by
        funext i
        simp [smul_eq_mul]
      rw [hfun]
      exact Submodule.sub_mem C (hcspec γ hγ).1 (Submodule.smul_mem C _ hcstarC)
    · intro i hi
      have hvi := hvzero i hi
      have hu1i : (u 1) i = cstar i := by
        rw [hu1 i, hvi, add_zero]
      constructor
      · show cγ γ i - γ * cstar i = (u 0) i
        have hline := (hcspec γ hγ).2 i hi
        rw [← hu1i]
        linear_combination hline
      · exact hu1i.symm
  -- choose hit points
  let xγ : F → ι := fun γ =>
    if h : ∃ x, x ∈ sv ∧ x ∈ Sγ γ then h.choose else Classical.arbitrary ι
  have hxspec : ∀ γ ∈ B, xγ γ ∈ sv ∧ w γ (xγ γ) = 0 := by
    intro γ hγ
    have h := hhit γ hγ
    simp only [xγ, dif_pos h]
    exact ⟨h.choose_spec.1, hwvanish γ hγ _ h.choose_spec.2⟩
  have hinjx : ∀ γ ∈ B, ∀ γ' ∈ B, xγ γ = xγ γ' → γ = γ' := by
    intro γ hγ γ' hγ' heq
    have h1 := hxspec γ hγ
    have h2 := hxspec γ' hγ'
    have hx : xγ γ ∈ sv := h1.1
    have hvx : v (xγ γ) ≠ 0 := (Finset.mem_filter.mp hx).2
    refine hinjzero (xγ γ) hvx γ hγ γ' hγ' h1.2 ?_
    rw [heq]
    exact h2.2
  have htle : B.card ≤ sv.card :=
    Finset.card_le_card_of_injOn xγ (fun γ hγ => (hxspec γ hγ).1)
      (fun γ hγ γ' hγ' h => hinjx γ hγ γ' hγ' h)
  -- THE PINCH
  have hzero_le_one : ∀ i ∈ sv, (B.filter (fun γ => w γ i = 0)).card ≤ 1 := by
    intro i hi
    have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [Finset.card_le_one]
    intro γ hγ' γ' hγ''
    have hγm := Finset.mem_filter.mp hγ'
    have hγm' := Finset.mem_filter.mp hγ''
    exact hinjzero i hvi γ hγm.1 γ' hγm'.1 hγm.2 hγm'.2
  have hcount : ∀ i ∈ sv, B.card - 1 ≤ (B.filter (fun γ => w γ i ≠ 0)).card := by
    intro i hi
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := B) (p := fun γ => w γ i = 0)
    have hsame : (B.filter (fun γ => ¬ w γ i = 0)).card
        = (B.filter (fun γ => w γ i ≠ 0)).card := rfl
    have := hzero_le_one i hi
    omega
  have hswap : ∑ i ∈ sv, (B.filter (fun γ => w γ i ≠ 0)).card
      = ∑ γ ∈ B, (sv.filter (fun i => w γ i ≠ 0)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hwt_ge : ∀ γ ∈ B, (sv.filter (fun i => w γ i ≠ 0)).card ≤ wt (w γ) := by
    intro γ _
    unfold wt
    refine Finset.card_le_card ?_
    intro i hi
    have := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, this.2⟩
  -- assemble: `sv·(t−1) ≤ ∑ wt ≤ t·j` and `t ≤ sv` ⟹ `t ≤ j+1` — contradiction.
  have hlhs : sv.card * (B.card - 1) ≤ ∑ γ ∈ B, wt (w γ) := by
    calc sv.card * (B.card - 1) = ∑ _i ∈ sv, (B.card - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ sv, (B.filter (fun γ => w γ i ≠ 0)).card :=
          Finset.sum_le_sum hcount
      _ = ∑ γ ∈ B, (sv.filter (fun i => w γ i ≠ 0)).card := hswap
      _ ≤ ∑ γ ∈ B, wt (w γ) := Finset.sum_le_sum hwt_ge
  have hrhs : ∑ γ ∈ B, wt (w γ) ≤ B.card * j := by
    calc ∑ γ ∈ B, wt (w γ) ≤ ∑ _γ ∈ B, j := Finset.sum_le_sum hwwt
      _ = B.card * j := by rw [Finset.sum_const, smul_eq_mul]
  have hfinal : B.card * (B.card - 1) ≤ B.card * j := by
    calc B.card * (B.card - 1) ≤ sv.card * (B.card - 1) :=
          Nat.mul_le_mul_right _ htle
      _ ≤ ∑ γ ∈ B, wt (w γ) := hlhs
      _ ≤ B.card * j := hrhs
  have hBpos : 0 < B.card := by omega
  have : B.card - 1 ≤ j := Nat.le_of_mul_le_mul_left
    (by simpa [Nat.mul_comm] using hfinal) hBpos
  omega

open Classical in
/-- **The band-`j` staircase upper bound:** `ε_mca(C, δ) ≤ (j+1)/q` whenever every nonzero
codeword has weight `> 3j` and the radius forces witness sets of size `≥ n − j`. With the
in-tree `(j+1)`-spike lower bound this is exact: the staircase side of the two-family
profile law. -/
theorem epsMCA_le_band
    (C : Submodule F (ι → F)) {j : ℕ} (δ : ℝ≥0)
    (hforce : ∀ S : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) →
        Fintype.card ι - j ≤ S.card)
    (hdist : ∀ c ∈ C, c ≠ (0 : ι → F) → 3 * j < wt c) :
    epsMCA (F := F) (A := F) (C : Set (ι → F)) δ
      ≤ (j + 1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  have := badScalar_card_le_band C δ hforce hdist u
  exact_mod_cast this

/-! ## Source audit -/

#print axioms badScalar_card_le_band
#print axioms epsMCA_le_band

end ProximityGap.BandCollapse
