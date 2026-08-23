/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26ObstructionCount

/-!
# S2(b′): the obstruction bound reduces to a one-row direction count (#357)

`Jo26ObstructionCount.lean` proved: if a `≤ q` family of proper subspaces dominates
every bad seed's obstruction (`ObstructionBound`), generator-MCA interleaving is exact
for every generator.  The probe campaign then found `ObstructionBound` is
**Johnson-gated**: it holds on every below-Johnson rung and fails exactly at `δ = 1−√ρ`.

This file explains the gating by *reducing the obstruction geometry to a 1-dimensional
list bound*.  At `s = 2`:

1. every proper obstruction subspace is `⊥` or a line (`proper_eq_bot_or_span` —
   two independent vectors of `F²` span it, by explicit determinant inversion);
2. every nonzero combiner in a *witness's* obstruction subspace is explainable on that
   witness — in particular its row-`j` combination is `δ`-close to `C` **with the
   witness itself as agreement set** (`rowClose_of_mem_jointStackSubmodule`);
3. hence `{⊥} ∪ {span(λ) : λ a δ-close direction of row j}` dominates every bad-seed
   obstruction (`obstructionBound_of_rowCloseSpans_cover`): **`ObstructionBound`
   follows from `#(close direction spans of one row) ≤ q − 1`** — for any row.

The corollary `epsMCAG_interleaved_eq_of_rowCloseSpans_card` chains this through the
landed exactness theorem.  The remaining open input — the direction count — is exactly
a proximity-gap/list statement about ONE affine line of words (`λ₀·U_{j,0} + λ₁·U_{j,1}`,
projectively), which is where the Johnson radius genuinely enters: below Johnson the
close-point count of a non-fully-close line is `ε_pg·q ≪ q`, while at Johnson lines can
be densely close without collapsing (the probe defeater at `δ = 1/2 = 1−√ρ` exhibits
exactly this).  The direction-count input is left as the named hypothesis of the
theorems — the honest residue, one dimension lower than where we started.
-/

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

namespace ProximityGap.Jo26Obstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Proper subspaces of `F²` are `⊥` or a line -/

omit [Fintype F] [DecidableEq F] in
/-- A single vector never spans `F²`. -/
theorem span_singleton_ne_top (lam : Fin 2 → F) :
    Submodule.span F {lam} ≠ ⊤ := by
  intro htop
  have he0 : (fun k : Fin 2 => if k = 0 then (1 : F) else 0) ∈
      Submodule.span F {lam} := by rw [htop]; trivial
  have he1 : (fun k : Fin 2 => if k = 1 then (1 : F) else 0) ∈
      Submodule.span F {lam} := by rw [htop]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he0
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp he1
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  simp only [Pi.smul_apply, smul_eq_mul] at ha0 ha1 hb0 hb1
  simp only [show (0:Fin 2) ≠ 1 by decide, show (1:Fin 2) ≠ 0 by decide,
    if_true, if_false, reduceIte] at ha0 ha1 hb0 hb1
  -- ha0 : a * lam 0 = 1, ha1 : a * lam 1 = 0, hb0 : b * lam 0 = 0, hb1 : b * lam 1 = 1
  have hl0 : lam 0 ≠ 0 := fun h => by simp [h] at ha0
  have hbz : b = 0 := by
    rcases mul_eq_zero.mp hb0 with h | h
    · exact h
    · exact absurd h hl0
  rw [hbz, zero_mul] at hb1
  exact zero_ne_one hb1

omit [Fintype F] [DecidableEq F] in
/-- **Proper subspaces of `F²` are `⊥` or a line.**  If `K ≠ ⊤` and `K ≠ ⊥`, any
nonzero `λ ∈ K` spans it: a second member independent of `λ` would invert the
determinant and force `K = ⊤`. -/
theorem proper_eq_bot_or_span (K : Submodule F (Fin 2 → F)) (hK : K ≠ ⊤) :
    K = ⊥ ∨ ∃ lam : Fin 2 → F, lam ≠ 0 ∧ lam ∈ K ∧ K = Submodule.span F {lam} := by
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  obtain ⟨lam, hlamK, hlam0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine Or.inr ⟨lam, hlam0, hlamK, le_antisymm ?_ ?_⟩
  · -- K ≤ span lam: any μ ∈ K is dependent on lam, else K = ⊤
    intro mu hmu
    by_cases hd : lam 0 * mu 1 - lam 1 * mu 0 = 0
    · -- dependent: mu = c • lam
      rw [Submodule.mem_span_singleton]
      by_cases hl0 : lam 0 = 0
      · have hl1 : lam 1 ≠ 0 := by
          intro hl1
          apply hlam0
          funext k
          fin_cases k
          · exact hl0
          · exact hl1
        refine ⟨mu 1 / lam 1, ?_⟩
        funext k
        fin_cases k
        · -- (mu 1 / lam 1) * lam 0 = mu 0; lam 0 = 0 and hd forces mu 0 = 0
          have hmu0 : mu 0 = 0 := by
            have := hd
            rw [hl0, zero_mul] at this
            rcases mul_eq_zero.mp (by linear_combination -this : lam 1 * mu 0 = 0) with h | h
            · exact absurd h hl1
            · exact h
          simp [Pi.smul_apply, hl0, hmu0]
        · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hl1]
      · refine ⟨mu 0 / lam 0, ?_⟩
        funext k
        fin_cases k
        · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hl0]
        · -- (mu 0 / lam 0) * lam 1 = mu 1  ⟺  mu 1 * lam 0 = mu 0 * lam 1  (det = 0)
          show (mu 0 / lam 0) • lam 1 = mu 1
          rw [smul_eq_mul, div_mul_eq_mul_div, eq_comm, eq_div_iff hl0]
          linear_combination hd
    · -- independent: K contains both basis vectors, contradiction with properness
      exfalso
      apply hK
      rw [Submodule.eq_top_iff']
      intro v
      -- v = c₁ • lam + c₂ • mu with c₁ = (v0·mu1 − v1·mu0)/d, c₂ = (lam0·v1 − lam1·v0)/d
      have hne : lam 0 * mu 1 - lam 1 * mu 0 ≠ 0 := hd
      have h0 : v 0 = ((v 0 * mu 1 - v 1 * mu 0) / (lam 0 * mu 1 - lam 1 * mu 0)) * lam 0
          + ((lam 0 * v 1 - lam 1 * v 0) / (lam 0 * mu 1 - lam 1 * mu 0)) * mu 0 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_comm,
          div_eq_iff hne]
        ring
      have h1 : v 1 = ((v 0 * mu 1 - v 1 * mu 0) / (lam 0 * mu 1 - lam 1 * mu 0)) * lam 1
          + ((lam 0 * v 1 - lam 1 * v 0) / (lam 0 * mu 1 - lam 1 * mu 0)) * mu 1 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_comm,
          div_eq_iff hne]
        ring
      have hv : v = ((v 0 * mu 1 - v 1 * mu 0) / (lam 0 * mu 1 - lam 1 * mu 0)) • lam
          + ((lam 0 * v 1 - lam 1 * v 0) / (lam 0 * mu 1 - lam 1 * mu 0)) • mu := by
        funext k
        fin_cases k
        · simpa using h0
        · simpa using h1
      rw [hv]
      exact K.add_mem (K.smul_mem _ hlamK) (K.smul_mem _ hmu)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hlamK

/-! ### Close directions of a row -/

/-- `λ` is a **δ-close direction of row `j`**: the row-`j` combination
`i ↦ ∑ₖ λₖ • U j i k` agrees with a codeword on a set of `≥ (1−δ)·n` positions. -/
def RowClose (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    (U : Fin l → ι → Fin 2 → A) (j : Fin l) (lam : Fin 2 → F) : Prop :=
  ∃ T : Finset ι, (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    ∃ c ∈ (C : Set (ι → A)), ∀ i ∈ T, c i = ∑ k, lam k • U j i k

/-- Every nonzero member of a *witness's* obstruction subspace is a δ-close direction
of every row — with the witness itself as the agreement set. -/
theorem rowClose_of_mem_jointStackSubmodule (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {l : ℕ} {U : Fin l → ι → Fin 2 → A} {T : Finset ι}
    (hT : (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    {lam : Fin 2 → F} (hlam : lam ∈ jointStackSubmodule C T U) (j : Fin l) :
    RowClose C δ U j lam := by
  obtain ⟨cs, hcs, hag⟩ := hlam
  exact ⟨T, hT, cs j, hcs j, fun i hi => hag i hi j⟩

/-! ### The reduction -/

open Classical in
/-- **The obstruction bound from a one-row direction count (S2(b′) reduction).**
If, for a chosen row `j`, the spans of δ-close directions of that row fit in a finset
`Ds` of at most `q − 1` subspaces, then `ObstructionBound` holds: the dominating
family is `{⊥} ∪ (Ds filtered to proper members)`.  The geometric content: a bad
seed's obstruction is proper, hence `⊥` or a line; a line obstruction consists of
close directions of *every* row, in particular row `j`, so its span lies in `Ds` (and
spans of single vectors are never `⊤`, so the filter keeps them). -/
theorem obstructionBound_of_rowCloseSpans_cover
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin 2 → A) (j : Fin l)
    (Ds : Finset (Submodule F (Fin 2 → F)))
    (hcover : ∀ lam : Fin 2 → F, lam ≠ 0 → RowClose C δ U j lam →
      Submodule.span F {lam} ∈ Ds)
    (hcard : Ds.card + 1 ≤ Fintype.card F) :
    ObstructionBound C δ G U := by
  refine ⟨insert ⊥ (Ds.filter (fun K => K ≠ ⊤)), ?_, ?_, ?_⟩
  · calc (insert ⊥ (Ds.filter (fun K => K ≠ ⊤))).card
        ≤ (Ds.filter (fun K => K ≠ ⊤)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Ds.card + 1 := by
          have := Finset.card_filter_le Ds (fun K => K ≠ ⊤)
          omega
      _ ≤ Fintype.card F := hcard
  · intro K hK
    rcases Finset.mem_insert.mp hK with h | h
    · subst h
      intro htop
      have h1 : (fun k : Fin 2 => if k = 0 then (1 : F) else 0)
          ∈ (⊥ : Submodule F (Fin 2 → F)) := by rw [htop]; trivial
      have h0 := congrFun ((Submodule.mem_bot F).mp h1) 0
      simp at h0
    · exact (Finset.mem_filter.mp h).2
  · intro ω hω
    obtain ⟨T, hW⟩ := hω
    refine ⟨T, hW, ?_⟩
    have hproper : jointStackSubmodule C T U ≠ ⊤ :=
      jointStackSubmodule_ne_top C U hW.2.2
    rcases proper_eq_bot_or_span _ hproper with hbot | ⟨lam, hlam0, hlamK, hspan⟩
    · rw [hbot]
      exact Finset.mem_insert_self _ _
    · rw [hspan]
      refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · exact hcover lam hlam0
          (rowClose_of_mem_jointStackSubmodule C δ hW.1 hlamK j)
      · exact span_singleton_ne_top lam

open Classical in
/-- **S2(b′) chained to exactness:** if every 2-column stack admits a row whose
δ-close direction spans number at most `q − 1`, generator-MCA interleaving is exact
for every generator.  The open input is now a 1-dimensional direction count — a
proximity-gap statement about a single line of words, which is precisely where the
Johnson radius enters (and where the probe defeater at `δ = 1−√ρ` lives). -/
theorem epsMCAG_interleaved_eq_of_rowCloseSpans_card
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (h : ∀ U : Fin l → ι → Fin 2 → A, ∃ (j : Fin l)
      (Ds : Finset (Submodule F (Fin 2 → F))),
      (∀ lam : Fin 2 → F, lam ≠ 0 → RowClose C δ U j lam →
        Submodule.span F {lam} ∈ Ds) ∧ Ds.card + 1 ≤ Fintype.card F) :
    epsMCAG (A := Fin 2 → A) ((C : Set (ι → A))^⋈ (Fin 2)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  refine epsMCAG_interleaved_eq_of_obstructionBound C 2 δ G (fun U => ?_)
  obtain ⟨j, Ds, hcover, hcard⟩ := h U
  exact obstructionBound_of_rowCloseSpans_cover C δ G U j Ds hcover hcard

end ProximityGap.Jo26Obstruction

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Jo26Obstruction.proper_eq_bot_or_span
#print axioms ProximityGap.Jo26Obstruction.obstructionBound_of_rowCloseSpans_cover
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_rowCloseSpans_card
