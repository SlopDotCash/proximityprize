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

The reduction in step 3 is per stack.  Chaining it through the landed exactness theorem
needs the count for the stacks that matter.  The uniform corollary
`epsMCAG_interleaved_eq_of_rowCloseSpans_card` asks for it at *every* stack, and that
hypothesis is unsatisfiable (`not_forall_rowCloseSpans_card`: at the zero stack every
direction of every row is close, giving `q + 1` spans; at `l = 0` there is no row).  The
usable corollary is `epsMCAG_interleaved_eq_of_badStack_rowCloseSpans_card`, which asks for
the count only on stacks with a bad seed (stacks without one satisfy `ObstructionBound`
trivially).  The remaining open input — the direction count on bad stacks — is exactly
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
/-- **S2(b′) chained to exactness (uniform form — its hypothesis is unsatisfiable).**
If every 2-column stack admits a row whose δ-close direction spans number at most
`q − 1`, generator-MCA interleaving is exact for every generator.  The implication is
valid, but the hypothesis quantifies over *all* stacks, including the zero stack, and
`not_forall_rowCloseSpans_card` proves it never holds: every direction of every row of the
zero stack is δ-close to the zero codeword, giving `q + 1` distinct spans (and at `l = 0`
there is no row at all).  So this theorem never fires; the usable form is
`epsMCAG_interleaved_eq_of_badStack_rowCloseSpans_card`, which asks for the count only on
stacks that have a bad seed. -/
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

open Classical in
/-- **The uniform one-row direction-count hypothesis is unsatisfiable.**  For every
submodule code `C`, radius `δ` and number of rows `l`, it is false that every 2-column stack
admits a row whose δ-close direction spans fit in some `Ds` with `#Ds + 1 ≤ q`.  Witness:
the zero stack.  Each direction `λ` of each row is δ-close (agreement set `univ`, codeword
`0`), and the `q + 1` lines `span{(1, β)}` (`β ∈ F`) and `span{(0, 1)}` are pairwise
distinct, so `#Ds ≥ q + 1`.  (At `l = 0` there is no row to choose.)  The zero stack has no
bad seed, so this is a defect of the uniform quantifier, not an obstruction to exactness. -/
theorem not_forall_rowCloseSpans_card (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ} :
    ¬ ∀ U : Fin l → ι → Fin 2 → A, ∃ (j : Fin l)
      (Ds : Finset (Submodule F (Fin 2 → F))),
      (∀ lam : Fin 2 → F, lam ≠ 0 → RowClose C δ U j lam →
        Submodule.span F {lam} ∈ Ds) ∧ Ds.card + 1 ≤ Fintype.card F := by
  intro h
  obtain ⟨j, Ds, hcover, hcard⟩ := h 0
  -- every direction of row `j` of the zero stack is δ-close: agreement set `univ`, codeword `0`
  have hclose : ∀ lam : Fin 2 → F, RowClose C δ (0 : Fin l → ι → Fin 2 → A) j lam := by
    intro lam
    refine ⟨Finset.univ, ?_, 0, C.zero_mem, fun i _ => by simp⟩
    rw [Finset.card_univ]
    exact mul_le_of_le_one_left zero_le tsub_le_self
  -- the `q + 1` lines of `F²`, indexed by `Option F`
  let v : Option F → Fin 2 → F := fun o => o.elim ![0, 1] (fun β => ![1, β])
  have hv0 : ∀ o, v o ≠ 0 := by
    intro o hvo
    cases o with
    | none => simpa [v] using congrFun hvo 1
    | some β => simpa [v] using congrFun hvo 0
  have hinj : Function.Injective (fun o => Submodule.span F {v o}) := by
    intro o o' heq
    have hmem : v o' ∈ Submodule.span F {v o} := by
      have heq' : Submodule.span F {v o} = Submodule.span F {v o'} := heq
      rw [heq']
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some β' => simp [v] at h0
    | some β =>
      cases o' with
      | none =>
        simp [v] at h0 h1
        simp [h0] at h1
      | some β' =>
        simp [v] at h0 h1
        rw [h0, one_mul] at h1
        rw [h1]
  have hsub : (Finset.univ : Finset (Option F)).image (fun o => Submodule.span F {v o})
      ⊆ Ds := by
    intro K hK
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hK
    exact hcover (v o) (hv0 o) (hclose (v o))
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_option] at hle
  omega

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [DecidableEq A] in
/-- A stack with no `G`-MCA-bad seed satisfies `ObstructionBound` with the empty family. -/
theorem obstructionBound_of_no_bad_seed
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin s → A)
    (hno : ∀ ω : Ω, ¬ mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)) :
    ObstructionBound C δ G U :=
  ⟨∅, by simp, by simp, fun ω hω => absurd hω (hno ω)⟩

open Classical in
/-- **S2(b′) chained to exactness (bad-stack form).**  If every 2-column stack *that has a
`G`-MCA-bad seed* admits a row whose δ-close direction spans fit in some `Ds` with
`#Ds + 1 ≤ q`, generator-MCA interleaving is exact for every generator.  Stacks without bad
seeds (the zero stack among them) satisfy `ObstructionBound` trivially
(`obstructionBound_of_no_bad_seed`), so they are not asked to meet the count.  This removes
the zero-stack obstruction of `not_forall_rowCloseSpans_card`; whether the restricted count
holds for a given code and radius is the open input and is not established here.  The
count still ranges over *all* close directions of the chosen row, which can be more than the
directions in realized obstructions. -/
theorem epsMCAG_interleaved_eq_of_badStack_rowCloseSpans_card
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (h : ∀ U : Fin l → ι → Fin 2 → A,
      (∃ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω)) →
      ∃ (j : Fin l) (Ds : Finset (Submodule F (Fin 2 → F))),
        (∀ lam : Fin 2 → F, lam ≠ 0 → RowClose C δ U j lam →
          Submodule.span F {lam} ∈ Ds) ∧ Ds.card + 1 ≤ Fintype.card F) :
    epsMCAG (A := Fin 2 → A) ((C : Set (ι → A))^⋈ (Fin 2)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  refine epsMCAG_interleaved_eq_of_obstructionBound C 2 δ G (fun U => ?_)
  by_cases hbad : ∃ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω)
  · obtain ⟨j, Ds, hcover, hcard⟩ := h U hbad
    exact obstructionBound_of_rowCloseSpans_cover C δ G U j Ds hcover hcard
  · push_neg at hbad
    exact obstructionBound_of_no_bad_seed C δ G U hbad

/-! ### Genuine line exclusion gives the containment cover

`Jo26ObstructionCount.LineExclusion` says some line `L₀` of `F²` is never a realized
bad-seed obstruction. Every proper obstruction is `⊥` or a line. A line other than `L₀`
is one of the remaining `q` lines, and `⊥` lies below any of them. So the `q` lines
other than `L₀` dominate every obstruction *by containment* (`ObstructionCover`). -/

/-- The `q + 1` lines of `F²`, indexed by `Option F`: `none ↦ span{(0,1)}` and
`some a ↦ span{(1,a)}`. -/
noncomputable def lineOf : Option F → Submodule F (Fin 2 → F)
  | none => Submodule.span F {![0, 1]}
  | some a => Submodule.span F {![1, a]}

/-- The index of the line spanned by a vector `v`: `none` if `v 0 = 0`, else
`some (v 1 / v 0)`. -/
def lineIndex (v : Fin 2 → F) : Option F :=
  if v 0 = 0 then none else some (v 1 / v 0)

omit [Fintype F] in
/-- Every line `span{v}` (`v ≠ 0`) is `lineOf (lineIndex v)`. -/
theorem span_eq_lineOf_lineIndex {v : Fin 2 → F} (hv : v ≠ 0) :
    Submodule.span F {v} = lineOf (lineIndex v) := by
  unfold lineIndex
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext k
      fin_cases k
      · exact h0
      · exact h1
    have hveq : v = v 1 • ![(0 : F), 1] := by
      funext k
      fin_cases k <;> simp [h0]
    rw [if_pos h0]
    show Submodule.span F {v} = Submodule.span F {![0, 1]}
    conv_lhs => rw [hveq]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ h1) _
  · have hveq : v = v 0 • ![(1 : F), v 1 / v 0] := by
      funext k
      fin_cases k
      · simp
      · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
          smul_eq_mul]
        field_simp
    rw [if_neg h0]
    show Submodule.span F {v} = Submodule.span F {![1, v 1 / v 0]}
    conv_lhs => rw [hveq]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ h0) _

omit [Fintype F] [DecidableEq F] in
/-- Every indexed line is a proper subspace. -/
theorem lineOf_ne_top (o : Option F) : lineOf o ≠ ⊤ := by
  cases o with
  | none => exact span_singleton_ne_top _
  | some a => exact span_singleton_ne_top _

open Classical in
/-- **Line exclusion implies the containment cover (S2(b) avoidance, `s = 2`).**  If some
line `L₀ = span{v}` is never a realized bad-seed obstruction of `U`, then the `q` lines other
than `L₀` form a family of at most `q` proper subspaces containing every realized obstruction.
The membership form `ObstructionBound` does not follow in general (over `F₂`, obstructions
`{⊥, L₁, L₂}`). -/
theorem obstructionCover_of_lineExclusion
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin 2 → A) (h : LineExclusion C δ G U) :
    ObstructionCover C δ G U := by
  obtain ⟨v, hv0, hex⟩ := h
  refine ⟨((Finset.univ : Finset (Option F)).erase (lineIndex v)).image lineOf, ?_, ?_, ?_⟩
  · calc (((Finset.univ : Finset (Option F)).erase (lineIndex v)).image lineOf).card
        ≤ ((Finset.univ : Finset (Option F)).erase (lineIndex v)).card :=
          Finset.card_image_le
      _ = Fintype.card F := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_option, Nat.add_sub_cancel]
  · intro K hK
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hK
    exact lineOf_ne_top o
  · intro ω hω
    obtain ⟨T, hW, hne⟩ := hex ω hω
    refine ⟨T, hW, ?_⟩
    have hproper : jointStackSubmodule C T U ≠ ⊤ :=
      jointStackSubmodule_ne_top C U hW.2.2
    rcases proper_eq_bot_or_span _ hproper with hbot | ⟨lam, hlam0, _, hspan⟩
    · refine ⟨lineOf (if lineIndex v = none then some 0 else none),
        Finset.mem_image.mpr ⟨_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩, ?_⟩
      · by_cases hn : lineIndex v = none
        · rw [if_pos hn, hn]
          exact Option.some_ne_none 0
        · rw [if_neg hn]
          exact fun e => hn e.symm
      · rw [hbot]
        exact bot_le
    · refine ⟨lineOf (lineIndex lam),
        Finset.mem_image.mpr ⟨_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩, ?_⟩
      · intro heq
        apply hne
        rw [hspan, span_eq_lineOf_lineIndex hlam0, heq, ← span_eq_lineOf_lineIndex hv0]
      · rw [hspan, span_eq_lineOf_lineIndex hlam0]

open Classical in
/-- **Exactness from genuine line exclusion (`s = 2`).**  If every 2-column stack has a line
that is never a realized bad-seed obstruction (`LineExclusion`, hypothesis S2(b), open in
general), generator-MCA interleaving is exact for every generator. -/
theorem epsMCAG_interleaved_eq_of_lineExclusion
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (hLE : ∀ U : Fin l → ι → Fin 2 → A, LineExclusion C δ G U) :
    epsMCAG (A := Fin 2 → A) ((C : Set (ι → A))^⋈ (Fin 2)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G :=
  epsMCAG_interleaved_eq_of_obstructionCover C 2 δ G
    (fun U => obstructionCover_of_lineExclusion C δ G U (hLE U))

end ProximityGap.Jo26Obstruction

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Jo26Obstruction.proper_eq_bot_or_span
#print axioms ProximityGap.Jo26Obstruction.obstructionBound_of_rowCloseSpans_cover
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_rowCloseSpans_card
#print axioms ProximityGap.Jo26Obstruction.not_forall_rowCloseSpans_card
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_badStack_rowCloseSpans_card
#print axioms ProximityGap.Jo26Obstruction.obstructionCover_of_lineExclusion
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_lineExclusion
