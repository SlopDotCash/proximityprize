/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceEveryLine
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The universal alignment law: MCA ≡ residual-pencil alignment at EVERY radius (#371)

The boundary-slice laws characterize the bad set at the boundary band only
(`(1−δ)n ≤ k+1`, single-tuple witnesses).  This file proves the **complete dictionary at
every radius and for every line**: for any agreement threshold `a ≥ k+1`
(`a−1 < (1−δ)n ≤ a`),

  **`γ` is MCA-bad ⟺ some `a`-point set `S` is `γ`-ALIGNED with a non-degenerate
  tuple** — every injective `(k+1)`-tuple of `S` satisfies `e_t(u₀) + γ·e_t(u₁) = 0`,
  and at least one tuple has `(e_t(u₀), e_t(u₁)) ≠ (0, 0)`

(`mcaEvent_iff_aligned_subset`).  The supporting dictionary:

* `explainableOn_iff_forall_residual` — a word extends to a codeword on `S` iff every
  tuple residual vanishes (Lagrange + the `k`-shared-node glue, the level-`a` analog of
  the extraction in `BoundarySliceEveryLine`);
* `pairJointAgreesOn_iff_forall_residual` — joint explanation ⟺ both components' tuple
  residuals all vanish;
* an aligned set with a non-degenerate tuple pins its scalar (`Aligned.gamma_eq`), so
  distinct bad scalars have distinct aligned sets:
  **`#bad(δ) ≤ #{γ-alignable a-sets}`** (`badScalars_card_le_alignable`) — the universal
  census bound, the exact generalization of the boundary count to every radius.

**Why this matters (#371).**  Every remaining open inequality of the programme — the
interior ceiling at constant rate included — is now literally a statement about the
alignment census of the residual-functional pencil `{e_•(u₀) + γ·e_•(u₁)}` over
`(k+1)`-tuples of the domain: `ε_mca(C, δ) ≤ ε*` **is** `#{γ-alignable ⌈(1−δ)n⌉-sets,
fibred over the pinned scalar} ≤ ε*·q`.  The boundary band (`a = k+1`: single tuples,
the ratio image) and the radius-free ownership counts (each aligned set burns its
tuples) are the first two shadows of this one geometry.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Enumeration helper -/

omit [NeZero n] in
/-- Enumeration of a finite index set of size `m`: injective, into the set, and onto it. -/
private lemma exists_enum (T : Finset (Fin n)) {m : ℕ} (hT : T.card = m) :
    ∃ e : Fin m → Fin n, Function.Injective e ∧ (∀ j, e j ∈ T) ∧
      ∀ i ∈ T, ∃ j, e j = i := by
  refine ⟨fun j => (T.equivFin.symm (Fin.cast hT.symm j) : Fin n), ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.cast_injective _ (T.equivFin.symm.injective (Subtype.ext hab))
  · exact fun j => (T.equivFin.symm (Fin.cast hT.symm j)).2
  · intro i hi
    obtain ⟨j', hj'⟩ := T.equivFin.symm.surjective ⟨i, hi⟩
    refine ⟨Fin.cast hT j', ?_⟩
    show ((T.equivFin.symm (Fin.cast hT.symm (Fin.cast hT j'))) : Fin n) = i
    rw [show Fin.cast hT.symm (Fin.cast hT j') = j' from Fin.ext rfl, hj']

/-! ## The explainability dictionary -/

/-- **Explainability ⟺ all tuple residuals vanish.**  The `⟸` direction at `|S| > k`
glues: interpolate on a `k`-subset; every further point is absorbed through the snoc
tuple, whose extension agrees with the interpolant on the `k` shared nodes. -/
theorem explainableOn_iff_forall_residual (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u : Fin n → F} {S : Finset (Fin n)} :
    (∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ S, c i = u i)
      ↔ ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S) →
          residual dom k t u = 0 := by
  have hinjOn : ∀ (T : Finset (Fin n)), Set.InjOn (fun i : Fin n => dom i) ↑T :=
    fun T a _ b _ hab => dom.injective hab
  constructor
  · rintro ⟨c, ⟨P, hPdeg, rfl⟩, hag⟩ t htinj htmem
    have hPdeg' : P.natDegree < k := by
      by_cases hP0 : P = 0
      · subst hP0
        simpa using hk
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    exact residual_eq_zero_of_extends dom k t hPdeg' fun b =>
      (hag (t b) (htmem b)).symm
  · intro hall
    by_cases hcard : S.card ≤ k
    · -- small sets: direct Lagrange interpolation
      refine ⟨fun i => (Lagrange.interpolate S (fun i : Fin n => dom i) u).eval (dom i),
        ⟨Lagrange.interpolate S (fun i : Fin n => dom i) u, ?_, rfl⟩, fun i hi =>
        Lagrange.eval_interpolate_at_node u (hinjOn S) hi⟩
      have h := Lagrange.degree_interpolate_lt (r := u) (hinjOn S)
      exact lt_of_lt_of_le h (by exact_mod_cast hcard)
    · push Not at hcard
      obtain ⟨T₀, hT₀S, hT₀card⟩ := Finset.exists_subset_card_eq (le_of_lt hcard)
      obtain ⟨e, heinj, hemem, hesurj⟩ := exists_enum T₀ hT₀card
      have hqdeg : (Lagrange.interpolate T₀ (fun i : Fin n => dom i) u).degree
          < (k : WithBot ℕ) := by
        have h := Lagrange.degree_interpolate_lt (r := u) (hinjOn T₀)
        rwa [hT₀card] at h
      have hqnode : ∀ i ∈ T₀,
          u i = (Lagrange.interpolate T₀ (fun i : Fin n => dom i) u).eval (dom i) :=
        fun i hi => (Lagrange.eval_interpolate_at_node u (hinjOn T₀) hi).symm
      refine ⟨fun i => (Lagrange.interpolate T₀ (fun i : Fin n => dom i) u).eval (dom i),
        ⟨Lagrange.interpolate T₀ (fun i : Fin n => dom i) u, hqdeg, rfl⟩,
        fun x hxS => ?_⟩
      by_cases hxT : x ∈ T₀
      · exact (hqnode x hxT).symm
      · -- the snoc tuple (e, x)
        have hex : ∀ j, e j ≠ x := fun j hj => hxT (hj ▸ hemem j)
        have htinj : Function.Injective (Fin.snoc e x : Fin (k + 1) → Fin n) := by
          intro a b hab
          obtain ⟨ja, rfl⟩ | rfl := a.eq_castSucc_or_eq_last <;>
            obtain ⟨jb, rfl⟩ | rfl := b.eq_castSucc_or_eq_last
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
            rw [heinj hab]
          · rw [Fin.snoc_castSucc, Fin.snoc_last] at hab
            exact absurd hab (hex ja)
          · rw [Fin.snoc_last, Fin.snoc_castSucc] at hab
            exact absurd hab.symm (hex jb)
          · rfl
        have htmem : ∀ b, (Fin.snoc e x : Fin (k + 1) → Fin n) b ∈ S := by
          intro b
          obtain ⟨jb, rfl⟩ | rfl := b.eq_castSucc_or_eq_last
          · rw [Fin.snoc_castSucc]
            exact hT₀S (hemem jb)
          · rw [Fin.snoc_last]
            exact hxS
        obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom
          (Fin.snoc e x) htinj (hall _ htinj htmem)
        obtain ⟨P, hPdeg, rfl⟩ := hcC
        have hPeq : P = Lagrange.interpolate T₀ (fun i : Fin n => dom i) u := by
          refine Polynomial.eq_of_degrees_lt_of_eval_index_eq T₀
            (hinjOn T₀) ?_ ?_ ?_
          · rw [hT₀card]; exact hPdeg
          · rw [hT₀card]; exact hqdeg
          · intro i hi
            obtain ⟨j, rfl⟩ := hesurj i hi
            have h1 : P.eval (dom ((Fin.snoc e x : Fin (k + 1) → Fin n) j.castSucc))
                = u ((Fin.snoc e x : Fin (k + 1) → Fin n) j.castSucc) := hcag j.castSucc
            rw [Fin.snoc_castSucc] at h1
            rw [h1, ← hqnode (e j) (hemem j)]
        have hlast : P.eval (dom ((Fin.snoc e x : Fin (k + 1) → Fin n) (Fin.last k)))
            = u ((Fin.snoc e x : Fin (k + 1) → Fin n) (Fin.last k)) := hcag (Fin.last k)
        rw [Fin.snoc_last, hPeq] at hlast
        exact hlast

/-- **Joint agreement ⟺ both components' tuple residuals vanish.** -/
theorem pairJointAgreesOn_iff_forall_residual (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {S : Finset (Fin n)} :
    pairJointAgreesOn
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁
      ↔ ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S) →
          residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0 := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩ t htinj htmem
    exact ⟨(explainableOn_iff_forall_residual dom hk).mp
        ⟨v₀, hv₀, fun i hi => (hag i hi).1⟩ t htinj htmem,
      (explainableOn_iff_forall_residual dom hk).mp
        ⟨v₁, hv₁, fun i hi => (hag i hi).2⟩ t htinj htmem⟩
  · intro hall
    obtain ⟨c₀, hc₀, hag₀⟩ := (explainableOn_iff_forall_residual dom hk).mpr
      (fun t h1 h2 => (hall t h1 h2).1)
    obtain ⟨c₁, hc₁, hag₁⟩ := (explainableOn_iff_forall_residual dom hk).mpr
      (fun t h1 h2 => (hall t h1 h2).2)
    exact ⟨c₀, hc₀, c₁, hc₁, fun i hi => ⟨hag₀ i hi, hag₁ i hi⟩⟩

/-! ## Alignment -/

/-- A set is `γ`-**aligned** when every injective `(k+1)`-tuple inside it lies on the
`γ`-fibre of the residual pencil. -/
def Aligned (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    (S : Finset (Fin n)) : Prop :=
  ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S) →
    residual dom k t u₀ + γ * residual dom k t u₁ = 0

open Classical in
/-- The `a`-point sets that are aligned for some scalar and contain a non-degenerate
tuple.  These are the census objects in `badScalars_card_le_alignable`. -/
noncomputable def alignableSets (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard a).filter (fun S : Finset (Fin n) =>
    ∃ γ : F, Aligned dom k u₀ u₁ γ S ∧
      ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
        ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- Alignment is monotone under subsets: every tuple of a subset is a tuple of the set. -/
theorem Aligned.mono {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ : F}
    {S S' : Finset (Fin n)} (h : Aligned dom k u₀ u₁ γ S) (hsub : S' ⊆ S) :
    Aligned dom k u₀ u₁ γ S' :=
  fun t htinj htmem => h t htinj (fun b => hsub (htmem b))

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- An aligned set with a non-degenerate tuple pins its scalar. -/
theorem Aligned.gamma_eq {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ γ' : F}
    {S : Finset (Fin n)} (h : Aligned dom k u₀ u₁ γ S) (h' : Aligned dom k u₀ u₁ γ' S)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) : γ = γ' := by
  have h1 := h t htinj htmem
  have h2 := h' t htinj htmem
  have hres1 : residual dom k t u₁ ≠ 0 := by
    intro hz
    refine hnd ⟨?_, hz⟩
    rwa [hz, mul_zero, add_zero] at h1
  have hkey : (γ - γ') * residual dom k t u₁ = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp hkey with hd | hd
  · exact sub_eq_zero.mp hd
  · exact absurd hd hres1

/-! ## THE UNIVERSAL ALIGNMENT LAW -/

/-- **THE UNIVERSAL ALIGNMENT LAW**: at every radius (agreement threshold
`a−1 < (1−δ)n ≤ a`, `a ≥ k+1`) and for every stack, `γ` is MCA-bad iff some `a`-point
set is `γ`-aligned with a non-degenerate tuple. -/
theorem mcaEvent_iff_aligned_subset (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) (γ : F) :
    mcaEvent (F := F) ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        δ u₀ u₁ γ
      ↔ ∃ S : Finset (Fin n), S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
          ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
            ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0) := by
  constructor
  · rintro ⟨S₀, hsz, hwC, hno⟩
    have hS₀card : a ≤ S₀.card := by
      have h1 : ((a - 1 : ℕ) : ℝ≥0) < (S₀.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
      have h2 : a - 1 < S₀.card := by exact_mod_cast h1
      omega
    -- the combined word is explainable on S₀, hence every tuple of S₀ is on the fibre
    have hexpl : ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S₀) →
        residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      refine (explainableOn_iff_forall_residual dom hk).mp ?_
      obtain ⟨w, hwmem, hwag⟩ := hwC
      exact ⟨w, hwmem, fun i hi => by rw [hwag i hi, smul_eq_mul]⟩
    -- a non-degenerate tuple from the no-joint clause
    have hnall : ¬ ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
        (∀ b, t b ∈ S₀) → residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0 :=
      fun hcontra => hno ((pairJointAgreesOn_iff_forall_residual dom hk).mpr hcontra)
    push Not at hnall
    obtain ⟨t, htinj, htmem, hnd'⟩ := hnall
    have hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0) :=
      fun hc => hnd' hc.1 hc.2
    -- an a-subset of S₀ containing the tuple's image
    have himsub : Finset.univ.image t ⊆ S₀ := by
      intro i hi
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hi
      exact htmem b
    have himcard : (Finset.univ.image t).card = k + 1 := by
      rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
    obtain ⟨S, hSsub1, hSsub2, hScard⟩ := Finset.exists_subsuperset_card_eq himsub
      (by omega) hS₀card
    refine ⟨S, hScard, ?_, t, htinj,
      fun b => hSsub1 (Finset.mem_image_of_mem t (Finset.mem_univ b)), hnd⟩
    intro t' ht'inj ht'mem
    have h := hexpl t' ht'inj (fun b => hSsub2 (ht'mem b))
    rwa [residual_line] at h
  · rintro ⟨S, hScard, halign, t, htinj, htmem, hnd⟩
    refine ⟨S, ?_, ?_, ?_⟩
    · rw [hScard]
      exact_mod_cast hhi
    · have hfib : ∀ t' : Fin (k + 1) → Fin n, Function.Injective t' →
          (∀ b, t' b ∈ S) → residual dom k t' (fun i => u₀ i + γ * u₁ i) = 0 := by
        intro t' h1 h2
        rw [residual_line]
        exact halign t' h1 h2
      obtain ⟨c, hcmem, hcag⟩ := (explainableOn_iff_forall_residual dom hk).mpr hfib
      exact ⟨c, hcmem, fun i hi => by rw [hcag i hi, smul_eq_mul]⟩
    · intro hjoint
      exact hnd ((pairJointAgreesOn_iff_forall_residual dom hk).mp hjoint t htinj htmem)

open Classical in
/-- **THE UNIVERSAL CENSUS BOUND**: at every radius, the number of bad scalars is at most
the number of `γ`-alignable `a`-sets — each bad scalar owns its aligned sets exclusively
(`Aligned.gamma_eq`). -/
theorem badScalars_card_le_alignable (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ ((Finset.univ.powersetCard a).filter (fun S : Finset (Fin n) =>
          ∃ γ : F, Aligned dom k u₀ u₁ γ S ∧
            ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
              ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun γ =>
    if h : mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ
    then ((mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ).mp h).choose
    else ∅) ?_ ?_
  · intro γ hγ
    have hbad := (Finset.mem_filter.mp hγ).2
    simp only [dif_pos hbad, Finset.mem_coe]
    have hspec := ((mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ).mp
      hbad).choose_spec
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hspec.1⟩, γ, hspec.2.1, hspec.2.2⟩
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    have hbad₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hγ₁)).2
    have hbad₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hγ₂)).2
    simp only [dif_pos hbad₁, dif_pos hbad₂] at heq
    have hspec₁ := ((mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ₁).mp
      hbad₁).choose_spec
    have hspec₂ := ((mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ₂).mp
      hbad₂).choose_spec
    obtain ⟨t, htinj, htmem, hnd⟩ := hspec₁.2.2
    exact Aligned.gamma_eq hspec₁.2.1 (heq ▸ hspec₂.2.1) htinj htmem hnd

open Classical in
/-- The universal census bound in `alignableSets` notation. -/
theorem badScalars_card_le_alignableSets (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (alignableSets dom k a u₀ u₁).card := by
  simpa [alignableSets] using badScalars_card_le_alignable dom hk hka hlo hhi u₀ u₁

open Classical in
/-- Any uniform census bound for alignable `a`-sets immediately gives the prize-side
`ε_mca` bound.  This is the main consumer for future alignment-census theorems. -/
theorem epsMCA_le_of_alignableSets_card_le (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ)) (L : ℕ)
    (hL : ∀ u₀ u₁ : Fin n → F, (alignableSets dom k a u₀ u₁).card ≤ L) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ L
    (fun u => le_trans
      (badScalars_card_le_alignableSets dom hk hka hlo hhi (u 0) (u 1))
      (hL (u 0) (u 1)))

open Classical in
/-- Coarse alignment census: before using any structure, there is at most one bad scalar
per `a`-subset. -/
theorem alignableSets_card_le_choose (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (alignableSets dom k a u₀ u₁).card ≤ n.choose a := by
  calc
    (alignableSets dom k a u₀ u₁).card
        ≤ ((Finset.univ : Finset (Fin n)).powersetCard a).card := by
          rw [alignableSets]
          exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = n.choose a := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- Coarse probability form of the universal alignment law:
`ε_mca(δ) ≤ C(n,a)/|F|` whenever `a−1 < (1−δ)n ≤ a` and `a ≥ k+1`. -/
theorem epsMCA_le_alignment_choose (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n.choose a : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_alignableSets_card_le dom hk hka hlo hhi (n.choose a)
    (fun u₀ u₁ => alignableSets_card_le_choose dom k a u₀ u₁)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.explainableOn_iff_forall_residual
#print axioms ProximityGap.Ownership.pairJointAgreesOn_iff_forall_residual
#print axioms ProximityGap.Ownership.mcaEvent_iff_aligned_subset
#print axioms ProximityGap.Ownership.badScalars_card_le_alignable
#print axioms ProximityGap.Ownership.badScalars_card_le_alignableSets
#print axioms ProximityGap.Ownership.epsMCA_le_of_alignableSets_card_le
#print axioms ProximityGap.Ownership.alignableSets_card_le_choose
#print axioms ProximityGap.Ownership.epsMCA_le_alignment_choose
