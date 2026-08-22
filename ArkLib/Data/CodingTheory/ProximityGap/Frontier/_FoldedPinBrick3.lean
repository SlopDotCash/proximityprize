/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CharSumDeltaStarBridge
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.CodingTheory.ReedSolomon.Folded

/-!
# Folded-RS capacity pin, brick 3 — the `epsMCA` weld on the folded alphabet (gap G4)
# (issue #466, lane L7; dossier v3 §6 Tier-3 ★; map doc
# `docs/kb/deltastar-466-folded-pin-map-2026-07-01.md`)

**Where this sits.** The map doc's chain had one missing arrow between the folded
determining-tuple machinery (brick 1, `_FoldedPinBrick1.lean`) and the lane target
`FrsMCAPin` (`epsMCA(frsCode) ≤ Λ/q`): gap **G4**, "the `epsMCA` weld — `mcaEvent`
bookkeeping, pattern = `LineListMCAWeld`".  The blocker was purely an alphabet gap: the
entire weld machinery (`LineListMCAWeld.lean`, `LineListReduction.lean`) is stated for
`C : Submodule F (Fin n → F)` (plain-RS alphabet `A = F`), while the folded code lives at
`A = Fin s → F`.  The `epsMCA ≤ M/q` consumer
(`CharSumDeltaStarBridge.epsMCA_le_of_forall_badCount_le`) is already alphabet-generic.

**What this file proves (all axiom-clean, no `sorry`).** The weld machinery re-derived for a
generic module alphabet `A` (a generic `F`-submodule code `C ≤ (ι → A)`,
`[NoZeroSMulDivisors F A]` where cancellation is needed), then instantiated at
`A = Fin s → F`, `C = frsCode`:

1. **Structural `mcaEvent` lemmas, generic alphabet** (§1): witness-farness is free from the
   `¬pairJointAgreesOn` clause (`no_direction_codeword_on_witness_of_mcaEvent`); aligned
   directions carry zero bad scalars (`mcaEvent_false_of_direction_mem`); `mcaEvent` is
   invariant under shifting the direction by a codeword
   (`mcaEvent_direction_sub_codeword_iff`).  Verbatim generalizations of the
   `LineListMCAWeld` originals — module operations only, no field-alphabet facts.
2. **The line-list vocabulary, generic alphabet** (§2): `lineAgreeSet`, `directionZeroSet`
   (a "zero coordinate" of a folded word is a whole zero *block*), `lineBadScalars`,
   `lineAppearingCodewords`, and the two named budget `Prop`s `FarLineListBudget` /
   `LargeZeroBadScalarBudget`.
3. **The incidence core** (§3): `codeword_scalars_card_le` — on a direction with `z < a` zero
   blocks, one codeword can have agreement `≥ a` at no more than `(n−z)/(a−z)` scalars
   (agreement sets of distinct scalars overlap only inside the direction's zero set, by
   `smul` cancellation); hence `lineBadScalars_card_le_appearing_mul` — bad scalars ≤
   (appearing codewords) · `(n−z)/(a−z)`.
4. **THE WELD** (§4): `epsMCA_le_of_farLineListBudgeted` — for ANY `F`-submodule code over
   ANY module alphabet: far-line list budget `L` + arithmetic fit + large-zero budget ⟹
   `epsMCA C δ ≤ max(B_far, B_near)/q`, via the coset dichotomy (every stack either shifts
   to a large-zero direction or is genuinely far).  Plus the `mcaDeltaStar` corollary.
5. **The folded headline** (§5): `frs_epsMCA_le_of_farLineListBudgeted` — the instantiation
   at `C = frsCode domain k s ω`.  Its conclusion is *literally* the lane target
   `FrsMCAPin domain k s ω δ (max B_far B_near)` of `_FoldedPinBrick1.lean` (definitional
   match; the two frontier files are import-independent, so the `FrsMCAPin`-typed alias
   belongs in a follow-up once both have oleans).  **Gap G4 of the map doc is CLOSED as a
   conditional reduction**: the folded MCA pin is now exactly two named counting budgets.
6. **Guards** (§6): `aligned_lineAppearingCodewords_card_ge` — aligned nonzero directions
   have `≥ q` appearing codewords on the folded domain too, so the far restriction in the
   budget is FORCED (`not_uniform_lineAppearing_budget_of_lt_card` is the generic refuter of
   any all-directions budget below `q`); harmless by `mcaEvent_false_of_direction_mem`.

**Scoping consequence for the map doc (recorded there).** The weld consumes the far-line
*list* budget directly at `ℓ = 1`; the curve engine
(`CurveListSizeLe → curveDecodable_of_curveListSize → all_seeds_close_of_curveDecodable`)
is NOT needed for the `Fin 2`-stack `epsMCA` target.  So gap G3 is re-aimed: what remains
between brick 1's span machinery (`FrsCloseListSpanBound`, gap G2) and this brick's
`FarLineListBudget` is the **curve-level list argument** (GG25 §4/JLR §5: the codewords
appearing anywhere on a far folded line number `poly(1/η)`) — one named counting statement,
zero character sums.

**Honest scope / relation to the prize (dossier §11.6).** `isPrizeClosure := False`.
Goal-(A)-adjacent banking (FRI/STIR/WHIR fold); does NOT touch plain-RS δ\* (goal (B)):
`FoldingTransferNoGo.folding_transfer_no_go` stands.  The generic weld also applies to plain
RS, where it reproduces the existing `LineListMCAWeld` shape — no new plain-RS strength (the
budgets there are exactly the open Tier-1 item-2 obligations).  Nothing here claims the
budgets: `FarLineListBudget` and `LargeZeroBadScalarBudget` are named OPEN inputs at the
folded parameters of interest.

References: map doc `docs/kb/deltastar-466-folded-pin-map-2026-07-01.md`; [GG25] ePrint
2025/2054 §3–4; [JLR] arXiv 2601.10047 §5; ABF26 (ePrint 2026/680) Def 4.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FoldedPinWeld

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open ProximityGap ProximityGap.FarCosetExplosion

/-! ### §1. Structural `mcaEvent` lemmas — generic module alphabet -/

/-- **Witness farness is free (generic alphabet).** If the line `u₀ + γ·u₁` agrees with a
codeword on `S` and no joint pair explains `(u₀, u₁)` on `S`, then no codeword agrees with
the *direction* `u₁` on all of `S` — otherwise `(w − γ·c, c)` is a joint pair on `S`.
Generalizes `LineListMCAWeld.no_direction_codeword_on_witness_of_mcaEvent` from `A = F` to
any module alphabet (the proof is module-operations-only). -/
theorem no_direction_codeword_on_witness_of_mcaEvent
    (C : Submodule F (ι → A)) {u₀ u₁ : ι → A} {γ : F}
    {S : Finset ι}
    (hline : ∃ w ∈ (C : Set (ι → A)), ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hnj : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁) :
    ∀ c ∈ (C : Set (ι → A)), ∃ i ∈ S, c i ≠ u₁ i := by
  intro c hc
  by_contra hno
  push_neg at hno
  obtain ⟨w, hw, hwl⟩ := hline
  apply hnj
  refine ⟨w - γ • c, ?_, c, hc, fun i hi => ⟨?_, hno i hi⟩⟩
  · exact Submodule.sub_mem C hw (Submodule.smul_mem C γ hc)
  · calc (w - γ • c) i = w i - γ • c i := rfl
      _ = (u₀ i + γ • u₁ i) - γ • u₁ i := by rw [hwl i hi, hno i hi]
      _ = u₀ i := add_sub_cancel_right _ _

/-- **Aligned directions are never bad (generic alphabet).** If the direction is itself a
codeword, `mcaEvent` never fires.  This is why the maximal folded line lists of aligned
directions (`aligned_lineAppearingCodewords_card_ge`) are harmless. -/
theorem mcaEvent_false_of_direction_mem
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {u₀ u₁ : ι → A}
    (hu₁ : u₁ ∈ C) (γ : F) :
    ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, -, hline, hnj⟩
  obtain ⟨i, -, hne⟩ :=
    no_direction_codeword_on_witness_of_mcaEvent C hline hnj u₁ hu₁
  exact hne rfl

/-- Shifting the direction by a codeword preserves `mcaEvent` (forward form, generic
alphabet).  The witness codeword shifts by `γ·v₁`; joint pairs transport by `p₁ ↦ p₁ − v₁`. -/
theorem mcaEvent_direction_add_codeword
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {u₀ u₁ v₁ : ι → A}
    (hv₁ : v₁ ∈ C) {γ : F}
    (h : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (u₁ + v₁) γ := by
  obtain ⟨S, hsz, ⟨w, hw, hwl⟩, hnj⟩ := h
  refine ⟨S, hsz,
    ⟨w + γ • v₁, Submodule.add_mem C hw (Submodule.smul_mem C γ hv₁), fun i hi => ?_⟩, ?_⟩
  · calc (w + γ • v₁) i = w i + γ • v₁ i := rfl
      _ = (u₀ i + γ • u₁ i) + γ • v₁ i := by rw [hwl i hi]
      _ = u₀ i + γ • (u₁ + v₁) i := by
          simp only [Pi.add_apply, smul_add]
          abel
  · rintro ⟨p₀, hp₀, p₁, hp₁, hpair⟩
    refine hnj ⟨p₀, hp₀, p₁ - v₁, Submodule.sub_mem C hp₁ hv₁, fun i hi =>
      ⟨(hpair i hi).1, ?_⟩⟩
    have h2 : p₁ i = u₁ i + v₁ i := (hpair i hi).2
    calc (p₁ - v₁) i = p₁ i - v₁ i := rfl
      _ = (u₁ i + v₁ i) - v₁ i := by rw [h2]
      _ = u₁ i := add_sub_cancel_right _ _

/-- **`mcaEvent` is invariant under shifting the direction by a codeword (generic
alphabet).**  Badness of a stack depends only on the coset `u₁ + C` of its direction. -/
theorem mcaEvent_direction_sub_codeword_iff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {u₀ u₁ v₁ : ι → A}
    (hv₁ : v₁ ∈ C) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (u₁ - v₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  constructor
  · intro h
    have := mcaEvent_direction_add_codeword C δ hv₁ h
    simpa [sub_add_cancel] using this
  · intro h
    have := mcaEvent_direction_add_codeword C δ (Submodule.neg_mem C hv₁) h
    simpa [sub_eq_add_neg] using this

open Classical in
/-- Bad-scalar counts are coset invariants of the direction (generic alphabet). -/
theorem mcaEvent_filter_card_direction_sub_codeword
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {u₀ u₁ v₁ : ι → A} (hv₁ : v₁ ∈ C) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)).card
      = (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (u₁ - v₁) γ)).card := by
  have hset : (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ))
      = (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (u₁ - v₁) γ)) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mcaEvent_direction_sub_codeword_iff C δ hv₁ γ).symm
  rw [hset]

/-! ### §2. The line-list vocabulary — generic module alphabet -/

open Classical in
/-- The agreement set of two words over a generic alphabet. -/
noncomputable def lineAgreeSet (c y : ι → A) : Finset ι :=
  Finset.univ.filter (fun i => c i = y i)

open Classical in
/-- The zero-coordinate set of a direction.  Over the folded alphabet `A = Fin s → F`, a
"zero coordinate" is a whole zero **block**. -/
noncomputable def directionZeroSet (u₁ : ι → A) : Finset ι :=
  Finset.univ.filter (fun i => u₁ i = 0)

open Classical in
/-- The scalars whose line word `u₀ + γ·u₁` is agreed with by some codeword on `≥ a`
coordinates (generic-alphabet `lineBadScalars`). -/
noncomputable def lineBadScalars (C : Set (ι → A)) (a : ℕ) (u₀ u₁ : ι → A) : Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => ∃ c ∈ C, a ≤ (lineAgreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The codewords appearing somewhere along the line `u₀ + γ·u₁` with agreement `≥ a`
(generic-alphabet `lineAppearingCodewords`). -/
noncomputable def lineAppearingCodewords (C : Set (ι → A)) (a : ℕ) (u₀ u₁ : ι → A) :
    Finset (ι → A) :=
  (Finset.univ : Finset (ι → A)).filter
    (fun c => c ∈ C ∧ ∃ γ : F, a ≤ (lineAgreeSet c (fun i => u₀ i + γ • u₁ i)).card)

/-- **NAMED BUDGET (OPEN at the folded parameters of interest — do not cite as proven).**
Every far line of `C` has at most `L` appearing codewords at agreement `a`.  For folded RS
this is the re-aimed gap G3 of the map doc (the GG25 §4/JLR §5 curve-level list argument);
for plain RS it is the open Tier-1 item-2 far-line budget. -/
def FarLineListBudget (C : Set (ι → A)) (a : ℕ) (δ : ℝ≥0) (L : ℕ) : Prop :=
  ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ →
    (lineAppearingCodewords (F := F) C a u₀ u₁).card ≤ L

open Classical in
/-- **NAMED BUDGET (OPEN — do not cite as proven).**  Stacks whose direction has `≥ a` zero
coordinates have at most `B` bad scalars.  The generic-alphabet analogue of the plain weld's
`hlow` (the low-profile / large-zero production obligation). -/
def LargeZeroBadScalarBudget (C : Set (ι → A)) (a : ℕ) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u₀ e₁ : ι → A, a ≤ (directionZeroSet e₁).card →
    (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F) C δ u₀ e₁ γ)).card ≤ B

open Classical in
/-- **Every bad scalar is a line-list bad scalar** (generic alphabet, unconditional — the
forward direction needs no farness). -/
theorem mcaEvent_filter_subset_lineBadScalars
    (C : Set (ι → A)) (a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (u₀ u₁ : ι → A) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ))
      ⊆ lineBadScalars (F := F) C a u₀ u₁ := by
  intro γ hγ
  obtain ⟨S, hsz, ⟨w, hw, hwl⟩, -⟩ := (Finset.mem_filter.mp hγ).2
  have haS : a ≤ S.card := haF S.card hsz
  simp only [lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨w, hw, le_trans haS (Finset.card_le_card ?_)⟩
  intro i hi
  simp only [lineAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hwl i hi

/-! ### §2b. Farness and the coset dichotomy — generic alphabet -/

/-- A far direction has fewer than `a` zero coordinates (for `a ≥ (1−δ)·n`): otherwise the
zero codeword agrees with it on an `a`-sized witness set (generic alphabet). -/
theorem directionZeroSet_card_lt_of_farFromCode
    (C : Submodule F (ι → A)) (a : ℕ) (δ : ℝ≥0)
    (haC : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (a : ℝ≥0))
    {u₁ : ι → A}
    (hfar : FarFromCode ((C : Set (ι → A))) δ u₁) :
    (directionZeroSet u₁).card < a := by
  by_contra hge
  push_neg at hge
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hge
  obtain ⟨i, hi, hne⟩ := hfar 0 (Submodule.zero_mem C) S (by
    rw [hcard]; exact haC)
  have hzi : u₁ i = 0 := by
    have hmem := hS hi
    simp only [directionZeroSet, Finset.mem_filter] at hmem
    exact hmem.2
  exact hne (by simp [hzi])

/-- **The coset dichotomy (generic alphabet).**  If no coset representative of the direction
has `≥ a` zero coordinates, the direction is far from the code. -/
theorem farFromCode_of_forall_coset_zeroSmall
    (C : Submodule F (ι → A)) (a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₁ : ι → A}
    (h : ∀ v₁ ∈ C, (directionZeroSet (u₁ - v₁)).card < a) :
    FarFromCode ((C : Set (ι → A))) δ u₁ := by
  intro c hc S hS
  by_contra hno
  push_neg at hno
  have hsub : S ⊆ directionZeroSet (u₁ - c) := by
    intro i hi
    simp only [directionZeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    show u₁ i - c i = 0
    rw [hno i hi, sub_self]
  have hcard : a ≤ (directionZeroSet (u₁ - c)).card :=
    le_trans (haF S.card hS) (Finset.card_le_card hsub)
  exact absurd hcard (not_le.mpr (h c hc))

/-! ### §3. The incidence core: per-codeword scalar multiplicity -/

open Classical in
/-- **The per-codeword scalar-multiplicity bound (generic alphabet).**  A single word `w`
can have agreement `≥ a` with the line `u₀ + γ·u₁` at no more than `(n − z)/(a − z)` scalars
`γ`, where `z < a` is the direction's zero count: agreement sets of distinct scalars overlap
only inside the direction's zero set (`(γ₁−γ₂)•u₁ᵢ = 0 ⟹ u₁ᵢ = 0` by `smul` cancellation),
so the punctured agreement sets are pairwise disjoint subsets of the `n − z` nonzero
coordinates, each of size `≥ a − z`. -/
theorem codeword_scalars_card_le [NoZeroSMulDivisors F A]
    (u₀ u₁ w : ι → A) {a z : ℕ}
    (hz : (directionZeroSet u₁).card = z) (hza : z < a) :
    ((Finset.univ : Finset F).filter
        (fun γ : F => a ≤ (lineAgreeSet w (fun i => u₀ i + γ • u₁ i)).card)).card
      ≤ (Fintype.card ι - z) / (a - z) := by
  classical
  set G := (Finset.univ : Finset F).filter
      (fun γ : F => a ≤ (lineAgreeSet w (fun i => u₀ i + γ • u₁ i)).card) with hG
  set T : F → Finset ι :=
      fun γ => lineAgreeSet w (fun i => u₀ i + γ • u₁ i) \ directionZeroSet u₁ with hT
  -- per-scalar size: each punctured agreement set has `≥ a − z` elements
  have hTcard : ∀ γ ∈ G, a - z ≤ (T γ).card := by
    intro γ hγ
    have hA : a ≤ (lineAgreeSet w (fun i => u₀ i + γ • u₁ i)).card := by
      rw [hG, Finset.mem_filter] at hγ
      exact hγ.2
    have h1 : a - z ≤ (lineAgreeSet w (fun i => u₀ i + γ • u₁ i)).card
        - (directionZeroSet u₁).card := by
      rw [hz]
      exact Nat.sub_le_sub_right hA z
    exact le_trans h1 (Finset.le_card_sdiff _ _)
  -- pairwise disjointness: overlap forces a zero coordinate of the direction
  have hdisj : ∀ γ₁ ∈ G, ∀ γ₂ ∈ G, γ₁ ≠ γ₂ → Disjoint (T γ₁) (T γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [hT, lineAgreeSet, directionZeroSet, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi1 hi2
    have heq : γ₁ • u₁ i = γ₂ • u₁ i :=
      add_left_cancel (hi1.1.symm.trans hi2.1)
    have hz0 : (γ₁ - γ₂) • u₁ i = 0 := by
      rw [sub_smul, heq, sub_self]
    rcases smul_eq_zero.mp hz0 with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hi1.2 h
  -- count: |G|·(a−z) ≤ Σ|T γ| = |⋃ T γ| ≤ n − z
  have hsum : G.card * (a - z) ≤ ∑ γ ∈ G, (T γ).card := by
    calc G.card * (a - z) = ∑ _γ ∈ G, (a - z) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ γ ∈ G, (T γ).card := Finset.sum_le_sum hTcard
  have hunion : ∑ γ ∈ G, (T γ).card = (G.biUnion T).card :=
    (Finset.card_biUnion hdisj).symm
  have hsub : G.biUnion T ⊆ Finset.univ \ directionZeroSet u₁ := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, -, hiT⟩ := hi
    rw [hT, Finset.mem_sdiff] at hiT
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, hiT.2⟩
  have hbound : (G.biUnion T).card ≤ Fintype.card ι - z := by
    calc (G.biUnion T).card ≤ (Finset.univ \ directionZeroSet u₁).card :=
          Finset.card_le_card hsub
      _ = Fintype.card ι - z := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hz]
  have hmul : G.card * (a - z) ≤ Fintype.card ι - z :=
    le_trans hsum (le_trans (le_of_eq hunion) hbound)
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

open Classical in
/-- **Bad scalars ≤ appearing codewords × per-codeword multiplicity (generic alphabet).**
The fiberwise count over the choice assignment `γ ↦ (a witness codeword at γ)`. -/
theorem lineBadScalars_card_le_appearing_mul [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (a : ℕ) (u₀ u₁ : ι → A)
    {z : ℕ} (hz : (directionZeroSet u₁).card = z) (hza : z < a) :
    (lineBadScalars (F := F) C a u₀ u₁).card
      ≤ (lineAppearingCodewords (F := F) C a u₀ u₁).card
        * ((Fintype.card ι - z) / (a - z)) := by
  classical
  -- the chooser: at each bad scalar pick a witnessing codeword
  have hex : ∀ γ ∈ lineBadScalars (F := F) C a u₀ u₁,
      ∃ c, c ∈ C ∧ a ≤ (lineAgreeSet c (fun i => u₀ i + γ • u₁ i)).card := by
    intro γ hγ
    simp only [lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    exact hγ
  set fc : F → ι → A := fun γ =>
    if h : ∃ c, c ∈ C ∧ a ≤ (lineAgreeSet c (fun i => u₀ i + γ • u₁ i)).card
    then h.choose else fun _ => 0 with hfc
  have hmaps : ∀ γ ∈ lineBadScalars (F := F) C a u₀ u₁,
      fc γ ∈ lineAppearingCodewords (F := F) C a u₀ u₁ := by
    intro γ hγ
    have h := hex γ hγ
    simp only [lineAppearingCodewords, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfc]
    simp only [dif_pos h]
    exact ⟨h.choose_spec.1, γ, h.choose_spec.2⟩
  have hfiber : ∀ c ∈ lineAppearingCodewords (F := F) C a u₀ u₁,
      ((lineBadScalars (F := F) C a u₀ u₁).filter (fun γ => fc γ = c)).card
        ≤ (Fintype.card ι - z) / (a - z) := by
    intro c _
    refine le_trans (Finset.card_le_card ?_) (codeword_scalars_card_le u₀ u₁ c hz hza)
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨hγbad, hγc⟩ := hγ
    have h := hex γ hγbad
    have hval : fc γ = h.choose := by
      rw [hfc]
      simp only [dif_pos h]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hγc, hval]
    exact h.choose_spec.2
  calc (lineBadScalars (F := F) C a u₀ u₁).card
      = ∑ c ∈ lineAppearingCodewords (F := F) C a u₀ u₁,
          ((lineBadScalars (F := F) C a u₀ u₁).filter (fun γ => fc γ = c)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _c ∈ lineAppearingCodewords (F := F) C a u₀ u₁,
          ((Fintype.card ι - z) / (a - z)) := Finset.sum_le_sum hfiber
    _ = (lineAppearingCodewords (F := F) C a u₀ u₁).card
          * ((Fintype.card ι - z) / (a - z)) := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### §4. THE WELD — `epsMCA ≤ max(B_far, B_near)/q` from the two budgets -/

open Classical in
/-- **The G4 weld, generic module alphabet.**  For any `F`-submodule code `C ≤ (ι → A)`
(`[NoZeroSMulDivisors F A]`), radius `δ`, agreement threshold `a` (canonically
`a = ⌈(1−δ)·n⌉`):

* `hfarL` — the **far-line list budget** (`FarLineListBudget`, named open input);
* `hfit` — the arithmetic fit `L·((n−z)/(a−z)) ≤ B_far` for all `z < a`;
* `hlow` — the **large-zero branch budget** (`LargeZeroBadScalarBudget`, named open input);

then `ε_mca(C, δ) ≤ max(B_far, B_near)/q`.  Every stack either shifts (by the coset
invariance) to a large-zero direction, or its direction is genuinely far
(`farFromCode_of_forall_coset_zeroSmall`) and the far branch counts through
`lineBadScalars_card_le_appearing_mul`.  This is `LineListMCAWeld`'s dichotomy re-derived
so it applies at the folded alphabet. -/
theorem epsMCA_le_of_farLineListBudgeted [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (a : ℕ) (δ : ℝ≥0) {L Bfar Bnear : ℕ}
    (haC : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : FarLineListBudget (F := F) ((C : Set (ι → A))) a δ L)
    (hfit : ∀ z : ℕ, z < a → L * ((Fintype.card ι - z) / (a - z)) ≤ Bfar)
    (hlow : LargeZeroBadScalarBudget (F := F) ((C : Set (ι → A))) a δ Bnear) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
      ≤ ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine ArkLib.ProximityGap.CharSumDeltaStarBridge.epsMCA_le_of_forall_badCount_le
    ((C : Set (ι → A))) δ (max Bfar Bnear) ?_
  intro u
  by_cases hcase : ∃ v₁ ∈ C, a ≤ (directionZeroSet ((u 1) - v₁)).card
  · obtain ⟨v₁, hv₁, hzc⟩ := hcase
    calc (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) ((C : Set (ι → A))) δ (u 0) (u 1) γ)).card
        = (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) ((C : Set (ι → A))) δ (u 0) ((u 1) - v₁) γ)).card :=
          mcaEvent_filter_card_direction_sub_codeword C δ hv₁
      _ ≤ Bnear := hlow (u 0) ((u 1) - v₁) hzc
      _ ≤ max Bfar Bnear := le_max_right _ _
  · push_neg at hcase
    have hfar : FarFromCode ((C : Set (ι → A))) δ (u 1) :=
      farFromCode_of_forall_coset_zeroSmall C a δ haF hcase
    have hzlt : (directionZeroSet (u 1)).card < a := by
      have h0 := hcase 0 (Submodule.zero_mem C)
      simpa [sub_zero] using h0
    calc (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) ((C : Set (ι → A))) δ (u 0) (u 1) γ)).card
        ≤ (lineBadScalars (F := F) ((C : Set (ι → A))) a (u 0) (u 1)).card :=
          Finset.card_le_card
            (mcaEvent_filter_subset_lineBadScalars ((C : Set (ι → A))) a δ haF (u 0) (u 1))
      _ ≤ (lineAppearingCodewords (F := F) ((C : Set (ι → A))) a (u 0) (u 1)).card
            * ((Fintype.card ι - (directionZeroSet (u 1)).card)
                / (a - (directionZeroSet (u 1)).card)) :=
          lineBadScalars_card_le_appearing_mul ((C : Set (ι → A))) a (u 0) (u 1) rfl hzlt
      _ ≤ L * ((Fintype.card ι - (directionZeroSet (u 1)).card)
                / (a - (directionZeroSet (u 1)).card)) :=
          Nat.mul_le_mul_right _ (hfarL (u 0) (u 1) hfar)
      _ ≤ Bfar := hfit _ hzlt
      _ ≤ max Bfar Bnear := le_max_left _ _

open Classical in
/-- **The `mcaDeltaStar` corollary of the weld (generic alphabet):** with the budget below
the target, `δ ≤ δ*(C, ε*)`. -/
theorem le_mcaDeltaStar_of_farLineListBudgeted [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞) {L Bfar Bnear : ℕ}
    (haC : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : FarLineListBudget (F := F) ((C : Set (ι → A))) a δ L)
    (hfit : ∀ z : ℕ, z < a → L * ((Fintype.card ι - z) / (a - z)) ≤ Bfar)
    (hlow : LargeZeroBadScalarBudget (F := F) ((C : Set (ι → A))) a δ Bnear)
    (hBudget : ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A)
      ((C : Set (ι → A))) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
    (F := F) (A := A) ((C : Set (ι → A))) εstar hδ1
    (le_trans (epsMCA_le_of_farLineListBudgeted C a δ haC haF hfarL hfit hlow) hBudget)

/-! ### §5. The folded headline — gap G4 closed as a conditional reduction -/

section Folded

/-- **The folded-RS MCA pin from the two counting budgets — gap G4 CLOSED (conditional
reduction, zero character sums).**  For the folded RS code `frsCode domain k s ω`: the
far-line list budget `L` + arithmetic fit + large-zero budget give
`ε_mca(FRS, δ) ≤ max(B_far, B_near)/q`.

The conclusion is *literally* the lane target `FrsMCAPin domain k s ω δ (max B_far B_near)`
of `_FoldedPinBrick1.lean` (definitional match — stated verbatim here because the two
frontier scratch files are import-independent).  The two hypotheses are the named open
inputs: `FarLineListBudget` at the folded alphabet is the re-aimed gap G3 (the GG25 §4/JLR
§5 curve-level list argument, expected `L = poly(1/η)` at `a/n = ρ_block + η`), and
`LargeZeroBadScalarBudget` is the folded analogue of the plain weld's `hlow`.  Nothing here
claims either. -/
theorem frs_epsMCA_le_of_farLineListBudgeted
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (a : ℕ) (δ : ℝ≥0) {L Bfar Bnear : ℕ}
    (haC : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : FarLineListBudget (F := F)
      ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) a δ L)
    (hfit : ∀ z : ℕ, z < a → L * ((Fintype.card ι - z) / (a - z)) ≤ Bfar)
    (hlow : LargeZeroBadScalarBudget (F := F)
      ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) a δ Bnear) :
    epsMCA (F := F)
      ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) δ
      ≤ ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_farLineListBudgeted
    (ReedSolomon.Folded.frsCode domain k s ω) a δ haC haF hfarL hfit hlow

end Folded

/-! ### §6. Guards — the far restriction is forced on the folded domain too -/

open Classical in
/-- **Aligned directions have maximal folded line lists.**  For a nonzero codeword direction
`u₁ ∈ C`, every scalar multiple `γ·u₁` appears on the line `{0 + γ·u₁}` with full agreement,
so the appearing-codeword count is `≥ q`.  The far restriction in `FarLineListBudget` is
therefore FORCED below `L = q` — and harmless, by `mcaEvent_false_of_direction_mem`. -/
theorem aligned_lineAppearingCodewords_card_ge [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (a : ℕ) (ha : a ≤ Fintype.card ι)
    {u₁ : ι → A} (hu₁ : u₁ ∈ C) (hne : u₁ ≠ 0) :
    Fintype.card F
      ≤ (lineAppearingCodewords (F := F) ((C : Set (ι → A))) a 0 u₁).card := by
  have hmaps : ∀ γ ∈ (Finset.univ : Finset F),
      γ • u₁ ∈ lineAppearingCodewords (F := F) ((C : Set (ι → A))) a 0 u₁ := by
    intro γ _
    simp only [lineAppearingCodewords, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Submodule.smul_mem C γ hu₁, γ, ?_⟩
    have hall : lineAgreeSet (γ • u₁) (fun i => (0 : ι → A) i + γ • u₁ i)
        = Finset.univ := by
      rw [lineAgreeSet]
      refine Finset.filter_true_of_mem ?_
      intro i _
      show (γ • u₁) i = (0 : ι → A) i + γ • u₁ i
      simp
    rw [hall, Finset.card_univ]
    exact ha
  have hinj : Set.InjOn (fun γ : F => γ • u₁)
      ((Finset.univ : Finset F) : Set F) := by
    intro γ _ γ' _ h
    obtain ⟨i, hi⟩ : ∃ i, u₁ i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (funext fun i => hall i)
    have hcoord : γ • u₁ i = γ' • u₁ i := congrFun h i
    have hz0 : (γ - γ') • u₁ i = 0 := by
      rw [sub_smul, hcoord, sub_self]
    rcases smul_eq_zero.mp hz0 with hc | hc
    · exact sub_eq_zero.mp hc
    · exact absurd hc hi
  calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
    _ ≤ (lineAppearingCodewords (F := F) ((C : Set (ι → A))) a 0 u₁).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The all-directions (unrestricted) list budget is unsatisfiable below `q`** for any
code with a nonzero codeword — the machine refuter forcing the far restriction, on any
alphabet (the folded analogue of `not_uniform_lineListBudgeted_of_lt_card`). -/
theorem not_uniform_lineAppearing_budget_of_lt_card [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (a : ℕ) (ha : a ≤ Fintype.card ι)
    (hex : ∃ u₁ ∈ C, u₁ ≠ (0 : ι → A)) {L : ℕ} (hL : L < Fintype.card F) :
    ¬ ∀ u₀ u₁ : ι → A,
      (lineAppearingCodewords (F := F) ((C : Set (ι → A))) a u₀ u₁).card ≤ L := by
  intro hall
  obtain ⟨u₁, hu₁, hne⟩ := hex
  exact absurd
    (le_trans (aligned_lineAppearingCodewords_card_ge C a ha hu₁ hne) (hall 0 u₁))
    (not_le.mpr hL)

/-! ### §7. Honest classification -/

/-- Honest classification: this brick closes gap G4 of the folded-pin map as a conditional
reduction (deployment-facing, FRI/STIR/WHIR); it does NOT close, advance, or bound the
plain-RS δ\* prize core (dossier §11.6 goal (B)) — `FoldingTransferNoGo` stands, and the
named budgets are OPEN. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end ProximityGap.FoldedPinWeld

-- Axiom audit: every theorem must report exactly `[propext, Classical.choice, Quot.sound]`
-- (no `sorryAx`).
#print axioms ProximityGap.FoldedPinWeld.no_direction_codeword_on_witness_of_mcaEvent
#print axioms ProximityGap.FoldedPinWeld.mcaEvent_false_of_direction_mem
#print axioms ProximityGap.FoldedPinWeld.mcaEvent_direction_add_codeword
#print axioms ProximityGap.FoldedPinWeld.mcaEvent_direction_sub_codeword_iff
#print axioms ProximityGap.FoldedPinWeld.mcaEvent_filter_card_direction_sub_codeword
#print axioms ProximityGap.FoldedPinWeld.mcaEvent_filter_subset_lineBadScalars
#print axioms ProximityGap.FoldedPinWeld.directionZeroSet_card_lt_of_farFromCode
#print axioms ProximityGap.FoldedPinWeld.farFromCode_of_forall_coset_zeroSmall
#print axioms ProximityGap.FoldedPinWeld.codeword_scalars_card_le
#print axioms ProximityGap.FoldedPinWeld.lineBadScalars_card_le_appearing_mul
#print axioms ProximityGap.FoldedPinWeld.epsMCA_le_of_farLineListBudgeted
#print axioms ProximityGap.FoldedPinWeld.le_mcaDeltaStar_of_farLineListBudgeted
#print axioms ProximityGap.FoldedPinWeld.frs_epsMCA_le_of_farLineListBudgeted
#print axioms ProximityGap.FoldedPinWeld.aligned_lineAppearingCodewords_card_ge
#print axioms ProximityGap.FoldedPinWeld.not_uniform_lineAppearing_budget_of_lt_card
#print axioms ProximityGap.FoldedPinWeld.not_prizeClosure
