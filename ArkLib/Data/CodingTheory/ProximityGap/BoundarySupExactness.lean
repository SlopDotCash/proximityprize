/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StripSupExactness

/-!
# Boundary sup-exactness: `ε_mca = n/q` EXACTLY on the band-3 boundary row at `3 ∣ n` (#357)

Closing-audit **item 4, boundary half**: the coset-clique boundary certificate
(`CosetCliqueBoundary.clique_eps_ge`, worth `n/q`) is **extremal** — no stack of any
distance-`≥ 3e−1` linear code carries more than `max(e, n)` bad scalars at band-`(e+1)`
radii.  At `e = 2` this is the `d = 5` band-3 boundary row, where with the certificate
it pins the **first exact boundary value** of the staircase: `ε_mca = n/q` whenever
`3 ∣ n`.

**The per-stack theorem** (`nearTop_badScalars_card_le`).  For any linear code with no
nonzero codeword of weight `≤ 3e−2` (distance `≥ 3e−1`, `2 ≤ e`), any radius with
`δ·n < e+1`, and any stack: the bad-scalar set has size `≤ max(e, n)` — via the sharper
invariant `≤ |⋃_γ E_γ|` (the domain points touched by the canonical error supports).

*Proof (the clump induction).*  Witnesses are first canonicalized to **maximal** form
(`E_γ` := the exact non-agreement set of the chosen line codeword; the no-joint clause
transports to the maximal witness by restriction).  A strong induction on sub-families
`S` of the bad set proves `|S| ≤ |⋃_{γ∈S} E_γ|`:
* if some `γ* ∈ S` has a partner with `|E_{γ*} ∪ E_{γ'}| ≤ 2e−1`, the pair pins an
  affine frame `U + γ·D`; the **dichotomy**: members `m` with `|E_m ∪ T| ≤ 3e−2` are
  *absorbed* (`w_m = U + γ_m·D` by distance forcing) and **escape-inject into `T`**
  through the no-joint clause, while the rest (*deviants*) have `E_m` **disjoint** from
  `T` (`|E_m ∩ T| ≤ |E_m| + |T| − (3e−1) ≤ 0` — the `d = 3e−1` coincidence), so the
  induction on the deviants telescopes off `T` exactly;
* otherwise `γ*`'s support is a fresh disjoint set of `≥ e` points and induction
  removes it.
Empty-support members collapse the whole family into a `≤ e`-point frame (`≤ e` bad
scalars total).

This matches the measured maximizer geometry exhaustively (`(8,4,17)`: two 3-frames
`{1,2,4} ⊔ {0,6,7}` + a singleton clump `{3,5}` = 7; `(9,5,19)`: 9; `(12,8,13)`: 12 —
`probe_boundary_sup_exactness.py`, pre-registered).

**Consequences.**
* `nearTop_epsMCA_le` : `ε_mca(C, δ) ≤ max(e, n)/|F|` for distance-`≥ 3e−1` codes — at
  `b ≥ 4` also the first nontrivial sup bound on the *second* strip row `d = 3b−4`
  (not sup-exact there; the conjectured value is `n/(b−1)`).
* `rs_boundary_epsMCA_eq` : for smooth `μ_n` with `3 ∣ n`, `6 < n`, `k = n − 4`
  (distance `d = 5`, the band-3 boundary row), every radius `2 ≤ δ·n < 3`:
  **`ε_mca(RS[F, μ_n, n−4], δ) = n/|F|`** — the boundary law's `n` is exact at `3 ∣ n`.

**Honest scope:** the `3 ∤ n` defect refinement (`≤ n−1`, probe-exact at `n = 8`)
needs the finer `3t + 2s ≤ n` clump accounting and is the named follow-up; the `b ≥ 4`
boundary rows `d ≤ 2b−2` and lower strip rows `2b ≤ d ≤ 3b−5` remain open.

## References

Issue #357 (closing-readiness audit item 4, boundary half); `StripSupExactness.lean`
(the sibling strip brick whose frame/escape machinery this extends),
`CosetCliqueBoundary.lean` (the matching `≥ n/q` certificate),
`UniversalStaircaseCollapse.lean` (`codeword_eq_of_eq_off`, `witness_compl_card_le`).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.BoundarySupExactness

open scoped NNReal ENNReal ProbabilityTheory
open Finset
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance
open ProximityGap.SpikeFloor
open ProximityGap.MCAThresholdLedger
open ProximityGap.StripSupExactness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The near-top per-stack bound via the clump induction.**  For any linear code with
no nonzero codeword of weight `≤ 3e−2` (distance `≥ 3e−1`, `2 ≤ e`), any radius with
`δ·n < e+1`, and any stack: at most `max(e, n)` bad scalars.  At `e = 2` this is the
band-3 boundary row (`d = 5`), where it is sharp (`clique_eps_ge`). -/
theorem nearTop_badScalars_card_le (e : ℕ) (he : 2 ≤ e) (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C (3 * e - 2)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((e + 1 : ℕ) : ℝ≥0)) (u₀ u₁ : ι → A) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ max e (Fintype.card ι) := by
  set B := Finset.univ.filter
    (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) with hB
  have hex : ∀ γ : F, γ ∈ B → ∃ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2
  choose! T hTsz hwEx hno using hex
  choose! w hwC hwAg using hwEx
  -- canonical (maximal) witnesses: E γ = the exact non-agreement set of w γ
  set E : F → Finset ι :=
    fun γ => Finset.univ.filter (fun i => w γ i ≠ u₀ i + γ • u₁ i) with hEdef
  have hagree : ∀ γ, ∀ i, i ∉ E γ → w γ i = u₀ i + γ • u₁ i := by
    intro γ i hi
    by_contra hne
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
  have hEsub : ∀ γ ∈ B, E γ ⊆ (T γ)ᶜ := by
    intro γ hγ i hi
    rw [Finset.mem_compl]
    intro hiT
    exact (Finset.mem_filter.mp hi).2 (hwAg γ hγ i hiT)
  have hEcard : ∀ γ ∈ B, (E γ).card ≤ e := by
    intro γ hγ
    have h1 := Finset.card_le_card (hEsub γ hγ)
    have h2 := witness_compl_card_le (j := e + 1) hδ (hTsz γ hγ)
    omega
  -- the no-joint clause transports to the maximal witness (restriction)
  have hnoE : ∀ γ ∈ B, ¬ pairJointAgreesOn (C : Set (ι → A)) ((E γ)ᶜ) u₀ u₁ := by
    intro γ hγ hjoint
    obtain ⟨v₀, hv₀, v₁, hv₁, hall⟩ := hjoint
    refine hno γ hγ ⟨v₀, hv₀, v₁, hv₁, fun i hi => hall i ?_⟩
    rw [Finset.mem_compl]
    intro hiE
    exact (Finset.mem_filter.mp hiE).2 (hwAg γ hγ i hi)
  -- ===== the frame package: absorbed members escape-inject into the frame =====
  have hframe : ∀ γ₁ ∈ B, ∀ γ₂ ∈ B, γ₁ ≠ γ₂ →
      ∀ S : Finset F, S ⊆ B →
      (S.filter (fun m => ((E m ∪ (E γ₁ ∪ E γ₂)).card ≤ 3 * e - 2))).card
        ≤ (E γ₁ ∪ E γ₂).card := by
    intro γ₁ hγ₁ γ₂ hγ₂ hne S hSB
    set T₃ := E γ₁ ∪ E γ₂ with hT₃
    set AS := S.filter (fun m => ((E m ∪ T₃).card ≤ 3 * e - 2)) with hAS
    have h12 : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    set D : ι → A := (γ₁ - γ₂)⁻¹ • (w γ₁ - w γ₂) with hD
    have hDC : D ∈ C := C.smul_mem _ (C.sub_mem (hwC γ₁ hγ₁) (hwC γ₂ hγ₂))
    set U : ι → A := w γ₁ - γ₁ • D with hU
    have hUC : U ∈ C := C.sub_mem (hwC γ₁ hγ₁) (C.smul_mem _ hDC)
    have hdiff : (γ₁ - γ₂) • D = w γ₁ - w γ₂ := by
      rw [hD, smul_smul, mul_inv_cancel₀ h12, one_smul]
    have hw₁ : w γ₁ = U + γ₁ • D := by rw [hU]; abel
    -- pointwise pinning off T₃
    have hpin : ∀ x, x ∉ T₃ → u₁ x = D x ∧ u₀ x = U x := by
      intro x hx
      rw [hT₃, Finset.mem_union] at hx
      push Not at hx
      have ha₁ := hagree γ₁ x hx.1
      have ha₂ := hagree γ₂ x hx.2
      have hsub : (γ₁ - γ₂) • u₁ x = (γ₁ - γ₂) • D x := by
        have hDx : (γ₁ - γ₂) • D x = w γ₁ x - w γ₂ x := by
          have := congrFun hdiff x
          simpa using this
        rw [hDx, ha₁, ha₂, sub_smul]
        abel
      have hu₁ : u₁ x = D x := by
        have := congrArg (fun z => (γ₁ - γ₂)⁻¹ • z) hsub
        simpa [smul_smul, inv_mul_cancel₀ h12] using this
      refine ⟨hu₁, ?_⟩
      have hux : u₀ x + γ₁ • u₁ x = U x + γ₁ • D x := by
        rw [← ha₁, hw₁]; simp
      rw [hu₁] at hux
      exact add_right_cancel hux
    -- absorption for the members of AS
    have habs : ∀ m ∈ AS, w m = U + m • D := by
      intro m hm
      obtain ⟨hmS, hm4⟩ := Finset.mem_filter.mp hm
      have hmB : m ∈ B := hSB hmS
      refine codeword_eq_of_eq_off C hC (hwC m hmB)
        (C.add_mem hUC (C.smul_mem m hDC)) (B := E m ∪ T₃) hm4 ?_
      intro x hx
      rw [Finset.mem_union] at hx
      push Not at hx
      obtain ⟨hu₁, hu₀⟩ := hpin x hx.2
      rw [hagree m x hx.1, hu₁, hu₀]
      simp
    -- escape: each absorbed member is tagged by a point of T₃, injectively
    have hesc : ∀ m : F, m ∈ AS → ∃ x : ι, x ∈ T₃ ∧ u₁ x ≠ D x ∧
        m • (u₁ x - D x) = U x - u₀ x := by
      intro m hm
      have hmB : m ∈ B := hSB (Finset.mem_filter.mp hm).1
      have hfail : ¬ ∀ i ∈ (E m)ᶜ, U i = u₀ i ∧ D i = u₁ i := by
        intro hall
        exact hnoE m hmB ⟨U, hUC, D, hDC, hall⟩
      push Not at hfail
      obtain ⟨x, hxc, hxne⟩ := hfail
      have hxE : x ∉ E m := Finset.mem_compl.mp hxc
      have hlin : u₀ x + m • u₁ x = U x + m • D x := by
        rw [← hagree m x hxE, habs m hm]; simp
      have hu₁ne : u₁ x ≠ D x := by
        intro h
        rw [h] at hlin
        exact hxne (add_right_cancel hlin).symm h.symm
      refine ⟨x, ?_, hu₁ne, ?_⟩
      · by_contra hxT
        exact hu₁ne (hpin x hxT).1
      · calc m • (u₁ x - D x)
            = (u₀ x + m • u₁ x) - u₀ x - m • D x := by rw [smul_sub]; abel
          _ = (U x + m • D x) - u₀ x - m • D x := by rw [hlin]
          _ = U x - u₀ x := by abel
    choose! ξ hξT hξne hξeq using hesc
    have hinj : Set.InjOn ξ AS := by
      intro a ha b hb hab
      by_contra hne'
      have hsubz : (a - b) • (u₁ (ξ a) - D (ξ a)) = 0 := by
        rw [sub_smul, hξeq a ha, hab, hξeq b hb]
        abel
      have hv : u₁ (ξ a) - D (ξ a) ≠ 0 := sub_ne_zero.mpr (hξne a ha)
      have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hne'
      have hz : u₁ (ξ a) - D (ξ a) = 0 := by
        have := congrArg (fun z => (a - b)⁻¹ • z) hsubz
        simpa [smul_smul, inv_mul_cancel₀ hab0] using this
      exact hv hz
    exact Finset.card_le_card_of_injOn ξ (fun m hm => hξT m hm) hinj
  -- ===== empty-support case: the whole family collapses into a ≤ e-point frame =====
  by_cases hempty : ∃ γ₀ ∈ B, E γ₀ = ∅
  · obtain ⟨γ₀, hγ₀, hE0⟩ := hempty
    by_cases hone : ∃ γ' ∈ B, γ' ≠ γ₀
    · obtain ⟨γ', hγ', hne'⟩ := hone
      have hkey := hframe γ₀ hγ₀ γ' hγ' (Ne.symm hne') B (Finset.Subset.refl B)
      have hT2 : (E γ₀ ∪ E γ').card ≤ e := by
        have hu := Finset.card_union_le (E γ₀) (E γ')
        have h0 : (E γ₀).card = 0 := by rw [hE0]; simp
        have h2 := hEcard γ' hγ'
        omega
      have hall : B.filter
          (fun m => ((E m ∪ (E γ₀ ∪ E γ')).card ≤ 3 * e - 2)) = B := by
        refine Finset.filter_true_of_mem ?_
        intro m hm
        have h1 := hEcard m hm
        have hu := Finset.card_union_le (E m) (E γ₀ ∪ E γ')
        omega
      rw [hall] at hkey
      exact le_trans hkey (le_trans hT2 (le_max_left _ _))
    · push Not at hone
      have hsub : B ⊆ {γ₀} := fun x hx => Finset.mem_singleton.mpr (hone x hx)
      have hle1 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle1
      exact le_trans hle1 (le_trans (by omega : 1 ≤ e) (le_max_left _ _))
  -- ===== main case: all supports nonempty — the clump induction =====
  · push Not at hempty
    have key : ∀ m : ℕ, ∀ S : Finset F, S ⊆ B → S.card ≤ m →
        S.card ≤ (S.biUnion E).card := by
      intro m
      induction m with
      | zero =>
        intro S _ hS0
        exact le_trans hS0 (Nat.zero_le _)
      | succ m ih =>
        intro S hSB hScard
        by_cases hS1 : S.card ≤ 1
        · rcases Finset.eq_empty_or_nonempty S with hS0 | ⟨γs, hγs⟩
          · rw [hS0]; simp
          · have hpos : 1 ≤ (E γs).card :=
              Finset.card_pos.mpr (hempty γs (hSB hγs))
            have hsub : E γs ⊆ S.biUnion E :=
              fun x hx => Finset.mem_biUnion.mpr ⟨γs, hγs, hx⟩
            have hbig := Finset.card_le_card hsub
            omega
        · push Not at hS1
          obtain ⟨γs, hγs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
          by_cases hpart : ∃ γ' ∈ S, γ' ≠ γs ∧ (E γs ∪ E γ').card ≤ 2 * e - 1
          · -- partnered: frame + dichotomy + telescoping
            obtain ⟨γ', hγ', hne', hsmall⟩ := hpart
            set T₃ := E γs ∪ E γ' with hT₃def
            set AS := S.filter
              (fun m' => ((E m' ∪ T₃).card ≤ 3 * e - 2)) with hASdef
            have hAcard : AS.card ≤ T₃.card :=
              hframe γs (hSB hγs) γ' (hSB hγ') (Ne.symm hne') S hSB
            have hγsA : γs ∈ AS := by
              refine Finset.mem_filter.mpr ⟨hγs, ?_⟩
              have hcup : E γs ∪ T₃ = T₃ := by
                rw [hT₃def, ← Finset.union_assoc, Finset.union_self]
              rw [hcup]
              omega
            set S' := S \ AS with hS'def
            have hS'sub : S' ⊆ B :=
              fun x hx => hSB (Finset.mem_sdiff.mp hx).1
            have hAsub : AS ⊆ S := Finset.filter_subset _ _
            have hS'card : S'.card = S.card - AS.card := by
              rw [hS'def, Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub]
            have hA1 : 1 ≤ AS.card := Finset.card_pos.mpr ⟨γs, hγsA⟩
            have hAle : AS.card ≤ S.card := Finset.card_le_card hAsub
            have hih := ih S' hS'sub (by omega)
            -- deviants avoid T₃
            have hdisj : ∀ x ∈ S'.biUnion E, x ∉ T₃ := by
              intro x hx hxT
              obtain ⟨m', hm'S', hxE⟩ := Finset.mem_biUnion.mp hx
              obtain ⟨hm'S, hm'A⟩ := Finset.mem_sdiff.mp hm'S'
              have hnotA : ¬((E m' ∪ T₃).card ≤ 3 * e - 2) := fun hc =>
                hm'A (Finset.mem_filter.mpr ⟨hm'S, hc⟩)
              apply hnotA
              have hint : 1 ≤ (E m' ∩ T₃).card :=
                Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxE, hxT⟩⟩
              have huni := Finset.card_union_add_card_inter (E m') T₃
              have h1 := hEcard m' (hSB hm'S)
              omega
            have hT₃sub : T₃ ⊆ S.biUnion E := by
              intro x hx
              rw [hT₃def, Finset.mem_union] at hx
              rcases hx with h | h
              · exact Finset.mem_biUnion.mpr ⟨γs, hγs, h⟩
              · exact Finset.mem_biUnion.mpr ⟨γ', hγ', h⟩
            have hsub' : S'.biUnion E ⊆ (S.biUnion E) \ T₃ := by
              intro x hx
              refine Finset.mem_sdiff.mpr ⟨?_, hdisj x hx⟩
              obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp hx
              exact Finset.mem_biUnion.mpr
                ⟨m', (Finset.mem_sdiff.mp hm').1, hxE⟩
            have hcount : (S'.biUnion E).card
                ≤ (S.biUnion E).card - T₃.card := by
              have h1 := Finset.card_le_card hsub'
              rwa [Finset.card_sdiff, Finset.inter_eq_left.mpr hT₃sub] at h1
            have hT₃big : T₃.card ≤ (S.biUnion E).card :=
              Finset.card_le_card hT₃sub
            omega
          · -- isolated: a fresh disjoint support of ≥ e points
            push Not at hpart
            set S' := S.erase γs with hS'def
            have hS'sub : S' ⊆ B :=
              fun x hx => hSB (Finset.mem_of_mem_erase hx)
            have hS'card : S'.card = S.card - 1 :=
              Finset.card_erase_of_mem hγs
            have hih := ih S' hS'sub (by omega)
            have hdisj : Disjoint (E γs) (S'.biUnion E) := by
              rw [Finset.disjoint_left]
              intro x hxγ hxU
              obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp hxU
              have hm'ne : m' ≠ γs := Finset.ne_of_mem_erase hm'
              have hbig := hpart m' (Finset.mem_of_mem_erase hm') hm'ne
              have hint : 1 ≤ (E γs ∩ E m').card :=
                Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxγ, hxE⟩⟩
              have huni := Finset.card_union_add_card_inter (E γs) (E m')
              have h1 := hEcard γs (hSB hγs)
              have h2 := hEcard m' (hS'sub hm')
              omega
            have hsize : e ≤ (E γs).card := by
              have hS'ne : S'.Nonempty := by
                rw [← Finset.card_pos]
                omega
              obtain ⟨γ', hγ'⟩ := hS'ne
              have hbig := hpart γ' (Finset.mem_of_mem_erase hγ')
                (Finset.ne_of_mem_erase hγ')
              have hu := Finset.card_union_le (E γs) (E γ')
              have h2 := hEcard γ' (hS'sub hγ')
              omega
            have hsub2 : (E γs) ∪ (S'.biUnion E) ⊆ S.biUnion E := by
              intro x hx
              rcases Finset.mem_union.mp hx with h | h
              · exact Finset.mem_biUnion.mpr ⟨γs, hγs, h⟩
              · obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp h
                exact Finset.mem_biUnion.mpr
                  ⟨m', Finset.mem_of_mem_erase hm', hxE⟩
            have hcard2 : (E γs).card + (S'.biUnion E).card
                ≤ (S.biUnion E).card := by
              rw [← Finset.card_union_of_disjoint hdisj]
              exact Finset.card_le_card hsub2
            omega
    have hfin := key B.card B (Finset.Subset.refl B) le_rfl
    have hcap : (B.biUnion E).card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    exact le_trans (le_trans hfin hcap) (le_max_right _ _)

open Classical in
/-- **The near-top collapse-to-`n`:** `ε_mca(C, δ) ≤ max(e, n)/|F|` at every radius
with `δ·n < e+1`, for every linear code of distance `≥ 3e−1`. -/
theorem nearTop_epsMCA_le (e : ℕ) (he : 2 ≤ e) (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C (3 * e - 2)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((e + 1 : ℕ) : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((max e (Fintype.card ι) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast nearTop_badScalars_card_le e he C hC hδ (u 0) (u 1)

variable {n k : ℕ}

open Classical in
/-- **THE EXACT BOUNDARY VALUE (band 3, `3 ∣ n`).**  For the smooth domain `μ_n = ⟨ζ⟩`
with `3 ∣ n`, `6 < n`, dimension `k = n − 4` (distance `d = 5`, the band-3 boundary
row), and every radius `2 ≤ δ·n < 3`:

  `ε_mca(RS[F, μ_n, n−4], δ) = n / |F|`.

The first exact boundary value of the staircase: the `≥` is the coset-clique
explosion (`clique_eps_ge` at `b = 3`), the `≤` is the clump induction
(`nearTop_epsMCA_le` at `e = 2`) — the boundary law's flat-`n` is exact at `3 ∣ n`
(closing-audit item 4, boundary half). -/
theorem rs_boundary_epsMCA_eq [Nonempty (Fin n)] (ζ : F) (hord : orderOf ζ = n)
    (h3n : 3 ∣ n) (hn6 : 6 < n) (hk : k = n - 4) {δ : ℝ≥0}
    (hδlo : (2 : ℝ≥0) ≤ δ * n) (hδhi : δ * n < 3) :
    epsMCA (F := F) (A := F) (evalCode (smoothDom ζ n) k : Set (Fin n → F)) δ
      = ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  have hnpos : 0 < n := by omega
  have hinj : Function.Injective (smoothDom ζ n) := smoothDom_injective ζ hord
  refine le_antisymm ?_ ?_
  · -- sup side: the clump induction at e = 2 (NoWeightLE 4 ⟸ k = n−4)
    have h := nearTop_epsMCA_le (F := F) 2 le_rfl (evalCode (smoothDom ζ n) k)
      (spikeFloor_noWeightLE_of_master
        (StripEdgeDeltaStar.evalCode_noWeightLE (m := 3 * 2 - 2) (smoothDom ζ n)
          hinj (by omega) (by omega)))
      (δ := δ) (by rw [Fintype.card_fin]; exact_mod_cast hδhi)
    have hmax : max 2 (Fintype.card (Fin n)) = n := by
      rw [Fintype.card_fin]
      omega
    rwa [hmax] at h
  · -- explosion side: `clique_eps_ge` at `b = 3`, transported up by monotonicity
    have hge := CosetCliqueBoundary.clique_eps_ge (b := 3) (k := k)
      (ζ := ζ) hord (by omega) h3n (by omega) (by omega) (by omega) (F := F)
    refine le_trans hge (epsMCA_mono _ ?_)
    -- ((3:ℕ):ℝ≥0 − 1)/n = 2/n ≤ δ
    have h31 : ((3 : ℕ) : ℝ≥0) - 1 = 2 := by
      rw [show ((3 : ℕ) : ℝ≥0) = 3 from by norm_num]
      exact tsub_eq_of_eq_add (by norm_num)
    rw [h31, div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
    exact hδlo

end ProximityGap.BoundarySupExactness

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BoundarySupExactness.nearTop_badScalars_card_le
#print axioms ProximityGap.BoundarySupExactness.nearTop_epsMCA_le
#print axioms ProximityGap.BoundarySupExactness.rs_boundary_epsMCA_eq
