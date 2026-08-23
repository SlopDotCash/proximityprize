/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The fit-family bound: the all-witness ownership floor (#371)

The subset-counting arc (`KKH26DimGeneralPin` → `OwnershipCensusSharpened` →
`KKH26DimGeneralSharpPin`/`KKH26CeilingMarch`) settled the per-scalar ownership constant at
the *minimal* witness (`= C(w−1,d+1)|_{w=d+3} = d+2`, two-sided).  At larger witnesses the
proven floors (the pair law, `C(w,d+1)/(d+2)` subset-equivalent) sat a factor `≈ d+2` below
the conjectured exact value `C(w−1, d+1)` — probe-true at every measured stack, attained by
the single-deviation configurations (`deviation_ownership_card`).  **This file proves the
floor at every witness size**, closing the scheme two-sided at every radius:

> **`ownership_floor`** — for `u` not explainable on a witness `S` of size `w`, at least
> `C(w−1, d+1)` of the `(d+2)`-subsets of `S` are non-explainable.

Equivalently (**`fit_family_card_le`**): the explainable `(d+2)`-subsets number at most
`C(w−1, d+2)`.

**The mechanism.**
1. *(blocks)* Explainable `(d+2)`-subsets organize into **maximal explainable blocks**:
   every explainable tuple extends to a maximal explainable superset
   (`exists_maxBlock`), and distinct maximal blocks meet in at most `d` points
   (`maxBlocks_inter_le` — two interpolants agreeing on `d+1` nodes are equal, and the
   glued explanation would one-point-extend a maximal block).  Blocks are proper subsets
   of `S` (else `S` itself is explainable).
2. *(the block-mass inequality, abstract)* **`block_mass_le`**: for ANY family `𝒜` of
   subsets of `S` with `|A| ≤ |S| − 1` and pairwise `|A ∩ B| ≤ k − 2` (`k ≥ 1`),
   `∑_{A ∈ 𝒜} C(|A|, k) ≤ C(|S| − 1, k)` — pure finite combinatorics (a `ToMathlib`
   candidate).  Double induction: at a point `x`, Pascal-split the through-`x` blocks;
   the *full punctured* family is a level-`k` system on `S ∖ {x}` while the *through-`x`
   punctured* family drops to level `k−1`; `C(w−2, k) + C(w−2, k−1) = C(w−1, k)` closes.

**Consequences.**
- **`badScalars_card_mul_choose_le`** — the radius-adaptive count: at witness floor `w₀`,
  `#bad · C(w₀−1, d+1) ≤ C(n, d+2)`.  At `w₀ = d+3` this is the landed band-edge law
  (`#bad·(d+2) ≤ C(n,d+2)`); at deeper radii it strictly dominates every landed bound
  (factor `≈ d+2` below the pair law uniformly) and matches the deviation-stack ceiling
  of `OwnershipCensusSharpened.lean` at EVERY witness size: per-witness subset counting
  is now exactly exhausted, two-sided, at every radius.
- **`epsMCA_le_adaptive`** — `ε_mca(δ) ≤ (C(n,d+2)/C(w₀−1,d+1))/q` at agreement
  floor `w₀`.

Probe: `scripts/probes/probe_fit_family_bound.py` — exhaustive over all words at six
`(p, w, d)` instances (`d ≤ 2`, `w ≤ 7`): zero violations of the bound and of the block
structure; the bound attained exactly by the single-deviation words in every case.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.FitFamilyBound

/-! ## Part A: the abstract block-mass inequality -/

open Classical in
/-- **The block-mass inequality.**  For any family `𝒜` of subsets of `S`, each of size at
most `|S| − 1`, pairwise intersecting in at most `k − 2` points (`k ≥ 1`):
`∑_{A ∈ 𝒜} C(|A|, k) ≤ C(|S| − 1, k)`. -/
theorem block_mass_le {ι : Type} [DecidableEq ι] :
    ∀ k : ℕ, 1 ≤ k → ∀ S : Finset ι, ∀ 𝒜 : Finset (Finset ι),
      (∀ A ∈ 𝒜, A ⊆ S) → (∀ A ∈ 𝒜, A.card + 1 ≤ S.card) →
      (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).card + 2 ≤ k) →
      (∑ A ∈ 𝒜, (A.card).choose k) ≤ (S.card - 1).choose k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ihk =>
    intro _ S
    induction S using Finset.strongInduction with
    | _ S ihS =>
      intro 𝒜 hsub hmax hpair
      -- prune the zero-contribution blocks: keep only those of size ≥ k + 1
      set 𝒜' := 𝒜.filter (fun A => k + 1 ≤ A.card) with h𝒜'def
      have hsum_eq : (∑ A ∈ 𝒜, (A.card).choose (k + 1))
          = ∑ A ∈ 𝒜', (A.card).choose (k + 1) := by
        rw [h𝒜'def]
        refine (Finset.sum_filter_of_ne ?_).symm
        intro A _ hne
        by_contra hlt
        exact hne (Nat.choose_eq_zero_of_lt (by omega))
      rw [hsum_eq]
      have hsub' : ∀ A ∈ 𝒜', A ⊆ S := fun A hA => hsub A (Finset.filter_subset _ _ hA)
      have hmax' : ∀ A ∈ 𝒜', A.card + 1 ≤ S.card :=
        fun A hA => hmax A (Finset.filter_subset _ _ hA)
      have hpair' : ∀ A ∈ 𝒜', ∀ B ∈ 𝒜', A ≠ B → (A ∩ B).card + 2 ≤ k + 1 :=
        fun A hA B hB => hpair A (Finset.filter_subset _ _ hA)
          B (Finset.filter_subset _ _ hB)
      have hmin' : ∀ A ∈ 𝒜', k + 1 ≤ A.card :=
        fun A hA => (Finset.mem_filter.mp hA).2
      rcases Finset.eq_empty_or_nonempty 𝒜' with hemp | hne
      · rw [hemp]
        simp
      -- the singleton case: k = 0 forces |𝒜'| ≤ 1
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨A, hA⟩ := hne
        have honly : 𝒜' = {A} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hA, fun B hB => ?_⟩
          by_contra hne'
          have := hpair' B hB A hA hne'
          omega
        rw [honly, Finset.sum_singleton, Nat.choose_one_right,
          Nat.choose_one_right]
        have := hmax' A hA
        omega
      -- the big-block case: some A has card = S.card − 1
      by_cases hbig : ∃ A ∈ 𝒜', S.card ≤ A.card + 1
      · obtain ⟨A, hA, hAbig⟩ := hbig
        have hAcard : A.card + 1 = S.card := le_antisymm (hmax' A hA) hAbig
        have honly : 𝒜' = {A} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hA, fun B hB => ?_⟩
          by_contra hne'
          have h1 : (B ∩ A).card + 2 ≤ k + 1 := hpair' B hB A hA hne'
          have h2 : B \ A ⊆ S \ A := Finset.sdiff_subset_sdiff (hsub' B hB) subset_rfl
          have h3 : (S \ A).card = S.card - A.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hsub' A hA)]
          have h4 : (B \ A).card ≤ 1 := by
            have := Finset.card_le_card h2
            omega
          have h5 : B.card ≤ (B ∩ A).card + (B \ A).card := by
            have := Finset.card_inter_add_card_sdiff B A
            omega
          have := hmin' B hB
          omega
        rw [honly, Finset.sum_singleton]
        have hAc : A.card = S.card - 1 := by omega
        rw [hAc]
      -- the deletion case: all blocks have card + 2 ≤ S.card
      · push_neg at hbig
        have hsmall : ∀ A ∈ 𝒜', A.card + 2 ≤ S.card := by
          intro A hA
          have := hbig A hA
          omega
        obtain ⟨A₀, hA₀⟩ := hne
        have hScard : 2 ≤ S.card := by
          have := hsmall A₀ hA₀
          omega
        obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
        have hinj : Set.InjOn (fun A : Finset ι => A.erase x) ↑𝒜' := by
          intro A hA B hB hAB
          by_contra hne'
          have hAB' : A.erase x = B.erase x := hAB
          have h1 : (A ∩ B).card + 2 ≤ k + 1 :=
            hpair' A (Finset.mem_coe.mp hA) B (Finset.mem_coe.mp hB) hne'
          have h2 : A.erase x ⊆ A ∩ B := by
            intro y hy
            have hyA : y ∈ A := Finset.mem_of_mem_erase hy
            have hyB : y ∈ B := by
              have hyB' : y ∈ B.erase x := by
                rw [← hAB']
                exact hy
              exact Finset.mem_of_mem_erase hyB'
            exact Finset.mem_inter.mpr ⟨hyA, hyB⟩
          have h3 : A.card - 1 ≤ (A ∩ B).card := by
            have hc1 := Finset.card_le_card h2
            have hc2 := Finset.pred_card_le_card_erase (a := x) (s := A)
            omega
          have := hmin' A (Finset.mem_coe.mp hA)
          omega
        -- Pascal split of the sum
        have hsplit : ∀ A ∈ 𝒜', (A.card).choose (k + 1)
            = ((A.erase x).card).choose (k + 1)
              + (if x ∈ A then ((A.erase x).card).choose k else 0) := by
          intro A hA
          by_cases hxA : x ∈ A
          · rw [if_pos hxA, Finset.card_erase_of_mem hxA]
            have hc : 1 ≤ A.card := by
              have := hmin' A hA
              omega
            have hc1 : A.card - 1 + 1 = A.card := by omega
            calc (A.card).choose (k + 1)
                = ((A.card - 1) + 1).choose (k + 1) := by rw [hc1]
            _ = (A.card - 1).choose k + (A.card - 1).choose (k + 1) :=
                Nat.choose_succ_succ _ _
            _ = (A.card - 1).choose (k + 1) + (A.card - 1).choose k :=
                Nat.add_comm _ _
          · rw [if_neg hxA, Finset.erase_eq_of_notMem hxA]
            omega
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
        -- first part: the full punctured family at level k + 1
        have hfirst : (∑ A ∈ 𝒜', ((A.erase x).card).choose (k + 1))
            ≤ ((S.erase x).card - 1).choose (k + 1) := by
          have himg : (∑ B ∈ 𝒜'.image (fun A : Finset ι => A.erase x),
                (B.card).choose (k + 1))
              = ∑ A ∈ 𝒜', ((A.erase x).card).choose (k + 1) :=
            Finset.sum_image (fun A hA B hB h => hinj hA hB h)
          rw [← himg]
          refine ihS (S.erase x) (Finset.erase_ssubset hx) _ ?_ ?_ ?_
          · intro B hB
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            intro y hy
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,
              hsub' A hA (Finset.mem_of_mem_erase hy)⟩
          · intro B hB
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            have h1 := hsmall A hA
            have h2 : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
            have h3 : (A.erase x).card ≤ A.card := Finset.card_erase_le
            omega
          · intro B hB B' hB' hne'
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hB'
            have hAne : A ≠ A' := fun h => hne' (by rw [h])
            have h1 := hpair' A hA A' hA' hAne
            have h2 : A.erase x ∩ A'.erase x ⊆ A ∩ A' := by
              intro y hy
              have hy' := Finset.mem_inter.mp hy
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_of_mem_erase hy'.1, Finset.mem_of_mem_erase hy'.2⟩
            have := Finset.card_le_card h2
            omega
        -- second part: the through-x punctured family at level k
        have hsecond : (∑ A ∈ 𝒜', if x ∈ A then ((A.erase x).card).choose k else 0)
            ≤ ((S.erase x).card - 1).choose k := by
          have hinjx : Set.InjOn (fun A : Finset ι => A.erase x)
              ↑(𝒜'.filter (fun A => x ∈ A)) :=
            hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
          have himg2 : (∑ B ∈ (𝒜'.filter (fun A => x ∈ A)).image
                (fun A : Finset ι => A.erase x), (B.card).choose k)
              = ∑ A ∈ 𝒜'.filter (fun A => x ∈ A), ((A.erase x).card).choose k :=
            Finset.sum_image (fun A hA B hB h => hinjx hA hB h)
          rw [← Finset.sum_filter, ← himg2]
          refine ihk hkpos (S.erase x) _ ?_ ?_ ?_
          · intro B hB
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            intro y hy
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,
              hsub' A (Finset.filter_subset _ _ hA) (Finset.mem_of_mem_erase hy)⟩
          · intro B hB
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            have h1 := hsmall A (Finset.filter_subset _ _ hA)
            have h2 : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
            have h3 : (A.erase x).card ≤ A.card := Finset.card_erase_le
            omega
          · intro B hB B' hB' hne'
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
            obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hB'
            have hAx : x ∈ A := (Finset.mem_filter.mp hA).2
            have hA'x : x ∈ A' := (Finset.mem_filter.mp hA').2
            have hAne : A ≠ A' := fun h => hne' (by rw [h])
            have h1 := hpair' A (Finset.filter_subset _ _ hA)
              A' (Finset.filter_subset _ _ hA') hAne
            have h2 : (A.erase x) ∩ (A'.erase x) = (A ∩ A').erase x := by
              ext y
              simp only [Finset.mem_inter, Finset.mem_erase]
              tauto
            have h3 : x ∈ A ∩ A' := Finset.mem_inter.mpr ⟨hAx, hA'x⟩
            have h4 : 0 < (A ∩ A').card := Finset.card_pos.mpr ⟨x, h3⟩
            rw [h2, Finset.card_erase_of_mem h3]
            omega
        have hpascal : ((S.erase x).card - 1).choose (k + 1)
            + ((S.erase x).card - 1).choose k = (S.card - 1).choose (k + 1) := by
          have h2 : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
          rw [h2]
          have e1 : S.card - 1 - 1 + 1 = S.card - 1 := by omega
          calc (S.card - 1 - 1).choose (k + 1) + (S.card - 1 - 1).choose k
              = (S.card - 1 - 1).choose k + (S.card - 1 - 1).choose (k + 1) :=
                Nat.add_comm _ _
          _ = (S.card - 1 - 1 + 1).choose (k + 1) := (Nat.choose_succ_succ _ _).symm
          _ = (S.card - 1).choose (k + 1) := by rw [e1]
        calc (∑ A ∈ 𝒜', ((A.erase x).card).choose (k + 1))
              + ∑ A ∈ 𝒜', (if x ∈ A then ((A.erase x).card).choose k else 0)
            ≤ ((S.erase x).card - 1).choose (k + 1)
              + ((S.erase x).card - 1).choose k := Nat.add_le_add hfirst hsecond
        _ = (S.card - 1).choose (k + 1) := hpascal

/-! ## Part B: maximal explainable blocks -/

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

open Classical in
/-- The maximal explainable blocks of a word inside a witness set: explainable subsets of
size at least `d + 2` admitting no one-point explainable extension within `S`. -/
noncomputable def maxBlocks (g : ZMod p) (d : ℕ) (u : Fin n → ZMod p)
    (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  S.powerset.filter (fun A => d + 2 ≤ A.card ∧ ExplainableOn g d u A ∧
    ∀ x ∈ S, x ∉ A → ¬ ExplainableOn g d u (insert x A))

open Classical in
theorem mem_maxBlocks {d : ℕ} {u : Fin n → ZMod p} {S A : Finset (Fin n)} :
    A ∈ maxBlocks g d u S ↔ A ⊆ S ∧ d + 2 ≤ A.card ∧ ExplainableOn g d u A ∧
      ∀ x ∈ S, x ∉ A → ¬ ExplainableOn g d u (insert x A) := by
  unfold maxBlocks
  rw [Finset.mem_filter, Finset.mem_powerset]

open Classical in
/-- Every explainable `(d+2)`-subset of `S` extends to a maximal explainable block. -/
theorem exists_maxBlock (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S T : Finset (Fin n)} (hTS : T ⊆ S) (hTcard : d + 2 ≤ T.card)
    (hTfit : ExplainableOn g d u T) :
    ∃ A ∈ maxBlocks g d u S, T ⊆ A := by
  classical
  set 𝒮 := S.powerset.filter (fun A => T ⊆ A ∧ ExplainableOn g d u A) with h𝒮
  have hT𝒮 : T ∈ 𝒮 := by
    rw [h𝒮]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS, subset_rfl, hTfit⟩
  obtain ⟨A, hA𝒮, hAmax⟩ := Finset.exists_max_image 𝒮 (fun A => A.card) ⟨T, hT𝒮⟩
  rw [h𝒮] at hA𝒮
  obtain ⟨hApow, hTA, hAfit⟩ := Finset.mem_filter.mp hA𝒮
  have hAS : A ⊆ S := Finset.mem_powerset.mp hApow
  refine ⟨A, mem_maxBlocks.mpr ⟨hAS,
    le_trans hTcard (Finset.card_le_card hTA), hAfit, ?_⟩, hTA⟩
  intro x hxS hxA hfit'
  have hmem : insert x A ∈ 𝒮 := by
    rw [h𝒮]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.insert_subset hxS hAS), subset_trans hTA (Finset.subset_insert x A), hfit'⟩
  have hcard := hAmax _ hmem
  rw [Finset.card_insert_of_notMem hxA] at hcard
  omega

open Classical in
/-- Distinct maximal blocks meet in at most `d` points: their interpolants would agree on
`d + 1` nodes, hence coincide, hence one-point-extend a maximal block. -/
theorem maxBlocks_inter_le (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S A B : Finset (Fin n)} (hA : A ∈ maxBlocks g d u S) (hB : B ∈ maxBlocks g d u S)
    (hne : A ≠ B) : (A ∩ B).card ≤ d := by
  by_contra hgt
  push_neg at hgt
  obtain ⟨hAS, hAcard, ⟨qA, hqAd, hqA⟩, hAmax⟩ := mem_maxBlocks.mp hA
  obtain ⟨hBS, hBcard, ⟨qB, hqBd, hqB⟩, hBmax⟩ := mem_maxBlocks.mp hB
  have hq : qA = qB := by
    refine explain_unique hg hqAd hqBd (S := A ∩ B) (by omega) (fun i hi => ?_)
    rw [← hqA i (Finset.mem_inter.mp hi).1, ← hqB i (Finset.mem_inter.mp hi).2]
  by_cases hBA : B ⊆ A
  · have hssub : B ⊂ A := lt_of_le_of_ne hBA (Ne.symm hne)
    obtain ⟨x, hxA, hxB⟩ := Finset.exists_of_ssubset hssub
    refine hBmax x (hAS hxA) hxB ⟨qB, hqBd, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hiB
    · rw [← hq]
      exact hqA _ hxA
    · exact hqB _ hiB
  · obtain ⟨x, hxB, hxA⟩ := Finset.not_subset.mp hBA
    refine hAmax x (hBS hxB) hxA ⟨qA, hqAd, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hiA
    · rw [hq]
      exact hqB _ hxB
    · exact hqA _ hiA

/-! ## The fit-family bound and the ownership floor -/

open Classical in
/-- **The fit-family bound**: a word not explainable on `S` has at most `C(|S|−1, d+2)`
explainable `(d+2)`-subsets. -/
theorem fit_family_card_le (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S : Finset (Fin n)} (hS : ¬ ExplainableOn g d u S) :
    ((Finset.powersetCard (d + 2) S).filter (fun T => ExplainableOn g d u T)).card
      ≤ (S.card - 1).choose (d + 2) := by
  classical
  have hcover : (Finset.powersetCard (d + 2) S).filter (fun T => ExplainableOn g d u T)
      ⊆ (maxBlocks g d u S).biUnion (fun A => Finset.powersetCard (d + 2) A) := by
    intro T hT
    obtain ⟨hTmem, hTfit⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    obtain ⟨A, hA, hTA⟩ := exists_maxBlock hg hTS (le_of_eq hTcard.symm) hTfit
    exact Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_powersetCard.mpr ⟨hTA, hTcard⟩⟩
  calc ((Finset.powersetCard (d + 2) S).filter
        (fun T => ExplainableOn g d u T)).card
      ≤ ((maxBlocks g d u S).biUnion (fun A => Finset.powersetCard (d + 2) A)).card :=
        Finset.card_le_card hcover
  _ ≤ ∑ A ∈ maxBlocks g d u S, (Finset.powersetCard (d + 2) A).card :=
        Finset.card_biUnion_le
  _ = ∑ A ∈ maxBlocks g d u S, (A.card).choose (d + 2) :=
        Finset.sum_congr rfl (fun A _ => Finset.card_powersetCard _ _)
  _ ≤ (S.card - 1).choose (d + 2) := by
        refine block_mass_le (d + 2) (by omega) S _ ?_ ?_ ?_
        · intro A hA
          exact (mem_maxBlocks.mp hA).1
        · intro A hA
          obtain ⟨hAS, _, hAfit, _⟩ := mem_maxBlocks.mp hA
          have hAne : A ≠ S := fun h => hS (h ▸ hAfit)
          have hss : A ⊂ S := lt_of_le_of_ne hAS hAne
          have := Finset.card_lt_card hss
          omega
        · intro A hA B hB hne
          have := maxBlocks_inter_le hg hA hB hne
          omega

open Classical in
/-- **The all-witness ownership floor**: a word not explainable on `S` has at least
`C(|S|−1, d+1)` non-explainable `(d+2)`-subsets — matching the single-deviation ceiling
exactly, at every witness size. -/
theorem ownership_floor (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S : Finset (Fin n)} (hS : ¬ ExplainableOn g d u S) :
    (S.card - 1).choose (d + 1)
      ≤ ((Finset.powersetCard (d + 2) S).filter
          (fun T => ¬ ExplainableOn g d u T)).card := by
  classical
  have hScard : d + 2 ≤ S.card := by
    by_contra hlt
    exact hS (explainableOn_of_card_le hg (by omega))
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.powersetCard (d + 2) S) (fun T => ExplainableOn g d u T)
  have htotal : (Finset.powersetCard (d + 2) S).card = (S.card).choose (d + 2) :=
    Finset.card_powersetCard _ _
  have hfit := fit_family_card_le hg hS
  have hpascal : (S.card).choose (d + 2)
      = (S.card - 1).choose (d + 1) + (S.card - 1).choose (d + 2) := by
    have hc1 : S.card - 1 + 1 = S.card := by omega
    calc (S.card).choose (d + 2)
        = ((S.card - 1) + 1).choose (d + 2) := by rw [hc1]
    _ = (S.card - 1).choose (d + 1) + (S.card - 1).choose (d + 2) :=
        Nat.choose_succ_succ _ _
  omega

/-! ## The radius-adaptive bad-scalar count -/

open Classical in
/-- **The radius-adaptive count** (the final form of per-witness subset counting): at
witness floor `w₀ ≥ d + 2`, every stack has `#bad · C(w₀−1, d+1) ≤ C(n, d+2)`.  At
`w₀ = d + 3` this is the band-edge law `#bad·(d+2) ≤ C(n, d+2)`; at deeper radii the
divisor grows binomially, matching the deviation-stack ceiling at every witness size. -/
theorem badScalars_card_mul_choose_le (hg : orderOf g = n) {d w₀ : ℕ}
    (hw₀ : d + 2 ≤ w₀) {δ : ℝ≥0}
    (hδ : ((w₀ : ℕ) : ℝ≥0) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card
        * (w₀ - 1).choose (d + 1)
      ≤ n.choose (d + 2) := by
  set B := Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ) with hBdef
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), w₀ ≤ S.card ∧
      ¬ ExplainableOn g d u₁ S ∧
      ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S := by
    intro γ hγ
    obtain ⟨S, hScard, hwC, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    have hcard : w₀ ≤ S.card := by
      have h2 : ((w₀ : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := le_trans hδ hScard
      exact_mod_cast h2
    have hnotexpl : ¬ ExplainableOn g d u₁ S := not_expl_dir_of_witness hwC hnojoint
    obtain ⟨w, ⟨qw, hqwd, hqw⟩, hagree⟩ := hwC
    refine ⟨S, hcard, hnotexpl, ⟨qw, hqwd, fun i hi => ?_⟩⟩
    show u₀ i + γ * u₁ i = qw.eval (g ^ (i : ℕ))
    have h1 := hagree i hi
    rw [smul_eq_mul] at h1
    rw [← h1]
    exact hqw i
  choose Sf hSfcard hSfnot hSfcomb using hwit
  set Φ : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    (Finset.powersetCard (d + 2) (Sf γ.1 γ.2)).filter
      (fun T => ¬ ExplainableOn g d u₁ T) with hΦdef
  have hmemΦ : ∀ (γ : {x // x ∈ B}) (T : Finset (Fin n)), T ∈ Φ γ →
      ¬ ExplainableOn g d u₁ T ∧
      ExplainableOn g d (fun i => u₀ i + γ.1 * u₁ i) T ∧ T.card = d + 2 := by
    intro γ T hT
    obtain ⟨hTmem, hTnot⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    exact ⟨hTnot, explainableOn_mono hTS (hSfcomb γ.1 γ.2), hTcard⟩
  have hP : ∀ γ : {x // x ∈ B}, (w₀ - 1).choose (d + 1) ≤ (Φ γ).card := by
    intro γ
    calc (w₀ - 1).choose (d + 1)
        ≤ ((Sf γ.1 γ.2).card - 1).choose (d + 1) :=
          Nat.choose_le_choose _ (by have := hSfcard γ.1 γ.2; omega)
    _ ≤ (Φ γ).card := ownership_floor hg (hSfnot γ.1 γ.2)
  have hdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (Φ γ₁) (Φ γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    obtain ⟨hnot1, hcomb1, _⟩ := hmemΦ γ₁ T hT1
    obtain ⟨_, hcomb2, _⟩ := hmemΦ γ₂ T hT2
    exact hne (Subtype.ext (scalar_eq_of_shared_tuple hg hnot1 hcomb1 hcomb2))
  have hbig : B.attach.card * (w₀ - 1).choose (d + 1) ≤ (B.attach.biUnion Φ).card := by
    rw [Finset.card_biUnion hdisj]
    calc B.attach.card * (w₀ - 1).choose (d + 1)
        = ∑ _γ ∈ B.attach, (w₀ - 1).choose (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP γ)
  have hsub : B.attach.biUnion Φ ⊆ Finset.powersetCard (d + 2) Finset.univ := by
    intro T hT
    obtain ⟨γ, _, hTΦ⟩ := Finset.mem_biUnion.mp hT
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (hmemΦ γ T hTΦ).2.2⟩
  calc B.card * (w₀ - 1).choose (d + 1)
      = B.attach.card * (w₀ - 1).choose (d + 1) := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Φ).card := hbig
  _ ≤ (Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).card :=
      Finset.card_le_card hsub
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The radius-adaptive `ε_mca` bound**: at agreement floor `w₀ ≥ d + 2`,
`ε_mca ≤ (C(n,d+2) / C(w₀−1,d+1)) / q`. -/
theorem epsMCA_le_adaptive (hg : orderOf g = n) {d w₀ : ℕ}
    (hw₀ : d + 2 ≤ w₀) {δ : ℝ≥0}
    (hδ : ((w₀ : ℕ) : ℝ≥0) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 2) / (w₀ - 1).choose (d + 1) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h4 := badScalars_card_mul_choose_le (g := g) hg hw₀ hδ (u 0) (u 1)
  have hpos : 0 < (w₀ - 1).choose (d + 1) :=
    Nat.choose_pos (by omega)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ n.choose (d + 2) / (w₀ - 1).choose (d + 1) :=
    (Nat.le_div_iff_mul_le hpos).mpr h4
  exact_mod_cast hle

end ArkLib.ProximityGap.FitFamilyBound

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.FitFamilyBound.block_mass_le
#print axioms ArkLib.ProximityGap.FitFamilyBound.fit_family_card_le
#print axioms ArkLib.ProximityGap.FitFamilyBound.ownership_floor
#print axioms ArkLib.ProximityGap.FitFamilyBound.badScalars_card_mul_choose_le
#print axioms ArkLib.ProximityGap.FitFamilyBound.epsMCA_le_adaptive
