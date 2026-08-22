/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# Shared-base Johnson packing for the P1 pencil layers

Successor to `_P1RateQuarterCrossPencilVoteReuse.lean`.  Every common-base pencil's aligned
region lies inside the same base-codeword agreement set `B`.  Packing inside `B`, rather than
the ambient `N` coordinates, strengthens Johnson and feeds back into the shared-base rider cap
`riders ≤ N-|B|+1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure

open ConstantWeightPlotkinBound

/-- **Johnson inside a finite carrier.**  If every member of a finite family lies in `B`,
has size at least `a`, and pair intersections at most `lambda`, then the exact-diagonal
Johnson inequality uses `|B|` as its universe size. -/
theorem johnson_inside_finset
    {I U : Type*} [Fintype I] [DecidableEq I] [DecidableEq U]
    (B : Finset U) (A : I → Finset U) (a lambda : ℕ)
    (hsub : ∀ i, A i ⊆ B)
    (hsize : ∀ i, a ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ lambda) :
    Fintype.card I * a ^ 2 ≤
      B.card * (a + (Fintype.card I - 1) * lambda) := by
  classical
  let T : I → Finset U := fun i => Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hTsub : ∀ i, T i ⊆ A i := fun i =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hsize i))).1
  have hTcard : ∀ i, (T i).card = a := fun i =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hsize i))).2
  have hTB : ∀ i, T i ⊆ B := fun i => (hTsub i).trans (hsub i)
  let emb (i : I) : {x // x ∈ T i} ↪ {x // x ∈ B} :=
    ⟨fun x => ⟨x.1, hTB i x.2⟩,
      fun x y h => Subtype.ext (congrArg (fun z : {x // x ∈ B} => z.1) h)⟩
  let L : I → Finset {x // x ∈ B} := fun i => (T i).attach.map (emb i)
  have hmemL : ∀ i (x : {x // x ∈ B}), x ∈ L i ↔ x.1 ∈ T i := by
    intro i x
    change x ∈ (T i).attach.map (emb i) ↔ x.1 ∈ T i
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, _hz, hzx⟩ := hx
      have hval : z.1 = x.1 := congrArg Subtype.val hzx
      simpa [hval] using z.2
    · intro hx
      rw [Finset.mem_map]
      refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
      exact Subtype.ext rfl
  have hLcard : ∀ i, (L i).card = a := by
    intro i
    change ((T i).attach.map (emb i)).card = a
    rw [Finset.card_map, Finset.card_attach, hTcard]
  have hLpair : ∀ i j, i ≠ j → (L i ∩ L j).card ≤ lambda := by
    intro i j hij
    calc
      (L i ∩ L j).card ≤ (T i ∩ T j).card := by
        refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
        · intro x hx
          change x ∈ L i ∩ L j at hx
          change x.1 ∈ T i ∩ T j
          rw [Finset.mem_inter] at hx ⊢
          exact ⟨(hmemL i x).mp hx.1, (hmemL j x).mp hx.2⟩
        · intro x _hx y _hy hxy
          exact Subtype.ext hxy
      _ ≤ (A i ∩ A j).card :=
        Finset.card_le_card (Finset.inter_subset_inter (hTsub i) (hTsub j))
      _ ≤ lambda := hpair i j hij
  simpa only [Fintype.card_coe] using
    constantWeight_johnson L a lambda hLcard hLpair

/-! ## Literal P1 heavy-layer arithmetic -/

abbrev N : ℕ := 2 ^ 30
abbrev k : ℕ := 2 ^ 28
abbrev tenRiderAlignment : ℕ := 539356427
abbrev predecessorThreshold : ℕ := 592794966
abbrev twoRiderAlignment : ℕ := 111848108
abbrev threeRiderAlignment : ℕ := 352321537
abbrev fourRiderAlignment : ℕ := 432479347

/-- Upper endpoint of the band where a shared non-base rider uniquely determines a common-base
pencil direction by complement packing. -/
abbrev sharedRiderUniqueAlignment : ℕ := 218103809

/-- At literal P1 scale, if the base carrier has threshold size or larger and an aligned core is
at most `218103809`, two vote sets for one non-base rider, each of the forced size `T-A`, overlap
on at least `k` coordinates. -/
theorem lowAlignment_sharedRider_packing
    {A B : ℕ} (hA : A ≤ sharedRiderUniqueAlignment)
    (hBT : predecessorThreshold ≤ B) (hBN : B ≤ N) :
    (N - B) + k ≤ 2 * (predecessorThreshold - A) := by
  norm_num [sharedRiderUniqueAlignment, predecessorThreshold, N, k] at hA hBT hBN ⊢
  omega

/-- The uniqueness band contains the two-rider floor but ends strictly before the three-rider
floor. -/
theorem sharedRiderUnique_band_separates_two_and_three :
    twoRiderAlignment ≤ sharedRiderUniqueAlignment ∧
      sharedRiderUniqueAlignment < threeRiderAlignment := by
  norm_num [twoRiderAlignment, sharedRiderUniqueAlignment, threeRiderAlignment]

/-- A convenient endpoint beyond the injective band where complement Johnson still gives a
small rider multiplicity. -/
abbrev sharedRiderJohnsonAlignment : ℕ := 230000000
abbrev sharedRiderJohnsonVoteFloor : ℕ := 362794966

theorem sharedRiderJohnsonVoteFloor_eq :
    sharedRiderJohnsonVoteFloor = predecessorThreshold - sharedRiderJohnsonAlignment := by
  norm_num [sharedRiderJohnsonVoteFloor, predecessorThreshold, sharedRiderJohnsonAlignment]

/-- Exact P1 arithmetic: at vote size `362794966`, Johnson packing in a carrier of size at most
`N-T` permits at most eighteen pencils through one non-base rider. -/
theorem sharedRider_230m_arithmetic
    {M C : ℕ} (hC : C ≤ N - predecessorThreshold)
    (hJ : M * sharedRiderJohnsonVoteFloor ^ 2 ≤
      C * (sharedRiderJohnsonVoteFloor + (M - 1) * (k - 1))) :
    M ≤ 18 := by
  have hJ' : M * sharedRiderJohnsonVoteFloor ^ 2 ≤
      (N - predecessorThreshold) *
        (sharedRiderJohnsonVoteFloor + (M - 1) * (k - 1)) :=
    hJ.trans (Nat.mul_le_mul_right _ hC)
  norm_num [sharedRiderJohnsonVoteFloor, N, predecessorThreshold, k] at hJ' ⊢
  omega

/-- **Complement-Johnson rider multiplicity cap.**  A family of vote sets for one fixed
non-base rider, all lying outside a threshold-size base carrier and having the P1 forced size
at alignment at most `230000000`, contains at most eighteen pencils. -/
theorem sharedRider_family_card_le_18
    {PIdx U : Type*} [DecidableEq PIdx] [DecidableEq U]
    (Fam : Finset PIdx) (C : Finset U) (V : PIdx → Finset U)
    (hC : C.card ≤ N - predecessorThreshold)
    (hsub : ∀ π ∈ Fam, V π ⊆ C)
    (hsize : ∀ π ∈ Fam, sharedRiderJohnsonVoteFloor ≤ (V π).card)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' →
      (V π ∩ V π').card ≤ k - 1) :
    Fam.card ≤ 18 := by
  classical
  have hJ := johnson_inside_finset C (fun π : ↥Fam => V π.1)
    sharedRiderJohnsonVoteFloor (k - 1)
    (fun π => hsub π.1 π.2)
    (fun π => hsize π.1 π.2)
    (fun π π' hne => hpair π.1 π.2 π'.1 π'.2 (fun heq => hne (Subtype.ext heq)))
  apply sharedRider_230m_arithmetic hC
  simpa only [Fintype.card_coe] using hJ

/-- Exact endpoint of the positive complement-Johnson denominator at the smallest possible
base carrier.  It dies more than 118 million coordinates before the three-rider floor. -/
theorem sharedRider_complementJohnson_exact_crossover :
    (N - predecessorThreshold) * (k - 1) <
      (predecessorThreshold - 233485644) ^ 2 ∧
    (predecessorThreshold - 233485645) ^ 2 ≤
      (N - predecessorThreshold) * (k - 1) := by
  norm_num [N, predecessorThreshold, k]

/-! ## Saturated three-rider binary-label barrier -/

/-- For two balanced binary color classes inside the same carrier, total matching agreement is
twice the intersection of the chosen color classes. -/
theorem balanced_binary_matching_card_eq_two_inter
    {U : Type*} [DecidableEq U] (C S T : Finset U)
    (hSC : S ⊆ C) (hTC : T ⊆ C)
    (hST : S.card = T.card) (hhalf : 2 * S.card = C.card) :
    ((S ∩ T) ∪ ((C \ S) ∩ (C \ T))).card = 2 * (S ∩ T).card := by
  have hcomp : (C \ S) ∩ (C \ T) = C \ (S ∪ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hdisj : Disjoint (S ∩ T) ((C \ S) ∩ (C \ T)) := by
    rw [Finset.disjoint_left]
    intro x hxI hxC
    obtain ⟨hxS, _hxT⟩ := Finset.mem_inter.mp hxI
    obtain ⟨hxCS, _hxCT⟩ := Finset.mem_inter.mp hxC
    exact (Finset.mem_sdiff.mp hxCS).2 hxS
  rw [Finset.card_union_of_disjoint hdisj, hcomp,
    Finset.card_sdiff_of_subset (Finset.union_subset hSC hTC)]
  have hinc := Finset.card_union_add_card_inter S T
  omega

/-- At P1 parameters, the combined matching cap `k-1` therefore limits either balanced color
intersection to `134217727 = k/2-1`. -/
theorem balancedBinary_inter_card_le_134217727
    {matching inter : ℕ} (hmatching : matching = 2 * inter)
    (hcap : matching ≤ k - 1) : inter ≤ 134217727 := by
  norm_num [k] at hcap ⊢
  omega

/-- The balanced intersection cap rounds the odd raw matching-distance floor up by one. -/
theorem balancedBinary_sharp_distance_value :
    2 * (240473429 - 134217727) = 212511404 := by norm_num

/-- If two non-base vote sets partition the smallest carrier complement, the two-label matching
cap translates to this minimum binary Hamming distance. -/
abbrev saturatedBinaryDistance : ℕ := 212511403

theorem saturatedBinaryDistance_eq :
    saturatedBinaryDistance = (N - predecessorThreshold) - (k - 1) := by
  norm_num [saturatedBinaryDistance, N, predecessorThreshold, k]

/-- The induced binary distance is below the Plotkin crossover: twice the distance does not
exceed the binary block length.  Thus ordinary binary Plotkin cannot bound the number of
saturated three-rider labelings. -/
theorem saturatedBinaryDistance_below_plotkin :
    2 * saturatedBinaryDistance ≤ N - predecessorThreshold := by
  norm_num [saturatedBinaryDistance, N, predecessorThreshold]

/-- Exact amount by which the saturated binary reduction misses the Plotkin crossover. -/
theorem saturatedBinaryPlotkin_slack :
    (N - predecessorThreshold) - 2 * saturatedBinaryDistance = 55924052 := by
  norm_num [saturatedBinaryDistance, N, predecessorThreshold]

/-- Even after halving the matching budget using balance, constant-weight Johnson remains below
its positive-denominator crossover. -/
theorem balancedBinary_constantWeightJohnson_denominator_zero :
    240473429 ^ 2 - 480946858 * 134217727 = 0 := by
  norm_num

/-! ## Two-rider aligned-plus-vote matching -/

/-- Inclusion--exclusion across complementary carriers: two core sets of size at least `a`
inside `B` and two vote sets of size at least `s` inside `C` have combined matching overlap at
least `2(a+s)-N` whenever `|B|+|C|=N`. -/
theorem twoCarrier_matching_floor
    {U : Type*} [DecidableEq U]
    (B C A1 A2 V1 V2 : Finset U) (a s N0 : ℕ)
    (hBC : B.card + C.card = N0)
    (hA1sub : A1 ⊆ B) (hA2sub : A2 ⊆ B)
    (hV1sub : V1 ⊆ C) (hV2sub : V2 ⊆ C)
    (hA1 : a ≤ A1.card) (hA2 : a ≤ A2.card)
    (hV1 : s ≤ V1.card) (hV2 : s ≤ V2.card) :
    2 * (a + s) - N0 ≤ (A1 ∩ A2).card + (V1 ∩ V2).card := by
  have hAU : (A1 ∪ A2).card ≤ B.card :=
    Finset.card_le_card (Finset.union_subset hA1sub hA2sub)
  have hVU : (V1 ∪ V2).card ≤ C.card :=
    Finset.card_le_card (Finset.union_subset hV1sub hV2sub)
  have hAinc := Finset.card_union_add_card_inter A1 A2
  have hVinc := Finset.card_union_add_card_inter V1 V2
  omega

/-- For a two-rider pencil `a+s=T`, the carrier-wise matching floor is the constant
`2T-N=111848108`, independent of the alignment split. -/
theorem twoRider_matching_floor_value :
    2 * predecessorThreshold - N = 111848108 := by
  norm_num [predecessorThreshold, N]

/-- The combined aligned-plus-vote floor remains below the RS root budget by `156587347`, so
plain inclusion--exclusion still does not force direction uniqueness in the upper band. -/
theorem twoRider_matching_floor_rootBudget_slack :
    (k - 1) - (2 * predecessorThreshold - N) = 156587347 := by
  norm_num [k, predecessorThreshold, N]

/-- Exact family-level Johnson arithmetic for combined aligned-plus-vote sets: six such sets are
impossible, so one charged non-base rider is reused by at most five pencils. -/
theorem combinedTwoRider_johnson_arithmetic
    {M : ℕ}
    (hJ : M * predecessorThreshold ^ 2 ≤
      N * (predecessorThreshold + (M - 1) * (k - 1))) :
    M ≤ 5 := by
  norm_num [predecessorThreshold, N, k] at hJ ⊢
  omega

/-- **Combined-set multiplicity cap.**  Any family of coordinate sets of size at least `T` with
pair intersections at most `k-1` has at most five members at literal P1 scale.  Applied to
`aligned core ∪ fixed-rider vote set`, this is the charged-rider reuse bound. -/
theorem combinedTwoRider_family_card_le_five
    {PIdx U : Type*} [DecidableEq PIdx] [Fintype U] [DecidableEq U]
    (Fam : Finset PIdx) (W : PIdx → Finset U)
    (hU : Fintype.card U = N)
    (hsize : ∀ π ∈ Fam, predecessorThreshold ≤ (W π).card)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' →
      (W π ∩ W π').card ≤ k - 1) :
    Fam.card ≤ 5 := by
  classical
  have hJ := johnson_inside_finset (Finset.univ : Finset U)
    (fun π : ↥Fam => W π.1) predecessorThreshold (k - 1)
    (fun _π => Finset.subset_univ _)
    (fun π => hsize π.1 π.2)
    (fun π π' hne => hpair π.1 π.2 π'.1 π'.2 (fun heq => hne (Subtype.ext heq)))
  apply combinedTwoRider_johnson_arithmetic
  simpa only [Fintype.card_coe, Finset.card_univ, hU] using hJ

/-- **Disjoint erased-fiber summation.**  Pairwise-disjoint non-base rider fibers contained in a
global bad-scalar set consume at most that set with the base scalar erased. -/
theorem disjointErasedFibers_sum_le_global
    {PIdx F0 : Type*} [DecidableEq PIdx] [DecidableEq F0]
    (Fam : Finset PIdx) (R : PIdx → Finset F0) (G : Finset F0) (gamma0 : F0)
    (hsub : ∀ π ∈ Fam, R π ⊆ G.erase gamma0)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' → Disjoint (R π) (R π')) :
    ∑ π ∈ Fam, (R π).card ≤ (G.erase gamma0).card := by
  classical
  rw [← Finset.card_biUnion (fun π hπ π' hπ' hne => hpair π hπ π' hπ' hne)]
  exact Finset.card_le_card (by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨π, hπ, hxR⟩ := hx
    exact hsub π hπ hxR)

/-- With the base scalar present globally, the disjoint erased fibers use at most `|G|-1` slots. -/
theorem disjointErasedFibers_sum_le_global_sub_one
    {PIdx F0 : Type*} [DecidableEq PIdx] [DecidableEq F0]
    (Fam : Finset PIdx) (R : PIdx → Finset F0) (G : Finset F0) (gamma0 : F0)
    (hgamma0 : gamma0 ∈ G)
    (hsub : ∀ π ∈ Fam, R π ⊆ G.erase gamma0)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' → Disjoint (R π) (R π')) :
    ∑ π ∈ Fam, (R π).card ≤ G.card - 1 := by
  simpa [Finset.card_erase_of_mem hgamma0] using
    disjointErasedFibers_sum_le_global Fam R G gamma0 hsub hpair

/-! ## Exact base-rider inclusion crossover -/

/-- If a threshold-size base carrier can accommodate three non-base vote sets of forced size
`T-A`, then the alignment has already reached the four-rider floor. -/
theorem threeNonbase_capacity_forces_fourRiderAlignment
    {A B : ℕ} (hBT : predecessorThreshold ≤ B) (hBN : B ≤ N)
    (hcap : 3 * (predecessorThreshold - A) ≤ N - B) :
    fourRiderAlignment ≤ A := by
  norm_num [predecessorThreshold, fourRiderAlignment, N] at hBT hBN hcap ⊢
  omega

/-- Sharpness of the preceding crossover: at one coordinate below the four-rider floor three
vote sets overflow the smallest carrier complement, while at the floor they fit arithmetically. -/
theorem threeNonbase_capacity_exact_crossover :
    N - predecessorThreshold <
        3 * (predecessorThreshold - (fourRiderAlignment - 1)) ∧
      3 * (predecessorThreshold - fourRiderAlignment) ≤
        N - predecessorThreshold := by
  norm_num [N, predecessorThreshold, fourRiderAlignment]

/-- Exact two-non-base-rider crossover: they overflow a threshold carrier complement one
coordinate below the three-rider floor and first fit at that floor. -/
theorem twoNonbase_capacity_exact_crossover :
    N - predecessorThreshold <
        2 * (predecessorThreshold - (threeRiderAlignment - 1)) ∧
      2 * (predecessorThreshold - threeRiderAlignment) ≤
        N - predecessorThreshold := by
  norm_num [N, predecessorThreshold, threeRiderAlignment]

/-- Exact inside-carrier Johnson crossover at the smallest possible base agreement carrier:
two- and three-rider pencils remain below the square barrier, while four riders cross it. -/
theorem minimalCarrier_lowRider_johnson_boundary :
    twoRiderAlignment ^ 2 ≤ predecessorThreshold * (k - 1) ∧
    threeRiderAlignment ^ 2 ≤ predecessorThreshold * (k - 1) ∧
    predecessorThreshold * (k - 1) < fourRiderAlignment ^ 2 := by
  constructor
  · norm_num [twoRiderAlignment, predecessorThreshold, k]
  · constructor <;> norm_num [threeRiderAlignment, fourRiderAlignment,
      predecessorThreshold, k]

/-- Thus no positive Johnson denominator exists for the three-rider stratum even in the most
favorable carrier `|B|=T`. -/
theorem threeRider_insideJohnson_gap_zero :
    threeRiderAlignment ^ 2 - predecessorThreshold * (k - 1) = 0 := by
  have h := minimalCarrier_lowRider_johnson_boundary.2.1
  omega

/-- **Shared-base heavy-layer arithmetic closure.**  For `2 ≤ M ≤ 108`, if `M` aligned
cores of size `tenRiderAlignment` satisfy the inside-`B` exact-diagonal Johnson inequality,
then `M` fibers each capped by `N-|B|` partner slots fit below the prize budget. -/
theorem heavy_sharedBase_arithmetic
    {M B : ℕ} (hM2 : 2 ≤ M) (hM108 : M ≤ 108) (_hBN : B ≤ N)
    (hJ : M * tenRiderAlignment ^ 2 ≤
      B * (tenRiderAlignment + (M - 1) * (k - 1))) :
    1 + M * (N - B) ≤ N := by
  interval_cases M <;> norm_num [N, k, tenRiderAlignment] at hJ ⊢ <;> omega

/-- Sharp uniform envelope over `2 ≤ M ≤ 108`; the maximum occurs at an interior value
(`M=10` in the exact probe). -/
theorem heavy_sharedBase_arithmetic_sharp
    {M B : ℕ} (hM2 : 2 ≤ M) (hM108 : M ≤ 108) (_hBN : B ≤ N)
    (hJ : M * tenRiderAlignment ^ 2 ≤
      B * (tenRiderAlignment + (M - 1) * (k - 1))) :
    1 + M * (N - B) ≤ 893823171 := by
  interval_cases M <;> norm_num [N, k, tenRiderAlignment] at hJ ⊢ <;> omega

theorem heavy_sharedBase_slack_eq : N - 893823171 = 179918653 := by
  norm_num [N]

/-- The sharp heavy envelope can absorb `22,489,831` light pencils carrying eight partner
slots each; one more such light pencil crosses `N`. -/
theorem heavy_plus_light_absorption_threshold :
    893823171 + 8 * 22489831 = 1073741819 ∧
    1073741819 ≤ N ∧ N < 893823171 + 8 * 22489832 := by
  constructor
  · norm_num
  · constructor <;> norm_num [N]

/-- Mixed-layer arithmetic consumer. -/
theorem heavyEnvelope_add_lightSlots_le_N
    {heavySlots lightPencils : ℕ}
    (hheavy : heavySlots ≤ 893823171)
    (hlight : lightPencils ≤ 22489831) :
    heavySlots + 8 * lightPencils ≤ N := by
  have h := heavy_plus_light_absorption_threshold
  omega

/-- The endpoint values of the feedback bound: its worst slot count occurs internally, not
at `M=2` or `M=108`; both endpoints are comfortably below `N`. -/
theorem heavy_sharedBase_endpoint_checks :
    706987095 ≤ N ∧ 7386337 ≤ N := by
  constructor <;> norm_num [N]

/-- **Generic heavy-family slot closure.**  A finite family of at most `108` heavy cores
inside one carrier `B`, with pair intersections at most `k-1` and per-fiber partner cap
`N-|B|`, contributes at most `N` scalar slots after its shared base is counted once. -/
theorem heavy_family_slots_le_N
    {κ U : Type*} [DecidableEq κ] [DecidableEq U]
    (B : Finset U) (Fam : Finset κ) (A : κ → Finset U) (riders : κ → ℕ)
    (hBN : B.card ≤ N)
    (hsub : ∀ π ∈ Fam, A π ⊆ B)
    (hsize : ∀ π ∈ Fam, tenRiderAlignment ≤ (A π).card)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' →
      (A π ∩ A π').card ≤ k - 1)
    (h108 : Fam.card ≤ 108)
    (hriders : ∀ π ∈ Fam, riders π ≤ N - B.card + 1) :
    1 + ∑ π ∈ Fam, (riders π - 1) ≤ N := by
  classical
  have hsum : (∑ π ∈ Fam, (riders π - 1)) ≤ Fam.card * (N - B.card) := by
    calc
      (∑ π ∈ Fam, (riders π - 1)) ≤ ∑ _π ∈ Fam, (N - B.card) := by
        exact Finset.sum_le_sum fun π hπ => by
          have := hriders π hπ
          omega
      _ = Fam.card * (N - B.card) := by simp
  by_cases hsmall : Fam.card ≤ 1
  · by_cases hzero : Fam.card = 0
    · have hempty : Fam = ∅ := Finset.card_eq_zero.mp hzero
      simp [hempty, N]
    · have hnonempty : Fam.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      obtain ⟨π, hπ⟩ := hnonempty
      have hBlarge : tenRiderAlignment ≤ B.card :=
        (hsize π hπ).trans (Finset.card_le_card (hsub π hπ))
      have hten : 1 ≤ tenRiderAlignment := by norm_num [tenRiderAlignment]
      have hNpos : 1 ≤ N := by norm_num [N]
      have hcard1 : Fam.card = 1 := by omega
      rw [hcard1, one_mul] at hsum
      omega
  · have hM2 : 2 ≤ Fam.card := by omega
    have hJ : Fam.card * tenRiderAlignment ^ 2 ≤
        B.card * (tenRiderAlignment + (Fam.card - 1) * (k - 1)) := by
      have hinside := johnson_inside_finset B (fun π : ↥Fam => A π.1)
        tenRiderAlignment (k - 1)
        (fun π => hsub π.1 π.2)
        (fun π => hsize π.1 π.2)
        (fun π π' hne => hpair π.1 π.2 π'.1 π'.2 (fun heq => hne (Subtype.ext heq)))
      simpa only [Fintype.card_coe] using hinside
    have harith := heavy_sharedBase_arithmetic hM2 h108 hBN hJ
    exact (Nat.add_le_add_left hsum 1).trans harith

/-- Sharp version of the generic family consumer for a nontrivial (`≥2`) heavy family. -/
theorem heavy_family_slots_le_893823171
    {κ U : Type*} [DecidableEq κ] [DecidableEq U]
    (B : Finset U) (Fam : Finset κ) (A : κ → Finset U) (riders : κ → ℕ)
    (hBN : B.card ≤ N)
    (hsub : ∀ π ∈ Fam, A π ⊆ B)
    (hsize : ∀ π ∈ Fam, tenRiderAlignment ≤ (A π).card)
    (hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' →
      (A π ∩ A π').card ≤ k - 1)
    (hM2 : 2 ≤ Fam.card) (h108 : Fam.card ≤ 108)
    (hriders : ∀ π ∈ Fam, riders π ≤ N - B.card + 1) :
    1 + ∑ π ∈ Fam, (riders π - 1) ≤ 893823171 := by
  classical
  have hsum : (∑ π ∈ Fam, (riders π - 1)) ≤ Fam.card * (N - B.card) := by
    calc
      (∑ π ∈ Fam, (riders π - 1)) ≤ ∑ _π ∈ Fam, (N - B.card) := by
        exact Finset.sum_le_sum fun π hπ => by
          have := hriders π hπ
          omega
      _ = Fam.card * (N - B.card) := by simp
  have hJ : Fam.card * tenRiderAlignment ^ 2 ≤
      B.card * (tenRiderAlignment + (Fam.card - 1) * (k - 1)) := by
    have hinside := johnson_inside_finset B (fun π : ↥Fam => A π.1)
      tenRiderAlignment (k - 1)
      (fun π => hsub π.1 π.2)
      (fun π => hsize π.1 π.2)
      (fun π π' hne => hpair π.1 π.2 π'.1 π'.2 (fun heq => hne (Subtype.ext heq)))
    simpa only [Fintype.card_coe] using hinside
  have harith := heavy_sharedBase_arithmetic_sharp hM2 h108 hBN hJ
  exact (Nat.add_le_add_left hsum 1).trans harith

end ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure

#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.johnson_inside_finset
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.heavy_sharedBase_arithmetic
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.minimalCarrier_lowRider_johnson_boundary
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.lowAlignment_sharedRider_packing
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.sharedRiderUnique_band_separates_two_and_three
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.sharedRider_family_card_le_18
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.sharedRider_complementJohnson_exact_crossover
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.saturatedBinaryDistance_below_plotkin
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.saturatedBinaryPlotkin_slack
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.balanced_binary_matching_card_eq_two_inter
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.balancedBinary_inter_card_le_134217727
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.balancedBinary_sharp_distance_value
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.balancedBinary_constantWeightJohnson_denominator_zero
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.threeNonbase_capacity_forces_fourRiderAlignment
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.threeNonbase_capacity_exact_crossover
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.twoNonbase_capacity_exact_crossover
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.twoCarrier_matching_floor
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.twoRider_matching_floor_rootBudget_slack
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.combinedTwoRider_johnson_arithmetic
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.combinedTwoRider_family_card_le_five
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.disjointErasedFibers_sum_le_global
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.disjointErasedFibers_sum_le_global_sub_one
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.heavy_sharedBase_arithmetic_sharp
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.heavyEnvelope_add_lightSlots_le_N
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.heavy_family_slots_le_N
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterSharedBaseLayerClosure.heavy_family_slots_le_893823171
