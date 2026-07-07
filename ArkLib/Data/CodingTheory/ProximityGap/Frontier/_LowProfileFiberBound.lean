/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiber

/-!
# LANE W2 (#466): the low-profile `D(t)` fiber — per-scalar decomposition, the corrected
# uniqueness threshold, and the vicious circularity

The weld's `hlow` branch (`LineListMCAWeld.lowWeight_badCount_le_of_largeZeroSafe_budget`)
needs, for `t < k`, a bound on
`D(t) = |lineAppearingCodewords ∩ coordinateAgreementFiber(u₀, S)|` for `t`-subsets `S` of the
direction zero set.  This file settles the structure of the proposed per-scalar attack:

1. **The key observation is TRUE** (`coordinateAgreementFiber_subset_agreeSet_line`): on
   direction-zero coordinates the line word equals `u₀` for EVERY `γ`, so agreement with `u₀`
   on `S ⊆ Z(u₁)` IS agreement with every line word on `S`.

2. **But its proposed consequence is FALSE**: "total agreement `≥ a ≥ k` ⟹ per-γ fiber ≤ 1 by
   `rsCode_pairwise_agreeSet_card_le`" conflates agreement-with-a-common-word with *pairwise*
   codeword agreement.  Two distinct codewords agreeing with the same `w_γ` on `≥ a` points
   need only agree with each other on `≥ 2a − n` points.  Machine countermodel (constructive,
   p ∈ {17, 41, 97}, n = 8, k = 2, a = 4 = k+2, t = 1):
   `scripts/probes/probe_466_lowprofile_dt.py`.  The correct ambient threshold is unique
   decoding, `n + k ≤ 2a` (`perScalarPlainFiber_card_le_one_of_unique_decoding`), which is
   **empty in the sub-Johnson window** (`not_ambient_unique_decoding_of_subJohnson`:
   `a² < n·k ⟹ ¬(n + k ≤ 2a)`).

3. **The rescue — support localization** (`perScalarExactFiber_card_le_one`): for the EXACT
   fiber (zero-agreement set exactly `S`), every agreement set satisfies `A ∩ Z = S`, hence
   `A ⊆ S ∪ supp(u₁)`, and the ambient `n` in the union bound drops to `t + s`.  Per-γ
   uniqueness then needs only `k + s + t ≤ 2a` — in the large-zero branch (`s ≤ n − a`) this
   follows from `n + k + t ≤ 3a` (`threshold_le_of_largeZero`), which is satisfiable STRICTLY
   BELOW the Johnson agreement `√(nk)` at prize rates (`threshold_demo_subJohnson`:
   n = 48, k = 12, a = 21 < 24 = √(nk)).  This is genuinely new sub-Johnson per-γ rigidity.

4. **The circularity — and its viciousness.**  What the per-γ uniqueness buys is
   `D_exact(t) ≤ Λ_b` (`exactAppearingZeroAgreementFiber_card_le_lineBadScalars_card`) —
   the bad-scalar count itself, for the SAME line.  The weld consumes fiber budgets `M t` to
   produce a bad-scalar budget through `ZeroCoordinateAgreementFiberBudgetFits`; feeding the
   circular `M t = Λ_b` back in is strictly expanding
   (`selfReferential_fiberFit_forces`: any budget `B` fit from the constant input `Λ` obeys
   `a·Λ·s ≤ B`), so no fixed point below the input exists
   (`no_selfReferential_fiberFit_fixedPoint`).  The circularity is VICIOUS, with exact
   quantifier structure: per-line `D_exact(t; u₀,u₁) ≤ Λ_b(u₀,u₁)` feeds a per-line budget
   whose output is `≥ a·s·Λ_b(u₀,u₁)` — the only nontrivial multiplier the per-γ route
   produces is the quantity being bounded.

All results axiom-clean.  Probe: `scripts/probes/probe_466_lowprofile_dt.py` (+ its `_out`).
Issue #466, dossier v3 §6 Tier-1 item 2 (the weld's `hlow` production obligation).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.LowProfileFiber

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The key observation (true half): the line word equals the offset on the zero set -/

/-- On a direction-zero coordinate the line word equals the offset, for every scalar. -/
theorem lineWord_eq_offset_of_direction_zero
    {u₁ : Fin n → F} (u₀ : Fin n → F) (γ : F) {i : Fin n}
    (hi : i ∈ directionZeroSet u₁) :
    u₀ i + γ • u₁ i = u₀ i := by
  classical
  have hz : u₁ i = 0 := by
    rw [directionZeroSet, Finset.mem_filter] at hi
    exact hi.2
  rw [hz, smul_zero, add_zero]

open Classical in
/-- **The key observation.**  A codeword in the coordinate fiber over `S ⊆ Z(u₁)` agrees with
EVERY line word on all of `S`: fiber agreement is line-word agreement on the zero set. -/
theorem coordinateAgreementFiber_subset_agreeSet_line
    (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    {S : Finset (Fin n)} (hS : S ⊆ directionZeroSet u₁)
    {c : Fin n → F} (hc : c ∈ coordinateAgreementFiber dom k u₀ S) :
    S ⊆ agreeSet c (fun i => u₀ i + γ • u₁ i) := by
  intro i hi
  rw [coordinateAgreementFiber, Finset.mem_filter] at hc
  rw [agreeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [lineWord_eq_offset_of_direction_zero u₀ γ (hS hi)]
  exact hc.2.2 i hi

/-! ### 2. The per-scalar fibers -/

open Classical in
/-- The per-scalar PLAIN fiber: codewords agreeing with `u₀` on `S` and with the line word
`u₀ + γ·u₁` on at least `a` coordinates. -/
noncomputable def perScalarPlainFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (coordinateAgreementFiber dom k u₀ S).filter
    (fun c => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The per-scalar EXACT fiber: codewords whose zero-direction agreement set is exactly `S`
and which agree with the line word `u₀ + γ·u₁` on at least `a` coordinates. -/
noncomputable def perScalarExactFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ directionZeroAgreementSet c u₀ u₁ = S
      ∧ a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

/-! ### 3. The per-scalar decomposition (covers over the bad-scalar set) -/

open Classical in
/-- The plain appearance fiber `D(t)` is covered by per-scalar plain fibers over the line's
bad-scalar set: every appearing codeword appears at SOME `γ`, and that `γ` is bad. -/
theorem appearingCoordinateAgreementFiber_subset_biUnion_perScalarPlain
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    appearingCoordinateAgreementFiber dom k a u₀ u₁ S ⊆
      (lineBadScalars dom k a u₀ u₁).biUnion
        (fun γ => perScalarPlainFiber dom k a u₀ u₁ γ S) := by
  intro c hc
  rw [mem_appearingCoordinateAgreementFiber] at hc
  obtain ⟨hfib, happ⟩ := hc
  have hcode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [coordinateAgreementFiber, Finset.mem_filter] at hfib
    exact hfib.2.1
  rw [lineAppearingCodewords, Finset.mem_filter] at happ
  obtain ⟨-, -, γ, hγ⟩ := happ
  refine Finset.mem_biUnion.mpr ⟨γ, ?_, ?_⟩
  · rw [lineBadScalars, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, c, hcode, hγ⟩
  · rw [perScalarPlainFiber, Finset.mem_filter]
    exact ⟨hfib, hγ⟩

open Classical in
/-- The exact appearance fiber is covered by per-scalar exact fibers over the bad scalars. -/
theorem exactAppearingZeroAgreementFiber_subset_biUnion_perScalarExact
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    exactAppearingZeroAgreementFiber dom k a u₀ u₁ S ⊆
      (lineBadScalars dom k a u₀ u₁).biUnion
        (fun γ => perScalarExactFiber dom k a u₀ u₁ γ S) := by
  intro c hc
  rw [mem_exactAppearingZeroAgreementFiber] at hc
  obtain ⟨happ, hzS⟩ := hc
  rw [lineAppearingCodewords, Finset.mem_filter] at happ
  obtain ⟨-, hcode, γ, hγ⟩ := happ
  refine Finset.mem_biUnion.mpr ⟨γ, ?_, ?_⟩
  · rw [lineBadScalars, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, c, hcode, hγ⟩
  · rw [perScalarExactFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcode, hzS, hγ⟩

open Classical in
/-- **The decomposition bound (candidate shape from the lane brief).**  `D(t)` is at most the
bad-scalar count times the worst per-scalar plain fiber. -/
theorem appearingCoordinateAgreementFiber_card_le_badScalars_mul
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) {m : ℕ}
    (hm : ∀ γ ∈ lineBadScalars dom k a u₀ u₁,
      (perScalarPlainFiber dom k a u₀ u₁ γ S).card ≤ m) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card
      ≤ (lineBadScalars dom k a u₀ u₁).card * m := by
  calc
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card
        ≤ ((lineBadScalars dom k a u₀ u₁).biUnion
            (fun γ => perScalarPlainFiber dom k a u₀ u₁ γ S)).card :=
          Finset.card_le_card
            (appearingCoordinateAgreementFiber_subset_biUnion_perScalarPlain dom k a u₀ u₁ S)
    _ ≤ ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          (perScalarPlainFiber dom k a u₀ u₁ γ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _γ ∈ lineBadScalars dom k a u₀ u₁, m := Finset.sum_le_sum hm
    _ = (lineBadScalars dom k a u₀ u₁).card * m := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### 4. Per-scalar uniqueness: the ambient threshold and its window emptiness -/

open Classical in
/-- **Ambient per-scalar uniqueness — the CORRECTED threshold.**  Two distinct codewords each
agreeing with the same line word on `≥ a` coordinates agree with each other on
`≥ 2a − n` coordinates; uniqueness needs `n + k ≤ 2a` (unique decoding), NOT the lane brief's
`a ≥ k` (machine countermodel at `a = k+2`: `probe_466_lowprofile_dt.py`). -/
theorem perScalarPlainFiber_card_le_one_of_unique_decoding
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hthr : n + k ≤ 2 * a)
    (u₀ u₁ : Fin n → F) (γ : F) (S : Finset (Fin n)) :
    (perScalarPlainFiber dom k a u₀ u₁ γ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro c hc c' hc'
  by_contra hne
  rw [perScalarPlainFiber, Finset.mem_filter, coordinateAgreementFiber,
    Finset.mem_filter] at hc hc'
  obtain ⟨⟨-, hcode, -⟩, hagr⟩ := hc
  obtain ⟨⟨-, hcode', -⟩, hagr'⟩ := hc'
  set w : Fin n → F := fun i => u₀ i + γ • u₁ i with hw
  have hunion : (agreeSet c w ∪ agreeSet c' w).card ≤ n := by
    calc (agreeSet c w ∪ agreeSet c' w).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have hkey : (agreeSet c w ∩ agreeSet c' w).card + (agreeSet c w ∪ agreeSet c' w).card
      = (agreeSet c w).card + (agreeSet c' w).card :=
    Finset.card_inter_add_card_union _ _
  have hpair : agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c' := by
    intro i hi
    rw [Finset.mem_inter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    rw [agreeSet, Finset.mem_filter] at hi1 hi2 ⊢
    exact ⟨Finset.mem_univ _, hi1.2.trans hi2.2.symm⟩
  have hcap : (agreeSet c c').card ≤ k - 1 :=
    rsCode_pairwise_agreeSet_card_le dom hk hcode hcode' hne
  have hmono : (agreeSet c w ∩ agreeSet c' w).card ≤ (agreeSet c c').card :=
    Finset.card_le_card hpair
  omega

/-- Pure arithmetic: strictly sub-Johnson agreement (`a² < n·k`) is strictly below the
unique-decoding threshold (`2a < n + k`).  Hence the ambient per-scalar uniqueness premise is
EMPTY everywhere in the window (which sits below Johnson). -/
theorem two_mul_lt_add_of_sq_lt {a b c : ℕ} (h : a * a < b * c) : 2 * a < b + c := by
  by_contra hle
  push_neg at hle
  zify at h hle
  nlinarith [sq_nonneg ((b : ℤ) - (c : ℤ))]

/-- Window emptiness of the ambient route: sub-Johnson agreement refutes `n + k ≤ 2a`. -/
theorem not_ambient_unique_decoding_of_subJohnson {a k : ℕ} (h : a * a < n * k) :
    ¬ (n + k ≤ 2 * a) := by
  intro hle
  exact absurd hle (not_le.mpr (two_mul_lt_add_of_sq_lt h))

/-! ### 5. The rescue: support-localized per-scalar uniqueness for EXACT fibers -/

open Classical in
/-- For a codeword whose zero-direction agreement set is exactly `S`, every line-word
agreement set is contained in `S ∪ supp(u₁)`: on the zero set, line agreement is exactly
offset agreement, which is exactly `S`. -/
theorem agreeSet_line_subset_union_of_exact
    {u₀ u₁ : Fin n → F} (γ : F) {c : Fin n → F} {S : Finset (Fin n)}
    (hzS : directionZeroAgreementSet c u₀ u₁ = S) :
    agreeSet c (fun i => u₀ i + γ • u₁ i) ⊆ S ∪ directionSupportSet u₁ := by
  intro i hi
  rw [agreeSet, Finset.mem_filter] at hi
  by_cases hz : u₁ i = 0
  · refine Finset.mem_union_left _ ?_
    rw [← hzS, directionZeroAgreementSet, Finset.mem_filter]
    have hiz : i ∈ directionZeroSet u₁ := by
      rw [directionZeroSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hz⟩
    refine ⟨hiz, ?_⟩
    have hline : u₀ i + γ • u₁ i = u₀ i :=
      lineWord_eq_offset_of_direction_zero u₀ γ hiz
    rw [← hline]
    exact hi.2
  · refine Finset.mem_union_right _ ?_
    rw [directionSupportSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hz⟩

open Classical in
/-- **Support-localized per-scalar uniqueness (the new theorem).**  For the exact fiber the
union bound lives in `S ∪ supp(u₁)` (size `t + s`), not the whole domain: per-γ uniqueness
holds as soon as `k + s + t ≤ 2a`.  In the large-zero branch (`s ≤ n − a`) this is
satisfiable strictly below the Johnson agreement — sub-Johnson rigidity the ambient bound
cannot see. -/
theorem perScalarExactFiber_card_le_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (u₀ u₁ : Fin n → F) (γ : F)
    {S : Finset (Fin n)}
    (hthr : k + (directionSupportSet u₁).card + S.card ≤ 2 * a) :
    (perScalarExactFiber dom k a u₀ u₁ γ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro c hc c' hc'
  by_contra hne
  rw [perScalarExactFiber, Finset.mem_filter] at hc hc'
  obtain ⟨-, hcode, hzS, hagr⟩ := hc
  obtain ⟨-, hcode', hzS', hagr'⟩ := hc'
  set w : Fin n → F := fun i => u₀ i + γ • u₁ i with hw
  have hunion : (agreeSet c w ∪ agreeSet c' w).card
      ≤ S.card + (directionSupportSet u₁).card := by
    calc (agreeSet c w ∪ agreeSet c' w).card
        ≤ (S ∪ directionSupportSet u₁).card :=
          Finset.card_le_card (Finset.union_subset
            (agreeSet_line_subset_union_of_exact γ hzS)
            (agreeSet_line_subset_union_of_exact γ hzS'))
      _ ≤ S.card + (directionSupportSet u₁).card := Finset.card_union_le _ _
  have hkey : (agreeSet c w ∩ agreeSet c' w).card + (agreeSet c w ∪ agreeSet c' w).card
      = (agreeSet c w).card + (agreeSet c' w).card :=
    Finset.card_inter_add_card_union _ _
  have hpair : agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c' := by
    intro i hi
    rw [Finset.mem_inter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    rw [agreeSet, Finset.mem_filter] at hi1 hi2 ⊢
    exact ⟨Finset.mem_univ _, hi1.2.trans hi2.2.symm⟩
  have hcap : (agreeSet c c').card ≤ k - 1 :=
    rsCode_pairwise_agreeSet_card_le dom hk hcode hcode' hne
  have hmono : (agreeSet c w ∩ agreeSet c' w).card ≤ (agreeSet c c').card :=
    Finset.card_le_card hpair
  omega

/-- In the large-zero branch (`z ≥ a`, i.e. `¬SupportEligibleLineDirection`), the
support-localized threshold `k + s + t ≤ 2a` follows from the parameter-only condition
`n + k + t ≤ 3a`. -/
theorem threshold_le_of_largeZero
    {a k t : ℕ} (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (h3 : n + k + t ≤ 3 * a) :
    k + (directionSupportSet u₁).card + t ≤ 2 * a := by
  classical
  have hzc : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hz
    omega
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.filter_card_add_filter_neg_card_eq_card]
    simp
  omega

/-- **Satisfiability demo, strictly sub-Johnson** (rate `ρ = 1/4`): at `n = 48`, `k = 12`,
`a = 21`, `t = 0` the large-zero threshold `n + k + t ≤ 3a` holds while `a` is strictly
below the Johnson agreement `√(nk) = 24` — so the exact-fiber uniqueness has genuine
in-window content, unlike the ambient unique-decoding route (which needs `2a ≥ 60`). -/
theorem threshold_demo_subJohnson :
    48 + 12 + 0 ≤ 3 * 21 ∧ 21 * 21 < 48 * 12 ∧ ¬ (48 + 12 ≤ 2 * 21) := by
  norm_num

/-! ### 6. The circular bound: what per-scalar uniqueness actually buys -/

open Classical in
/-- Under the support-localized threshold, the exact appearance fiber is bounded by the
line's OWN bad-scalar count: `D_exact(t) ≤ Λ_b`.  This is the sharpest conclusion the
per-scalar route yields — and it is self-referential (see §7). -/
theorem exactAppearingZeroAgreementFiber_card_le_lineBadScalars_card
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (u₀ u₁ : Fin n → F)
    {S : Finset (Fin n)}
    (hthr : k + (directionSupportSet u₁).card + S.card ≤ 2 * a) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
      ≤ (lineBadScalars dom k a u₀ u₁).card := by
  calc
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
        ≤ ((lineBadScalars dom k a u₀ u₁).biUnion
            (fun γ => perScalarExactFiber dom k a u₀ u₁ γ S)).card :=
          Finset.card_le_card
            (exactAppearingZeroAgreementFiber_subset_biUnion_perScalarExact dom k a u₀ u₁ S)
    _ ≤ ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          (perScalarExactFiber dom k a u₀ u₁ γ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _γ ∈ lineBadScalars dom k a u₀ u₁, 1 :=
        Finset.sum_le_sum (fun γ _ => perScalarExactFiber_card_le_one dom hk u₀ u₁ γ hthr)
    _ = (lineBadScalars dom k a u₀ u₁).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]

open Classical in
/-- Stratum consequence of the circular bound: under the threshold at profile `t`, the whole
`t`-stratum is at most `choose(z, t) · Λ_b`. -/
theorem zeroAgreementStratum_card_le_choose_mul_lineBadScalars_card
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (u₀ u₁ : Fin n → F) {t : ℕ}
    (hthr : k + (directionSupportSet u₁).card + t ≤ 2 * a) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ (directionZeroSet u₁).card.choose t * (lineBadScalars dom k a u₀ u₁).card := by
  refine zeroAgreementStratum_card_le_choose_mul_exactAppearingZeroAgreementFiberBound
    dom k a u₀ u₁ t _ ?_
  intro S hS
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  exact exactAppearingZeroAgreementFiber_card_le_lineBadScalars_card dom hk u₀ u₁
    (by rw [hScard]; exact hthr)

/-! ### 7. The viciousness: the self-referential budget strictly expands -/

open Classical in
/-- **Feeding the circular bound back into the weld's fiber-fit is strictly expanding.**
If the constant fiber budget `M t = Λ` fits into `B` on a large-zero direction
(`ZeroCoordinateAgreementFiberBudgetFits`), then already the top profile `t = a−1` forces
`a · Λ · s ≤ B`: the produced bad-scalar budget is at least `a·s` times the input.  Since the
only nontrivial input the per-scalar route supplies is `Λ = Λ_b` itself, the recursion
`Λ_b ≤ B` requires `B ≥ a·s·Λ_b` — no self-referential fixed point below the input exists. -/
theorem selfReferential_fiberFit_forces
    {a B Λ : ℕ} (ha : 1 ≤ a) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ)) :
    a * (Λ * (directionSupportSet u₁).card) ≤ B := by
  have hterm := zeroCoordinateAgreementFiberBudgetFits_term_le (F := F) (n := n)
    a B (a - 1) u₁ (fun _ => Λ) (by omega) hFits
  have hsub : a - (a - 1) = 1 := by omega
  rw [hsub, Nat.div_one] at hterm
  have hzc : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hz
    omega
  have hchoose : a ≤ (directionZeroSet u₁).card.choose (a - 1) := by
    have h1 : a.choose (a - 1) = a := by
      have h2 : a - 1 = a - 1 := rfl
      have h3 := Nat.choose_symm (n := a) (k := 1) (by omega)
      rw [h3, Nat.choose_one_right]
    calc a = a.choose (a - 1) := h1.symm
      _ ≤ (directionZeroSet u₁).card.choose (a - 1) := Nat.choose_le_choose _ hzc
  calc
    a * (Λ * (directionSupportSet u₁).card)
        = (a * Λ) * (directionSupportSet u₁).card := by ring
    _ ≤ ((directionZeroSet u₁).card.choose (a - 1) * Λ) * (directionSupportSet u₁).card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hchoose)
    _ ≤ B := hterm

open Classical in
/-- **No self-referential fixed point.**  On any large-zero direction with nonempty moving
support and `a ≥ 2`, the constant fiber budget `Λ ≥ 1` can never fit into a bad-scalar
budget `B ≤ Λ`: the circularity `D_exact ≤ Λ_b` cannot be closed into any improvement of
`Λ_b` itself.  This is the precise sense in which the circularity is VICIOUS. -/
theorem no_selfReferential_fiberFit_fixedPoint
    {a B Λ : ℕ} (ha : 2 ≤ a) (hΛ : 1 ≤ Λ) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hs : 1 ≤ (directionSupportSet u₁).card)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ))
    (hB : B ≤ Λ) : False := by
  have hforce := selfReferential_fiberFit_forces (by omega) u₁ hz hFits
  have hgrow : 2 * Λ ≤ a * (Λ * (directionSupportSet u₁).card) := by
    calc 2 * Λ ≤ a * Λ := Nat.mul_le_mul_right _ ha
      _ ≤ a * (Λ * (directionSupportSet u₁).card) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hs)
  omega

end ProximityGap.LowProfileFiber

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LowProfileFiber.coordinateAgreementFiber_subset_agreeSet_line
#print axioms ProximityGap.LowProfileFiber.appearingCoordinateAgreementFiber_card_le_badScalars_mul
#print axioms ProximityGap.LowProfileFiber.perScalarPlainFiber_card_le_one_of_unique_decoding
#print axioms ProximityGap.LowProfileFiber.not_ambient_unique_decoding_of_subJohnson
#print axioms ProximityGap.LowProfileFiber.perScalarExactFiber_card_le_one
#print axioms ProximityGap.LowProfileFiber.threshold_le_of_largeZero
#print axioms ProximityGap.LowProfileFiber.threshold_demo_subJohnson
#print axioms ProximityGap.LowProfileFiber.exactAppearingZeroAgreementFiber_card_le_lineBadScalars_card
#print axioms ProximityGap.LowProfileFiber.zeroAgreementStratum_card_le_choose_mul_lineBadScalars_card
#print axioms ProximityGap.LowProfileFiber.selfReferential_fiberFit_forces
#print axioms ProximityGap.LowProfileFiber.no_selfReferential_fiberFit_fixedPoint
