/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.RatFunc.Basic
import ArkLib.Research.ProximityGap.Frontier.TwoSurfaceFactorAccounting
import ArkLib.Research.ProximityGap.Frontier.EighthRichHeadSafety
import ArkLib.Research.ProximityGap.Frontier.EighthCollinearOutlier
import ArkLib.Research.ProximityGap.Frontier.EighthFourPlusOne
import ArkLib.Research.ProximityGap.Frontier.EighthSaturatedOppositeDirections
import ArkLib.Research.ProximityGap.Frontier.EighthRichDeficits
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # End-to-end second-prime rate-1/8 MCA safety assembly (Packet L4c)

Provides shared `RatFunc`-extension, agreement-ceiling, collinear-union, and `mcaDeltaStar`-lifting
helpers, and closes the second-prime rate-`1/8` (`e = 671,088,639`) safety bound
(`mcaDeltaStar ≥ 671,088,640 / 2^30`) end-to-end conditional only on
`NonlinearComponentCap logDerivPrice`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SecondPrimeEighthAssembly

open Finset Polynomial Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting
open ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open scoped NNReal ENNReal

section SharedHelpers

/-- `RatFunc F` is an infinite field extension of any field `F`. -/
theorem ratFunc_infinite (F : Type) [Field F] : Infinite (RatFunc F) := by
  refine Infinite.of_injective (fun n : ℕ => algebraMap F[X] (RatFunc F) ((Polynomial.X : F[X]) ^ n)) ?_
  intro a b hab
  have hpoly : (Polynomial.X : F[X]) ^ a = (Polynomial.X : F[X]) ^ b :=
    RatFunc.algebraMap_injective F hab
  have hdeg := congrArg Polynomial.natDegree hpoly
  simpa using hdeg

/-- Canonical field embedding `F →+* RatFunc F`. -/
noncomputable def ratFuncHom (F : Type) [Field F] : F →+* RatFunc F :=
  (algebraMap F[X] (RatFunc F)).comp Polynomial.C

/-- Characteristic nonvanishing lifts from `ringChar F > bound` to `RatFunc F`. -/
theorem char_ok_of_ringChar_gt {F : Type} [Field F] {bound : ℕ}
    (hchar : bound < ringChar F) :
    ∀ r : ℕ, 0 < r → r ≤ bound → (r : RatFunc F) ≠ 0 := by
  intro r hrpos hrle hz
  have hF : (r : F) = 0 := by
    apply (ratFuncHom F).injective
    simpa [map_natCast, map_zero] using hz
  have hdvd : ringChar F ∣ r := (CharP.cast_eq_zero_iff F (ringChar F) r).mp hF
  have hle : ringChar F ≤ r := Nat.le_of_dvd hrpos hdvd
  omega

/-- Exact agreement ceiling `⌈(1 - e / n) * |I|⌉₊ = n - e` for `|I| = n` and `0 < n`. -/
theorem agreement_ceiling_of_card_eq {I : Type} [Fintype I] {n e : ℕ}
    (hn : Fintype.card I = n) (hpos : 0 < n) :
    ⌈(1 - (e : ℝ≥0) / (n : ℝ≥0)) * (Fintype.card I : ℝ≥0)⌉₊ = n - e := by
  rw [hn, tsub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast hpos.ne'), ← Nat.cast_tsub,
    Nat.ceil_natCast]

/-- Enumerate `m` distinct elements from any finset of cardinality `≥ m`. -/
theorem enumerate_finset {α : Type*} (H : Finset α) {m : ℕ} (hm : m ≤ H.card) :
    ∃ f : Fin m → α, Function.Injective f ∧ ∀ i, f i ∈ H := by
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hm
  let e := S.equivFinOfCardEq hcard
  exact ⟨fun i => (e.symm i).val, fun _ _ h => e.symm.injective (Subtype.ext h),
    fun i => hsub (e.symm i).property⟩

/-- Bridge between `EighthSaturatedOppositeDirections.count` and filtered cardinality. -/
theorem card_true_eq_count (b : Fin 4 → Bool) :
    (Finset.univ.filter fun i : Fin 4 => b i = true).card =
      EighthSaturatedOppositeDirections.count b := by
  revert b; decide

/-- Bridge between `EighthSaturatedOppositeDirections.count` and explicit `if`-sum. -/
theorem count_eq_four_sum (b : Fin 4 → Bool) :
    EighthSaturatedOppositeDirections.count b =
      (if b 0 then 1 else 0) + (if b 1 then 1 else 0) +
      (if b 2 then 1 else 0) + (if b 3 then 1 else 0) := by
  revert b; decide

/-- Bridge between `EighthSaturatedOppositeDirections.charge` and explicit `if`-sum. -/
theorem charge_eq_three_sum (b : Fin 4 → Bool) (j : Fin 4) :
    EighthSaturatedOppositeDirections.charge b j =
      (if b (EighthSaturatedOppositeDirections.face j 0) then 1 else 0) +
      (if b (EighthSaturatedOppositeDirections.face j 1) then 1 else 0) +
      (if b (EighthSaturatedOppositeDirections.face j 2) then 1 else 0) - 1 := by
  revert b j; decide

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Every head in `lineParameters fam` carries at most `e + 1` bad scalars when `t + e = n`. -/
theorem line_occupancy_le_e_add_one {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    {n t e : ℕ} (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hte : t + e = n)
    {h : LineParameter F} (hh : h ∈ lineParameters fam) :
    (pointsOn fam h).card ≤ e + 1 := by
  let c := (jointCore dom (u 0) (u 1) h.1 h.2).card
  have hpack := pointsOn_card_mul_max_add_core_le fam hh
  rw [hn] at hpack
  have hsub : max 1 (t - c) ≤ max 1 (⌈(1 - δ) * (n : ℝ≥0)⌉₊ - c) :=
    max_le_max_left 1 (Nat.sub_le_sub_right (hn ▸ ht) c)
  have h1 : (pointsOn fam h).card * max 1 (t - c) + c ≤ n :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hsub) c).trans hpack
  have hshare := EighthRichDeficits.head_share hte h1
  have hdiv : e / EighthRichDeficits.deficit t c ≤ e := Nat.div_le_self e _
  unfold EighthRichDeficits.price at hshare
  omega

/-- Distinct heads in `lineParameters fam` have joint-core overlap at most `k - 1`. -/
theorem pairwise_core_inter_le {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) {h₁ h₂ : LineParameter F}
    (hh₁ : h₁ ∈ lineParameters fam) (hh₂ : h₂ ∈ lineParameters fam) (hne : h₁ ≠ h₂) :
    (jointCore dom (u 0) (u 1) h₁.1 h₁.2 ∩ jointCore dom (u 0) (u 1) h₂.1 h₂.2).card ≤ k - 1 := by
  have hd₁ := lineParameter_degree_lt fam hh₁
  have hd₂ := lineParameter_degree_lt fam hh₂
  have hne' : h₁.1 ≠ h₂.1 ∨ h₁.2 ≠ h₂.2 := by
    by_contra! heq
    exact hne (Prod.ext heq.1 heq.2)
  exact FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le dom (u 0) (u 1) hk
    hd₁.1 hd₁.2 hd₂.1 hd₂.2 hne'

/-- Combined collinear head union cap via `TerminalCollinearHeadCount.collinear_card` and
`cauchy_core_union`. -/
theorem collinear_union_cap {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) {n t e c : ℕ} (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hte : t + e = n)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (a b : LineParameter F) (hab : a ≠ b) (hcoll : ∀ h ∈ H, lineDeterminant a b h = 0)
    (hcore : ∀ h ∈ H, c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card) :
    let d := k - 1
    let denom := c + (H.card - 1) * d
    let U := (H.card * c ^ 2 + denom - 1) / denom
    (H.biUnion (pointsOn fam)).card ≤ min (H.card * (e + 1)) (H.card * n - (H.card - 1) * U) := by
  classical
  dsimp only
  apply le_min
  · exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun h hh =>
        line_occupancy_le_e_add_one fam hn ht hte (hH hh)).trans_eq (by simp))
  · rcases H.eq_empty_or_nonempty with rfl | hne
    · simp
    have hcard : 1 ≤ H.card := Finset.card_pos.mpr hne
    let C (h : LineParameter F) := jointCore dom (u 0) (u 1) h.1 h.2
    let Uset := H.biUnion C
    have hcol := TerminalCollinearHeadCount.collinear_card fam H hH a b hab hcoll
    change (H.biUnion (pointsOn fam)).card ≤ Uset.card + (Fintype.card I - Uset.card) * H.card at hcol
    rw [hn] at hcol
    have hUn : Uset.card ≤ n := hn ▸ Finset.card_le_univ Uset
    have hcs := cauchy_core_union H C hcore (fun h₁ hh₁ h₂ hh₂ hne' =>
      pairwise_core_inter_le fam hk (hH hh₁) (hH hh₂) hne')
    change _ ≤ Uset.card at hcs
    have hrew : Uset.card + (n - Uset.card) * H.card = H.card * n - (H.card - 1) * Uset.card := by
      have h1 : (n - Uset.card) * H.card + Uset.card * H.card = n * H.card := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hUn]
      have h2 : (H.card - 1) * Uset.card + Uset.card = Uset.card * H.card := by
        rw [Nat.mul_comm Uset.card H.card]
        cases hH0 : H.card with
        | zero => omega
        | succ m => simp [Nat.succ_mul, Nat.add_comm]
      rw [Nat.mul_comm H.card n]
      omega
    rw [hrew] at hcol
    exact hcol.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left (H.card - 1) hcs) _)

/-- If `n + 2 * (k - 1) < 3 * c`, then every family of at least two heads with core size `≥ c`
lies on a single polynomial line. -/
theorem collinear_of_three_core_overflow {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    {n c : ℕ} (hn : Fintype.card I = n)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hcard : 2 ≤ H.card) (hcore : ∀ h ∈ H, c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card)
    (hover : n + 2 * (k - 1) < 3 * c) :
    ∃ a b : LineParameter F, a ≠ b ∧ ∀ h ∈ H, lineDeterminant a b h = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < H.card)
  refine ⟨a, b, hab, ?_⟩
  intro h hh
  by_contra hne
  have hdet : threeLineDeterminant a b h ≠ 0 := by
    intro hz; apply hne
    unfold lineDeterminant; unfold threeLineDeterminant at hz; linear_combination hz
  have hu := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b h hdet
  simp only [coreSet_eq_jointCore] at hu
  have hda := lineParameter_degree_lt fam (hH ha)
  have hdb := lineParameter_degree_lt fam (hH hb)
  have hdh := lineParameter_degree_lt fam (hH hh)
  have hdeg := natDegree_threeLineDeterminant_le_two_mul_sub_two hda.1 hda.2 hdb.1 hdb.2 hdh.1 hdh.2
  have hUn : (jointCore dom (u 0) (u 1) a.1 a.2 ∪ jointCore dom (u 0) (u 1) b.1 b.2 ∪
      jointCore dom (u 0) (u 1) h.1 h.2).card ≤ n := hn ▸ Finset.card_le_univ _
  have hca := hcore a ha
  have hcb := hcore b hb
  have hch := hcore h hh
  omega

/-- Lift a uniform bad-scalar cap `≤ 2^31` on `dom : I ↪ F` (`|I| = 2^30`) into both
`epsMCA ≤ 1 / 2^128` and `((e + 1) / 2^30) ≤ mcaDeltaStar` at every positive interleaving width. -/
theorem safety_of_badCount_le {k e : ℕ} (hk : 1 ≤ k) (he : e < 2 ^ 30)
    (dom : I ↪ F) (hn : Fintype.card I = 2 ^ 30)
    (hF : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card F)
    (hbad : ∀ u : WordStack F (Fin 2) I,
      (canonicalBadScalarRichPointFamily dom (k := k) ((e : ℝ≥0) / (2 ^ 30 : ℕ)) u hk).G.card ≤
        2 ^ 31)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((e : ℝ≥0) / (2 ^ 30 : ℕ)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 ∧
      ((e + 1 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) := by
  classical
  dsimp only
  have heps : epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) ((e : ℝ≥0) / (2 ^ 30 : ℕ)) ≤
      1 / (2 : ℝ≥0∞) ^ 128 := by
    apply (epsMCA_le_of_badCount_le _ _ (2 ^ 31) hbad).trans
    have hdiv := PrizeShapeRateHalfBracket.natCast_div_le_inv_of_mul_le (E := 2 ^ 31) (Q := 2 ^ 128)
      (p := Fintype.card F) (by decide) Fintype.card_pos hF
    simpa only [one_div, Nat.cast_pow, Nat.cast_ofNat] using hdiv
  refine ⟨by rw [epsMCA_interleaved_eq]; exact heps, ?_⟩
  rw [mcaDeltaStar_interleaved_eq]
  let eqv := (Fintype.equivFinOfCardEq hn).symm
  let x : Fin (2 ^ 30) ↪ F := eqv.toEmbedding.trans dom
  rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq
    eqv x dom (fun _ => rfl)]
  have hepsX : epsMCA (F := F) (ReedSolomon.code x k : Set (Fin (2 ^ 30) → F))
      (PrizeShapeRateHalfBracket.predecessorRadius (2 ^ 30) (e + 1)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 := by
    simp only [PrizeShapeRateHalfBracket.predecessorRadius, Nat.add_sub_cancel]
    rwa [← ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
      eqv x dom (fun _ => rfl)]
  exact PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (a := e + 1) (by omega) (by omega) _ _ hepsX

end SharedHelpers

/-! ## Rate 1/8 (`e = 671,088,639`) -/

section RateEighth

private theorem eighth_logDeriv_le_price :
    ∀ l j b : Fin 17, j.val ≤ l.val → 2 ≤ b.val → b.val ≤ l.val - j.val →
      max EighthRichHeadSafety.cutoff
        (logDerivPrice EighthRichHeadSafety.n EighthRichHeadSafety.d EighthRichHeadSafety.t
          (6 * EighthRichHeadSafety.t - 1 - (l.val - b.val) * EighthRichHeadSafety.d)
          (128 - j.val) b.val) ≤
        EighthRichHeadSafety.price l.val j.val b.val := by
  set_option maxRecDepth 30000 in
  set_option maxHeartbeats 1500000 in
  decide

private theorem eighth_linear_price_le :
    ∀ l j : Fin 17, j.val ≤ l.val →
      EighthRichHeadSafety.cutoff ≤ EighthRichHeadSafety.price l.val j.val 1 := by
  decide

private theorem eighth_lin_gap :
    (128 * (EighthRichHeadSafety.cutoff + 1 - 128) +
      3 * (EighthRichHeadSafety.cutoff + 1) * (128 - 1)) * EighthRichHeadSafety.n <
      (EighthRichHeadSafety.cutoff + 1) * (EighthRichHeadSafety.cutoff + 1 - 128) *
        (EighthRichHeadSafety.t - EighthRichHeadSafety.d) := by
  decide

private def reorder6 (q : Fin 5) : Fin 6 → Fin 6 :=
  ![(q.succAbove 0).castSucc, (q.succAbove 1).castSucc, (q.succAbove 2).castSucc,
    (q.succAbove 3).castSucc, q.castSucc, 5]

private theorem reorder6_inj : ∀ q, Function.Injective (reorder6 q) := by decide

private theorem sort_fin4_by {α : Type*} (f : Fin 4 → α) (w : α → ℕ) :
    ∃ σ : Equiv.Perm (Fin 4), Monotone (fun i => w (f (σ i))) :=
  ⟨Tuple.sort (fun i : Fin 4 => w (f i)), Tuple.monotone_sort (fun i : Fin 4 => w (f i))⟩

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem lineDet_self_left (a b : LineParameter F) : lineDeterminant a b a = 0 := by
  unfold lineDeterminant; ring

omit [Fintype F] [DecidableEq F] in
private theorem lineDet_self_right (a b : LineParameter F) : lineDeterminant a b b = 0 := by
  unfold lineDeterminant; ring

/-- Every index `i : Fin 4` is either `j` itself or one of the three vertices of `face j`. -/
private theorem fin4_eq_or_mem_face (j i : Fin 4) :
    i = j ∨ ∃ r : Fin 3, EighthSaturatedOppositeDirections.face j r = i := by
  revert j i; decide

omit [Fintype F] [DecidableEq F] in
theorem lineDet_eq_threeLineDet (a b c : LineParameter F) :
    lineDeterminant a b c = threeLineDeterminant a b c := by
  unfold lineDeterminant threeLineDeterminant; ring

set_option maxHeartbeats 600000 in
private theorem eighth_saturated_four_cap {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (W : Fin 4 → LineParameter F) (hW : ∀ i, W i ∈ lineParameters fam)
    (hcore0 : (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card = 402653180)
    (hcore1 : (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card = 402653184)
    (hcore2 : (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card = 402653184)
    (hcore3 : (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card = 402653184)
    (htri : ∀ j : Fin 4, threeLineDeterminant
      (W (EighthSaturatedOppositeDirections.face j 0))
      (W (EighthSaturatedOppositeDirections.face j 1))
      (W (EighthSaturatedOppositeDirections.face j 2)) ≠ 0) :
    (Finset.univ.biUnion fun i => pointsOn fam (W i)).card ≤ 2125114027 := by
  let core (i : Fin 4) := jointCore dom (u 0) (u 1) (W i).1 (W i).2
  have hb_ex : ∃ b : I → Fin 4 → Bool,
      ∀ x i, b x i = true ↔ AgreesAt (u 0 x) (u 1 x) (dom x) (W i) :=
    ⟨fun x i => decide ((W i).1.eval (dom x) = u 0 x ∧ (W i).2.eval (dom x) = u 1 x),
      fun x i => by simp only [decide_eq_true_eq, AgreesAt]⟩
  obtain ⟨b, hmask⟩ := hb_ex
  have hmemCore (x : I) (i : Fin 4) : x ∈ core i ↔ b x i = true := by
    rw [hmask]; simp only [core, jointCore, Finset.mem_filter, Finset.mem_univ, true_and, AgreesAt]
  have hdeg (i : Fin 4) : (W i).1.natDegree < 134217728 ∧ (W i).2.natDegree < 134217728 :=
    lineParameter_degree_lt fam (hW i)
  have hfaces0 := EighthSaturatedOppositeDirections.face_budgets dom (u 0) (u 1) W b hmask hdeg htri
  have hfaces : ∀ j : Fin 4, (∑ x : I, ((if b x (EighthSaturatedOppositeDirections.face j 0) then 1 else 0 : ℕ) +
      (if b x (EighthSaturatedOppositeDirections.face j 1) then 1 else 0) +
      (if b x (EighthSaturatedOppositeDirections.face j 2) then 1 else 0) - 1)) ≤ 268435454 := by
    intro j
    simpa only [← charge_eq_three_sum] using hfaces0 j
  have hcolSum (i : Fin 4) : (∑ x : I, if b x i then 1 else 0) = (core i).card := by
    simp only [Finset.sum_boole, Nat.cast_id]
    congr 1; ext x; simp [hmemCore]
  have htot : (∑ x : I, ∑ i : Fin 4, if b x i then 1 else 0) = 1610612732 := by
    rw [Finset.sum_comm]
    simp_rw [hcolSum]
    rw [Fin.sum_univ_four, hcore0, hcore1, hcore2, hcore3]
  have hfourth : (∑ x : I, if b x 0 then 1 else 0) = 402653180 := by
    rw [hcolSum 0, hcore0]
  obtain ⟨hreg, hdoub, hsing⟩ :=
    EighthSaturatedOppositeDirections.layout b hn htot hfourth hfaces
  let Dsites := Finset.univ.filter fun x : I => EighthSaturatedOppositeDirections.count (b x) = 2
  let P : Finset I := Finset.univ.filter fun x : I =>
    EighthSaturatedOppositeDirections.count (b x) = 1 ∧ b x 0 = false
  have hDsEq : Dsites.card = 536870908 := hdoub
  have hPeq : P.card = 402653190 := hsing
  classical
  let E := Dsites.image dom
  have hE : E.card = 4 * 134217727 := by
    rw [Finset.card_image_of_injective _ dom.injective, hDsEq]
  have hfit : ∀ y ∈ E, ∃ (O : Finset (Fin 4)) (u₀ v₀ : F), O.card = 2 ∧
      ∀ i ∈ O, (W i).1.eval y = u₀ ∧ (W i).2.eval y = v₀ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    let O := Finset.univ.filter fun i : Fin 4 => b x i = true
    have hOcard : O.card = 2 := by
      have hcnt := (Finset.mem_filter.mp hx).2
      rw [card_true_eq_count (b x)]
      exact hcnt
    refine ⟨O, u 0 x, u 1 x, hOcard, fun i hi => ?_⟩
    exact (hmask x i).mp (Finset.mem_filter.mp hi).2
  have hfreshEq {i : Fin 4} {z : F} {x : I}
      (hz : z ∈ pointsOn fam (W i))
      (hx : x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z))
      (hxout : x ∉ core i) :
      ((W i).2.eval (dom x) - u 1 x) ≠ 0 ∧
      ((W i).1.eval (dom x) - u 0 x) + z * ((W i).2.eval (dom x) - u 1 x) = 0 ∧
      z = (u 0 x - (W i).1.eval (dom x)) / ((W i).2.eval (dom x) - u 1 x) := by
    obtain ⟨_, hq⟩ := (mem_pointsOn_iff fam (W i) z).mp hz
    rw [hq] at hx
    have hag := (Finset.mem_filter.mp hx).2
    simp only [eval_add, eval_mul, eval_C] at hag
    have hden : (W i).2.eval (dom x) - u 1 x ≠ 0 := by
      intro h0
      have hv : (W i).2.eval (dom x) = u 1 x := sub_eq_zero.mp h0
      apply hxout
      simp only [core, jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [hv] at hag; exact add_right_cancel hag, hv⟩
    exact ⟨hden, by linear_combination hag, (eq_div_iff hden).mpr (by linear_combination hag)⟩
  let S : Finset (Fin 3 × I) := Finset.univ.filter fun p => p.2 ∉ core p.1.succ
  have hS : S.card ≤ 2013265920 := by
    have hSc : S.card = ∑ k : Fin 3, (Finset.univ.filter fun x : I => x ∉ core k.succ).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
      · intro p hp; simp [S] at hp ⊢; exact hp
      · intro p₁ _ p₂ _ h; cases p₁; cases p₂; simp at h; exact Prod.ext h.1 h.2
      · intro q hq; refine ⟨(q.1, q.2), ?_, rfl⟩; simp [S] at hq ⊢; exact hq
    have hcomp (k : Fin 3) :
        (Finset.univ.filter fun x : I => x ∉ core k.succ).card = 1073741824 - (core k.succ).card := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
        (p := fun x => x ∈ core k.succ)
      have h2 : (Finset.univ.filter fun x : I => x ∈ core k.succ).card = (core k.succ).card := by
        simp
      rw [Finset.card_univ, hn, h2] at h1
      omega
    rw [hSc]; simp_rw [hcomp]; rw [Fin.sum_univ_three]
    change (1073741824 - (core 1).card) + (1073741824 - (core 2).card) +
      (1073741824 - (core 3).card) ≤ 2013265920
    rw [hcore1, hcore2, hcore3]
  let L123 : Finset F := pointsOn fam (W 1) ∪ pointsOn fam (W 2) ∪ pointsOn fam (W 3)
  have hcov123 : ∀ z ∈ L123, ∃ k ∈ (Finset.univ : Finset (Fin 3)), z ∈ pointsOn fam (W k.succ) := by
    intro z hz
    simp only [L123, Finset.mem_union] at hz
    rcases hz with (h1 | h2) | h3
    · exact ⟨0, Finset.mem_univ _, h1⟩
    · exact ⟨1, Finset.mem_univ _, h2⟩
    · exact ⟨2, Finset.mem_univ _, h3⟩
  obtain ⟨G123, _, hG123mem, hG123dis, hG123card⟩ :=
    exists_disjoint_assignment (α := F) (β := Fin 3) L123 Finset.univ
      (fun (z : F) (k : Fin 3) => z ∈ pointsOn fam (W k.succ)) hcov123
  have hhasFresh (k : Fin 3) (z : F) (hz : z ∈ pointsOn fam (W k.succ)) :
      ∃ x : I, x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) ∧ x ∉ core k.succ := by
    obtain ⟨hzG, _⟩ := (mem_pointsOn_iff fam (W k.succ) z).mp hz
    exact Finset.not_subset.mp (not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (W k.succ).1 (W k.succ).2
      (hdeg k.succ).1 (hdeg k.succ).2 (fam.noJoint z hzG))
  let freshSite (k : Fin 3) (z : F) : I :=
    if hz : z ∈ pointsOn fam (W k.succ) then Classical.choose (hhasFresh k z hz)
    else Classical.arbitrary I
  let U : Finset (Fin 3 × I) :=
    Finset.univ.biUnion fun k : Fin 3 => (G123 k).image fun z => (k, freshSite k z)
  let first (p : Fin 3 × I) : F :=
    (u 0 p.2 - (W p.1.succ).1.eval (dom p.2)) / ((W p.1.succ).2.eval (dom p.2) - u 1 p.2)
  have hUmem : ∀ p ∈ U, ∃ z ∈ G123 p.1, p.2 ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) ∧
      p.2 ∉ core p.1.succ ∧ first p = z := by
    intro p hp
    obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hpk
    have hzW : z ∈ pointsOn fam (W k.succ) := hG123mem k (Finset.mem_univ k) z hz
    have hspec := Classical.choose_spec (hhasFresh k z hzW)
    have hfs : freshSite k z = Classical.choose (hhasFresh k z hzW) := dite_eq_left hzW
    rw [← hfs] at hspec
    exact ⟨z, hz, hspec.1, hspec.2, (hfreshEq hzW hspec.1 hspec.2).2.2.symm⟩
  have hUsub : U ⊆ S := by
    intro p hp; obtain ⟨_, _, _, hout, _⟩ := hUmem p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩
  have hUinj : Set.InjOn first ↑U := by
    intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨z₁, hz₁, _, _, hf₁⟩ := hUmem p₁ hp₁
    obtain ⟨z₂, hz₂, _, _, hf₂⟩ := hUmem p₂ hp₂
    have hzeq : z₁ = z₂ := hf₁.symm.trans (heq.trans hf₂)
    subst hzeq
    have hk : p₁.1 = p₂.1 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hG123dis p₁.1 (Finset.mem_univ _) p₂.1 (Finset.mem_univ _) hne)
        hz₁ hz₂
    obtain ⟨k₁, _, hp₁k⟩ := Finset.mem_biUnion.mp hp₁
    obtain ⟨w₁, hw₁, hw₁eq⟩ := Finset.mem_image.mp hp₁k
    obtain ⟨k₂, _, hp₂k⟩ := Finset.mem_biUnion.mp hp₂
    obtain ⟨w₂, hw₂, hw₂eq⟩ := Finset.mem_image.mp hp₂k
    have hk₁ : k₁ = p₁.1 := congrArg Prod.fst hw₁eq
    have hk₂ : k₂ = p₂.1 := congrArg Prod.fst hw₂eq
    subst hk₁; subst hk₂
    have hw₁eqz : w₁ = z₁ := by
      have hw₁W := hG123mem p₁.1 (Finset.mem_univ _) w₁ hw₁
      have hspec := Classical.choose_spec (hhasFresh p₁.1 w₁ hw₁W)
      have hfs : freshSite p₁.1 w₁ = Classical.choose (hhasFresh p₁.1 w₁ hw₁W) := dite_eq_left hw₁W
      rw [← hfs] at hspec
      have : first p₁ = w₁ := by rw [← hw₁eq]; exact (hfreshEq hw₁W hspec.1 hspec.2).2.2.symm
      exact this.symm.trans hf₁
    have hw₂eqz : w₂ = z₁ := by
      have hw₂W := hG123mem p₂.1 (Finset.mem_univ _) w₂ hw₂
      have hspec := Classical.choose_spec (hhasFresh p₂.1 w₂ hw₂W)
      have hfs : freshSite p₂.1 w₂ = Classical.choose (hhasFresh p₂.1 w₂ hw₂W) := dite_eq_left hw₂W
      rw [← hfs] at hspec
      have : first p₂ = w₂ := by rw [← hw₂eq]; exact (hfreshEq hw₂W hspec.1 hspec.2).2.2.symm
      exact this.symm.trans hf₂
    rw [← hw₁eq, ← hw₂eq, hk, hw₁eqz, hw₂eqz]
  have hUcard : U.card = L123.card := by
    rw [hG123card, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro k _
      apply Finset.card_image_of_injOn
      intro z₁ hz₁ z₂ hz₂ heq
      have h1 : first (k, freshSite k z₁) = z₁ := by
        have hW₁ := hG123mem k (Finset.mem_univ k) z₁ hz₁
        have hspec := Classical.choose_spec (hhasFresh k z₁ hW₁)
        have hfs : freshSite k z₁ = Classical.choose (hhasFresh k z₁ hW₁) := dite_eq_left hW₁
        rw [← hfs] at hspec
        exact (hfreshEq hW₁ hspec.1 hspec.2).2.2.symm
      have h2 : first (k, freshSite k z₂) = z₂ := by
        have hW₂ := hG123mem k (Finset.mem_univ k) z₂ hz₂
        have hspec := Classical.choose_spec (hhasFresh k z₂ hW₂)
        have hfs : freshSite k z₂ = Classical.choose (hhasFresh k z₂ hW₂) := dite_eq_left hW₂
        rw [← hfs] at hspec
        exact (hfreshEq hW₂ hspec.1 hspec.2).2.2.symm
      exact h1.symm.trans ((congrArg first heq).trans h2)
    · intro k₁ _ k₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hp₂
      exact hne (congrArg Prod.fst h2).symm
  let M : Finset F := pointsOn fam (W 0)
  let fresh0 (z : F) : Finset I := fullAgreement dom (u 0) (u 1) z (fam.q z) \ core 0
  let T : Finset I := M.biUnion fresh0
  let last (x : I) : F :=
    (u 0 x - (W 0).1.eval (dom x)) / ((W 0).2.eval (dom x) - u 1 x)
  have hTfive : 5 * M.card ≤ T.card := by
    have hdis0 : ∀ z₁ ∈ M, ∀ z₂ ∈ M, z₁ ≠ z₂ → Disjoint (fresh0 z₁) (fresh0 z₂) := by
      intro z₁ hz₁ z₂ hz₂ hne
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      obtain ⟨ha₁, ho₁⟩ := Finset.mem_sdiff.mp hx₁
      obtain ⟨ha₂, _⟩ := Finset.mem_sdiff.mp hx₂
      exact hne ((hfreshEq hz₁ ha₁ ho₁).2.2.trans (hfreshEq hz₂ ha₂ ho₁).2.2.symm)
    rw [Finset.card_biUnion (fun z₁ hz₁ z₂ hz₂ hne => hdis0 z₁ hz₁ z₂ hz₂ hne)]
    have hge5 : ∀ z ∈ M, 5 ≤ (fresh0 z).card := by
      intro z hz
      obtain ⟨hzG, _⟩ := (mem_pointsOn_iff fam (W 0) z).mp hz
      have hth := ht.trans (fam.threshold_le z hzG)
      have hsd := Finset.card_sdiff_add_card_inter (fullAgreement dom (u 0) (u 1) z (fam.q z)) (core 0)
      have hin := Finset.card_le_card (Finset.inter_subset_right
        (s₁ := fullAgreement dom (u 0) (u 1) z (fam.q z)) (s₂ := core 0))
      have hc0 : (core 0).card = 402653180 := hcore0
      change (fresh0 z).card + _ = (fullAgreement dom (u 0) (u 1) z (fam.q z)).card at hsd
      omega
    exact (Finset.sum_le_sum hge5).trans_eq' (by simp [Nat.mul_comm])
  have hTval : ∀ x ∈ T, last x ∈ M := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨ha, ho⟩ := Finset.mem_sdiff.mp hxz
    have : last x = z := (hfreshEq hz ha ho).2.2.symm
    rwa [this]
  let remaining (x : I) : Fin 3 := if b x 1 = false then 0 else if b x 2 = false then 1 else 2
  let facing (x : I) : Fin 3 := if b x 1 = false then 1 else 0
  have hTdouble {x : I} (hxT : x ∈ T) (hxP : x ∉ P) :
      b x 0 = false ∧ EighthSaturatedOppositeDirections.count (b x) = 2 := by
    obtain ⟨_, _, hxz⟩ := Finset.mem_biUnion.mp hxT
    have hx0 : x ∉ core 0 := (Finset.mem_sdiff.mp hxz).2
    have hb0 : b x 0 = false := by
      cases h : b x 0
      · rfl
      · exact absurd ((hmemCore x 0).mpr h) hx0
    rcases hreg x with h1 | h2
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, hb0⟩) hxP
    · exact ⟨hb0, h2⟩
  have hres : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ S := by
    intro x hxT hxP
    obtain ⟨hb0, hc2⟩ := hTdouble hxT hxP
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hxIn => ?_⟩
    have hbt := (hmemCore x (remaining x).succ).mp hxIn
    have hsum := (count_eq_four_sum (b x)).symm.trans hc2
    dsimp only [remaining] at hbt
    cases h1 : b x 1 <;> cases h2 : b x 2 <;> cases h3 : b x 3 <;>
      simp [hb0, h1, h2, h3] at hbt hsum
  have hfolds : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ U →
      let j := facing x
      (FourHeadCoreDeterminant.nearSide (fun i => (W i).2) j).eval (dom x) ≠ 0 ∧
      (FourHeadCoreDeterminant.farSide (fun i => (W i).2) j).eval (dom x) ≠ 0 ∧
      (FourHeadCoreDeterminant.nearSide (fun i => (W i).1) j).eval (dom x) +
        last x * (FourHeadCoreDeterminant.nearSide (fun i => (W i).2) j).eval (dom x) = 0 ∧
      (FourHeadCoreDeterminant.farSide (fun i => (W i).1) j).eval (dom x) +
        first (remaining x, x) * (FourHeadCoreDeterminant.farSide (fun i => (W i).2) j).eval (dom x) = 0 := by
    intro x hxT hxP hxU
    obtain ⟨hb0, hc2⟩ := hTdouble hxT hxP
    obtain ⟨z0, hz0, hxz0⟩ := Finset.mem_biUnion.mp hxT
    obtain ⟨ha0, ho0⟩ := Finset.mem_sdiff.mp hxz0
    obtain ⟨hden0, hlin0, hlast⟩ := hfreshEq hz0 ha0 ho0
    have hlast' : last x = z0 := hlast.symm
    obtain ⟨z1, hz1, ha1, ho1, hfirst'⟩ := hUmem (remaining x, x) hxU
    obtain ⟨hden1, hlin1, _⟩ := hfreshEq (hG123mem (remaining x) (Finset.mem_univ _) z1 hz1) ha1 ho1
    have hsum := (count_eq_four_sum (b x)).symm.trans hc2
    have hAg (i : Fin 4) (hi : b x i = true) :
        (W i).1.eval (dom x) = u 0 x ∧ (W i).2.eval (dom x) = u 1 x := (hmask x i).mp hi
    dsimp only
    cases h1 : b x 1 <;> cases h2 : b x 2 <;> cases h3 : b x 3 <;>
      simp [hb0, h1, h2, h3] at hsum
    · have hrem : remaining x = 0 := by simp [remaining, h1]
      have hfac : facing x = 1 := by simp [facing, h1]
      obtain ⟨hu2, hv2⟩ := hAg 2 h2; obtain ⟨hu3, hv3⟩ := hAg 3 h3
      rw [hfac]
      simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
        Matrix.cons_val_one, Matrix.cons_val_zero, eval_sub, Fin.succ_one_eq_two,
        hu2, hv2, hu3, hv3]
      rw [hrem] at hden1 hlin1 hfirst'
      simp only [Fin.succ_zero_eq_one] at hden1 hlin1
      exact ⟨fun h => hden0 (by linear_combination -h), fun h => hden1 (by linear_combination -h),
        by rw [hlast']; linear_combination -hlin0, by rw [hrem, hfirst']; linear_combination -hlin1⟩
    · have hrem : remaining x = 1 := by simp [remaining, h1, h2]
      have hfac : facing x = 0 := by simp [facing, h1]
      obtain ⟨hu1, hv1⟩ := hAg 1 h1; obtain ⟨hu3, hv3⟩ := hAg 3 h3
      rw [hfac]
      simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
        Matrix.cons_val_zero, eval_sub, Fin.succ_zero_eq_one, hu1, hv1, hu3, hv3]
      rw [hrem] at hden1 hlin1 hfirst'
      simp only [Fin.succ_one_eq_two] at hden1 hlin1
      exact ⟨fun h => hden0 (by linear_combination -h), fun h => hden1 (by linear_combination -h),
        by rw [hlast']; linear_combination -hlin0, by rw [hrem, hfirst']; linear_combination -hlin1⟩
    · have hrem : remaining x = 2 := by simp [remaining, h1, h2]
      have hfac : facing x = 0 := by simp [facing, h1]
      obtain ⟨hu1, hv1⟩ := hAg 1 h1; obtain ⟨hu2, hv2⟩ := hAg 2 h2
      rw [hfac]
      simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
        Matrix.cons_val_zero, eval_sub, Fin.succ_zero_eq_one, hu1, hv1, hu2, hv2]
      rw [hrem] at hden1 hlin1 hfirst'
      simp only [show (2 : Fin 3).succ = 3 from rfl] at hden1 hlin1
      exact ⟨fun h => hden0 (by linear_combination -h), hden1,
        by rw [hlast']; linear_combination -hlin0, by rw [hrem, hfirst']; linear_combination hlin1⟩
  have htr : FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 1 2 *
      FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 1 3 *
      FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 2 3 *
      FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 1 2 3 ≠ 0 := by
    have htriEq (i j k : Fin 4) :
        FourHeadCoreDeterminant.triangle (fun r => (W r).1) (fun r => (W r).2) i j k =
          threeLineDeterminant (W i) (W j) (W k) := by
      unfold FourHeadCoreDeterminant.triangle threeLineDeterminant; ring
    rw [htriEq 0 1 2, htriEq 0 1 3, htriEq 0 2 3, htriEq 1 2 3]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (htri 3) (htri 2)) (htri 1)) (htri 0)
  have hPcard : P.card ≤ 402653190 := hPeq.le
  have hsat := EighthSaturatedOppositeDirections.saturated_cap
    (fun i => (W i).1) (fun i => (W i).2) 134217727 E
    (fun i => Nat.le_of_lt_succ (hdeg i).1) (fun i => Nat.le_of_lt_succ (hdeg i).2)
    htr hE hfit dom S U T P M remaining facing first last
    hS hUsub hUinj hPcard hTfive hTval hres hfolds
  have hUeq : (Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (W i)) = M ∪ L123 := by
    ext z
    simp only [M, L123, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl (Or.inl hi))
      · exact Or.inr (Or.inl (Or.inr hi))
      · exact Or.inr (Or.inr hi)
    · rintro (h0 | (h1 | h2) | h3)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
  rw [hUeq]
  have hcardU := Finset.card_union_le M L123
  omega

set_option maxHeartbeats 600000 in
/-- Complete `j = 4` rich-head union cap for rate `1/8` (`e = 671,088,639`). -/
private theorem eighth_four_head_cap {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hcard : H.card = 4) (hrich : ∀ h ∈ H, 81920 < (pointsOn fam h).card) :
    (H.biUnion (pointsOn fam)).card ≤ EighthRichHeadSafety.headBound 4 := by
  classical
  have hcoreAll : ∀ h ∈ H, EighthRichHeadSafety.c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card :=
    fun h hh => rich_head_core_ge fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
      (by decide : 0 < 81920) (hH hh) (hrich h hh)
  obtain ⟨L0, hL0inj, hL0mem⟩ := enumerate_finset H (by omega : 4 ≤ H.card)
  by_cases hAllColl : ∀ i : Fin 4, lineDeterminant (L0 0) (L0 1) (L0 i) = 0
  · have hHcoll : ∀ h ∈ H, lineDeterminant (L0 0) (L0 1) h = 0 := by
      have himg : Finset.univ.image L0 = H :=
        Finset.eq_of_subset_of_card_le
          (fun _ hx => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hL0mem i)
          (by rw [Finset.card_image_of_injective _ hL0inj, Finset.card_univ, Fintype.card_fin, hcard])
      intro h hh
      rw [← himg] at hh
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
      exact hAllColl i
    have hcol := collinear_union_cap fam (by decide) hn ht (by decide : 402653185 + 671088639 = 1073741824)
      H hH (L0 0) (L0 1) (hL0inj.ne (by decide)) hHcoll hcoreAll
    rw [hcard] at hcol
    exact hcol.trans (by
      unfold EighthRichHeadSafety.headBound
      simp only [show ¬(4 ≤ 3) by decide, ↓reduceIte]
      exact le_max_left _ _)
  · push Not at hAllColl
    obtain ⟨k0, hk0⟩ := hAllColl
    have hdet0 : threeLineDeterminant (L0 0) (L0 1) (L0 k0) ≠ 0 := by
      rwa [← lineDet_eq_threeLineDet]
    have hk0ne : k0 ≠ 0 ∧ k0 ≠ 1 := by
      constructor <;> intro heq <;> subst heq <;> apply hdet0 <;> unfold threeLineDeterminant <;> ring
    let m0 : Fin 4 := if k0 = 2 then 3 else 2
    let idxQ : Fin 4 → Fin 4 := ![0, 1, k0, m0]
    let Q : Fin 4 → LineParameter F := L0 ∘ idxQ
    have hidxInj : Function.Injective idxQ := by
      intro i j hij
      fin_cases k0
      · exact absurd rfl hk0ne.1
      · exact absurd rfl hk0ne.2
      · fin_cases i <;> fin_cases j <;> simp [idxQ, m0] at hij ⊢
      · fin_cases i <;> fin_cases j <;> simp [idxQ, m0] at hij ⊢
    have hQinj : Function.Injective Q := hL0inj.comp hidxInj
    have hQmem : ∀ i, Q i ∈ H := fun i => hL0mem (idxQ i)
    have hQdeg (i : Fin 4) := lineParameter_degree_lt fam (hH (hQmem i))
    have hcore4 := _root_.ProximityGap.FourHeadCoreDeterminant.core_union_bound dom (u 0) (u 1)
      (fun i => (Q i).1) (fun i => (Q i).2) 134217727
      (fun i => Nat.le_of_lt_succ (hQdeg i).1) (fun i => Nat.le_of_lt_succ (hQdeg i).2)
      (by simpa [Q, idxQ, threeLineDeterminant] using hdet0)
      (fun i => by
        simpa only [Prod.mk.eta] using hQinj.ne (show (3 : Fin 4) ≠ i.castSucc by fin_cases i <;> decide))
      (fun i => jointCore dom (u 0) (u 1) (Q i).1 (Q i).2)
      (fun _ _ hx => (Finset.mem_filter.mp hx).2)
    have hUn : (Finset.univ.biUnion fun i : Fin 4 =>
        jointCore dom (u 0) (u 1) (Q i).1 (Q i).2).card ≤ 1073741824 :=
      hn ▸ Finset.card_le_univ _
    let defOf (h : LineParameter F) : ℕ :=
      EighthRichDeficits.deficit 402653185 (jointCore dom (u 0) (u 1) h.1 h.2).card
    obtain ⟨σ, hσ⟩ := sort_fin4_by Q defOf
    let S4 : Fin 4 → LineParameter F := Q ∘ σ
    have hS4inj : Function.Injective S4 := hQinj.comp σ.injective
    have hS4mem : ∀ i, S4 i ∈ H := fun i => hQmem (σ i)
    have hS4img : Finset.univ.image S4 = H :=
      Finset.eq_of_subset_of_card_le
        (fun _ hx => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hS4mem i)
        (by rw [Finset.card_image_of_injective _ hS4inj, Finset.card_univ, Fintype.card_fin, hcard])
    have hS4CoreSum :
        (jointCore dom (u 0) (u 1) (S4 0).1 (S4 0).2).card +
        (jointCore dom (u 0) (u 1) (S4 1).1 (S4 1).2).card +
        (jointCore dom (u 0) (u 1) (S4 2).1 (S4 2).2).card +
        (jointCore dom (u 0) (u 1) (S4 3).1 (S4 3).2).card ≤ 1073741824 + 4 * 134217727 := by
      have heq := Equiv.sum_comp σ (fun i => (jointCore dom (u 0) (u 1) (Q i).1 (Q i).2).card)
      rw [Fin.sum_univ_four] at heq
      dsimp only [S4, Function.comp_apply]
      omega
    have hDefSum := EighthRichDeficits.four_sum hS4CoreSum
    have hPopPrice (i : Fin 4) : (pointsOn fam (S4 i)).card ≤
        EighthRichDeficits.price 671088639 (defOf (S4 i)) := by
      have hpack := pointsOn_card_mul_max_add_core_le fam (hH (hS4mem i))
      rw [hn] at hpack
      have ht' : 402653185 ≤ ⌈(1 - δ) * (1073741824 : ℝ≥0)⌉₊ := by rwa [hn] at ht
      have hsub : max 1 (402653185 - (jointCore dom (u 0) (u 1) (S4 i).1 (S4 i).2).card) ≤
          max 1 (⌈(1 - δ) * (1073741824 : ℝ≥0)⌉₊ - (jointCore dom (u 0) (u 1) (S4 i).1 (S4 i).2).card) :=
        max_le_max_left 1 (Nat.sub_le_sub_right ht' _)
      exact EighthRichDeficits.head_share (by decide : 402653185 + 671088639 = 1073741824)
        ((Nat.add_le_add_right (Nat.mul_le_mul_left _ hsub) _).trans hpack)
    have hHb4 : 2125114027 ≤ EighthRichHeadSafety.headBound 4 := by
      unfold EighthRichHeadSafety.headBound
      simp only [show ¬(4 ≤ 3) by decide, ↓reduceIte]
      exact le_max_right _ _
    have hUnionEq : H.biUnion (pointsOn fam) = Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (S4 i) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, hh, hz⟩
        rw [← hS4img] at hh
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
        exact ⟨i, hz⟩
      · rintro ⟨i, hz⟩
        exact ⟨S4 i, hS4mem i, hz⟩
    by_cases hex : defOf (S4 0) = 1 ∧ defOf (S4 1) = 1 ∧ defOf (S4 2) = 1 ∧ defOf (S4 3) = 5
    · obtain ⟨hA, hB, hC, hD⟩ :=
        EighthRichDeficits.exceptional_cores hS4CoreSum hex.1 hex.2.1 hex.2.2.1 hex.2.2.2
      let W : Fin 4 → LineParameter F := ![S4 3, S4 0, S4 1, S4 2]
      have hWinj : Function.Injective W := by
        intro i j hij
        have hidx := hS4inj (show S4 (![3, 0, 1, 2] i) = S4 (![3, 0, 1, 2] j) by
          fin_cases i <;> fin_cases j <;> simp [W] at hij ⊢ <;> exact hij)
        fin_cases i <;> fin_cases j <;> simp at hidx ⊢
      have hWmem : ∀ i, W i ∈ lineParameters fam := fun i => by fin_cases i <;> simp [W, hH (hS4mem _)]
      have hWunion : H.biUnion (pointsOn fam) = Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (W i) := by
        rw [hUnionEq]; ext z
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi⟩
          fin_cases i
          · exact ⟨1, hi⟩
          · exact ⟨2, hi⟩
          · exact ⟨3, hi⟩
          · exact ⟨0, hi⟩
        · rintro ⟨i, hi⟩
          fin_cases i
          · exact ⟨3, hi⟩
          · exact ⟨0, hi⟩
          · exact ⟨1, hi⟩
          · exact ⟨2, hi⟩
      by_cases hallTri : ∀ j : Fin 4, threeLineDeterminant
          (W (EighthSaturatedOppositeDirections.face j 0))
          (W (EighthSaturatedOppositeDirections.face j 1))
          (W (EighthSaturatedOppositeDirections.face j 2)) ≠ 0
      · rw [hWunion]
        exact (eighth_saturated_four_cap fam hn ht W hWmem hD hA hB hC hallTri).trans hHb4
      · push Not at hallTri
        obtain ⟨j0, hj0⟩ := hallTri
        let T3 : Fin 3 → LineParameter F := fun i => W (EighthSaturatedOppositeDirections.face j0 i)
        let z0 : LineParameter F := W j0
        have hT3inj : Function.Injective T3 := by
          intro a b hab
          have := hWinj hab
          fin_cases j0 <;> fin_cases a <;> fin_cases b <;>
            simp [EighthSaturatedOppositeDirections.face] at this ⊢
        have hT3coll : ∀ i : Fin 3, lineDeterminant (T3 0) (T3 1) (T3 i) = 0 := by
          intro i
          fin_cases i
          · exact lineDet_self_left _ _
          · exact lineDet_self_right _ _
          · rw [lineDet_eq_threeLineDet]; exact hj0
        have hz0out : threeLineDeterminant (T3 0) (T3 1) z0 ≠ 0 := by
          intro hzero
          have hzero' : lineDeterminant (T3 0) (T3 1) (W j0) = 0 := by
            rw [lineDet_eq_threeLineDet]; exact hzero
          have hAllW : ∀ i : Fin 4, lineDeterminant (T3 0) (T3 1) (W i) = 0 := by
            intro i
            rcases fin4_eq_or_mem_face j0 i with rfl | ⟨r, hr⟩
            · exact hzero'
            · rw [← hr]; exact hT3coll r
          have hW01 : T3 0 ≠ T3 1 := hT3inj.ne (by decide)
          have hQon : ∀ i : Fin 4, lineDeterminant (T3 0) (T3 1) (Q i) = 0 := by
            intro i
            have hiH : Q i ∈ H := hQmem i
            rw [← hS4img] at hiH
            obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hiH
            rw [← hr]
            fin_cases r
            · exact hAllW 1
            · exact hAllW 2
            · exact hAllW 3
            · exact hAllW 0
          obtain ⟨f0, hf0, hg0⟩ := exists_polynomial_factor_of_lineDeterminant_eq_zero (T3 0) (T3 1) (Q 0) hW01 (hQon 0)
          obtain ⟨f1, hf1, hg1⟩ := exists_polynomial_factor_of_lineDeterminant_eq_zero (T3 0) (T3 1) (Q 1) hW01 (hQon 1)
          obtain ⟨f2, hf2, hg2⟩ := exists_polynomial_factor_of_lineDeterminant_eq_zero (T3 0) (T3 1) (Q 2) hW01 (hQon 2)
          apply hdet0
          change threeLineDeterminant (Q 0) (Q 1) (Q 2) = 0
          unfold threeLineDeterminant
          have h1x : (Q 1).1 - (Q 0).1 = primitiveIntercept (T3 0) (T3 1) * (f1 - f0) := by linear_combination hf1 - hf0
          have h1y : (Q 1).2 - (Q 0).2 = primitiveSlope (T3 0) (T3 1) * (f1 - f0) := by linear_combination hg1 - hg0
          have h2x : (Q 2).1 - (Q 0).1 = primitiveIntercept (T3 0) (T3 1) * (f2 - f0) := by linear_combination hf2 - hf0
          have h2y : (Q 2).2 - (Q 0).2 = primitiveSlope (T3 0) (T3 1) * (f2 - f0) := by linear_combination hg2 - hg0
          rw [h1x, h1y, h2x, h2y]; ring
        have hT3deg (i : Fin 3) : (T3 i).1.natDegree ≤ 134217727 ∧ (T3 i).2.natDegree ≤ 134217727 := by
          have hd := lineParameter_degree_lt fam (hWmem (EighthSaturatedOppositeDirections.face j0 i))
          exact ⟨Nat.le_of_lt_succ hd.1, Nat.le_of_lt_succ hd.2⟩
        have hz0deg : z0.1.natDegree ≤ 134217727 ∧ z0.2.natDegree ≤ 134217727 := by
          have hd := lineParameter_degree_lt fam (hWmem j0)
          exact ⟨Nat.le_of_lt_succ hd.1, Nat.le_of_lt_succ hd.2⟩
        obtain ⟨hpairs, htrans⟩ := EighthCollinearOutlier.overlap dom (u 0) (u 1)
          (T3 0) (T3 1) z0 (hT3inj.ne (by decide)) hz0out T3 hT3inj hT3coll
          (hT3deg 0) hz0deg hT3deg
        let r := max (primitiveIntercept (T3 0) (T3 1)).natDegree (primitiveSlope (T3 0) (T3 1)).natDegree
        let C3 (i : Fin 3) := jointCore dom (u 0) (u 1) (T3 i).1 (T3 i).2
        let U3 := Finset.univ.biUnion C3
        let Cz := jointCore dom (u 0) (u 1) z0.1 z0.2
        have hU3lb : (C3 0).card + (C3 1).card + (C3 2).card ≤ U3.card + 3 * (134217727 - r) := by
          have h01 := hpairs 0 1 (by decide)
          have h02 := hpairs 0 2 (by decide)
          have h12 := hpairs 1 2 (by decide)
          have hq1 := Finset.card_union_add_card_inter (C3 0) (C3 1)
          have hq2 := Finset.card_union_add_card_inter (C3 0 ∪ C3 1) (C3 2)
          rw [Finset.union_inter_distrib_right] at hq2
          have hj := Finset.card_union_le (C3 0 ∩ C3 2) (C3 1 ∩ C3 2)
          have hU3eq : U3 = (C3 0 ∪ C3 1) ∪ C3 2 := by
            ext x
            simp only [U3, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
            constructor
            · rintro ⟨i, hi⟩
              fin_cases i
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr hi)
              · exact Or.inr hi
            · rintro ((h | h) | h)
              · exact ⟨0, h⟩
              · exact ⟨1, h⟩
              · exact ⟨2, h⟩
          rw [hU3eq]
          change (C3 0 ∩ C3 1).card + r ≤ 134217727 at h01
          change (C3 0 ∩ C3 2).card + r ≤ 134217727 at h02
          change (C3 1 ∩ C3 2).card + r ≤ 134217727 at h12
          omega
        by_cases hr0 : r = 0
        · have hWcore (k : Fin 4) : 402653180 ≤ (jointCore dom (u 0) (u 1) (W k).1 (W k).2).card := by
            fin_cases k
            · dsimp [W]; omega
            · dsimp [W]; omega
            · dsimp [W]; omega
            · dsimp [W]; omega
          have hC3ge (i : Fin 3) : 402653180 ≤ (C3 i).card :=
            hWcore (EighthSaturatedOppositeDirections.face j0 i)
          let G3 (i : Fin 3) : Finset F := pointsOn fam (T3 i) \
            (Finset.univ.filter fun j : Fin 3 => j < i).biUnion (fun j => pointsOn fam (T3 j))
          have hG3dis (i j : Fin 3) (hij : i ≠ j) : Disjoint (G3 i) (G3 j) := by
            rw [Finset.disjoint_left]
            intro z hzi hzj
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · exact (Finset.mem_sdiff.mp hzj).2 (Finset.mem_biUnion.mpr
                ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, (Finset.mem_sdiff.mp hzi).1⟩)
            · exact (Finset.mem_sdiff.mp hzi).2 (Finset.mem_biUnion.mpr
                ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, (Finset.mem_sdiff.mp hzj).1⟩)
          have hconst := EighthFourPlusOne.constant_direction fam (hT3inj.ne (by decide))
            (fun i => hWmem _) hT3coll (G := G3) (fun _ => Finset.sdiff_subset) hG3dis hr0 U3 Subset.rfl
          rw [hn] at hconst
          have hT3cov : (Finset.univ.biUnion fun i : Fin 3 => pointsOn fam (T3 i)).card ≤ ∑ i : Fin 3, (G3 i).card := by
            rw [← Finset.card_biUnion (fun i _ j _ hij => hG3dis i j hij)]
            apply Finset.card_le_card
            intro z hz
            obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hz
            by_cases h0 : z ∈ pointsOn fam (T3 0)
            · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨h0, by simp⟩⟩
            · by_cases h1 : z ∈ pointsOn fam (T3 1)
              · refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨h1, ?_⟩⟩
                intro hbad
                obtain ⟨j, hjf, hjz⟩ := Finset.mem_biUnion.mp hbad
                have hlt := (Finset.mem_filter.mp hjf).2
                fin_cases j
                · exact h0 hjz
                · exact absurd hlt (by decide)
                · exact absurd hlt (by decide)
              · have h2 : z ∈ pointsOn fam (T3 2) := by
                  fin_cases i <;> first | exact absurd hzi h0 | exact absurd hzi h1 | exact hzi
                refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨h2, ?_⟩⟩
                intro hbad
                obtain ⟨j, hjf, hjz⟩ := Finset.mem_biUnion.mp hbad
                have hlt := (Finset.mem_filter.mp hjf).2
                fin_cases j
                · exact h0 hjz
                · exact h1 hjz
                · exact absurd hlt (by decide)
          have hz0le : (pointsOn fam z0).card ≤ 671088639 + 1 :=
            line_occupancy_le_e_add_one fam hn ht
              (by decide : 402653185 + 671088639 = 1073741824) (hWmem j0)
          have hWsplit : (Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (W i)) ⊆
              (Finset.univ.biUnion fun i : Fin 3 => pointsOn fam (T3 i)) ∪ pointsOn fam z0 := by
            intro z hz
            obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
            rcases fin4_eq_or_mem_face j0 i with rfl | ⟨r, hr⟩
            · exact Finset.mem_union_right _ hi
            · rw [← hr] at hi
              exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hi⟩)
          have hAll := (Finset.card_le_card hWsplit).trans (Finset.card_union_le _ _)
          have hC0 := hC3ge 0; have hC1 := hC3ge 1; have hC2 := hC3ge 2
          rw [hWunion]
          omega
        · have hr1 : 1 ≤ r := by omega
          have hUnZ := Finset.card_union_add_card_inter U3 Cz
          have hUZle : (U3 ∪ Cz).card ≤ 1073741824 := hn ▸ Finset.card_le_univ _
          change (U3 ∩ Cz).card ≤ 134217727 + r at htrans
          have hSum4 : (C3 0).card + (C3 1).card + (C3 2).card + Cz.card = 1610612732 := by
            have hW0 : (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card = 402653180 := hD
            have hW1 : (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card = 402653184 := hA
            have hW2 : (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card = 402653184 := hB
            have hW3 : (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card = 402653184 := hC
            dsimp only [C3, T3, Cz, z0]
            fin_cases j0
            · change (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card +
                (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card +
                (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card +
                (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card = 1610612732; omega
            · change (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card +
                (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card +
                (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card +
                (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card = 1610612732; omega
            · change (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card +
                (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card +
                (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card +
                (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card = 1610612732; omega
            · change (jointCore dom (u 0) (u 1) (W 0).1 (W 0).2).card +
                (jointCore dom (u 0) (u 1) (W 1).1 (W 1).2).card +
                (jointCore dom (u 0) (u 1) (W 2).1 (W 2).2).card +
                (jointCore dom (u 0) (u 1) (W 3).1 (W 3).2).card = 1610612732; omega
          have h01 := hpairs 0 1 (by decide)
          change _ + r ≤ 134217727 at h01
          omega
    · have hbd := EighthRichDeficits.four_except (a := defOf (S4 0)) (b := defOf (S4 1))
        (c := defOf (S4 2)) (d := defOf (S4 3))
        (by unfold defOf EighthRichDeficits.deficit; omega)
        (hσ (by decide)) (hσ (by decide)) (hσ (by decide)) hDefSum hex
      dsimp only [EighthRichDeficits.e] at hbd
      rw [hUnionEq]
      have hsum : (Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (S4 i)).card ≤
          (pointsOn fam (S4 0)).card + (pointsOn fam (S4 1)).card +
          (pointsOn fam (S4 2)).card + (pointsOn fam (S4 3)).card :=
        Finset.card_biUnion_le.trans_eq (Fin.sum_univ_four _)
      have h0 := hPopPrice 0; have h1 := hPopPrice 1; have h2 := hPopPrice 2; have h3 := hPopPrice 3
      omega

/-- Any 5 rich heads at rate `1/8` (`e = 671,088,639`) have a 4-head collinear subset. -/
private theorem eighth_five_has_four_collinear {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (L : Fin 5 → LineParameter F) (hinj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam) (hrich : ∀ i, 81920 < (pointsOn fam (L i)).card) :
    ∃ q : Fin 5, ∀ e : Equiv.Perm (Fin 4),
      threeLineDeterminant (L (FiveHeadTrianglePacking.four q e 0))
        (L (FiveHeadTrianglePacking.four q e 1))
        (L (FiveHeadTrianglePacking.four q e 2)) = 0 := by
  classical
  by_contra! hdet
  have hdeg (i : Fin 5) := lineParameter_degree_lt fam (hl i)
  have hu := FiveHeadTrianglePacking.four_incidence dom (u 0) (u 1) L 134217727 hinj
    (fun i => ⟨Nat.le_of_lt_succ (hdeg i).1, Nat.le_of_lt_succ (hdeg i).2⟩) hdet
  rw [hn] at hu
  have hbig (i : Fin 5) : EighthRichHeadSafety.c ≤ (jointCore dom (u 0) (u 1) (L i).1 (L i).2).card :=
    rich_head_core_ge fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
      (by decide : 0 < 81920) (hl i) (hrich i)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) fun i _ => hbig i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hparam := EighthRichHeadSafety.parameters.2.2.2.1
  dsimp [EighthRichHeadSafety.n, EighthRichHeadSafety.d, EighthRichHeadSafety.c,
    EighthRichHeadSafety.t, EighthRichHeadSafety.e] at hparam hsum
  omega

/-- Complete `j = 5` rich-head union cap for rate `1/8` (`e = 671,088,639`). -/
private theorem eighth_five_head_cap {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hcard : H.card = 5) (hrich : ∀ h ∈ H, 81920 < (pointsOn fam h).card) :
    (H.biUnion (pointsOn fam)).card ≤ EighthRichHeadSafety.headBound 5 := by
  classical
  obtain ⟨L, hLinj, hLmem⟩ := enumerate_finset H (by omega : 5 ≤ H.card)
  have hLimg : Finset.univ.image L = H :=
    Finset.eq_of_subset_of_card_le
      (fun _ hx => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hLmem i)
      (by rw [Finset.card_image_of_injective _ hLinj, Finset.card_univ, Fintype.card_fin, hcard])
  obtain ⟨q, hq⟩ := eighth_five_has_four_collinear fam hn ht L hLinj
    (fun i => hH (hLmem i)) (fun i => hrich _ (hLmem i))
  let A : Fin 4 → LineParameter F := fun i => L (q.succAbove i)
  have hAinj : Function.Injective A := hLinj.comp Fin.succAbove_right_injective
  have hAcoll : ∀ i : Fin 4, lineDeterminant (A 0) (A 1) (A i) = 0 := by
    intro i
    fin_cases i
    · exact lineDet_self_left _ _
    · exact lineDet_self_right _ _
    · rw [lineDet_eq_threeLineDet]; simpa [A, FiveHeadTrianglePacking.four] using hq (Equiv.refl _)
    · rw [lineDet_eq_threeLineDet]
      simpa [A, FiveHeadTrianglePacking.four, Equiv.swap_apply_def] using hq (Equiv.swap 2 3)
  by_cases h5coll : threeLineDeterminant (A 0) (A 1) (L q) = 0
  · have hHcoll : ∀ h ∈ H, lineDeterminant (A 0) (A 1) h = 0 := by
      intro h hh
      rw [← hLimg] at hh
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
      by_cases hi : i = q
      · subst hi; rw [lineDet_eq_threeLineDet]; exact h5coll
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        exact hAcoll j
    have hcoreAll : ∀ h ∈ H, EighthRichHeadSafety.c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card :=
      fun h hh => rich_head_core_ge fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
        (by decide : 0 < 81920) (hH hh) (hrich h hh)
    have hcol := collinear_union_cap fam (by decide) hn ht
      (by decide : 402653185 + 671088639 = 1073741824) H hH (A 0) (A 1)
      (hAinj.ne (by decide)) hHcoll hcoreAll
    rw [hcard] at hcol
    exact hcol.trans (by
      unfold EighthRichHeadSafety.headBound
      simp only [show ¬(5 ≤ 3) by decide, ↓reduceIte]
      exact le_max_left _ _)
  · have hcov := EighthFourPlusOne.covered fam hn
      (by omega : 402653184 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
      A hAinj (fun i => hH (hLmem (q.succAbove i))) hAcoll (L q) (hH (hLmem q)) h5coll
    have hHeq : H.biUnion (pointsOn fam) =
        (Finset.univ.biUnion fun i : Fin 4 => pointsOn fam (A i)) ∪ pointsOn fam (L q) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨h, hh, hz⟩
        rw [← hLimg] at hh
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
        by_cases hiq : i = q
        · exact Or.inr (hiq ▸ hz)
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hiq
          exact Or.inl ⟨j, hz⟩
      · rintro (⟨j, hj⟩ | hq')
        · exact ⟨A j, hLmem (q.succAbove j), hj⟩
        · exact ⟨L q, hLmem q, hq'⟩
    rw [hHeq]
    have hHb5 : 2125114028 ≤ EighthRichHeadSafety.headBound 5 := by
      unfold EighthRichHeadSafety.headBound
      simp only [show ¬(5 ≤ 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
      exact le_max_right _ _
    omega

set_option maxHeartbeats 600000 in
/-- Any `j ≥ 6` rich heads at rate `1/8` (`e = 671,088,639`) are ALL collinear. -/
private theorem eighth_six_plus_collinear {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hcard : 6 ≤ H.card) (hrich : ∀ h ∈ H, 81920 < (pointsOn fam h).card) :
    ∃ a b : LineParameter F, a ≠ b ∧ ∀ h ∈ H, lineDeterminant a b h = 0 := by
  classical
  have hcoreAll : ∀ h ∈ H, EighthRichHeadSafety.c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card :=
    fun h hh => rich_head_core_ge fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
      (by decide : 0 < 81920) (hH hh) (hrich h hh)
  have hfiveForce (L5 : Fin 5 → LineParameter F) (hL5inj : Function.Injective L5)
      (hL5mem : ∀ i, L5 i ∈ H) (hL5coll : ∀ i, lineDeterminant (L5 0) (L5 1) (L5 i) = 0)
      (z : LineParameter F) (hz : z ∈ H) : lineDeterminant (L5 0) (L5 1) z = 0 := by
    by_contra hne
    have hout : threeLineDeterminant (L5 0) (L5 1) z ≠ 0 := by
      rwa [← lineDet_eq_threeLineDet]
    have hdeg {w : LineParameter F} (hw : w ∈ H) :
        w.1.natDegree ≤ 134217727 ∧ w.2.natDegree ≤ 134217727 := by
      have hd := lineParameter_degree_lt fam (hH hw)
      exact ⟨Nat.le_of_lt_succ hd.1, Nat.le_of_lt_succ hd.2⟩
    have hcap := (EighthCollinearOutlier.cluster_cap dom (u 0) (u 1) (L5 0) (L5 1) z
      (hL5inj.ne (by decide)) hout L5 hL5inj hL5coll
      (hdeg (hL5mem 0)) (hdeg hz) (fun i => hdeg (hL5mem i))
      (fun i => hcoreAll _ (hL5mem i)) (hcoreAll z hz)).1 rfl
    rw [hn] at hcap
    have hparam := EighthRichHeadSafety.parameters.2.2.2.2
    dsimp [EighthRichHeadSafety.n, EighthRichHeadSafety.d, EighthRichHeadSafety.c,
      EighthRichHeadSafety.t, EighthRichHeadSafety.e] at hparam hcap
    omega
  obtain ⟨L6, hL6inj, hL6mem⟩ := enumerate_finset H hcard
  obtain ⟨q, hq⟩ := eighth_five_has_four_collinear fam hn ht (L6 ∘ Fin.castSucc)
    (hL6inj.comp (Fin.castSucc_injective _)) (fun i => hH (hL6mem _)) (fun i => hrich _ (hL6mem _))
  let A := L6 ∘ reorder6 q
  have hAinj : Function.Injective A := hL6inj.comp (reorder6_inj q)
  have hAcoll2 : threeLineDeterminant (A 0) (A 1) (A 2) = 0 := hq (Equiv.refl _)
  have hAcoll3 : threeLineDeterminant (A 0) (A 1) (A 3) = 0 := by
    simpa [A, reorder6, FiveHeadTrianglePacking.four, Equiv.swap_apply_def, Fin.reduceEq] using
      hq (Equiv.swap 2 3)
  have h4or5 : threeLineDeterminant (A 0) (A 1) (A 4) = 0 ∨
      threeLineDeterminant (A 0) (A 1) (A 5) = 0 := by
    by_contra! hboth
    have hsame (a b c x : LineParameter F) (hca : c ≠ a)
        (hcol : threeLineDeterminant a b c = 0) (hout : threeLineDeterminant a b x ≠ 0) :
        threeLineDeterminant a c x ≠ 0 := by
      intro h
      apply hca
      have hx : (c.1 - a.1) * threeLineDeterminant a b x = 0 := by
        unfold threeLineDeterminant at *; linear_combination (b.1 - a.1) * h + (x.1 - a.1) * hcol
      have hy : (c.2 - a.2) * threeLineDeterminant a b x = 0 := by
        unfold threeLineDeterminant at *; linear_combination (b.2 - a.2) * h + (x.2 - a.2) * hcol
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hout))
        (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hout))
    have hswap (a b c : LineParameter F) :
        threeLineDeterminant b a c = -threeLineDeterminant a b c := by
      unfold threeLineDeterminant; ring
    let idx5 : Fin 5 → Fin 6 := ![0, 1, 2, 4, 5]
    obtain ⟨q', hq'⟩ := eighth_five_has_four_collinear fam hn ht (A ∘ idx5)
      (hAinj.comp (by decide : Function.Injective idx5))
      (fun i => hH (hL6mem _)) (fun i => hrich _ (hL6mem _))
    have h12 : threeLineDeterminant (A 1) (A 0) (A 2) = 0 := by rw [hswap, hAcoll2, neg_zero]
    have h024 := hsame (A 0) (A 1) (A 2) (A 4) (hAinj.ne (by decide)) hAcoll2 hboth.1
    have h124 := hsame (A 1) (A 0) (A 2) (A 4) (hAinj.ne (by decide)) h12
      (by rw [hswap]; exact neg_ne_zero.mpr hboth.1)
    fin_cases q'
    · exact h124 (by exact hq' (Equiv.refl _))
    · exact h024 (by exact hq' (Equiv.refl _))
    · exact hboth.1 (by exact hq' (Equiv.refl _))
    · exact hboth.2 (by exact hq' (Equiv.swap 2 3))
    · exact hboth.1 (by exact hq' (Equiv.swap 2 3))
  refine ⟨A 0, A 1, hAinj.ne (by decide), ?_⟩
  intro z hz
  have hToLineDet {x : LineParameter F} (h0 : threeLineDeterminant (A 0) (A 1) x = 0) :
      lineDeterminant (A 0) (A 1) x = 0 := by
    rw [lineDet_eq_threeLineDet]; exact h0
  rcases h4or5 with h4 | h5
  · let L5 : Fin 5 → LineParameter F := A ∘ ![0, 1, 2, 3, 4]
    have hL5inj : Function.Injective L5 := hAinj.comp (by decide)
    exact hfiveForce L5 hL5inj (fun i => hL6mem _) (fun i => by
      fin_cases i
      · exact lineDet_self_left _ _
      · exact lineDet_self_right _ _
      · exact hToLineDet hAcoll2
      · exact hToLineDet hAcoll3
      · exact hToLineDet h4) z hz
  · let L5 : Fin 5 → LineParameter F := A ∘ ![0, 1, 2, 3, 5]
    have hL5inj : Function.Injective L5 := hAinj.comp (by decide)
    exact hfiveForce L5 hL5inj (fun i => hL6mem _) (fun i => by
      fin_cases i
      · exact lineDet_self_left _ _
      · exact lineDet_self_right _ _
      · exact hToLineDet hAcoll2
      · exact hToLineDet hAcoll3
      · exact hToLineDet h5) z hz

/-- Unified rich-head union bound `(H.biUnion (pointsOn fam)).card ≤ EighthRichHeadSafety.headBound H.card`
for EVERY `j = H.card` at rate `1/8` (`e = 671,088,639`). -/
theorem eighth_rich_head_union_le {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hrich : ∀ h ∈ H, 81920 < (pointsOn fam h).card) :
    (H.biUnion (pointsOn fam)).card ≤ EighthRichHeadSafety.headBound H.card := by
  by_cases hle3 : H.card ≤ 3
  · unfold EighthRichHeadSafety.headBound
    simp only [hle3, ↓reduceIte]
    exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun h hh =>
        line_occupancy_le_e_add_one fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
          (hH hh)).trans_eq (by simp))
  · by_cases h4 : H.card = 4
    · rw [h4]; exact eighth_four_head_cap fam hn ht H hH h4 hrich
    · by_cases h5 : H.card = 5
      · rw [h5]; exact eighth_five_head_cap fam hn ht H hH h5 hrich
      · obtain ⟨a, b, hab, hcoll⟩ := eighth_six_plus_collinear fam hn ht H hH (by omega) hrich
        have hcoreAll : ∀ h ∈ H, EighthRichHeadSafety.c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card :=
          fun h hh => rich_head_core_ge fam hn ht (by decide : 402653185 + 671088639 = 1073741824)
            (by decide : 0 < 81920) (hH hh) (hrich h hh)
        have hcol := collinear_union_cap fam (by decide) hn ht
          (by decide : 402653185 + 671088639 = 1073741824) H hH a b hab hcoll hcoreAll
        unfold EighthRichHeadSafety.headBound
        simp only [hle3, ↓reduceIte]
        exact hcol.trans (le_max_left _ _)

/-- Rate-`1/8` (`e = 671,088,639`) bad-scalar family cap `≤ 2^31` conditional on
`NonlinearComponentCap logDerivPrice`. -/
theorem eighth_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 402653185 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : (2 * 16 - 2) * (6 * 402653185 - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  have : Infinite (RatFunc F) := ratFunc_infinite F
  let φ := ratFuncHom F
  let domK : I ↪ RatFunc F := dom.trans ⟨φ, φ.injective⟩
  obtain ⟨Q₁, hQ₁ne, hQ₁supp, hQ₁root⟩ := EighthRichHeadSafety.surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn false
  obtain ⟨Q₂, hQ₂ne, hQ₂supp, hQ₂root⟩ := EighthRichHeadSafety.surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn true
  simp only [Bool.false_eq_true, ↓reduceIte] at hQ₁supp hQ₂supp
  obtain ⟨hQ₁Deg, hQ₁Tot, hQ₁Wt⟩ := surface_bounds_of_support hQ₁supp
  obtain ⟨hQ₂Deg, hQ₂Tot, _⟩ := surface_bounds_of_support hQ₂supp
  have hrootGen (Q : (RatFunc F)[X][X][X])
      (hQr : ∀ z : RatFunc F, ∀ q : (RatFunc F)[X], q.natDegree ≤ 134217727 →
        ∀ B : Finset I, 402653185 ≤ B.card →
        (∀ x ∈ B, q.eval (domK x) = φ (u 0 x) + z * φ (u 1 x)) →
        Q.eval₂ (evalRingHom (C z)) q = 0) :
      ∀ z ∈ fam.G, Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    intro z hz
    refine hQr (φ z) ((fam.q z).map φ) (natDegree_map_le.trans (by have := fam.degree_lt z hz; omega))
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht.trans (fam.threshold_le z hz)) ?_
    intro x hx
    have hag := (Finset.mem_filter.mp hx).2
    simpa only [domK, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      eval_map_apply, map_add, map_mul] using congrArg φ hag
  have hComp := companion_dvd_of_resultant φ fam Q₁ Q₂ hQ₁ne hQ₁Deg hQ₁Tot hQ₂Deg hQ₂Tot
    (hrootGen Q₂ hQ₂root) (by decide : 16 * 128 + 26 * 335 ≤ EighthRichHeadSafety.cutoff)
  obtain ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, hEach⟩ :=
    two_surface_accounting_simple φ fam hn ht (by decide) (by decide)
      (by decide : 1 ≤ 128) (by decide : 128 < EighthRichHeadSafety.cutoff + 1)
      Q₁ Q₂ hQ₁ne hQ₂ne hQ₁Deg hQ₁Tot hQ₁Wt hQ₂Tot
      (hrootGen Q₁ hQ₁root) hComp eighth_lin_gap hcap
      (char_ok_of_ringChar_gt (by omega : max ((2 * 16 - 2) * (6 * 402653185 - 1)) 16 < ringChar F))
  have hHbd := eighth_rich_head_union_le fam hn ht H hHsub hHrich
  let lFin : Fin 17 := ⟨l, by omega⟩
  let jFin : Fin 17 := ⟨H.card, by omega⟩
  have hAlloc := EighthRichHeadSafety.all_allocations S natDegree labels lFin jFin hHle hSpos hSdeg (by
    intro f hf
    have hfEach := hEach f hf
    have hfPos := hSpos f hf
    have hfLe : f.natDegree ≤ l - H.card := by
      rw [← hSdeg]
      exact Finset.single_le_sum (f := natDegree) (fun _ _ => Nat.zero_le _) hf
    by_cases h1 : f.natDegree ≤ 1
    · simp only [h1, ↓reduceIte] at hfEach
      have hfEq : f.natDegree = 1 := by omega
      rw [hfEq]
      exact hfEach.trans (eighth_linear_price_le lFin jFin hHle)
    · simp only [h1, ↓reduceIte] at hfEach
      let bFin : Fin 17 := ⟨f.natDegree, by omega⟩
      exact hfEach.trans (eighth_logDeriv_le_price lFin jFin bFin hHle (by dsimp [bFin]; omega)
        (by dsimp [bFin, lFin, jFin]; omega)))
  dsimp only [lFin, jFin] at hAlloc
  omega

/-- End-to-end rate-`1/8` (`e = 671,088,639`) safety and `mcaDeltaStar ≥ 671,088,640 / 2^30` on
every injective length-`2^30` domain and every positive interleaving width. -/
theorem eighth_safety (hcap : NonlinearComponentCap logDerivPrice)
    (dom : I ↪ F) (hn : Fintype.card I = 2 ^ 30)
    (hF : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card F)
    (hchar : (2 * 16 - 2) * (6 * 402653185 - 1) < ringChar F)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (2 ^ 27) : Set (I → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((671088639 : ℝ≥0) / (2 ^ 30 : ℕ)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 ∧
      ((671088640 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) := by
  refine safety_of_badCount_le (k := 2 ^ 27) (e := 671088639) (by decide) (by decide) dom hn hF ?_ width
  intro u
  have ht : 402653185 ≤ ⌈(1 - ((671088639 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ)) * (Fintype.card I : ℝ≥0)⌉₊ := by
    rw [agreement_ceiling_of_card_eq hn (by decide)]; decide
  exact eighth_badCount_le hcap _ hn ht hchar

end RateEighth

#print axioms safety_of_badCount_le
#print axioms eighth_rich_head_union_le
#print axioms eighth_badCount_le
#print axioms eighth_safety

end ArkLib.ProximityGap.Frontier.SecondPrimeEighthAssembly
