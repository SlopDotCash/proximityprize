/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeEighthAssembly
import ArkLib.Research.ProximityGap.Frontier.QuarterCoreWeightedJets

/-! # End-to-end second-prime MCA safety assembly at rates 1/4, 1/2, and all three rates (Packet L4c)

Wires `TwoSurfaceFactorAccounting`, `SecondPrimeEighthAssembly`, `QuarterCoreWeightedJets`, and
`HalfSuccessorJetInterpolation` into end-to-end `epsMCA` and `mcaDeltaStar` theorems at length
`n = 2^30`, conditional only on `NonlinearComponentCap logDerivPrice`:
1. Rate `1/8`: `e = 671,088,639` safe (`mcaDeltaStar ≥ 671,088,640 / 2^30`).
2. Rate `1/4`: `e = 525,150,000` safe (`mcaDeltaStar ≥ 525,150,001 / 2^30`).
3. Rate `1/2`: `e = 306,780,000` safe (`mcaDeltaStar ≥ 306,780,001 / 2^30`).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SecondPrimeRatesAssembly

open Finset Polynomial Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting
open ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree
open ArkLib.ProximityGap.Frontier.SecondPrimeEighthAssembly
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open scoped NNReal ENNReal

/-! ## Window 2: Second-prime rate 1/4 (`e = 525,150,000`) -/

section RateQuarter

private theorem quarter_logDeriv_le_price :
    ∀ l j b : Fin 23, j.val ≤ l.val → 2 ≤ b.val → b.val ≤ l.val - j.val →
      max 2051368
        (logDerivPrice QuarterCoreWeightedJets.n QuarterCoreWeightedJets.d QuarterCoreWeightedJets.t
          (11 * QuarterCoreWeightedJets.t - 1 - (l.val - b.val) * QuarterCoreWeightedJets.d)
          (min (379 - j.val) (if 3 ≤ j.val then 301 else 379)) b.val) ≤
        QuarterCoreWeightedJets.price l.val j.val b.val := by
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 2500000 in
  decide

private theorem quarter_linear_price_le :
    ∀ l j : Fin 23, j.val ≤ l.val →
      2051368 ≤ QuarterCoreWeightedJets.price l.val j.val 1 := by
  decide

private theorem quarter_lin_gap :
    (379 * (2051368 + 1 - 379) + 3 * (2051368 + 1) * (379 - 1)) * QuarterCoreWeightedJets.n <
      (2051368 + 1) * (2051368 + 1 - 379) *
        (QuarterCoreWeightedJets.t - QuarterCoreWeightedJets.d) := by
  decide

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Rate-`1/4` (`e = 525,150,000`) bad-scalar family cap `≤ 2^31` conditional on
`NonlinearComponentCap logDerivPrice`. -/
theorem quarter_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 548591824 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : (2 * 22 - 2) * (11 * 548591824 - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  have : Infinite (RatFunc F) := ratFunc_infinite F
  let φ := ratFuncHom F
  let domK : I ↪ RatFunc F := dom.trans ⟨φ, φ.injective⟩
  obtain ⟨Q₁, hQ₁ne, hQ₁supp, hQ₁root⟩ := QuarterCoreWeightedJets.ordinary_surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn false
  obtain ⟨Q₂, hQ₂ne, hQ₂supp, hQ₂root⟩ := QuarterCoreWeightedJets.ordinary_surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn true
  simp only [Bool.false_eq_true, ↓reduceIte] at hQ₁supp hQ₂supp
  obtain ⟨hQ₁Deg, hQ₁Tot, hQ₁Wt⟩ := surface_bounds_of_support hQ₁supp
  obtain ⟨hQ₂Deg, hQ₂Tot, _⟩ := surface_bounds_of_support hQ₂supp
  have hrootGen (Q : (RatFunc F)[X][X][X])
      (hQr : ∀ g : RatFunc F, ∀ q : (RatFunc F)[X], q.natDegree ≤ 268435455 →
        ∀ S : Finset I, 548591824 ≤ S.card →
        (∀ x ∈ S, q.eval (domK x) = φ (u 0 x) + g * φ (u 1 x)) →
        Q.eval₂ (evalRingHom (C g)) q = 0) :
      ∀ z ∈ fam.G, Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    intro z hz
    refine hQr (φ z) ((fam.q z).map φ) (natDegree_map_le.trans (by have := fam.degree_lt z hz; omega))
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht.trans (fam.threshold_le z hz)) ?_
    intro x hx
    have hag := (Finset.mem_filter.mp hx).2
    simpa only [domK, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      eval_map_apply, map_add, map_mul] using congrArg φ hag
  have hComp := companion_dvd_of_resultant φ fam Q₁ Q₂ hQ₁ne hQ₁Deg hQ₁Tot hQ₂Deg hQ₂Tot
    (hrootGen Q₂ hQ₂root) (by decide : 22 * 379 + 44 * 21569 ≤ 2051368)
  let extraDeg (H : Finset (LineParameter F)) : ℕ := if 3 ≤ H.card then 301 else 379
  have hExtra : ∀ (H : Finset (LineParameter F)),
      H ⊆ lineParameters fam → (∀ h ∈ H, 2051368 < (pointsOn fam h).card) →
      ∀ (f : (RatFunc F)[X][X][X]) (G : Finset F), Irreducible f → 2 ≤ f.natDegree →
      f ∣ Q₁ → f ∣ Q₂ → G ⊆ fam.G → (∀ h ∈ H, Disjoint G (pointsOn fam h)) →
      2051368 < G.card →
      (∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) →
      TotalDegreeLe f (extraDeg H) := by
    intro H hHsub hHrich f G hIrr hb2 hfQ₁ hfQ₂ hGsub hGdis hGL hGroot
    by_cases h3 : 3 ≤ H.card
    · simp only [extraDeg, h3, ↓reduceIte]
      obtain ⟨L3, hL3inj, hL3mem⟩ := enumerate_finset H h3
      let C3 (i : Fin 3) := jointCore dom (u 0) (u 1) (L3 i).1 (L3 i).2
      have hC3ge (i : Fin 3) : QuarterCoreWeightedJets.c ≤ (C3 i).card :=
        rich_head_core_ge fam hn ht (by decide : 548591824 + 525150000 = 1073741824)
          (by decide : 0 < 2051368) (hHsub (hL3mem i)) (hHrich _ (hL3mem i))
      have hC3pair (i j : Fin 3) (hij : i ≠ j) : (C3 i ∩ C3 j).card ≤ QuarterCoreWeightedJets.d :=
        pairwise_core_inter_le fam (by decide) (hHsub (hL3mem i)) (hHsub (hL3mem j)) (hL3inj.ne hij)
      obtain ⟨Q₃, hQ₃ne, hQ₃supp, hQ₃root⟩ := QuarterCoreWeightedJets.residual_surface domK
        (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) (C3 0) (C3 1) (C3 2) hn
        (hC3ge 0) (hC3ge 1) (hC3ge 2)
        (hC3pair 0 1 (by decide)) (hC3pair 0 2 (by decide)) (hC3pair 1 2 (by decide))
      obtain ⟨hQ₃Deg, hQ₃Tot, _⟩ := surface_bounds_of_support hQ₃supp
      have hQ₃G : ∀ z ∈ G, Q₃.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
        intro z hz
        have hzG := hGsub hz
        have hdegZ : (fam.q z).natDegree ≤ 268435455 := by have := fam.degree_lt z hzG; omega
        have hov (i : Fin 3) : (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ C3 i).card ≤ 268435455 := by
          have hdL := lineParameter_degree_lt fam (hHsub (hL3mem i))
          have hne : fam.q z ≠ (L3 i).1 + C z * (L3 i).2 := by
            intro heq
            exact Finset.disjoint_left.mp (hGdis (L3 i) (hL3mem i)) hz
              ((mem_pointsOn_iff fam (L3 i) z).mpr ⟨hzG, heq⟩)
          exact QuarterCoreWeightedJets.outside_overlap dom (u 0) (u 1) (L3 i).1 (L3 i).2
            (fam.q z) z (C3 i) (fullAgreement dom (u 0) (u 1) z (fam.q z))
            (Nat.le_of_lt_succ hdL.1) (Nat.le_of_lt_succ hdL.2) hdegZ hne
            (fun x hx => (Finset.mem_filter.mp hx).2) (fun x hx => (Finset.mem_filter.mp hx).2)
        refine hQ₃root (φ z) ((fam.q z).map φ) (natDegree_map_le.trans hdegZ)
          (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht.trans (fam.threshold_le z hzG))
          (hov 0) (hov 1) (hov 2) ?_
        intro x hx
        have hag := (Finset.mem_filter.mp hx).2
        simpa only [domK, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          eval_map_apply, map_add, map_mul] using congrArg φ hag
      have hfDeg : f.natDegree ≤ 22 := (natDegree_le_of_dvd hfQ₁ hQ₁ne).trans hQ₁Deg
      have hfTot1 : TotalDegreeLe f 21569 := by
        have hQ₁t := totalDegree_le_of_totalDegreeLe hQ₁Tot
        obtain ⟨R, hR⟩ := hfQ₁
        have hft : Bivariate.totalDegree f ≤ 21569 := by
          rw [hR, Bivariate.totalDegree_mul hIrr.ne_zero (right_ne_zero_of_mul (hR ▸ hQ₁ne))] at hQ₁t
          omega
        exact fun j hj => (totalDegreeLe_self f j hj).trans hft
      have hfQ₃ : f ∣ Q₃ := by
        apply SecondPrimeSectionResultant.divides_of_many_sections φ f Q₃ hIrr (by omega)
          hfTot1 hQ₃Tot G (fun z => (fam.q z).map φ) (fun z hz => ⟨hGroot z hz, hQ₃G z hz⟩)
        have h1 : f.natDegree * 301 ≤ 22 * 301 := Nat.mul_le_mul_right 301 hfDeg
        have h2 : Q₃.natDegree * 21569 ≤ 40 * 21569 := Nat.mul_le_mul_right 21569 hQ₃Deg
        exact (Nat.sub_le _ _).trans_lt (by omega)
      obtain ⟨R, hR⟩ := hfQ₃
      have hQ₃t := totalDegree_le_of_totalDegreeLe hQ₃Tot
      have hft : Bivariate.totalDegree f ≤ 301 := by
        rw [hR, Bivariate.totalDegree_mul hIrr.ne_zero (right_ne_zero_of_mul (hR ▸ hQ₃ne))] at hQ₃t
        omega
      exact fun j hj => (totalDegreeLe_self f j hj).trans hft
    · simp only [extraDeg, h3, ↓reduceIte]
      obtain ⟨R, hR⟩ := hfQ₂
      have hQ₂t := totalDegree_le_of_totalDegreeLe hQ₂Tot
      have hft : Bivariate.totalDegree f ≤ 379 := by
        rw [hR, Bivariate.totalDegree_mul hIrr.ne_zero (right_ne_zero_of_mul (hR ▸ hQ₂ne))] at hQ₂t
        omega
      exact fun j hj => (totalDegreeLe_self f j hj).trans hft
  obtain ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, hEach⟩ :=
    two_surface_accounting φ fam hn ht (by decide) (by decide)
      (by decide : 1 ≤ 379) (by decide : 379 < 2051368 + 1)
      Q₁ Q₂ hQ₁ne hQ₂ne hQ₁Deg hQ₁Tot hQ₁Wt hQ₂Tot
      (hrootGen Q₁ hQ₁root) hComp quarter_lin_gap hcap
      (char_ok_of_ringChar_gt (by omega : max ((2 * 22 - 2) * (11 * 548591824 - 1)) 22 < ringChar F))
      extraDeg hExtra
  have hHbd : (H.biUnion (pointsOn fam)).card ≤ QuarterCoreWeightedJets.headBound H.card := by
    by_cases hlt3 : H.card < 3
    · unfold QuarterCoreWeightedJets.headBound
      simp only [hlt3, ↓reduceIte]
      exact Finset.card_biUnion_le.trans
        ((Finset.sum_le_sum fun h hh =>
          line_occupancy_le_e_add_one fam hn ht (by decide : 548591824 + 525150000 = 1073741824)
            (hHsub hh)).trans_eq (by simp))
    · have hcoreAll : ∀ h ∈ H, QuarterCoreWeightedJets.c ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card :=
        fun h hh => rich_head_core_ge fam hn ht (by decide : 548591824 + 525150000 = 1073741824)
          (by decide : 0 < 2051368) (hHsub hh) (hHrich h hh)
      obtain ⟨a, b, hab, hcoll⟩ := collinear_of_three_core_overflow fam hn H hHsub (by omega) hcoreAll
        QuarterCoreWeightedJets.parameters.2.2.1
      have hcol := collinear_union_cap fam (by decide) hn ht
        (by decide : 548591824 + 525150000 = 1073741824) H hHsub a b hab hcoll hcoreAll
      unfold QuarterCoreWeightedJets.headBound
      simp only [hlt3, ↓reduceIte]
      exact hcol
  let lFin : Fin 23 := ⟨l, by omega⟩
  let jFin : Fin 23 := ⟨H.card, by omega⟩
  have hAlloc := QuarterCoreWeightedJets.allocation S natDegree labels lFin jFin hHle hSpos hSdeg (by
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
      exact hfEach.trans (quarter_linear_price_le lFin jFin hHle)
    · simp only [h1, ↓reduceIte] at hfEach
      let bFin : Fin 23 := ⟨f.natDegree, by omega⟩
      exact hfEach.trans (quarter_logDeriv_le_price lFin jFin bFin hHle (by dsimp [bFin]; omega)
        (by dsimp [bFin, lFin, jFin]; omega)))
  dsimp only [lFin, jFin] at hAlloc
  omega

/-- End-to-end rate-`1/4` (`e = 525,150,000`) safety and `mcaDeltaStar ≥ 525,150,001 / 2^30` on
every injective length-`2^30` domain and every positive interleaving width. -/
theorem quarter_safety (hcap : NonlinearComponentCap logDerivPrice)
    (dom : I ↪ F) (hn : Fintype.card I = 2 ^ 30)
    (hF : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card F)
    (hchar : (2 * 22 - 2) * (11 * 548591824 - 1) < ringChar F)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (2 ^ 28) : Set (I → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((525150000 : ℝ≥0) / (2 ^ 30 : ℕ)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 ∧
      ((525150001 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) := by
  refine safety_of_badCount_le (k := 2 ^ 28) (e := 525150000) (by decide) (by decide) dom hn hF ?_ width
  intro u
  have ht : 548591824 ≤ ⌈(1 - ((525150000 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ)) * (Fintype.card I : ℝ≥0)⌉₊ := by
    rw [agreement_ceiling_of_card_eq hn (by decide)]; decide
  exact quarter_badCount_le hcap _ hn ht hchar

end RateQuarter

/-! ## Window 3: Second-prime rate 1/2 (`e = 306,780,000`) -/

section RateHalf

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

private abbrev halfN : ℕ := 1073741824
private abbrev halfD : ℕ := 536870911
private abbrev halfE : ℕ := 306780000
private abbrev halfT : ℕ := halfN - halfE
private abbrev halfC : ℕ := halfT - 255
private abbrev halfL : ℕ := 9064673

private def halfHeadBound (j : ℕ) : ℕ :=
  if j < 3 then j * (halfE + 1)
  else
    let denom := halfC + (j - 1) * halfD
    let U := (j * halfC ^ 2 + denom - 1) / denom
    min (j * (halfE + 1)) (j * halfN - (j - 1) * U)

private def halfPrice (l j b : ℕ) : ℕ :=
  if b ≤ 1 then halfL
  else max halfL (logDerivPrice halfN halfD halfT (14 * halfT - 1 - (l - b) * halfD) (412 - j) b)

private theorem half_lin_gap :
    (412 * (halfL + 1 - 412) + 3 * (halfL + 1) * (412 - 1)) * halfN <
      (halfL + 1) * (halfL + 1 - 412) * (halfT - halfD) := by
  decide

private theorem half_prices_table : ∀ l j b : Fin 20, j.val ≤ l.val →
    238338 + halfHeadBound j.val ≤ 2147483648 ∧
    (0 < b.val → b.val ≤ l.val - j.val →
      (l.val - j.val) * halfPrice l.val j.val b.val ≤
        b.val * (2147483648 - (238338 + halfHeadBound j.val))) := by
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 2500000 in
  decide

private theorem half_all_allocations {ι : Type*} (S : Finset ι) (deg labels : ι → ℕ)
    (l j : Fin 20) (hj : j.val ≤ l.val) (hpos : ∀ a ∈ S, 0 < deg a)
    (hdeg : ∑ a ∈ S, deg a = l.val - j.val)
    (hcost : ∀ a ∈ S, labels a ≤ halfPrice l.val j.val (deg a)) :
    238338 + halfHeadBound j.val + ∑ a ∈ S, labels a ≤ 2147483648 := by
  have hbase := (half_prices_table l j 0 hj).1
  by_cases hz : l.val - j.val = 0
  · have hemp : S = ∅ := by
      by_contra hne
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) ha
      rw [hdeg, hz] at h1
      exact (hpos a ha).not_ge h1
    simpa [hemp] using hbase
  · apply TangentHeadWindows.sum_prices S deg labels (Nat.pos_of_ne_zero hz) hbase hdeg
    intro a ha
    have h1 := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) ha
    rw [hdeg] at h1
    let b : Fin 20 := ⟨deg a, h1.trans_lt ((Nat.sub_le _ _).trans_lt l.isLt)⟩
    exact (Nat.mul_le_mul_left _ (hcost a ha)).trans ((half_prices_table l j b hj).2 (hpos a ha) h1)

/-- Transparent mixed-Hasse surfaces for the rate-`1/2` (`e = 306,780,000`) window. -/
private theorem half_surfaces {K : Type} [Field K] {ι : Type*} [Fintype ι]
    (dom : ι ↪ K) (u v : ι → K) (hn : Fintype.card ι = halfN) (second : Bool) :
    let r := if second then 27 else 14
    let b := if second then 38 else 19
    let s := if second then 412 else 238338
    ∃ Q : Polynomial (Polynomial K[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * halfD < r * halfT) ∧
      ∀ z : K, ∀ q : K[X], q.natDegree ≤ halfD → ∀ B : Finset ι, halfT ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z * v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  dsimp only
  let r := if second then 27 else 14
  let b := if second then 38 else 19
  let s := if second then 412 else 238338
  have hnum : 0 < r ∧ 0 < halfT ∧ r ≤ s + 1 ∧
      Fintype.card ι * Fintype.card (JetRows s r) < Fintype.card (Monomials s b halfD (r * halfT)) := by
    rw [hn]
    cases second <;>
      simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] <;>
      norm_num [Fin.sum_univ_succ, r, s, b, halfD, halfT, halfN, halfE] <;> decide +kernel
  obtain ⟨c, hc, _, hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  refine ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h, ?_⟩
  intro z q hq B hB hg
  rw [surface_eval]
  exact hf z q hq B hB hg

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Rate-`1/2` (`e = 306,780,000`) bad-scalar family cap `≤ 2^31` conditional on
`NonlinearComponentCap logDerivPrice`. -/
theorem half_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 766961824 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : (2 * 19 - 2) * (14 * 766961824 - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  have : Infinite (RatFunc F) := ratFunc_infinite F
  let φ := ratFuncHom F
  let domK : I ↪ RatFunc F := dom.trans ⟨φ, φ.injective⟩
  obtain ⟨Q₁, hQ₁ne, hQ₁supp, hQ₁root⟩ := half_surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn false
  obtain ⟨Q₂, hQ₂ne, hQ₂supp, hQ₂root⟩ := half_surfaces domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn true
  simp only [Bool.false_eq_true, ↓reduceIte] at hQ₁supp hQ₂supp
  obtain ⟨hQ₁Deg, hQ₁Tot, hQ₁Wt⟩ := surface_bounds_of_support hQ₁supp
  obtain ⟨hQ₂Deg, hQ₂Tot, _⟩ := surface_bounds_of_support hQ₂supp
  have hrootGen (Q : (RatFunc F)[X][X][X])
      (hQr : ∀ z : RatFunc F, ∀ q : (RatFunc F)[X], q.natDegree ≤ 536870911 →
        ∀ B : Finset I, 766961824 ≤ B.card →
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
    (hrootGen Q₂ hQ₂root) (by decide : 19 * 412 + 38 * 238338 ≤ halfL)
  obtain ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, hEach⟩ :=
    two_surface_accounting_simple φ fam hn ht (by decide) (by decide)
      (by decide : 1 ≤ 412) (by decide : 412 < halfL + 1)
      Q₁ Q₂ hQ₁ne hQ₂ne hQ₁Deg hQ₁Tot hQ₁Wt hQ₂Tot
      (hrootGen Q₁ hQ₁root) hComp half_lin_gap hcap
      (char_ok_of_ringChar_gt (by omega : max ((2 * 19 - 2) * (14 * 766961824 - 1)) 19 < ringChar F))
  have hHbd : (H.biUnion (pointsOn fam)).card ≤ halfHeadBound H.card := by
    by_cases hlt3 : H.card < 3
    · unfold halfHeadBound
      simp only [hlt3, ↓reduceIte]
      exact Finset.card_biUnion_le.trans
        ((Finset.sum_le_sum fun h hh =>
          line_occupancy_le_e_add_one fam hn ht (by decide : 766961824 + 306780000 = 1073741824)
            (hHsub hh)).trans_eq (by simp))
    · have hcoreAll : ∀ h ∈ H, halfC ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card := by
        intro h hh
        have h1 := rich_head_core_ge fam hn ht (by decide : 766961824 + 306780000 = 1073741824)
          (by decide : 0 < halfL) (hHsub hh) (hHrich h hh)
        dsimp [halfC, halfT, halfN, halfE, halfL] at h1 ⊢
        omega
      obtain ⟨a, b, hab, hcoll⟩ := collinear_of_three_core_overflow fam hn H hHsub (by omega) hcoreAll
        (by decide)
      have hcol := collinear_union_cap fam (by decide) hn ht
        (by decide : 766961824 + 306780000 = 1073741824) H hHsub a b hab hcoll hcoreAll
      unfold halfHeadBound
      simp only [hlt3, ↓reduceIte]
      exact hcol
  let lFin : Fin 20 := ⟨l, by omega⟩
  let jFin : Fin 20 := ⟨H.card, by omega⟩
  have hAlloc := half_all_allocations S natDegree labels lFin jFin hHle hSpos hSdeg (fun f hf => hEach f hf)
  dsimp only [lFin, jFin] at hAlloc
  omega

/-- End-to-end rate-`1/2` (`e = 306,780,000`) safety and `mcaDeltaStar ≥ 306,780,001 / 2^30` on
every injective length-`2^30` domain and every positive interleaving width. -/
theorem half_safety (hcap : NonlinearComponentCap logDerivPrice)
    (dom : I ↪ F) (hn : Fintype.card I = 2 ^ 30)
    (hF : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card F)
    (hchar : (2 * 19 - 2) * (14 * 766961824 - 1) < ringChar F)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (2 ^ 29) : Set (I → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((306780000 : ℝ≥0) / (2 ^ 30 : ℕ)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 ∧
      ((306780001 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) := by
  refine safety_of_badCount_le (k := 2 ^ 29) (e := 306780000) (by decide) (by decide) dom hn hF ?_ width
  intro u
  have ht : 766961824 ≤ ⌈(1 - ((306780000 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ)) * (Fintype.card I : ℝ≥0)⌉₊ := by
    rw [agreement_ceiling_of_card_eq hn (by decide)]; decide
  exact half_badCount_le hcap _ hn ht hchar

end RateHalf

/-! ## Literal specialization to `PrizeShapePrimeP30Second` -/

section SecondPrimeLiteral

open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance : Fact P.Prime := ⟨prime_P⟩

private theorem second_prime_card_ge : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card (ZMod P) := by
  rw [ZMod.card]; decide

private theorem second_prime_ringChar : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P

/-- Literal `PrizeShapePrimeP30Second` rate `1/8`, `1/4`, and `1/2` MCA lower bounds at every
positive interleaving width, conditional only on `NonlinearComponentCap logDerivPrice`. -/
theorem second_prime_three_rates (hcap : NonlinearComponentCap logDerivPrice)
    (width : ℕ) [NeZero width] :
    let C8 := (evalCode g (2 ^ 30) (2 ^ 27 - 1)) ^⋈ (Fin width)
    let C4 := (evalCode g (2 ^ 30) (2 ^ 28 - 1)) ^⋈ (Fin width)
    let C2 := (evalCode g (2 ^ 30) (2 ^ 29 - 1)) ^⋈ (Fin width)
    ((671088640 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := ZMod P) C8 (1 / (2 : ℝ≥0∞) ^ 128) ∧
    ((525150001 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := ZMod P) C4 (1 / (2 : ℝ≥0∞) ^ 128) ∧
    ((306780001 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := ZMod P) C2 (1 / (2 : ℝ≥0∞) ^ 128) := by
  have hg := KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  let dom := KKH26RegimeSplit.powDomain g orderOf_g hg
  dsimp only
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon g orderOf_g hg (2 ^ 27 - 1),
    KKH26RegimeSplit.evalCode_eq_reedSolomon g orderOf_g hg (2 ^ 28 - 1),
    KKH26RegimeSplit.evalCode_eq_reedSolomon g orderOf_g hg (2 ^ 29 - 1)]
  refine ⟨?_, ?_, ?_⟩
  · exact (eighth_safety hcap dom (Fintype.card_fin _) second_prime_card_ge
      (by rw [second_prime_ringChar]; decide) width).2
  · exact (quarter_safety hcap dom (Fintype.card_fin _) second_prime_card_ge
      (by rw [second_prime_ringChar]; decide) width).2
  · exact (half_safety hcap dom (Fintype.card_fin _) second_prime_card_ge
      (by rw [second_prime_ringChar]; decide) width).2

end SecondPrimeLiteral

#print axioms quarter_badCount_le
#print axioms quarter_safety
#print axioms half_badCount_le
#print axioms half_safety
#print axioms second_prime_three_rates

end ArkLib.ProximityGap.Frontier.SecondPrimeRatesAssembly
