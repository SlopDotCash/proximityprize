/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateFactorDivisibility
import ArkLib.Research.ProximityGap.Frontier.QuarterRateFactorSelection
import ArkLib.Research.ProximityGap.Frontier.QuarterRateQuadraticSafety
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicCharacteristic
import ArkLib.Research.ProximityGap.Frontier.QuarterRateCommonPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface

/-! # Actual quarter-rate MCA safety at 447392427 errors

Factor the degree-three interpolant. A component carrying too many labels to
intersect the degree-two interpolant properly is a common factor. Two distinct
rich secants must then occur, contradicting the saturated overlap bound.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateCompleteSafety
open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry
open scoped NNReal

variable {F I : Type} [Field F] [Finite F] [DecidableEq F] [Fintype I] [Nonempty I]
  {D : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Every actual received pair on an injective domain meets the scalar budget
at the first designated prime's quarter-rate agreement step. -/
theorem family_cap (fam : BadScalarRichPointFamily D 268435456 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1252698792 → (i : F) ≠ 0) : fam.G.card ≤ 1073741824 := by
  classical
  let _ := Fintype.ofFinite F
  by_contra! big
  obtain ⟨a,b,ha,hb,roots⟩ := QuarterRateRichSecants.shared_equations fam hn ht.ge
  obtain ⟨val, triangle⟩ := QuarterRateSharedResultant.surface_bounds b
  have scalar (j : ℕ) : ((surface b).coeff j).natDegree ≤ 16 := by
    by_cases hj : (surface b).coeff j = 0
    · simp [hj]
    · have := triangle j hj
      omega
  let φ := RingHom.id F
  obtain ⟨P,E,hP,hprim,hPB,hdegree,_,exc,rest⟩ :=
    SecondPrimePrimitiveSurface.primitive_surface φ (surface_ne_zero hb) fam.G fam.q 16 scalar
      (fun z hz => by simpa only [φ, RingHom.id_apply, surface_eval] using (roots z hz).2)
  obtain ⟨U,factors,sumdeg,_,covered⟩ := SecondPrimePrimitiveSurface.factor_cover P hP hprim
  let pop := QuarterRateCommonPopulation.population fam φ
  have mem (f : F[X][X][X]) (z : F) : z ∈ pop f ↔ z ∈ fam.G ∧
      f.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    simp only [pop, QuarterRateCommonPopulation.population, φ, RingHom.id_apply,
      Polynomial.map_id, mem_filter]
  have cover (z : F) (hz : z ∈ fam.G) : z ∈ E ∨ ∃ f ∈ U, z ∈ pop f := by
    by_cases he : z ∈ E
    · exact Or.inl he
    · obtain ⟨f,hf,hit⟩ := covered z (fam.q z) (rest z hz he)
      exact Or.inr ⟨f,hf,(mem f z).mpr ⟨hz,hit⟩⟩
  let H := {l : LineParameter F // l ∈ lineParameters fam}
  let points (l : H) := pointsOn fam l.1
  have cap (l : H) : (points l).card ≤ 447392428 :=
    TwoLargeCoreCount.line_occupancy_le fam (t := 626349397) (e := 447392427) hn ht l.2
  have capture (f : F[X][X][X]) (hf : f ∈ U) (L : Finset F)
      (hLG : L ⊆ fam.G) (hLF : L ⊆ pop f) (hL : f.natDegree * 268435458 + 32 < L.card) :
      ∃ l : H, L ⊆ points l := by
    obtain ⟨irr, pos, dvdP⟩ := factors f hf
    have dvdB := dvdP.trans hPB
    have dvdA := QuarterRateFactorDivisibility.divides hb f irr pos dvdB L fam.q
      (fun z hz => (roots z (hLG hz)).1) (fun z hz => ((mem f z).mp (hLF hz)).2) hL
    have hbig : 263 < (pop f).card := by
      have := card_le_card hLF
      omega
    obtain ⟨l,hl,hp⟩ := QuarterRateCommonPopulation.head_of_large_population fam φ a b
      ha hb f irr pos dvdA dvdB hn ht.ge hchar hbig
    exact ⟨⟨l,hl⟩,hLF.trans hp⟩
  obtain ⟨p,q,hpq,rp,rq⟩ := QuarterRateFactorSelection.two_heads
    fam.G E U Polynomial.natDegree pop points big exc (sumdeg.le.trans (hdegree.le.trans val))
    (fun f hf => (factors f hf).2.1) cover cap capture
  apply big.not_ge
  exact QuarterRateRichSecants.two_rich_cap fam hn ht p.1 q.1 p.2 q.2
    (fun he => hpq (Subtype.ext he)) (rp.trans (card_le_card inter_subset_right))
    (rq.trans (card_le_card inter_subset_right))

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

/-- At 447392427 errors, at most one length's worth of scalars is bad on any
received pair. The normalized bound holds on every injective evaluation domain. -/
theorem predecessor_eps {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]
    (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1252698792 → (i : F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code D 268435456 : Set (I → F))
      ((447392427 : ℝ≥0) / Fintype.card I) ≤ (1073741824 : ℝ≥0∞) / Fintype.card F := by
  classical
  apply epsMCA_le_of_badCount_le
  intro u
  let δ : ℝ≥0 := 447392427 / Fintype.card I
  let fam := canonicalBadScalarRichPointFamily D δ u (by decide : 1 ≤ 268435456)
  change fam.G.card ≤ 1073741824
  apply family_cap fam hn _ hchar
  have hc : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  dsimp only [δ]
  rw [tsub_mul, one_mul, div_mul_cancel₀ _ hc, hn]
  norm_num

/-- Every positive width is safe through 447392427 errors for a smooth length-
two-to-the-thirtieth domain in a sponsor-size field with budget at least the length. -/
theorem smooth_safe {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    (hq : Fintype.card F < 2 ^ 256) (hB : 1073741824 ≤ Fintype.card F / 2 ^ 128)
    (m : ℕ) [NeZero m] {δ : ℝ≥0} (hδ : δ ≤ 447392427 / 1073741824) :
    epsMCA (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m)) δ ≤
      (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  classical
  have hp := SmoothCubicCharacteristic.characteristic D hn hq
  have mass := predecessor_eps D hn (by
    intro i hi hj hc
    have := Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff F (ringChar F) i).mp hc)
    omega)
  rw [hn] at mass
  rw [epsMCA_interleaved_eq]
  exact ((epsMCA_mono _ hδ).trans mass).trans
    (natCast_div_le_inv_of_mul_le (Q := 2 ^ 128) (by decide) Fintype.card_pos
      ((Nat.le_div_iff_mul_le (by decide)).mp hB))

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterCanonicalCodeBridge P1RateQuarterScaleArithmetic

local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

/-- The first designated prime's quarter-rate first failing count lies in the
closed interval from 447392428 to 480946859. -/
theorem named_bracket :
    let radius := mcaDeltaStar (F := ZMod P) canonicalCode ((((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹)
    (447392428 : ℝ≥0) / 1073741824 ≤ radius ∧ radius ≤ 480946859 / 1073741824 := by
  dsimp only
  refine ⟨?_, QuarterRateApolarBracket.named_bracket.2⟩
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 447392428)
    (by decide) (by decide : 447392428 ≤ N)
  change epsMCA (F := ZMod P) canonicalCode ((447392427 : ℝ≥0) / N) ≤ _
  have mass := predecessor_eps canonicalDomain (Fintype.card_fin _) (by
    intro i hi hj hc
    have hP : 1252698792 < P := by decide
    exact (lt_of_le_of_lt hj hP).not_ge
      (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod P) P i).mp hc)))
  rw [Fintype.card_fin, ZMod.card] at mass
  exact mass.trans (natCast_div_le_inv_of_mul_le (Q := 2 ^ 128) (by decide) prime_P.pos (by decide))

end ArkLib.ProximityGap.Frontier.QuarterRateCompleteSafety
