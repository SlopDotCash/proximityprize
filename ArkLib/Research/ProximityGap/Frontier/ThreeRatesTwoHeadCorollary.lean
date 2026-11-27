/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DoubleQuadraticThreshold
import ArkLib.Research.ProximityGap.Frontier.SmoothTwoHeadProduction

/-! # Exact two-head error curves at rates 1/4, 1/8, and 1/16

Direct corollary of `DoubleQuadraticThreshold` and `SmoothTwoHeadProduction` matching the exact
statement and production endpoint table of `docs/research/proximity-gap/three-rates-two-head-window.md`:
for `16 ∣ n`, `2^30 ≤ n`, `n / 16 ≤ k ≤ n / 4`, and every finite field of characteristic `> 2n`,
every injective `n`-point domain has exact worst-case MCA numerator `2 (e + 1)` throughout
`E ≤ e ≤ U` and exact operational radius `⌊B / 2⌋ / n` for every budget `2E ≤ B ≤ 2(U + 1) + 1`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ThreeRatesTwoHeadCorollary

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open _root_.ProximityGap.DoubleQuadraticThreshold
open ArkLib.ProximityGap.Frontier ProximityPrize
open scoped NNReal ENNReal

/-- Lower endpoint `E = ⌈(n - k) / 2⌉` of the exact two-head error interval. -/
def lowerErr (n k : ℕ) : ℕ := (n - k + 1) / 2

/-- Minimum agreement count `T = ⌊(n + 3(k - 1) + 4) / 3⌋ + 1` in the written statement. -/
def minAgree (n k : ℕ) : ℕ := (n + 3 * (k - 1) + 4) / 3 + 1

/-- Upper endpoint `U = n - T` of the exact two-head error interval. -/
def upperErr (n k : ℕ) : ℕ := n - minAgree n k

theorem agreements_le_minAgree (n k : ℕ) : agreements n k ≤ minAgree n k := by
  unfold agreements minAgree
  have hm : margin n k ≤ 5 := margin_le_five n k
  omega

private theorem ringChar_le_card (F : Type) [Field F] [Fintype F] :
    ringChar F ≤ Fintype.card F := by
  have hz : ((Fintype.card F : ℕ) : F) = 0 := by
    rw [← nsmul_one]
    exact card_nsmul_eq_zero
  have hdvd : ringChar F ∣ Fintype.card F :=
    (CharP.cast_eq_zero_iff F (ringChar F) (Fintype.card F)).mp hz
  exact Nat.le_of_dvd Fintype.card_pos hdvd

private theorem natCast_ne_zero_of_lt_ringChar {F : Type} [Field F]
    {i : ℕ} (hi : 0 < i) (hlt : i < ringChar F) : (i : F) ≠ 0 := by
  intro hz
  have hdvd : ringChar F ∣ i := (CharP.cast_eq_zero_iff F (ringChar F) i).mp hz
  have hle : ringChar F ≤ i := Nat.le_of_dvd hi hdvd
  omega

variable {F : Type} [Field F] [Fintype F]

/-- Exact worst-case MCA probability `2(e + 1) / |F|` for `E ≤ e ≤ U` over any finite field
of characteristic `> 2n`, at every positive interleaving width. -/
theorem exact_mass {n k e : ℕ} [NeZero n] (x : Fin n ↪ F)
    (h16 : 16 ∣ n) (hn : 2 ^ 30 ≤ n) (hkLo : n / 16 ≤ k) (hkHi : k ≤ n / 4)
    (hchar : 2 * n < ringChar F)
    (heLo : lowerErr n k ≤ e) (heHi : e ≤ upperErr n k)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((e : ℝ≥0) / n) = ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  dsimp only
  rw [epsMCA_interleaved_eq]
  have hT : agreements n k ≤ minAgree n k := agreements_le_minAgree n k
  have hcard : ringChar F ≤ Fintype.card F := ringChar_le_card F
  unfold lowerErr at heLo
  unfold upperErr minAgree at heHi
  unfold minAgree at hT
  have hmass := DoubleQuadraticThreshold.exact_mass (k := k) (e := e) x
    (hk := by omega) (rate := by omega) (large := by omega)
    (pack := by omega) (pin := by omega) (enough := by omega)
    (hchar := fun i hi hb => natCast_ne_zero_of_lt_ringChar hi (by omega))
  rwa [min_eq_right (by omega : 2 * (e + 1) ≤ Fintype.card F)] at hmass

/-- Exact first failure `⌊B / 2⌋` and operational radius `⌊B / 2⌋ / n` for every integer budget
`2E ≤ B ≤ 2(U + 1) + 1`, over any finite field of characteristic `> 2n` and any positive width. -/
theorem classification {n k Q B : ℕ} [NeZero n] (x : Fin n ↪ F)
    (h16 : 16 ∣ n) (hn : 2 ^ 30 ≤ n) (hkLo : n / 16 ≤ k) (hkHi : k ≤ n / 4)
    (hchar : 2 * n < ringChar F)
    (hQ : 2 ≤ Q) (hB : Fintype.card F / Q = B)
    (hBLo : 2 * lowerErr n k ≤ B) (hBHi : B ≤ 2 * (upperErr n k + 1) + 1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let ε := 1 / (Q : ℝ≥0∞)
    let bound := ((B / 2 : ℕ) : ℝ≥0) / n
    mcaDeltaStar (F := F) C ε = bound ∧ ∀ δ, epsMCA (F := F) C δ ≤ ε ↔ δ < bound := by
  classical
  have hT : agreements n k ≤ minAgree n k := agreements_le_minAgree n k
  unfold lowerErr at hBLo
  unfold upperErr minAgree at hBHi
  unfold minAgree at hT
  exact DoubleQuadraticThreshold.classification (j := B / 2) x hQ (by rw [hB])
    (hk := by omega) (rate := by omega) (large := by omega)
    (pack := by omega) (pin := by omega) (prev := by omega)
    (hchar := fun i hi hb => natCast_ne_zero_of_lt_ringChar hi (by omega)) width

/-- Exact reindexed version on an arbitrary finite domain `I` of cardinality `n`. -/
theorem exact_mass_domain {I : Type} [Fintype I] {n k e : ℕ} [NeZero n]
    (D : I ↪ F) (hcardI : Fintype.card I = n)
    (h16 : 16 ∣ n) (hn : 2 ^ 30 ≤ n) (hkLo : n / 16 ≤ k) (hkHi : k ≤ n / 4)
    (hchar : 2 * n < ringChar F)
    (heLo : lowerErr n k ≤ e) (heHi : e ≤ upperErr n k)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width)
    epsMCA (F := F) C ((e : ℝ≥0) / n) = ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  have : Nonempty I := Fintype.card_pos_iff.mp (hcardI ▸ Nat.pos_of_ne_zero (NeZero.ne n))
  dsimp only
  let eqv := (Fintype.equivFinOfCardEq hcardI).symm
  let x : Fin n ↪ F := eqv.toEmbedding.trans D
  have h := exact_mass x h16 hn hkLo hkHi hchar heLo heHi width
  dsimp only at h
  rw [epsMCA_interleaved_eq] at h ⊢
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv x D (fun _ => rfl)]
  exact h

/-- Exact reindexed classification on an arbitrary finite domain `I` of cardinality `n`. -/
theorem classification_domain {I : Type} [Fintype I] {n k Q B : ℕ} [NeZero n]
    (D : I ↪ F) (hcardI : Fintype.card I = n)
    (h16 : 16 ∣ n) (hn : 2 ^ 30 ≤ n) (hkLo : n / 16 ≤ k) (hkHi : k ≤ n / 4)
    (hchar : 2 * n < ringChar F)
    (hQ : 2 ≤ Q) (hB : Fintype.card F / Q = B)
    (hBLo : 2 * lowerErr n k ≤ B) (hBHi : B ≤ 2 * (upperErr n k + 1) + 1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width)
    let ε := 1 / (Q : ℝ≥0∞)
    let bound := ((B / 2 : ℕ) : ℝ≥0) / n
    mcaDeltaStar (F := F) C ε = bound ∧ ∀ δ, epsMCA (F := F) C δ ≤ ε ↔ δ < bound := by
  classical
  have : Nonempty I := Fintype.card_pos_iff.mp (hcardI ▸ Nat.pos_of_ne_zero (NeZero.ne n))
  dsimp only
  let eqv := (Fintype.equivFinOfCardEq hcardI).symm
  let x : Fin n ↪ F := eqv.toEmbedding.trans D
  have h := classification x h16 hn hkLo hkHi hchar hQ hB hBLo hBHi width
  dsimp only at h
  rw [mcaDeltaStar_interleaved_eq] at h ⊢
  simp_rw [epsMCA_interleaved_eq] at h ⊢
  rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv x D (fun _ => rfl)]
  simp_rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv x D (fun _ => rfl)]
  exact h

/-- Literal endpoint table at length `n = 2^30` for rates `1/4`, `1/8`, and `1/16` from
`docs/research/proximity-gap/three-rates-two-head-window.md`. -/
theorem production_endpoints :
    (lowerErr (2 ^ 30) (2 ^ 28), upperErr (2 ^ 30) (2 ^ 28), 2 * (upperErr (2 ^ 30) (2 ^ 28) + 1) + 1) =
      (402653184, 447392426, 894784855) ∧
    (lowerErr (2 ^ 30) (2 ^ 27), upperErr (2 ^ 30) (2 ^ 27), 2 * (upperErr (2 ^ 30) (2 ^ 27) + 1) + 1) =
      (469762048, 581610154, 1163220311) ∧
    (lowerErr (2 ^ 30) (2 ^ 26), upperErr (2 ^ 30) (2 ^ 26), 2 * (upperErr (2 ^ 30) (2 ^ 26) + 1) + 1) =
      (503316480, 648719018, 1297438039) := by
  decide

/-- Smooth length-`2^30` 128-bit production corollary at rates `1/4`, `1/8`, and `1/16`
(including finite extension fields, via `SmoothTwoHeadProduction.curve` and `rank_answer`). -/
theorem smooth_production_window [DecidableEq F] {I : Type} [Fintype I] [Nonempty I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2 ^ 30)
    {k B : ℕ} (hkLo : 2 ^ 26 ≤ k) (hkHi : k ≤ 2 ^ 28) (heven : 2 ∣ k)
    (hB : Fintype.card F / 2 ^ 128 = B)
    (hBHi : B ≤ 2 * (upperErr (2 ^ 30) k + 1) + 1)
    (width : ℕ) [NeZero width] :
    let a := (2 ^ 30 - k) / 2
    let C := (ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width)
    let r := ((SmoothTwoHeadProduction.first a B : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ)
    (mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) = r ∧
      ∀ δ, epsMCA (F := F) C δ ≤ 1 / (2 : ℝ≥0∞) ^ 128 ↔ δ < r) ∧
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val =
      some (SmoothTwoHeadProduction.first a B) := by
  have hT : agreements SmoothTwoHeadProduction.n k ≤ minAgree SmoothTwoHeadProduction.n k :=
    agreements_le_minAgree SmoothTwoHeadProduction.n k
  unfold minAgree SmoothTwoHeadProduction.n at hT
  unfold upperErr minAgree at hBHi
  have hshape : k + 2 * ((2 ^ 30 - k) / 2) = SmoothTwoHeadProduction.n := by
    dsimp [SmoothTwoHeadProduction.n]; omega
  have hlow : SmoothTwoHeadProduction.n < 3 * ((2 ^ 30 - k) / 2) := by
    dsimp [SmoothTwoHeadProduction.n]; omega
  have hcap : agreements SmoothTwoHeadProduction.n k ≤ SmoothTwoHeadProduction.n - B / 2 + 1 := by
    dsimp [SmoothTwoHeadProduction.n]; omega
  have hbound : B / 2 < SmoothTwoHeadProduction.n := by
    dsimp [SmoothTwoHeadProduction.n]; omega
  exact ⟨SmoothTwoHeadProduction.curve D hn (by omega) hshape hlow hB hcap hbound width,
    SmoothTwoHeadProduction.rank_answer D hn (by omega) hshape hlow hB hcap hbound⟩

#print axioms exact_mass
#print axioms classification
#print axioms exact_mass_domain
#print axioms classification_domain
#print axioms production_endpoints
#print axioms smooth_production_window

end ArkLib.ProximityGap.Frontier.ThreeRatesTwoHeadCorollary
