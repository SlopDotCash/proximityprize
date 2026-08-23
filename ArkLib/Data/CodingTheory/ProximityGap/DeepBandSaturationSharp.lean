/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentSharp
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSaturationDischarge
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentEps

/-!
# The SHARP saturation law — the deep condition relaxed by a factor `q` (#389)

`DeepBandSaturationDischarge.deep_band_saturation_*` discharges the moment budget from
two binomial conditions using the *crude* deep-stratum fiber `q^(M−m)`.  The sharp
second moment (`DeepBandSecondMomentSharp.sum_N2_le_sharp`, from the unconditional
deep-stratum rank `≥ m+1`) replaces the deep term's fiber by `q^(M−(m+1))` — a factor
`q` smaller.  This file discharges the **sharp** budget by the same optimal choice
`L := 2⌊P/q^(m+1)⌋`, `W := q/8`, yielding the saturation law under a deep condition
that is **a factor `q` weaker** — covering a factor-`q` deeper into the band hierarchy:

> **`deep_band_saturation_sharp_count`** — at every band-`m` radius, every domain: if
> `8·q^(m+1) ≤ C(n,t)` (`H1`) and **`4·C(t,k+1)·C(n−k−1,m)·q^m ≤ C(n,t)`** (`H2'`, the
> sharp condition, `q×` weaker than the crude `…·q^(m+1) ≤ …`), then some stack carries
> `≥ q/8` bad scalars — `ε_mca(RS[F,dom,k], δ) ≥ (q/8)/q`, with the ledger bracket.

`t = k+m+1`.  Same constant `q/8`, strictly wider applicability.  Honest scope: this
extends the *constant-mass failure region* one factor `q` deeper toward Johnson; the
window-interior pin remains the open list-decoding core.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The sharp saturation arithmetic.**  With `A = q^(m+1)`, `B = q^(2m+1)`
(`q·B = A²`), `s = P/A`, `W = q/8`: the **sharp** budget
`P² + Ddeep + P·A + (2s)²·W·B ≤ 2·(2s)·P·A` holds whenever `8A ≤ P` and
`4·Ddeep ≤ P²` — the deep term `Ddeep` enters with no `A` factor (the `q×` saving). -/
theorem saturation_arith_sharp {P A B q Ddeep s W : ℕ}
    (hA : 0 < A) (hqB : q * B = A * A) (hs : s = P / A) (hW : W = q / 8)
    (h1 : 8 * A ≤ P) (h2 : 4 * Ddeep ≤ P * P) :
    P * P + Ddeep + P * A + (2 * s) ^ 2 * W * B ≤ 2 * (2 * s) * P * A := by
  have hPdecomp : A * s + P % A = P := by
    rw [hs]; exact Nat.div_add_mod P A
  set r : ℕ := P % A with hrdef
  have hrA : r < A := Nat.mod_lt P hA
  have hs8 : 8 ≤ s := by
    rw [hs]; exact (Nat.le_div_iff_mul_le hA).mpr (by omega)
  have h8W : 8 * W ≤ q := by
    rw [hW, mul_comm]; exact Nat.div_mul_le_self q 8
  have hWB : 8 * W * B ≤ A * A := by
    calc 8 * W * B ≤ q * B := Nat.mul_le_mul_right B h8W
      _ = A * A := hqB
  have hPzNat : P = A * s + r := by omega
  zify at h2 hWB ⊢
  have hPz : (P : ℤ) = A * s + r := by exact_mod_cast hPzNat
  have hrz : (r : ℤ) < (A : ℤ) := by exact_mod_cast hrA
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  have hsz : (8 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs8
  have hAz : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA
  have hDd0 : (0 : ℤ) ≤ (Ddeep : ℤ) := Int.natCast_nonneg Ddeep
  rw [hPz] at h2 ⊢
  have hAAs : (0 : ℤ) ≤ A * A * s := by positivity
  have t3 : (8 : ℤ) * (A * A * s) ≤ s * (A * A * s) :=
    mul_le_mul_of_nonneg_right hsz hAAs
  have t4 : (4 : ℤ) * (s * s) * (8 * W * B) ≤ 4 * (s * s) * (A * A) := by
    refine mul_le_mul_of_nonneg_left hWB ?_; positivity
  nlinarith [t3, t4, h2, hsz, hAz, hr0, hDd0,
    mul_nonneg (mul_nonneg hAz.le hAz.le)
      (mul_nonneg (Int.natCast_nonneg s) (Int.natCast_nonneg s)),
    mul_nonneg (mul_nonneg hAz.le (Int.natCast_nonneg s)) hr0,
    mul_nonneg hAz.le hr0, mul_nonneg (Int.natCast_nonneg s) hr0]

open Classical in
/-- **THE SHARP SATURATION LAW (count form).**  At every band-`m` radius, every
evaluation domain: if `8·q^(m+1) ≤ C(n,k+m+1)` and the **sharp** deep condition
`4·C(k+m+1,k+1)·C(n−(k+1),m)·q^m ≤ C(n,k+m+1)` holds (a factor `q` weaker than the
crude condition), some stack carries at least `q/8` bad scalars. -/
theorem deep_band_saturation_sharp_count (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ m ≤ n.choose (k + m + 1)) :
    ∃ Q₀ : F[X],
      (Fintype.card F) / 8
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card := by
  classical
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set P : ℕ := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card with hP
  have hPchoose : P = n.choose (k + m + 1) := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  set A : ℕ := q ^ (m + 1) with hAdef
  set B : ℕ := q ^ (2 * m + 1) with hBdef
  have hA : 0 < A := pow_pos (by omega) _
  have hqB : q * B = A * A := by
    rw [hAdef, hBdef, ← pow_add, ← pow_succ']; congr 1; omega
  set s : ℕ := P / A with hsdef
  set L : ℕ := 2 * s with hLdef
  set W : ℕ := q / 8 with hWdef
  set V : ℕ := L ^ 2 * W with hVdef
  set MM : ℕ := 2 * (k + m + 1) with hMdef
  set Cb : ℕ := (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m with hCb
  have hDD := deepPairs_card_le (n := n) k m
  set DD : ℕ := (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
      (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) with hDDdef
  have hDb : DD ≤ P * Cb := hDD
  -- the SHARP deep term: Ddeep := DD · q^m, condition 4·Ddeep ≤ P²
  set Ddeep : ℕ := DD * q ^ m with hDdeep
  have h2' : 4 * Ddeep ≤ P * P := by
    calc 4 * Ddeep = 4 * (DD * q ^ m) := by rw [hDdeep]
      _ ≤ 4 * ((P * Cb) * q ^ m) := by
          refine Nat.mul_le_mul_left 4 ?_
          exact Nat.mul_le_mul_right (q ^ m) hDb
      _ = P * (4 * Cb * q ^ m) := by ring
      _ ≤ P * P := by
          refine Nat.mul_le_mul_left P ?_
          rw [hPchoose, hCb]; exact H2
  have H1' : 8 * A ≤ P := by rw [hPchoose, hAdef]; exact H1
  have key := saturation_arith_sharp (B := B) (Ddeep := Ddeep) (s := s) (W := W)
    hA hqB hsdef hWdef H1' h2'
  -- assemble the sharp budget
  have hnum : P ^ 2 * q ^ (MM - (2 * m + 1))
        + DD * q ^ (MM - (m + 1)) + P * q ^ (MM - m) + V * q ^ MM
      ≤ 2 * L * (P * q ^ (MM - m)) := by
    set base := q ^ (2 * k + 1) with hbasedef
    have e1 : q ^ (MM - (2 * m + 1)) = base := by rw [hbasedef]; congr 1; omega
    have e2 : q ^ (MM - m) = base * A := by
      rw [hbasedef, hAdef, ← pow_add]; congr 1; omega
    have e2b : q ^ (MM - (m + 1)) = base * q ^ m := by
      rw [hbasedef, ← pow_add]; congr 1; omega
    have e3 : q ^ MM = base * B := by
      rw [hbasedef, hBdef, ← pow_add]; congr 1; omega
    rw [e1, e2, e2b, e3]
    calc P ^ 2 * base + DD * (base * q ^ m) + P * (base * A) + V * (base * B)
        = base * (P * P + Ddeep + P * A + V * B) := by
          rw [hDdeep, sq]; ring
      _ ≤ base * (2 * L * P * A) := by
          refine Nat.mul_le_mul_left base ?_
          calc P * P + Ddeep + P * A + V * B
              = P * P + Ddeep + P * A + (2 * s) ^ 2 * W * B := by rw [hVdef, hLdef]
            _ ≤ 2 * (2 * s) * P * A := key
            _ = 2 * L * P * A := by rw [hLdef]
      _ = 2 * L * (P * (base * A)) := by ring
  -- run the sharp machine; reduce ΣN₁ to P·q^(MM−m) via sum_N1_eq
  have hN1 := sum_N1_eq dom k m (M := MM) (by omega)
  have hsumN1 : (∑ c : Fin MM → F,
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => IsCoherent dom k m T (genPoly c))).card) = P * q ^ (MM - m) := by
    have hqm : q ^ MM = q ^ (MM - m) * q ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [hqm, ← mul_assoc] at hN1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) m) hN1
  obtain ⟨Q₀, hV⟩ := deep_band_badSet_card_of_moments_sharp dom hk hhi
    (by omega : 2 * (k + m + 1) ≤ MM) (by rw [hsumN1]; exact hnum)
  refine ⟨Q₀, ?_⟩
  have hs8 : 8 ≤ s := by
    rw [hsdef]; exact (Nat.le_div_iff_mul_le hA).mpr (by omega)
  have hL2pos : 0 < L ^ 2 := by rw [hLdef]; positivity
  refine Nat.le_of_mul_le_mul_right ?_ hL2pos
  calc W * L ^ 2 = V := by rw [hVdef]; ring
    _ ≤ _ := hV

open Classical in
/-- **THE SHARP SATURATION LAW (`ε_mca` form).** -/
theorem deep_band_saturation_sharp_eps (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ m ≤ n.choose (k + m + 1)) :
    (((Fintype.card F) / 8 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  classical
  obtain ⟨Q₀, hcount⟩ := deep_band_saturation_sharp_count dom hk hhi H1 H2
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    ![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k]
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)) ?_
  · refine le_trans ?_ h
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast hcount
  · intro γ hγ
    exact (Finset.mem_filter.mp hγ).2

open Classical in
/-- **THE SHARP SATURATION LAW (`δ*` ledger form).** -/
theorem deep_band_saturation_sharp_deltaStar (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ m ≤ n.choose (k + m + 1))
    {εstar : ℝ≥0∞}
    (hε : εstar < (((Fintype.card F) / 8 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hε (deep_band_saturation_sharp_eps dom hk hhi H1 H2))

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.saturation_arith_sharp
#print axioms ProximityGap.PairRank.deep_band_saturation_sharp_count
#print axioms ProximityGap.PairRank.deep_band_saturation_sharp_deltaStar
