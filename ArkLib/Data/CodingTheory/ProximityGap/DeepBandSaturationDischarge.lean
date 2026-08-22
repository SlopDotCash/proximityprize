/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentEps

/-!
# The deep-band saturation law — budget DISCHARGED (#389, route 2)

The sibling `B5DeepBandSaturation.lean` packages the saturation law *given* the
numeric moment budget as a hypothesis.  This file removes that hypothesis: the
budget is **automatically satisfied** by the optimal choice `L := 2·(P/q^{m+1})`
and `W := q/8` under two clean binomial conditions, proven by the arithmetic
lemma `saturation_arith`.

For `P := C(n,k+m+1)`, `q := |F|`, under

* `H1 : 8·q^{m+1} ≤ P`  (core count clears the value space), and
* `H2 : 4·C(k+m+1,k+1)·C(n−(k+1),m)·q^{m+1} ≤ P`  (deep pairs dominated),

at **every** band-`m` radius and **every** evaluation domain (no smoothness):

  **`ε_mca(RS[F,dom,k], δ) ≥ (q/8)/q`** — constant MCA failure mass,

with the ledger bracket `mcaDeltaStar ≤ δ` for every `ε* < (q/8)/q`.  At `q ≈ n`,
fixed `k ≥ 2`, the conditions clear through the strip of band radii
`capacity − O(m+1)/n` with `(m+k+1)! ≲ n^{k−1}`, and the mass is `Θ(1)` —
against the `poly(n)/q` of every prior construction-based bound, and against
Round 81's `C(n,k+m+1)/(2q^m·C(n,k))` which is vacuous at high rate.

The optimization: at `L ≈ P/q^{m+1}` (twice the mean coherent count per value)
the small-overlap strata contribute `P²/q^{m+1}` (brick-1 exact fiber), the
deep strata `≤ D` (brick-3 binomial bound), and the quadratic loss `L²·W·q^m`
balances at `W = q/8`.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The saturation arithmetic** (the divided budget, per `q^{2k+1}`).
With `A = q^{m+1}`, `B = q^{2m+1}` (so `q·B = A²`), `s = P/A`, `W = q/8`:
the budget `P² + (D+P)·A + (2s)²·W·B ≤ 2·(2s)·P·A` holds whenever `8A ≤ P`
and `4·D·A ≤ P²`. -/
theorem saturation_arith {P A B q D s W : ℕ}
    (hA : 0 < A) (hqB : q * B = A * A) (hs : s = P / A) (hW : W = q / 8)
    (h1 : 8 * A ≤ P) (h2 : 4 * (D * A) ≤ P * P) :
    P * P + (D + P) * A + (2 * s) ^ 2 * W * B ≤ 2 * (2 * s) * P * A := by
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
  rw [hPz] at h2 ⊢
  have t1 : (r : ℤ) * r ≤ r * A := mul_le_mul_of_nonneg_left hrz.le hr0
  have t2 : (r : ℤ) * A ≤ A * A := mul_le_mul_of_nonneg_right hrz.le hAz.le
  have hAAs : (0 : ℤ) ≤ A * A * s := by positivity
  have t3 : (8 : ℤ) * (A * A * s) ≤ s * (A * A * s) :=
    mul_le_mul_of_nonneg_right hsz hAAs
  have t4 : (4 : ℤ) * (s * s) * (8 * W * B) ≤ 4 * (s * s) * (A * A) := by
    refine mul_le_mul_of_nonneg_left hWB ?_; positivity
  nlinarith [t1, t2, t3, t4, h2, hsz, hAz, hr0,
    mul_nonneg (mul_nonneg hAz.le hAz.le)
      (mul_nonneg (Int.natCast_nonneg s) (Int.natCast_nonneg s)),
    mul_nonneg (mul_nonneg hAz.le (Int.natCast_nonneg s)) hr0]

open Classical in
/-- **THE DEEP-BAND SATURATION LAW (count form, budget discharged).**  At every
band-`m` radius, for every evaluation domain: if `8·q^{m+1} ≤ C(n,k+m+1)` and
`4·C(k+m+1,k+1)·C(n−(k+1),m)·q^{m+1} ≤ C(n,k+m+1)`, some stack of the generated
family carries at least `q/8` bad scalars. -/
theorem deep_band_saturation_count (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1)) :
    ∃ Q₀ : F[X],
      (Fintype.card F) / 8
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card := by
  classical
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set P : ℕ := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
    with hP
  have hPchoose : P = n.choose (k + m + 1) := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  set A : ℕ := q ^ (m + 1) with hAdef
  set B : ℕ := q ^ (2 * m + 1) with hBdef
  have hA : 0 < A := pow_pos (by omega) _
  have hqB : q * B = A * A := by
    rw [hAdef, hBdef, ← pow_add, ← pow_succ']
    congr 1; omega
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
  have h2' : 4 * ((P * Cb) * A) ≤ P * P := by
    calc 4 * ((P * Cb) * A) = P * (4 * Cb * A) := by ring
      _ ≤ P * P := by
          refine Nat.mul_le_mul_left P ?_
          rw [hPchoose, hCb, hAdef]; exact H2
  have H1' : 8 * A ≤ P := by rw [hPchoose, hAdef]; exact H1
  have key := saturation_arith (B := B) (D := P * Cb) (s := s) (W := W)
    hA hqB hsdef hWdef H1' h2'
  set base := q ^ (2 * k + 1) with hbasedef
  have e1 : q ^ (MM - (2 * m + 1)) = base := by rw [hbasedef]; congr 1; omega
  have e2 : q ^ (MM - m) = base * A := by
    rw [hbasedef, hAdef, ← pow_add]; congr 1; omega
  have e3 : q ^ MM = base * B := by
    rw [hbasedef, hBdef, ← pow_add]; congr 1; omega
  have hbase_ineq : P * P + (DD + P) * A + V * B ≤ 2 * L * P * A := by
    calc P * P + (DD + P) * A + V * B
        ≤ P * P + ((P * Cb) + P) * A + V * B := by
          refine Nat.add_le_add_right (Nat.add_le_add_left ?_ _) _
          exact Nat.mul_le_mul_right A (Nat.add_le_add_right hDb P)
      _ = P * P + ((P * Cb) + P) * A + (2 * s) ^ 2 * W * B := by
          rw [hVdef, hLdef]
      _ ≤ 2 * (2 * s) * P * A := key
      _ = 2 * L * P * A := by rw [hLdef]
  have hnum : P ^ 2 * q ^ (MM - (2 * m + 1))
        + (DD + P) * q ^ (MM - m) + V * q ^ MM
      ≤ 2 * L * (P * q ^ (MM - m)) := by
    rw [e1, e2, e3]
    calc P ^ 2 * base + (DD + P) * (base * A) + V * (base * B)
        = base * (P * P + (DD + P) * A + V * B) := by ring
      _ ≤ base * (2 * L * P * A) := Nat.mul_le_mul_left base hbase_ineq
      _ = 2 * L * (P * (base * A)) := by ring
  obtain ⟨Q₀, hV⟩ := deep_band_badSet_card_of_moments dom hk hhi
    (by omega : 2 * (k + m + 1) ≤ MM)
    (budget_of_numeric dom k m (by omega) hnum)
  refine ⟨Q₀, ?_⟩
  have hs8 : 8 ≤ s := by
    rw [hsdef]; exact (Nat.le_div_iff_mul_le hA).mpr (by
      have : 8 * A ≤ P := H1'
      omega)
  have hL2pos : 0 < L ^ 2 := by rw [hLdef]; positivity
  refine Nat.le_of_mul_le_mul_right ?_ hL2pos
  calc W * L ^ 2 = V := by rw [hVdef]; ring
    _ ≤ _ := hV

open Classical in
/-- **THE SATURATION LAW (`ε_mca` form, budget discharged).**
`ε_mca(RS[F,dom,k], δ) ≥ (q/8)/q` at every band-`m` radius. -/
theorem deep_band_saturation_eps (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1)) :
    (((Fintype.card F) / 8 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  classical
  obtain ⟨Q₀, hcount⟩ := deep_band_saturation_count dom hk hhi H1 H2
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
/-- **THE SATURATION LAW (`δ*` ledger form, budget discharged).**
`ε* < (q/8)/q  ⟹  mcaDeltaStar(RS[F,dom,k], ε*) ≤ δ` at the band-`m` radius. -/
theorem deep_band_saturation_deltaStar (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (H1 : 8 * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    (H2 : 4 * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m)
        * (Fintype.card F) ^ (m + 1) ≤ n.choose (k + m + 1))
    {εstar : ℝ≥0∞}
    (hε : εstar < (((Fintype.card F) / 8 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hε (deep_band_saturation_eps dom hk hhi H1 H2))

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.saturation_arith
#print axioms ProximityGap.PairRank.deep_band_saturation_count
#print axioms ProximityGap.PairRank.deep_band_saturation_eps
#print axioms ProximityGap.PairRank.deep_band_saturation_deltaStar
