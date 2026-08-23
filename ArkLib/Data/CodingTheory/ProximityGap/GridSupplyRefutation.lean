/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The sheared-grid word: the FIXED-BAND word-capped supply floor (#389)

Companion to the #389 countermodel convergence (`SubplaneSupplyFloor.lean`,
`FrobeniusSubfieldBlowup.lean`, `AffinePlaneSharpness.lean`).  Those witnesses live at
the Johnson-scale band (their cap `2k+m+1 = r` grows like `√n`) or need subfield
structure; this file contributes the two cells they leave open:

1. **The fixed-band word-capped floor.**  The `6×6` sheared-grid word
   (`(i,j) ↦ (i+7j, j)`, abscissae = base-7 digits, so the grid is a word graph and
   shears preserve lines) at `(k, m) = (2, 1)`, `t = 4`, `cap = 6`, `n = 36` lies in
   the exact hypothesis class of `SubJohnsonSupplyResidual gridDom 2 1` — *no* affine
   codeword agrees with it on more than `6` points, proved structurally
   (`grid_word_cap`: a non-constant line meets each constant row at most once; a
   constant one lives in one row).  Yet `subJohnsonSupplyResidual_floor_grid`:
   every valid `B` satisfies `234 ≤ B` — strictly above the partition target
   `⌊n/cap⌋·C(cap,t) = 90` and the mean-degree-law target `(2n/cap)·C(cap,t) = 180`
   (inside the proven unconditional pair-count `C(36,2) = 630`).  The mean-degree
   form `grid_mean_degree_violation`: `22` codewords with agreement `≥ 4` and mass
   `> 2n`, all inside the cap.  So the announced `Σ_c a_c ≤ 2n` law is false *on the
   residual's own hypothesis class*, already at one fixed band.

2. **The prime-field additive mechanism.**  The grid is a rank-2 generalized
   arithmetic progression: the construction transfers verbatim (ℤ-collinearity) to
   `F_p` for EVERY prime `p > 2N³` — including subfield-free production primes
   (M31/BabyBear/Goldilocks) where the subplane and Frobenius mechanisms vanish.
   Asymptotically (family-capped, `N ≥ cap`) it is the Szemerédi–Trotter extremal:
   `Θ(n²/t³)` `t`-rich lines, mass `Θ(n²/t²)`, violation `×11.2` at `n = 400`
   (`scripts/probes/probe_grid_supply_refutation.py`).  Hence "prime `q`" alone
   cannot rescue a linear supply law — the positive side must couple to the
   *domain* (`μ_n` additive unstructure), and the corrected shape target for
   additive domains is the small-set finite-field ST curve `L_t = O(n²/t³ + n/t)`
   (Stevens–de Zeeuw gives the unconditional partial `O(n^{11/4}/t^{15/4})`,
   beating packing for `t > n^{3/7}`).

Issue #389; DISPROOF_LOG 2026-06-12 mean-degree entry.  Axiom-clean.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor

instance primeFact_GridSupplyRefutation_1 : Fact (Nat.Prime 41) := ⟨by decide⟩

instance moduleInstance_GridSupplyRefutation_1 : NeZero (36 : ℕ) := ⟨by norm_num⟩

/-- The sheared `6 × 6` grid evaluation domain in `ZMod 41`: index `i = col + 6·row`
maps to the abscissa `col + 7·row` (base-7 digits, hence injective). -/
def gridDom : Fin 36 ↪ ZMod 41 :=
  ⟨fun i => ((i.val % 6 + 7 * (i.val / 6) : ℕ) : ZMod 41), by decide⟩

/-- The grid word: the row index, `w(col + 6·row) = row`. -/
def gridWord : Fin 36 → ZMod 41 := fun i => ((i.val / 6 : ℕ) : ZMod 41)

/-- The affine codeword attached to a (slope, intercept) pair. -/
def lineFn (p : ZMod 41 × ZMod 41) : Fin 36 → ZMod 41 :=
  fun i => p.1 * gridDom i + p.2

theorem lineFn_mem (p : ZMod 41 × ZMod 41) :
    lineFn p ∈ (rsCode gridDom 2 : Submodule (ZMod 41) (Fin 36 → ZMod 41)) := by
  refine ⟨C p.1 * X + C p.2, ?_, ?_⟩
  · exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast Nat.one_lt_two)
  · funext i; simp [lineFn]

/-- Natural-number casts below `41` are injective in `ZMod 41`. -/
private theorem cast_inj_41 {a b : ℕ} (ha : a < 41) (hb : b < 41)
    (h : (a : ZMod 41) = (b : ZMod 41)) : a = b := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hval

/-- A subset of the domain on which the row map `i ↦ i/6` is injective has `≤ 6`
elements (six rows). -/
private theorem card_le_six_of_injOn_row {S : Finset (Fin 36)}
    (h : Set.InjOn (fun i : Fin 36 => i.val / 6) ↑S) : S.card ≤ 6 := by
  have hle := Finset.card_le_card_of_injOn (fun i : Fin 36 => i.val / 6)
    (fun i _ => Finset.mem_range.mpr
      ((by have hb := i.isLt; omega) : i.val / 6 < 6)) h
  simpa using hle

/-- A subset of the domain on which the column map `i ↦ i % 6` is injective has `≤ 6`
elements (six columns). -/
private theorem card_le_six_of_injOn_col {S : Finset (Fin 36)}
    (h : Set.InjOn (fun i : Fin 36 => i.val % 6) ↑S) : S.card ≤ 6 := by
  have hle := Finset.card_le_card_of_injOn (fun i : Fin 36 => i.val % 6)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))) h
  simpa using hle

/-- **The word cap (structural, field-robust).**  No degree-`< 2` codeword agrees with
the grid word on more than `2k + m + 1 = 6` points: a constant codeword agrees only
inside one row, and a non-constant one meets each row at most once.  This is exactly
the hypothesis class of `SubJohnsonSupplyResidual gridDom 2 1`. -/
theorem grid_word_cap :
    ∀ c ∈ (rsCode gridDom 2 : Submodule (ZMod 41) (Fin 36 → ZMod 41)),
      (agreeSet c gridWord).card ≤ 2 * 2 + 1 + 1 := by
  rintro c ⟨P, hdeg, rfl⟩
  have hnd : P.natDegree ≤ 1 := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have hlt := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hdeg
      omega
  obtain ⟨pa, pb, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hnd
  have hmem : ∀ i ∈ agreeSet (fun i => (C pa * X + C pb).eval (gridDom i)) gridWord,
      pa * gridDom i + pb = ((i.val / 6 : ℕ) : ZMod 41) := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    simpa [gridWord] using h
  by_cases hpa : pa = 0
  · -- constant codeword: all agreement points share one row, columns are injective
    refine le_trans (card_le_six_of_injOn_col ?_) (by norm_num)
    intro i hi j hj hij
    have hi' := hmem i hi
    have hj' := hmem j hj
    rw [hpa, zero_mul, zero_add] at hi' hj'
    have hrow : i.val / 6 = j.val / 6 :=
      cast_inj_41 (by omega) (by omega) (hi'.symm.trans hj')
    have hcol : i.val % 6 = j.val % 6 := hij
    have : i.val = j.val := by omega
    exact Fin.ext this
  · -- non-constant codeword: at most one agreement point per row
    refine le_trans (card_le_six_of_injOn_row ?_) (by norm_num)
    intro i hi j hj hij
    have hrow : ((i.val / 6 : ℕ) : ZMod 41) = ((j.val / 6 : ℕ) : ZMod 41) := by
      exact_mod_cast congrArg (fun a : ℕ => ((a : ZMod 41))) hij
    have heq : pa * gridDom i = pa * gridDom j := by
      have hi' := hmem i hi
      have hj' := hmem j hj
      have := hi'.trans (hrow.trans hj'.symm)
      exact add_right_cancel this
    exact gridDom.injective (mul_left_cancel₀ hpa heq)

/-- The 22 rich lines of the sheared grid: the six rows (slope 0), the six columns
(slope `7⁻¹ = 6`), and the two diagonal families (slopes `6⁻¹ = 7` and `8⁻¹ = 36`). -/
def gridLines : Finset (ZMod 41 × ZMod 41) :=
  {(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (6, 0), (6, 11), (6, 17), (6, 23), (6, 29), (6, 35),
   (7, 6), (36, 0), (7, 13), (7, 40), (36, 5), (36, 36),
   (7, 20), (7, 33), (36, 10), (36, 31)}

theorem gridLines_card : gridLines.card = 22 := by decide

set_option maxRecDepth 100000 in
/-- Every listed line agrees with the grid word on at least `t = k + m + 1 = 4`
points (kernel-checked; the true sizes are `14×6 + 4×5 + 4×4`, mass `120`). -/
theorem gridLines_agree :
    ∀ p ∈ gridLines, 4 ≤ (agreeSet (lineFn p) gridWord).card := by decide

set_option maxRecDepth 100000 in
/-- Distinct (slope, intercept) pairs give distinct codeword functions. -/
theorem lineFn_inj :
    ∀ p ∈ gridLines, ∀ q ∈ gridLines, lineFn p = lineFn q → p = q := by decide

/-- Two distinct lines share at most one agreement point with the word
(they cross at most once). -/
theorem line_pair_agree_le_one (p q : ZMod 41 × ZMod 41) (hpq : p ≠ q) :
    ((agreeSet (lineFn p) gridWord) ∩ (agreeSet (lineFn q) gridWord)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro i hi j hj
  by_contra hij
  apply hpq
  have hip := (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hi)).2
  have hiq := (Finset.mem_filter.mp (Finset.mem_of_mem_inter_right hi)).2
  have hjp := (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hj)).2
  have hjq := (Finset.mem_filter.mp (Finset.mem_of_mem_inter_right hj)).2
  -- both lines pass through the two distinct graph points at `i` and `j`
  have hi2 : lineFn p i = lineFn q i := hip.trans hiq.symm
  have hj2 : lineFn p j = lineFn q j := hjp.trans hjq.symm
  have hdom : gridDom i ≠ gridDom j := fun h => hij (gridDom.injective h)
  simp only [lineFn] at hi2 hj2
  have hslope : p.1 = q.1 := by
    have hsub : (p.1 - q.1) * (gridDom i - gridDom j) = 0 := by
      linear_combination hi2 - hj2
    rcases mul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hdom
  have hint : p.2 = q.2 := by
    have := hi2
    rw [hslope] at this
    exact add_left_cancel this
  exact Prod.ext hslope hint

/-- **THE COUNTERMODEL (mean-degree form).**  A word over a 36-point domain in
`ZMod 41`, *word-capped at `2k+m+1 = 6`* (every degree-`<2` codeword agreement is
`≤ 6`), carrying an explicit family of `22` codewords each with agreement
`≥ t = 4` and total agreement mass `> 2n`:  the announced sub-Johnson linear law
`Σ_c a_c ≤ 2n` is false, even on the `SubJohnsonSupplyResidual` hypothesis class. -/
theorem grid_mean_degree_violation :
    ∃ w : Fin 36 → ZMod 41,
      (∀ c ∈ (rsCode gridDom 2 : Submodule (ZMod 41) (Fin 36 → ZMod 41)),
        (agreeSet c w).card ≤ 2 * 2 + 1 + 1) ∧
      ∃ L : Finset (Fin 36 → ZMod 41),
        (∀ c ∈ L, c ∈ (rsCode gridDom 2 : Submodule (ZMod 41) (Fin 36 → ZMod 41))) ∧
        (∀ c ∈ L, 2 + 1 + 1 ≤ (agreeSet c w).card) ∧
        2 * 36 < ∑ c ∈ L, (agreeSet c w).card := by
  refine ⟨gridWord, grid_word_cap, gridLines.image lineFn, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    exact lineFn_mem p
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact gridLines_agree p hp
  · have hcard : (gridLines.image lineFn).card = 22 := by
      rw [Finset.card_image_of_injOn
        (fun p hp q hq h => lineFn_inj p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) h)]
      exact gridLines_card
    have hsum : ∑ c ∈ gridLines.image lineFn, 4
        ≤ ∑ c ∈ gridLines.image lineFn, (agreeSet c gridWord).card := by
      refine Finset.sum_le_sum ?_
      intro c hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      exact gridLines_agree p hp
    have hconst : ∑ _c ∈ gridLines.image lineFn, 4 = 88 := by
      rw [Finset.sum_const, hcard, smul_eq_mul]
    omega

set_option maxRecDepth 100000 in
/-- The per-line core mass: `Σ_c C(a_c, 4) = 234` (kernel-checked). -/
theorem gridLines_core_mass :
    ∑ p ∈ gridLines, ((agreeSet (lineFn p) gridWord).card).choose 4 = 234 := by decide

/-- **THE B-FLOOR ON THE NAMED OPEN PROP.**  Any supply bound `B` for which
`SubJohnsonSupplyResidual gridDom 2 1 B` holds satisfies `234 ≤ B`: the word-capped
grid word has at least `234` explainable `4`-cores.  This refutes, at `n = 36`,
both the partition target `⌊n/cap⌋·C(cap,t) = 90` and the mean-degree-law target
`(2n/cap)·C(cap,t) = 180` for the residual, while sitting inside the proven
unconditional `C(n,2) = 630` (`subJohnsonSupplyResidual_pairCount`). -/
theorem subJohnsonSupplyResidual_floor_grid {B : ℕ}
    (h : SubJohnsonSupplyResidual gridDom 2 1 B) : 234 ≤ B := by
  classical
  have hb := h gridWord grid_word_cap
  refine le_trans ?_ hb
  -- the disjoint union of the per-line 4-subset families injects into the cores
  have hdisj : ∀ p ∈ gridLines, ∀ q ∈ gridLines, p ≠ q →
      Disjoint ((agreeSet (lineFn p) gridWord).powersetCard 4)
        ((agreeSet (lineFn q) gridWord).powersetCard 4) := by
    intro p _ q _ hpq
    rw [Finset.disjoint_left]
    intro T hTp hTq
    have hp' := Finset.mem_powersetCard.mp hTp
    have hq' := Finset.mem_powersetCard.mp hTq
    have hsub : T ⊆ (agreeSet (lineFn p) gridWord) ∩ (agreeSet (lineFn q) gridWord) :=
      Finset.subset_inter hp'.1 hq'.1
    have hle := Finset.card_le_card hsub
    have h1 := line_pair_agree_le_one p q hpq
    omega
  have hunion :
      (gridLines.biUnion
        (fun p => (agreeSet (lineFn p) gridWord).powersetCard 4)).card = 234 := by
    rw [Finset.card_biUnion hdisj]
    calc ∑ p ∈ gridLines, ((agreeSet (lineFn p) gridWord).powersetCard 4).card
        = ∑ p ∈ gridLines, ((agreeSet (lineFn p) gridWord).card).choose 4 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_powersetCard 4 _
      _ = 234 := gridLines_core_mass
  rw [← hunion]
  refine Finset.card_le_card ?_
  intro T hT
  obtain ⟨p, hp, hTp⟩ := Finset.mem_biUnion.mp hT
  have hT' := Finset.mem_powersetCard.mp hTp
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨Finset.subset_univ T, hT'.2⟩, lineFn p, lineFn_mem p, ?_⟩
  intro i hi
  exact (Finset.mem_filter.mp (hT'.1 hi)).2

end ProximityGap.Ownership
