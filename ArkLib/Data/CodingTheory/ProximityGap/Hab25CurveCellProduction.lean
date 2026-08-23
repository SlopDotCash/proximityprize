/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent
import ArkLib.ToMathlib.CurveHenselSupply

/-!
# K1 production at general arity: per-stack cells for the `L`-ary curve fold

`GSCellProduction.lean` produced K1 — the per-cell uniform decode families and the
per-irreducible-factor K4 input surface — for the pair case (`L = 2`, the affine fold
`u₀ + γ·u₁` of `mcaEvent`).  This file is the **general-arity mirror**: the same chain for
the `L`-ary curve fold `∑ⱼ γʲ·uⱼ` of `mcaEventCurve` (the `parℓ > 2` Hab25/WHIR event),
built on the landed `L`-ary GS supply (`curve_fold_decoded_divides_specialization`,
`exists_gs_curve_chain`):

* `McaDecodeCurve` — the polynomial-side destructuring of one `mcaEventCurve` witness;
  `McaDecodeCurve.mcaEventCurve` / `exists_mcaDecodeCurve_of_mcaEventCurve` prove it
  faithful (mirrors `McaDecode` and its seam theorems);
* `mcaDecodeCurve_hammingDist_le` — a decode's polynomial is within distance `δ·n` of the
  scalar curve fold (mirrors `mcaDecode_hammingDist_le`);
* `mcaDecodeCurve_matching_dvd` — at the GS Johnson radius the decode's matching factor
  divides the specialized integer interpolant of the generic curve fold (mirrors
  `mcaDecode_matching_dvd`, via the proven `curve_fold_decoded_divides_specialization`);
* **`exists_curve_cell_production`** — the capstone mirror of `exists_cell_production`:
  the bad scalars of every `L`-row stack decompose into `≤ #factors(Q₀) + 1` cells with
  (i) a uniform decode family (K1, proven, every cell), (ii) one designated degenerate
  cell of size `≤ T`, and (iii) a single irreducible factor of `Q₀` per remaining cell
  with `(Y − C (P γ)) ∣ R|_{Z:=γ}` — the exact per-cell surface the `L`-ary Steps 5–7
  Hensel lane (K4) consumes;
* `bad_card_le_of_curve_cell_production` — composed with a per-cell K4 pinning input: the
  stack's bad-scalar count is `≤ (#factors(Q₀) + 1)·T` (mirrors
  `bad_card_le_of_cell_production`);
* `exists_curve_cell_production_total` — composed with the landed `exists_gs_curve_chain`:
  the interpolant, its `Conditions`, and the integer representative are produced; the sole
  remaining input is the degenerate-set budget, which stays **parametrized** (conditional
  on a budget for the produced `Q₀`) because the `L`-ary Z-degree-bounded interpolant
  (the `gs_existence_over_ratfunc_zDegree_card` analogue) is not in-tree yet.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **A decoded `mcaEventCurve` witness, polynomial side** — the `L`-ary mirror of
`McaDecode`: a witness set `S` of size `≥ (1−δ)·n`, a degree-`< k` polynomial `P` whose
evaluations agree with the curve fold `∑ⱼ γʲ·uⱼ` on `S`, and the forbidden
joint-agreement clause of the stack, carried verbatim. -/
structure McaDecodeCurve {n L : ℕ} (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin L) (Fin n)) (γ : F₀) : Type where
  /-- the `mcaEventCurve` witness set -/
  S : Finset (Fin n)
  /-- the decoded polynomial -/
  P : F₀[X]
  /-- the decoded polynomial has Reed–Solomon degree -/
  hdeg : P.degree < k
  /-- the witness set is large -/
  hcard : ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n))
  /-- the decoded polynomial agrees with the curve fold on the witness set -/
  hagree : ∀ i ∈ S, P.eval (domain i) = ∑ j : Fin L, γ ^ (j : ℕ) • u j i
  /-- no stack of codewords jointly agrees with `u` on the witness set -/
  hnjp : ¬ _root_.ProximityGap.stackJointAgreesOn
    ((ReedSolomon.code domain k : Set (Fin n → F₀))) S u

/-- A curve decode certifies the `mcaEventCurve`: the destructuring is sound. -/
theorem McaDecodeCurve.mcaEventCurve {n L : ℕ} {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin L) (Fin n)} {γ : F₀}
    (d : McaDecodeCurve domain k δ u γ) :
    _root_.ProximityGap.mcaEventCurve ((ReedSolomon.code domain k : Set (Fin n → F₀)))
      δ u γ := by
  refine ⟨d.S, d.hcard, ⟨fun i => d.P.eval (domain i), ?_, fun i hi => d.hagree i hi⟩,
    d.hnjp⟩
  exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval d.P d.hdeg fun i => rfl

/-- Every `mcaEventCurve` admits a decode: the destructuring is complete. The codeword of
the witness is realized as the evaluation of a degree-`< k` polynomial via
`ReedSolomon.mem_code_iff_exists_polynomial` (mirrors `exists_mcaDecode_of_mcaEvent`). -/
theorem exists_mcaDecodeCurve_of_mcaEventCurve {n L : ℕ} {domain : Fin n ↪ F₀} {k : ℕ}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)} {γ : F₀}
    (h : _root_.ProximityGap.mcaEventCurve
      ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ) :
    Nonempty (McaDecodeCurve domain k δ u γ) := by
  obtain ⟨S, hcard, ⟨w, hw, hagree⟩, hnjp⟩ := h
  obtain ⟨p, hdeg, hev⟩ := ReedSolomon.mem_code_iff_exists_polynomial.mp hw
  refine ⟨⟨S, p, hdeg, hcard, fun i hi => ?_, hnjp⟩⟩
  have hwi : w i = p.eval (domain i) := by rw [hev]; rfl
  rw [← hwi]
  exact hagree i hi

/-- **Decode distance**: an `mcaEventCurve` decode's polynomial is within Hamming distance
`δ·n` of the scalar curve fold — its disagreements avoid the witness set (mirrors
`mcaDecode_hammingDist_le`). -/
lemma mcaDecodeCurve_hammingDist_le {n k L : ℕ} [NeZero n] {domain : Fin n ↪ F₀}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)} {γ : F₀}
    (d : McaDecodeCurve domain k δ u γ) (hδ1 : δ ≤ 1) :
    (hammingDist (fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i)
      (fun i => d.P.eval (domain i)) : ℝ) ≤ (δ : ℝ) * n := by
  classical
  -- the disagreement set avoids the witness set
  have hsub : Finset.univ.filter
      (fun i => (fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i) i ≠
        (fun i => d.P.eval (domain i)) i) ⊆
      Finset.univ \ d.S := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hiS => hi.2 (d.hagree i hiS).symm⟩
  have hcount : hammingDist (fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i)
      (fun i => d.P.eval (domain i)) ≤ n - d.S.card := by
    rw [hammingDist]
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  -- the witness set is large, in real form
  have hScard : ((1 : ℝ) - (δ : ℝ)) * n ≤ (d.S.card : ℝ) := by
    have hco := NNReal.coe_le_coe.mpr d.hcard.le
    rw [NNReal.coe_mul, NNReal.coe_sub hδ1] at hco
    simpa [Fintype.card_fin] using hco
  have hSn : d.S.card ≤ n := by
    have h := Finset.card_le_univ d.S
    simpa using h
  calc (hammingDist (fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i)
        (fun i => d.P.eval (domain i)) : ℝ)
      ≤ ((n - d.S.card : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (n : ℝ) - d.S.card := by push_cast [Nat.cast_sub hSn]; ring
    _ ≤ (δ : ℝ) * n := by nlinarith

/-- **Decode ⟹ matching-factor divisibility, `L`-ary.** In the Johnson regime, every
`mcaEventCurve` decode's matching factor divides the specialized integer interpolant of
the generic curve fold: chain the distance bound through the proven
`curve_fold_decoded_divides_specialization` (mirrors `mcaDecode_matching_dvd`). -/
theorem mcaDecodeCurve_matching_dvd {n k m L : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    {u : WordStack F₀ (Fin L) (Fin n)} {δ : ℝ≥0}
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    {γ : F₀} (d : McaDecodeCurve domain k δ u γ)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) :
    (Polynomial.X - Polynomial.C d.P) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- the decode's codeword
  have hmem : (fun i => d.P.eval (domain i)) ∈ ReedSolomon.code domain k :=
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval d.P d.hdeg fun i => rfl
  set p : ReedSolomon.code domain k := ⟨fun i => d.P.eval (domain i), hmem⟩ with hp
  have hround : ReedSolomon.codewordToPoly p = d.P :=
    codewordToPoly_eval_vector domain (by omega) d.P d.hdeg hmem
  -- the distance bound, in the `gs_divisibility` shape
  have hdist : (hammingDist (fun i => ∑ j : Fin L, γ ^ (j : ℕ) * u j i)
      (fun i => (ReedSolomon.codewordToPoly p).eval (domain i)) : ℝ) / n <
      gs_johnson k n m := by
    rw [hround]
    have hle := mcaDecodeCurve_hammingDist_le d hδ1
    have hsmul : (fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i) =
        (fun i => ∑ j : Fin L, γ ^ (j : ℕ) * u j i) := by
      funext i
      exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]
    rw [hsmul] at hle
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hnR]
    calc (hammingDist (fun i => ∑ j : Fin L, γ ^ (j : ℕ) * u j i)
          (fun i => d.P.eval (domain i)) : ℝ)
        ≤ (δ : ℝ) * n := hle
      _ < gs_johnson k n m * n := mul_lt_mul_of_pos_right hδJ hnR
  -- the landed `L`-ary GS list decoder (its `hammingDist` was elaborated with Classical
  -- decidability — `convert` discharges the `Subsingleton Decidable` instance gap)
  have hdvd : Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    refine curve_fold_decoded_divides_specialization domain (fun j i => u j i)
      hQ hrep γ hz hkn hm p ?_
    convert hdist using 3
    congr!
  rwa [hround] at hdvd

/-- **K1 production at general arity — the per-stack cells, decode families, and the K4
input surface for the `L`-ary curve fold** (mirrors `exists_cell_production`).

The bad scalars of the `L`-row stack decompose into `≤ #factors(Q₀) + 1` cells such that:
1. *(K1, proven)* every cell carries the uniform decode family `P` — every scalar of every
   cell is an `mcaEventCurve` decode with that polynomial;
2. the designated cell `none` collects the degenerate scalars (`Q₀|_{Z:=γ} = 0`) and has
   `≤ T` members (the Z-degree-budget input `hbadz`, in the instance-free `∀`-form);
3. every other cell comes with a **single irreducible factor `R` of `Q₀`** such that the
   matching factor of every member divides `R|_{Z:=γ}` — the exact per-cell surface the
   `L`-ary Steps 5–7 Hensel lane (K4) pins to a polynomial curve tuple. -/
theorem exists_curve_cell_production {n k m L : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T) :
    ∃ (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀) (P : F₀ → F₀[X]),
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEventCurve
          ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)) ⊆
        Index.biUnion Ecell ∧
      (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
        ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) ∧
      none ∈ Index ∧ (Ecell none).card ≤ T ∧
      (∀ R : (F₀[X])[X][Y], some R ∈ Index →
        R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
        ∀ γ ∈ Ecell (some R),
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  set bad : Finset F₀ := Finset.univ.filter (fun γ : F₀ =>
    _root_.ProximityGap.mcaEventCurve
      ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ) with hbad
  -- the uniform decode family, by choice (kept behind opaque `choose` fvars — embedding
  -- choice terms in `dite` branches sends later unifications into whnf blowup)
  have hex : ∀ γ : F₀, ∃ p : F₀[X],
      γ ∈ bad → ∃ d : McaDecodeCurve domain k δ u γ, d.P = p := by
    intro γ
    by_cases hγ : γ ∈ bad
    · obtain ⟨d⟩ := exists_mcaDecodeCurve_of_mcaEventCurve (Finset.mem_filter.mp hγ).2
      exact ⟨d.P, fun _ => ⟨d, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose P hPdec using hex
  -- the factor assignment for the non-degenerate scalars
  have hassign : ∀ γ ∈ bad,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 →
      ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    intro γ hγ hz
    obtain ⟨d, hd⟩ := hPdec γ hγ
    have hdvd : (Polynomial.X - Polynomial.C (P γ)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      rw [← hd]
      exact mcaDecodeCurve_matching_dvd domain hQ hrep hkn hm hδ1 hδJ d hz
    obtain ⟨R, hRmem, hRd⟩ :=
      exists_integral_factor_assignment_multiset hQ₀0 γ (P γ) hdvd
    exact ⟨R, Multiset.mem_toFinset.mpr hRmem, hRd⟩
  -- the cells: `none` is the degenerate cell, `some R` the factor cells
  have hex2 : ∀ γ : F₀, ∃ ij : Option ((F₀[X])[X][Y]),
      ((γ ∈ bad ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, ij = some R ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
      (¬ (γ ∈ bad ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ij = none) := by
    intro γ
    by_cases h : γ ∈ bad ∧
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
    · obtain ⟨R, hR, hdvd⟩ := hassign γ h.1 h.2
      exact ⟨some R, fun _ => ⟨R, hR, rfl, hdvd⟩, fun hc => absurd h hc⟩
    · exact ⟨none, fun hc => absurd hc h, fun _ => rfl⟩
  choose assign hassignpos hassignneg using hex2
  set Index : Finset (Option ((F₀[X])[X][Y])) :=
    insert none ((UniqueFactorizationMonoid.factors Q₀).toFinset.image some) with hIndex
  set Ecell : Option ((F₀[X])[X][Y]) → Finset F₀ :=
    fun ij => bad.filter (fun γ => assign γ = ij) with hEcell
  refine ⟨Index, Ecell, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- index count
    simp only [hIndex]
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors Q₀).toFinset) (f := Option.some)
    omega
  · -- cover
    intro γ hγ
    have hγbad : γ ∈ bad := hγ
    rw [Finset.mem_biUnion]
    refine ⟨assign γ, ?_, ?_⟩
    · simp only [hIndex]
      by_cases h : γ ∈ bad ∧
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R, hR, hEq, _⟩ := hassignpos γ h
        rw [hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hR)
      · rw [hassignneg γ h]
        exact Finset.mem_insert_self _ _
    · exact Finset.mem_filter.mpr ⟨hγbad, rfl⟩
  · -- K1: the uniform decode family, on every cell
    intro ij _ γ hγ
    have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = ij) := hγ
    exact hPdec γ (Finset.mem_filter.mp hγ').1
  · -- the degenerate cell is indexed
    simp only [hIndex]
    exact Finset.mem_insert_self _ _
  · -- the degenerate cell is small: its members specialize `Q₀` to zero
    refine hbadz (Ecell none) ?_
    intro γ hγ
    have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = none) := hγ
    obtain ⟨hγbad, hass⟩ := Finset.mem_filter.mp hγ'
    by_contra hz
    obtain ⟨R, _, hEq, _⟩ := hassignpos γ ⟨hγbad, hz⟩
    rw [hass] at hEq
    exact absurd hEq.symm (Option.some_ne_none _)
  · -- every factor cell carries its irreducible factor of `Q₀`, nondegenerately
    intro R hRIndex
    simp only [hIndex, Finset.mem_insert] at hRIndex
    rcases hRIndex with h | h
    · exact absurd h (Option.some_ne_none R)
    · obtain ⟨R', hR', hEq⟩ := Finset.mem_image.mp h
      obtain rfl : R' = R := Option.some.inj hEq
      refine ⟨hR', ?_⟩
      intro γ hγ
      have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = some R') := hγ
      obtain ⟨hγbad, hass⟩ := Finset.mem_filter.mp hγ'
      by_cases hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R'', hR'', hEq2, hdvd⟩ := hassignpos γ ⟨hγbad, hz⟩
        rw [hass] at hEq2
        exact ⟨hz, by rwa [← Option.some.inj hEq2] at hdvd⟩
      · rw [hassignneg γ (fun hc => hz hc.2)] at hass
        exact absurd hass.symm (Option.some_ne_none _)

/-- **The K1-complete count at general arity**: composing the curve cell production with a
per-cell K4 pinning input (any decode-family cell whose members' matching factors all
divide one specialized irreducible factor obeys the size-`T` bound), the `L`-row stack's
bad-scalar count is `≤ (#factors(Q₀) + 1)·T` (mirrors `bad_card_le_of_cell_production`). -/
theorem bad_card_le_of_curve_cell_production {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (hK4 : ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset →
      (∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEventCurve
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card ≤
      ((UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1) * T := by
  classical
  obtain ⟨Index, Ecell, P, hcardI, hcover, hdec, hnone, hbadcell, hfactor⟩ :=
    exists_curve_cell_production domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ hbadz
  have hcell : ∀ ij ∈ Index, (Ecell ij).card ≤ T := by
    intro ij hij
    cases ij with
    | none => exact hbadcell
    | some R =>
      obtain ⟨hRmem, hsurf⟩ := hfactor R hij
      exact hK4 (Ecell (some R)) P R hRmem (hdec _ hij) (fun γ hγ => (hsurf γ hγ).2)
  calc (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEventCurve
          ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card
      ≤ (Index.biUnion Ecell).card := Finset.card_le_card hcover
    _ ≤ ∑ ij ∈ Index, (Ecell ij).card := Finset.card_biUnion_le
    _ ≤ Index.card * T := by
        have h := Finset.sum_le_card_nsmul Index (fun ij => (Ecell ij).card) T hcell
        simpa [smul_eq_mul] using h
    _ ≤ ((UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1) * T :=
        Nat.mul_le_mul_right T hcardI

/-- **The total curve cell production** — the GS interpolant hypotheses discharged by the
landed `L`-ary chain `exists_gs_curve_chain` (S2 interpolation for the generic curve fold
+ integer representative, with `Q₀ ≠ 0` derived from `d ≠ 0` and the `Conditions`).  The
degenerate-set budget stays **parametrized**: the conclusion exposes the produced
interpolant (with its `Conditions` and representative identity) and, conditionally on any
budget `T` valid for it, the full cell decomposition.  The `L`-ary Z-degree-bounded
interpolant (the `gs_existence_over_ratfunc_zDegree_card` analogue) is the recognized
producer of that budget and is not in-tree yet. -/
theorem exists_curve_cell_production_total {n k m L : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m) :
    ∃ (Q : (RatFunc F₀)[X][Y]) (dd : F₀[X]) (Q₀ : (F₀[X])[X][Y]),
      dd ≠ 0 ∧ Q₀ ≠ 0 ∧
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain domain) (curveFold (fun j i => u j i)) Q ∧
      Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
        Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q ∧
      ∀ T : ℕ,
        (∀ S : Finset F₀,
          (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
          S.card ≤ T) →
        ∃ (Index : Finset (Option ((F₀[X])[X][Y])))
          (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀) (P : F₀ → F₀[X]),
          Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
          (Finset.univ.filter (fun γ : F₀ =>
            _root_.ProximityGap.mcaEventCurve
              ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)) ⊆
            Index.biUnion Ecell ∧
          (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) ∧
          none ∈ Index ∧ (Ecell none).card ≤ T ∧
          (∀ R : (F₀[X])[X][Y], some R ∈ Index →
            R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
            ∀ γ ∈ Ecell (some R),
              Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
              (Polynomial.X - Polynomial.C (P γ)) ∣
                R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  obtain ⟨Q, dd, Q₀, hdd, hQcond, hrep⟩ :=
    exists_gs_curve_chain k m domain (fun j i => u j i) hk2 (NeZero.ne n) hm
  have hQ₀0 : Q₀ ≠ 0 := by
    intro h0
    have h := hrep
    rw [h0, Polynomial.map_zero] at h
    rcases mul_eq_zero.mp h.symm with hc | hQzero
    · have hdd0 : algebraMap F₀[X] (RatFunc F₀) dd = 0 :=
        Polynomial.C_eq_zero.mp (Polynomial.C_eq_zero.mp hc)
      exact hdd (RatFunc.algebraMap_injective F₀ (by rw [hdd0, map_zero]))
    · exact hQcond.Q_ne_0 hQzero
  refine ⟨Q, dd, Q₀, hdd, hQ₀0, hQcond, hrep, ?_⟩
  intro T hbadz
  exact exists_curve_cell_production domain u δ T hQcond hrep hQ₀0 hkn hm hδ1 hδJ hbadz

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms McaDecodeCurve.mcaEventCurve
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_mcaDecodeCurve_of_mcaEventCurve
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms mcaDecodeCurve_hammingDist_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms mcaDecodeCurve_matching_dvd
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_curve_cell_production
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms bad_card_le_of_curve_cell_production
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_curve_cell_production_total
