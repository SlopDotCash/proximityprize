/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCACurveSeam
import ArkLib.ProofSystem.Whir.Hab25WhirBridge
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ConjectureGlue

/-!
# The ℓ-ary Johnson MCA conjecture, reduced to the per-`δ` deep input at every `parℓ`

`MCAConjecturePairReduction.lean` reduces the verbatim `mca_johnson_bound_CONJECTURE` at
`parℓ = Fin 2` to the per-`δ` Johnson numeric residual (`JohnsonNumericBound` at
`η := μ(δ)`) and further to per-stack Claim-1 cell data. This file is the **ℓ-ary final
splice** (#302 unit (4)): the same reduction at **every** `parℓ = Fin L`, `L ≥ 2`, with the
power exponents `exp j = j` — through the proven ℓ-ary curve seam
(`hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`, `MCACurveSeam.lean`) and the curve MCA
error `epsMCACurve` (`MCACurveEvent.lean`).

The ℓ-ary deep input is `CurveJohnsonNumericBound`: the curve MCA error at `Fin L` is
within `(L−1)·johnsonBoundReal` — the same closed form as the pair case, scaled by the
curve degree `L−1` exactly as the conjecture's `errStar` numerator scales. The numeric
comparison is **not** re-derived: the proven pair comparison
`johnsonBoundReal ≤ 2^{2m}/(|F|·(2μ)⁷)` (`Hab25ConjectureGlue.lean`) is multiplied by
`(L−1) ≥ 1`.

* `rate_genRSC_ellary` — the power generator's rate is `2^m/|ι|` for any `parℓ`;
* `curveGap` / `curveDisagreeSet` / `curve_match_card_le` — the ℓ-ary endgame pivot: a
  non-trivial degree-`< L` gap polynomial has `≤ L−1` roots per disagreement coordinate
  (the `L = 2` case is the proven `affine_match_card_le_one`, and this is exactly where
  the conjecture's `(parℓ−1)` factor enters);
* `curve_endgame_count` — Hab25 Claim-1 endgame, ℓ-ary: improving scalars number
  `≤ (L−1)·n`;
* `CurveCaptured` / `curveCaptured_improve` — ℓ-ary affine capture (the polynomial-tuple
  shape produced by the GS curve-fold kernel `GSCurveTuple.lean`) and the improvement
  lemma;
* `curve_claim1_dichotomy` / `curve_bad_card_le_of_claim1_cells` — Claim-1 dichotomy and
  the per-stack bad-scalar count `≤ Lc·(L−1)·n` from cells;
* `epsMCACurve_le_of_card_le` / `epsMCACurve_le_ofReal_of_card_le` — the S11 scaling for
  the curve error;
* `CurveJohnsonNumericBound` + `curveJohnsonNumericBound_of_claim1_cells` — the ℓ-ary
  numeric residual, discharged end-to-end from per-stack Claim-1 cells in the GS
  list-size shape (same `Lc ≤ (m+½)/√ρ₊` shape as the pair case);
* **`mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound`** — the verbatim
  Conjecture 4.12 (Johnson regime) at `parℓ = Fin L`, every `L ≥ 2`, from the per-`δ`
  curve numeric residual at `η := μ(δ)`;
* **`mca_johnson_bound_CONJECTURE_ellary_of_claim1_cells`** — the same from per-`δ`,
  per-stack ℓ-ary Claim-1 cell data alone (capture above `(L−1)·n` — the ℓ-ary
  BCIKS20 Steps 5–7 output, the single remaining deep input, converging with the pair
  case's);
* sanity at `L = 2`: `curveJohnsonNumericBound_two_iff` identifies the ℓ-ary deep input
  with the pair `JohnsonNumericBound`, and
  `mca_johnson_bound_CONJECTURE_pair_via_ellary` re-derives the
  landed pair theorem through the ℓ-ary route from the identical hypothesis.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The rate of the `parℓ`-power generator is exactly `2^m / |ι|` (as a real number) —
the rate field of `genRSC` does not depend on `parℓ`. -/
theorem rate_genRSC_ellary (parℓ : Type) [Fintype parℓ] (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (exp : parℓ ↪ ℕ) (hk : 2 ^ m ≤ Fintype.card ι) :
    (RSGenerator.genRSC parℓ φ m exp).rate =
      (2 ^ m : ℝ) / (Fintype.card ι : ℝ) := by
  have h := rate_smoothCode_coe (F₀ := F) (ι₀ := ι) φ m hk
  simpa [RSGenerator.genRSC] using h

/-! ## The ℓ-ary endgame pivot: gap polynomials have `≤ L − 1` roots per coordinate -/

/-- The ℓ-ary gap functional at one coordinate: `γ ↦ ∑ⱼ γʲ·cⱼ` — the `L`-ary
generalization of the affine functional `affineGap` (`c₀ + γ·c₁` at `L = 2`). -/
def curveGap {L : ℕ} (c : Fin L → F) (γ : F) : F :=
  ∑ j : Fin L, γ ^ (j : ℕ) * c j

/-- The ℓ-ary disagreement set: coordinates where some row of the difference stack is
nonzero — the `L`-ary generalization of `disagreeSet`. -/
def curveDisagreeSet {L : ℕ} (d : Fin L → ι → F) : Finset ι :=
  Finset.univ.filter (fun x => ∃ j, d j x ≠ 0)

/-- **The ℓ-ary per-coordinate pivot.** A non-trivial gap functional `γ ↦ ∑ⱼ γʲ·cⱼ` is a
nonzero polynomial of degree `≤ L − 1`, so at most `L − 1` elements of any finite scalar
set are roots. At `L = 2` this is the proven `affine_match_card_le_one`; the `L − 1` here
is **exactly** the `(parℓ − 1)` factor of the conjecture's `errStar`. -/
theorem curve_match_card_le {L : ℕ} (c : Fin L → F) (hne : ∃ j, c j ≠ 0)
    (S : Finset F) :
    (S.filter (fun γ => curveGap c γ = 0)).card ≤ L - 1 := by
  classical
  set p : F[X] := ∑ j : Fin L, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  -- the coefficients of `p` are the `c j` (the degrees `j` are distinct)
  have hcoeff : ∀ j₀ : Fin L, p.coeff (j₀ : ℕ) = c j₀ := by
    intro j₀
    rw [hp, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j₀]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro b _ hb
      have hbv : (j₀ : ℕ) ≠ (b : ℕ) := fun hv => hb (Fin.val_injective hv.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbv]
    · intro habs
      exact absurd (Finset.mem_univ j₀) habs
  obtain ⟨j₀, hj₀⟩ := hne
  have hp0 : p ≠ 0 := fun h => hj₀ (by rw [← hcoeff j₀, h, Polynomial.coeff_zero])
  have hdeg : p.natDegree ≤ L - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have := j.isLt
    omega
  have heval : ∀ γ : F, p.eval γ = curveGap c γ := by
    intro γ
    rw [hp, curveGap, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      mul_comm]
  have hsub : S.filter (fun γ => curveGap c γ = 0) ⊆ p.roots.toFinset := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp0, by rw [Polynomial.IsRoot, heval]; exact hγ.2⟩
  calc (S.filter (fun γ => curveGap c γ = 0)).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ L - 1 := hdeg

/-- **Hab25 Claim-1 endgame, ℓ-ary.** If every scalar of `T` matches the fold at some
coordinate of the ℓ-ary disagreement set, then `|T| ≤ (L−1)·n`: each disagreement
coordinate kills at most `L − 1` scalars (`curve_match_card_le`), and there are at most
`n` coordinates. At `L = 2` this is the proven `hab25_endgame_count` bound `|T| ≤ n`. -/
theorem curve_endgame_count {L : ℕ} (d : Fin L → ι → F) (T : Finset F)
    (hT : ∀ γ ∈ T, ∃ x ∈ curveDisagreeSet d, curveGap (fun j => d j x) γ = 0) :
    T.card ≤ (L - 1) * Fintype.card ι := by
  classical
  have hsub : T ⊆ (curveDisagreeSet d).biUnion
      (fun x => T.filter (fun γ => curveGap (fun j => d j x) γ = 0)) := by
    intro γ hγ
    obtain ⟨x, hx, hzero⟩ := hT γ hγ
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hγ, hzero⟩⟩
  calc T.card
      ≤ ((curveDisagreeSet d).biUnion
          (fun x => T.filter (fun γ => curveGap (fun j => d j x) γ = 0))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ x ∈ curveDisagreeSet d,
          (T.filter (fun γ => curveGap (fun j => d j x) γ = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ curveDisagreeSet d, (L - 1) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hne : ∃ j, d j x ≠ 0 := by
          simpa [curveDisagreeSet] using hx
        exact curve_match_card_le (fun j => d j x) hne T
    _ = (curveDisagreeSet d).card * (L - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card ι * (L - 1) :=
        Nat.mul_le_mul_right _ (Finset.card_le_univ _)
    _ = (L - 1) * Fintype.card ι := Nat.mul_comm _ _

/-! ## ℓ-ary capture and the Claim-1 dichotomy -/

/-- **ℓ-ary curve capture.** The bad scalar `γ` is captured by the polynomial tuple
`a : Fin L → F[X]` when some `mcaEventCurve`-shaped witness set `S` (large, no joint
stack agreement) certifies the curve fold's closeness with the specialized curve codeword
`∑ⱼ C(γʲ)·aⱼ` itself. This is exactly the tuple shape the `K = F(Z)` GS curve-fold kernel
produces (`GSCurveTuple.curve_tuple_of_hammingDist`, specialized at `Z := γ`) — the
`L`-ary generalization of `AffineCaptured`. -/
def CurveCaptured (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    {L : ℕ} (u : Code.WordStack F (Fin L) ι) (γ : F) (a : Fin L → F[X]) : Prop :=
  ∃ S : Finset ι, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) ∧
    (∀ i ∈ S, (∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j).eval (domain i) =
      ∑ j : Fin L, γ ^ (j : ℕ) • u j i) ∧
    ¬ _root_.ProximityGap.stackJointAgreesOn
      ((ReedSolomon.code domain k : Set (ι → F))) S u

/-- **The ℓ-ary improvement lemma** (Hab25 "from the proof of Lemma 1", curve form). If
`γ` is curve-captured by the tuple `a` (with the degree bounds making each row a
codeword), then the tuple disagrees with the stack at some coordinate of the witness set
— else the stack would jointly agree — and there the fold agreement forces the ℓ-ary gap
functional to vanish. The `L`-ary generalization of `affineCaptured_improve`. -/
theorem curveCaptured_improve {domain : ι ↪ F} {k : ℕ} {δ : ℝ≥0}
    {L : ℕ} {u : Code.WordStack F (Fin L) ι} {γ : F} {a : Fin L → F[X]}
    (hdeg : ∀ j, (a j).natDegree < k)
    (hcap : CurveCaptured domain k δ u γ a) :
    ∃ x ∈ curveDisagreeSet (fun j i => (a j).eval (domain i) - u j i),
      curveGap (fun j => (a j).eval (domain x) - u j x) γ = 0 := by
  classical
  obtain ⟨S, _hScard, hagree, hnjp⟩ := hcap
  -- the tuple's rows are Reed–Solomon codewords
  have hv : ∀ j, (fun i => (a j).eval (domain i)) ∈
      (ReedSolomon.code domain k : Set (ι → F)) := fun j =>
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (a j) (hdeg j)
      fun i => rfl
  -- forbidden joint agreement ⇒ a disagreement coordinate on `S`
  have hdis : ¬ ∀ i ∈ S, ∀ j, (a j).eval (domain i) = u j i := by
    intro hall
    exact hnjp ⟨fun j i => (a j).eval (domain i), hv, fun i hi j => hall i hi j⟩
  push Not at hdis
  obtain ⟨x, hxS, j₀, hxne⟩ := hdis
  refine ⟨x, ?_, ?_⟩
  · rw [curveDisagreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨j₀, sub_ne_zero.mpr hxne⟩⟩
  · -- the fold agreement at `x` kills the ℓ-ary gap functional
    have h := hagree x hxS
    rw [Polynomial.eval_finset_sum] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul] at h
    show ∑ j : Fin L, γ ^ (j : ℕ) * ((a j).eval (domain x) - u j x) = 0
    calc ∑ j : Fin L, γ ^ (j : ℕ) * ((a j).eval (domain x) - u j x)
        = (∑ j : Fin L, γ ^ (j : ℕ) * (a j).eval (domain x)) -
            ∑ j : Fin L, γ ^ (j : ℕ) * u j x := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, sub_self]

/-- **Hab25 Claim 1, ℓ-ary dichotomy.** If capture-above-`T` holds (the ℓ-ary Steps 5–7
output: past the threshold a single degree-`< k` polynomial tuple captures all scalars of
the cell), then `|Ecell| ≤ T` for any threshold `T ≥ (L−1)·n` — the `L`-ary
`claim1_dichotomy`, with the endgame count scaled by the curve degree `L − 1`. -/
theorem curve_claim1_dichotomy (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    {L : ℕ} (u : Code.WordStack F (Fin L) ι) (Ecell : Finset F) (T : ℕ)
    (hn : (L - 1) * Fintype.card ι ≤ T)
    (hsteps57 : T < Ecell.card →
      ∃ a : Fin L → F[X], (∀ j, (a j).natDegree < k) ∧
        ∀ γ ∈ Ecell, CurveCaptured domain k δ u γ a) :
    Ecell.card ≤ T := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a, hdeg, hcap⟩ := hsteps57 hcon
  have himprove : ∀ γ ∈ Ecell,
      ∃ x ∈ curveDisagreeSet (fun j i => (a j).eval (domain i) - u j i),
        curveGap (fun j => (a j).eval (domain x) - u j x) γ = 0 := fun γ hγ =>
    curveCaptured_improve hdeg (hcap γ hγ)
  have hcount := curve_endgame_count (fun j i => (a j).eval (domain i) - u j i)
    Ecell himprove
  omega

open Classical in
/-- **Per-stack ℓ-ary bad-scalar count from Claim-1 cells.** A decomposition of the
stack's `mcaEventCurve` bad scalars into `≤ Lc` cells, each subject to the ℓ-ary Claim-1
dichotomy at threshold `(L−1)·n`, bounds the bad set by `Lc·(L−1)·n` — the `L`-ary
`bad_card_le_of_claim1_cells`. -/
theorem curve_bad_card_le_of_claim1_cells (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    {L : ℕ} (u : Code.WordStack F (Fin L) ι)
    {Idx : Type} [DecidableEq Idx]
    (Index : Finset Idx) (Ecell : Idx → Finset F) (Lc : ℕ)
    (hLc : Index.card ≤ Lc)
    (hcover : (Finset.univ.filter
      (fun γ : F => _root_.ProximityGap.mcaEventCurve (F := F)
        ((ReedSolomon.code domain k : Set (ι → F))) δ u γ)) ⊆
      Index.biUnion Ecell)
    (hsteps57 : ∀ ij ∈ Index, (L - 1) * Fintype.card ι < (Ecell ij).card →
      ∃ a : Fin L → F[X], (∀ j, (a j).natDegree < k) ∧
        ∀ γ ∈ Ecell ij, CurveCaptured domain k δ u γ a) :
    (Finset.univ.filter
      (fun γ : F => _root_.ProximityGap.mcaEventCurve (F := F)
        ((ReedSolomon.code domain k : Set (ι → F))) δ u γ)).card ≤
      Lc * ((L - 1) * Fintype.card ι) := by
  refine le_trans (theorem2_union_bound _ Index Ecell ((L - 1) * Fintype.card ι)
    hcover fun ij hij =>
      curve_claim1_dichotomy domain k δ u (Ecell ij) ((L - 1) * Fintype.card ι)
        le_rfl (hsteps57 ij hij)) ?_
  exact Nat.mul_le_mul_right _ hLc

/-! ## The S11 scaling for the curve error -/

open Classical in
/-- **S11 scaling, ℓ-ary.** A per-stack cardinality bound on the `mcaEventCurve` bad
scalars bounds `ε_mcaCurve(C, L, δ) ≤ N/|F|` — the curve analogue of
`epsMCA_le_of_card_le`. -/
theorem epsMCACurve_le_of_card_le (C : Set (ι → F)) {L : ℕ} (δ : ℝ≥0) (N : ℕ)
    (hN : ∀ u : Code.WordStack F (Fin L) ι,
      (Finset.filter (fun γ : F =>
        _root_.ProximityGap.mcaEventCurve (F := F) C δ u γ) Finset.univ).card ≤ N) :
    _root_.ProximityGap.epsMCACurve (F := F) C L δ ≤
      ((N : ℝ≥0) : ENNReal) / (Fintype.card F : ℝ≥0) := by
  unfold _root_.ProximityGap.epsMCACurve
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card (F := F)
    (P := fun γ => _root_.ProximityGap.mcaEventCurve (F := F) C δ u γ)]
  gcongr
  exact_mod_cast hN u

open Classical in
/-- **S11 integer→real bridge, ℓ-ary.** From the per-stack count `N` and the scaled
comparison `N/|F| ≤ B`, conclude `ε_mcaCurve(C, L, δ) ≤ ofReal B` — the curve analogue of
`epsMCA_le_ofReal_div_of_card_le`. -/
theorem epsMCACurve_le_ofReal_of_card_le (C : Set (ι → F)) {L : ℕ} (δ : ℝ≥0)
    (N : ℕ) (B : ℝ)
    (hNB : (N : ℝ) / (Fintype.card F : ℝ) ≤ B)
    (hN : ∀ u : Code.WordStack F (Fin L) ι,
      (Finset.filter (fun γ : F =>
        _root_.ProximityGap.mcaEventCurve (F := F) C δ u γ) Finset.univ).card ≤ N) :
    _root_.ProximityGap.epsMCACurve (F := F) C L δ ≤ ENNReal.ofReal B := by
  refine le_trans (epsMCACurve_le_of_card_le C δ N hN) ?_
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    have h0 : Fintype.card F ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast h0
  have hkey : ((N : ℝ≥0) : ENNReal) / (Fintype.card F : ℝ≥0)
      = ENNReal.ofReal ((N : ℝ) / (Fintype.card F : ℝ)) := by
    rw [← ENNReal.coe_div hFne, ENNReal.coe_nnreal_eq]
    congr 1
  rw [hkey]
  exact ENNReal.ofReal_le_ofReal hNB

/-! ## The ℓ-ary curve Johnson numeric residual -/

/-- **The ℓ-ary curve Johnson numeric residual** — the `parℓ = Fin L` deep input,
converging with the pair case's `JohnsonNumericBound`: the curve MCA error is within
`(L−1)·johnsonBoundReal`, the same closed form as the pair case scaled by the curve
degree `L − 1` (exactly as the GS budgets `D_X, D_{YZ}` scale along the curve fold).
At `L = 2` this **is** `JohnsonNumericBound` (`curveJohnsonNumericBound_two_iff`). -/
def CurveJohnsonNumericBound (domain : ι ↪ F) (k L : ℕ) (η δ : ℝ≥0) : Prop :=
  _root_.ProximityGap.epsMCACurve (F := F) (A := F)
    ((ReedSolomon.code domain k : Set (ι → F))) L δ ≤
    ENNReal.ofReal (((L : ℝ) - 1) * johnsonBoundReal domain k η δ)

/-- **Sanity at `L = 2`: the ℓ-ary residual is the pair residual.** Via
`epsMCACurve_two_eq_epsMCA` and `(2 − 1) = 1`, `CurveJohnsonNumericBound` at `L = 2` is
literally the pair `JohnsonNumericBound` — the generalization is conservative. -/
theorem curveJohnsonNumericBound_two_iff (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) :
    CurveJohnsonNumericBound domain k 2 η δ ↔
      JohnsonNumericBound (F₀ := F) (ι₀ := ι) domain k η δ := by
  unfold CurveJohnsonNumericBound JohnsonNumericBound
  rw [_root_.ProximityGap.epsMCACurve_two_eq_epsMCA,
    show (((2 : ℕ) : ℝ) - 1) = 1 by norm_num, one_mul]

/-- The closed-form Johnson bound is nonnegative (the `L = 0` instance of the proven
numeric edge). -/
theorem johnsonBoundReal_nonneg (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) :
    0 ≤ johnsonBoundReal domain k η δ := by
  have hm := hab25M_ge_three (Fintype.card ι) k η
  have hρ : (0 : ℝ) < hab25RhoPlus (Fintype.card ι) k :=
    hab25RhoPlus_pos Fintype.card_pos k
  have hρ32 : (0 : ℝ) < hab25RhoPlus (Fintype.card ι) k ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hρ _
  have hb5 : (0 : ℝ) ≤ (hab25M (Fintype.card ι) k η + 1 / 2) ^ 5 :=
    pow_nonneg (by linarith) 5
  have hbudget : (0 : ℝ) ≤ 2 * (hab25M (Fintype.card ι) k η + 1 / 2) ^ 5 /
      (3 * hab25RhoPlus (Fintype.card ι) k ^ ((3 : ℝ) / 2)) :=
    div_nonneg (by linarith) (by positivity)
  have h := nat_mul_card_div_le_johnsonBoundReal domain k η δ 0 (by simpa using hbudget)
  simpa using h

/-- **The ℓ-ary residual from the unscaled bound.** A bound by the *pair-case* closed
form `johnsonBoundReal` (without the `(L−1)` headroom) is a stronger input: it implies
`CurveJohnsonNumericBound` outright, since `(L−1) ≥ 1`. -/
theorem curveJohnsonNumericBound_of_epsMCACurve_le_johnsonBoundReal
    (domain : ι ↪ F) (k : ℕ) {L : ℕ} (hL : 2 ≤ L) (η δ : ℝ≥0)
    (h : _root_.ProximityGap.epsMCACurve (F := F) (A := F)
      ((ReedSolomon.code domain k : Set (ι → F))) L δ ≤
      ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    CurveJohnsonNumericBound domain k L η δ := by
  unfold CurveJohnsonNumericBound
  refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
  have h0 := johnsonBoundReal_nonneg domain k η δ
  have h1L : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have h2L : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  exact le_mul_of_one_le_left h0 h1L

open Classical in
/-- **End-to-end: per-stack ℓ-ary Claim-1 cells discharge the curve numeric residual.**
Given, for every `L`-row word stack, a decomposition of its `mcaEventCurve` bad scalars
into `≤ Lc` cells (`Lc` within the *same* GS list-size shape `(m+½)/√ρ₊` as the pair
case) with the per-cell capture-above-`(L−1)·n` hypothesis (the ℓ-ary BCIKS20 Steps 5–7
output), `CurveJohnsonNumericBound` follows: the per-stack count is `≤ Lc·(L−1)·n`
(`curve_bad_card_le_of_claim1_cells`) and `Lc·n/|F| ≤ johnsonBoundReal` is the proven
closed-form arithmetic, scaled by `(L−1)`. -/
theorem curveJohnsonNumericBound_of_claim1_cells
    (domain : ι ↪ F) (k : ℕ) {L : ℕ} (hL : 2 ≤ L) (η δ : ℝ≥0) (Lc : ℕ)
    (hk : k ≤ Fintype.card ι)
    (hLc : (Lc : ℝ) ≤ (hab25M (Fintype.card ι) k η + 1/2) /
      hab25RhoPlus (Fintype.card ι) k ^ ((1 : ℝ) / 2))
    (hdata : ∀ u : Code.WordStack F (Fin L) ι,
      ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
        (Ecell : Idx → Finset F),
        Index.card ≤ Lc ∧
        (Finset.univ.filter
          (fun γ : F => _root_.ProximityGap.mcaEventCurve (F := F)
            ((ReedSolomon.code domain k : Set (ι → F))) δ u γ)) ⊆
          Index.biUnion Ecell ∧
        ∀ ij ∈ Index, (L - 1) * Fintype.card ι < (Ecell ij).card →
          ∃ a : Fin L → F[X], (∀ j, (a j).natDegree < k) ∧
            ∀ γ ∈ Ecell ij, CurveCaptured domain k δ u γ a) :
    CurveJohnsonNumericBound domain k L η δ := by
  unfold CurveJohnsonNumericBound
  have hcount : ∀ u : Code.WordStack F (Fin L) ι,
      (Finset.filter (fun γ : F =>
        _root_.ProximityGap.mcaEventCurve (F := F)
          ((ReedSolomon.code domain k : Set (ι → F))) δ u γ) Finset.univ).card ≤
        Lc * ((L - 1) * Fintype.card ι) := by
    intro u
    obtain ⟨Idx, hIdx, Index, Ecell, hLcard, hcover, hsteps⟩ := hdata u
    letI : DecidableEq Idx := hIdx
    exact curve_bad_card_le_of_claim1_cells domain k δ u Index Ecell Lc
      hLcard hcover hsteps
  -- the closed-form arithmetic: `Lc·n/|F| ≤ johnsonBoundReal`, scaled by `(L − 1)`
  have hpair := nat_mul_card_div_le_johnsonBoundReal domain k η δ Lc
    (le_trans hLc (list_shape_le_budget η Fintype.card_pos hk))
  have h1L : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have h2L : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have h1 : (1 : ℕ) ≤ L := le_trans one_le_two hL
  have hcast : ((Lc * ((L - 1) * Fintype.card ι) : ℕ) : ℝ) =
      ((L : ℝ) - 1) * ((Lc * Fintype.card ι : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]
    ring
  have hNB : ((Lc * ((L - 1) * Fintype.card ι) : ℕ) : ℝ) / (Fintype.card F : ℝ) ≤
      ((L : ℝ) - 1) * johnsonBoundReal domain k η δ := by
    rw [hcast, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hpair (by linarith)
  exact epsMCACurve_le_ofReal_of_card_le _ δ _ _ hNB hcount

/-! ## The verbatim conjecture at every `parℓ = Fin L`, `L ≥ 2` -/

open Classical in
/-- **The literal ℓ-ary Johnson conjecture from the per-`δ` curve numeric residual.**
If, for every admissible `δ` (`0 < δ < 1 − √ρ`, `ρ = 2^m/|ι|`), the ℓ-ary curve residual
`CurveJohnsonNumericBound` holds at the per-`δ` parameter `η := μ(δ) = min(1 − √ρ − δ,
√ρ/20)`, then `mca_johnson_bound_CONJECTURE` holds **verbatim** at `parℓ = Fin L` with
power exponents `exp j = j` — `BStar = √ρ` and the conjecture's exact `errStar` with its
`(parℓ − 1) = L − 1` numerator factor. The closed-form comparison is the proven pair
comparison `johnsonBoundReal_le_errStar_real` multiplied by `(L−1) ≥ 1`; no side
hypotheses remain. -/
theorem mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound
    {L : ℕ} (hL : 2 ≤ L)
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin L ↪ ℕ)
    (hexp : ∀ j : Fin L, exp j = (j : ℕ))
    (hk : 2 ^ m ≤ Fintype.card ι)
    (hJNB : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      CurveJohnsonNumericBound φ (2 ^ m) L
        (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
          (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal δ) :
    mca_johnson_bound_CONJECTURE α φ m (Fin L) exp := by
  classical
  have hrate := rate_genRSC_ellary (Fin L) φ m exp hk
  have h1L : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have h2L : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hmca :
      haveI : Fintype (RSGenerator.genRSC (Fin L) φ m exp).parℓ :=
        (RSGenerator.genRSC (Fin L) φ m exp).hℓ
      hasMutualCorrAgreement (RSGenerator.genRSC (Fin L) φ m exp)
        (Real.sqrt (RSGenerator.genRSC (Fin L) φ m exp).rate)
        (fun x =>
          ENNReal.ofReal
            (((Fintype.card (Fin L) : ℝ) - 1) * 2 ^ (2 * m) /
              ((Fintype.card F : ℝ) *
                (2 * min
                  (1 - Real.sqrt (RSGenerator.genRSC (Fin L) φ m exp).rate - x)
                  (Real.sqrt (RSGenerator.genRSC (Fin L) φ m exp).rate / 20)) ^ 7))) := by
    refine hasMutualCorrAgreement_genRSC_of_epsMCACurve_le hL φ m exp hexp
      _ (Real.sqrt_nonneg _) _ ?_
    intro δ hδ0 hδB
    rw [hrate] at hδB
    refine le_trans (hJNB δ hδ0 hδB) ?_
    rw [hrate, Fintype.card_fin]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (johnsonBoundReal_le_errStar_real φ m hk δ hδB) (by linarith)
  unfold mca_johnson_bound_CONJECTURE
  exact hmca

open Classical in
/-- **The literal ℓ-ary Johnson conjecture from per-stack Claim-1 cells alone.** For
every admissible `δ` and every `L`-row word stack, suppose the `mcaEventCurve` bad
scalars decompose into `≤ Lc` cells satisfying the capture-above-`(L−1)·n` dichotomy (the
ℓ-ary BCIKS20 Steps 5–7 output — the same remaining deep input as the pair case, in its
curve-tuple form), with `Lc` within the per-`δ` GS list-size shape. Then
`mca_johnson_bound_CONJECTURE` holds **verbatim** at `parℓ = Fin L`, for every `L ≥ 2`:
nothing between the capture data and the literal conjecture statement remains unproven. -/
theorem mca_johnson_bound_CONJECTURE_ellary_of_claim1_cells
    {L : ℕ} (hL : 2 ≤ L)
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin L ↪ ℕ)
    (hexp : ∀ j : Fin L, exp j = (j : ℕ))
    (hk : 2 ^ m ≤ Fintype.card ι) (Lc : ℕ)
    (hLc : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (Lc : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin L) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F),
          Index.card ≤ Lc ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEventCurve (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ u γ)) ⊆
            Index.biUnion Ecell ∧
          ∀ ij ∈ Index, (L - 1) * Fintype.card ι < (Ecell ij).card →
            ∃ a : Fin L → F[X], (∀ j, (a j).natDegree < 2 ^ m) ∧
              ∀ γ ∈ Ecell ij, CurveCaptured φ (2 ^ m) δ u γ a) :
    mca_johnson_bound_CONJECTURE α φ m (Fin L) exp := by
  refine mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound hL α φ m exp
    hexp hk ?_
  intro δ hδ0 hδB
  exact curveJohnsonNumericBound_of_claim1_cells φ (2 ^ m) hL _ δ Lc hk
    (hLc δ hδ0 hδB) (hdata δ hδ0 hδB)

open Classical in
/-- **Sanity: `L = 2` recovers the landed pair theorem.** The hypothesis is the
*identical* per-`δ` pair residual `JohnsonNumericBound` at `η := μ(δ)` consumed by the
landed `mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound`; the conclusion is
re-derived through the ℓ-ary route (`curveJohnsonNumericBound_two_iff` + the `Fin 2`
instance of the ℓ-ary theorem). -/
theorem mca_johnson_bound_CONJECTURE_pair_via_ellary
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι)
    (hJNB : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      JohnsonNumericBound (F₀ := F) (ι₀ := ι) φ (2 ^ m)
        (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
          (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal δ) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  have hexp : ∀ j : Fin 2, exp j = (j : ℕ) := by
    intro j
    fin_cases j
    · simpa using hexp0
    · simpa using hexp1
  refine mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound
    (le_refl 2) α φ m exp hexp hk ?_
  intro δ hδ0 hδB
  exact (curveJohnsonNumericBound_two_iff φ (2 ^ m) _ δ).mpr (hJNB δ hδ0 hδB)

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.rate_genRSC_ellary
#print axioms MutualCorrAgreement.curve_match_card_le
#print axioms MutualCorrAgreement.curve_endgame_count
#print axioms MutualCorrAgreement.curveCaptured_improve
#print axioms MutualCorrAgreement.curve_claim1_dichotomy
#print axioms MutualCorrAgreement.curve_bad_card_le_of_claim1_cells
#print axioms MutualCorrAgreement.epsMCACurve_le_of_card_le
#print axioms MutualCorrAgreement.epsMCACurve_le_ofReal_of_card_le
#print axioms MutualCorrAgreement.curveJohnsonNumericBound_two_iff
#print axioms MutualCorrAgreement.johnsonBoundReal_nonneg
#print axioms MutualCorrAgreement.curveJohnsonNumericBound_of_epsMCACurve_le_johnsonBoundReal
#print axioms MutualCorrAgreement.curveJohnsonNumericBound_of_claim1_cells
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_ellary_of_claim1_cells
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_via_ellary
