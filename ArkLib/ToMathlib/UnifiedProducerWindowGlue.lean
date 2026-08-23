/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.UnifiedExtractionTarget
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCaptureUD

/-!
# Issues #301/#302/#304 — the first unconditional `UnifiedProducer` instantiation:
# the unique-decoding window glue

`UnifiedExtractionTarget.lean` (a3fff5b42) pinned **both** #304 cores and the closed-boundary
Johnson-endpoint keystone to ONE production target: `UnifiedProducer k deg domain δ` — per
word-stack and count-triggered decoded family, a faithful `CurveFamilyData`.  This file lands
the first **regime-unconditional** instantiation of that target: on the curve unique-decoding
window

  `curveUDWindow k deg n δ  :=  (k+1)·n + deg ≤ (k+2)·(n − ⌊δ·n⌋)`

(the `(k+2)`-fold agreement-floor pigeonhole window, the arity-`(k+1)` analogue of the
depth-0 K4 window of `Hab25CaptureKernelUD`/`Hab25CurveCaptureUD`), the producer holds with
NO list-decoding, Guruswami–Sudan, Hensel, or weight-budget input: `k+1` good scalars pin the
decoded family to the Lagrange curve through any `k+1` of its members, and root counting on
the `(k+2)`-fold witness intersection forces every further good scalar onto the same curve.

* `floor_agreement_card_of_relHammingDist_le` — proximity to agreement-set floor `n − ⌊δ·n⌋`;
* `exists_curve_tuple_of_window` — **the pinning**: the generic-domain, joint-agreement-free
  mirror of `exists_curve_tuple_of_decode_family_window` (same Lagrange machinery, consumed
  from plain per-scalar proximity data instead of `McaDecodeCurve`);
* `unifiedProducer_of_window` — **deliverable (a), the glue**: `UnifiedProducer` on the window;
* `curveUDWindow_floor_congr` — the window depends only on `⌊δ·n⌋`, so the boundary cell
  radius of `BoundaryHalfState` satisfies it iff `δ` does;
* `correlatedAgreementCurves_johnsonClosed_of_window` — **deliverable (b)**: the closed-boundary
  keystone `δ_ε_correlatedAgreementCurves` at `δ = 1 − √ρ` with the explicit positive error
  `max (errorBound (cell)) ((n+1)/|F|)`, from the single window hypothesis;
* `strictCoeffPolysLargeResidual_of_window` / `strictCoeffPolysResidual_of_window` — the strict
  §5 residuals on the window (feeding the #301 checking bridge non-small-field);
* `correlatedAgreement_affine_curves_of_window` — `δ_ε_correlatedAgreementCurves` at any
  `δ < 1 − √ρ` on the window, with error `errorBound δ deg domain`;
* `curveUDWindow_all_of_floor_eq_zero` — in the zero-error corner `⌊δ·n⌋ = 0` (with
  `deg ≤ n`) the window holds at **every** width `k`, giving the full `∀ k` residual family
  the STIR checking bridge consumes.

## The honest regime statement

The window is a genuine unique-decoding-strength constraint: at width `k` it forces
`δ ≲ (1 − ρ)/(k+2)` (`ρ = deg/n`).  Consequences, stated honestly:

* `unifiedProducer_of_window` is **non-vacuous on the whole window**: the count trigger
  `k < |good|` and the per-scalar proximity data are jointly satisfiable throughout, and the
  produced `CurveFamilyData` is the real Lagrange curve.  This is the `UD-window` leg of the
  producer programme; the `F7 / d_H = 1` matching-lane leg (the `MatchingLaneData` suppliers)
  remains the open route to the Johnson-regime producer.
* In `correlatedAgreementCurves_johnsonClosed_of_window` the window is demanded **at the
  Johnson boundary** `δ = 1 − √ρ`; for `k ≥ 1` this intersects the window only where
  `⌊√ρ·n⌋`-ceiling slack absorbs `(1−√ρ)(k+1−√ρ)·n` — i.e. essentially the high-rate /
  zero-error corner (`⌊δ·n⌋ = 0` forces `deg ∈ {n−1, n}`-type parameters).  The theorem is
  stated for whatever parameters satisfy both; no claim is made beyond that.
* In `correlatedAgreement_affine_curves_of_window` (strict regime `δ < 1 − √ρ`), on most of
  the window the supplied strict residual is consumed only through its Johnson-side hypothesis
  `(1−ρ)/2 < δ` (false for `δ` deep in the window, where the front door's own dichotomy
  carries the load); the two hypotheses are simultaneously satisfiable only near the
  zero-error/high-rate corner.  The non-vacuous content of this file is therefore the
  **producer** (count-triggered, no Johnson-side hypotheses) and the residual family feed —
  not a Johnson-regime proximity gap, which remains #304's open core.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §4 (unique-decoding regime), §5; issues #301, #302, #304.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial ProximityGap Code NNReal Finset Function ProbabilityTheory
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace UnifiedProducerWindowGlue

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1 — the window and the agreement floor -/

/-- **The curve unique-decoding window at width `k`** (`n` = domain size): the `(k+2)`-fold
agreement floor `n − ⌊δ·n⌋` covers `(k+1)` whole domains plus `deg` spare points.  This is the
arity-`(k+1)` analogue of the K4 window `L·n + k ≤ (L+1)·⌈(1−δ)·n⌉` of
`Hab25CurveCaptureUD`, phrased with the floor-complement agreement count (the two agree for
`δ ≤ 1`).  At width `k` it forces `δ ≲ (1−ρ)/(k+2)` — a genuine unique-decoding-strength
regime restriction, stated honestly as a hypothesis everywhere below. -/
def curveUDWindow (k deg n : ℕ) (δ : ℝ≥0) : Prop :=
  (k + 1) * n + deg ≤ (k + 2) * (n - Nat.floor (δ * n))

/-- The window depends on `δ` only through `⌊δ·n⌋`. -/
theorem curveUDWindow_floor_congr {k deg n : ℕ} {δ δ' : ℝ≥0}
    (hfloor : Nat.floor (δ' * n) = Nat.floor (δ * n)) :
    curveUDWindow k deg n δ ↔ curveUDWindow k deg n δ' := by
  unfold curveUDWindow
  rw [hfloor]

/-- **Proximity to agreement floor**: a word within relative distance `δ` of a comparison word
agrees with it on at least `n − ⌊δ·n⌋` coordinates. -/
theorem floor_agreement_card_of_relHammingDist_le {w v : ι → F} {δ : ℝ≥0}
    (h : (δᵣ(w, v) : ℝ≥0) ≤ δ) :
    Fintype.card ι - Nat.floor (δ * (Fintype.card ι : ℝ≥0)) ≤
      (Finset.univ.filter (fun i : ι => v i = w i)).card := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  -- the Hamming distance is at most ⌊δ·n⌋
  have hdist : hammingDist w v ≤ Nat.floor (δ * (n : ℝ≥0)) := by
    refine Nat.le_floor ?_
    have hcast : ((relHammingDist w v : ℚ≥0) : ℝ≥0) =
        (hammingDist w v : ℝ≥0) / (n : ℝ≥0) := by
      rw [relHammingDist]
      push_cast
      rfl
    have h' : (hammingDist w v : ℝ≥0) / (n : ℝ≥0) ≤ δ := by
      rw [← hcast]; exact h
    have hnne : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
    calc (hammingDist w v : ℝ≥0)
        = (hammingDist w v : ℝ≥0) / (n : ℝ≥0) * (n : ℝ≥0) := by
          rw [div_mul_cancel₀ _ hnne.ne']
      _ ≤ δ * (n : ℝ≥0) := by gcongr
  -- the agreement set is the complement of the disagreement set
  have hsplit : (Finset.univ.filter (fun i : ι => v i = w i)).card
      + (Finset.univ.filter (fun i : ι => ¬ (v i = w i))).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    exact Finset.card_univ
  have hne : (Finset.univ.filter (fun i : ι => ¬ (v i = w i))).card = hammingDist w v := by
    unfold hammingDist
    congr 1
    ext i
    simp [eq_comm]
  omega

/-! ## §2 — the pinning: the generic-domain, joint-agreement-free K4 at arity `k + 1` -/

/-- **The window pinning** (the glue core): on `curveUDWindow k deg n δ`, any decoded family
with per-scalar proximity data on a set of more than `k` scalars lies on a single polynomial
curve with `k + 1` coefficient polynomials of degree `< deg` — the Lagrange curve through any
`k + 1` of its members.  Generic-domain, joint-agreement-clause-free mirror of
`exists_curve_tuple_of_decode_family_window` (same internal machinery: the Lagrange tuple,
monomial reproduction, the iterated intersection bound, and root counting). -/
theorem exists_curve_tuple_of_window {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ)
    (u : WordStack F (Fin (k + 1)) ι) (good : Finset F) (hcount : k < good.card)
    (P : F → Polynomial F)
    (hP : ∀ z ∈ good, (P z).natDegree < deg ∧
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) :
    ∃ a : Fin (k + 1) → F[X], (∀ j, (a j).natDegree < deg) ∧
      ∀ z ∈ good, P z = ∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) * a j := by
  classical
  set n : ℕ := Fintype.card ι with hn
  set t₀ : ℕ := n - Nat.floor (δ * (n : ℝ≥0)) with ht₀
  -- per-scalar agreement sets
  set S : F → Finset ι := fun z =>
    Finset.univ.filter (fun i : ι =>
      (P z).eval (domain i) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i) with hS
  have hScard : ∀ z ∈ good, t₀ ≤ (S z).card := fun z hz =>
    floor_agreement_card_of_relHammingDist_le (hP z hz).2
  have hSagree : ∀ z ∈ good, ∀ i ∈ S z,
      (P z).eval (domain i) = ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i := by
    intro z hz i hi
    have h := (Finset.mem_filter.mp hi).2
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  -- choose k + 1 distinct nodes in the good set
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hcount
  set e : Fin (k + 1) ≃ {x // x ∈ s} :=
    (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm with he
  set ν : Fin (k + 1) → F := fun t => (e t : F) with hν
  have hνinj : Function.Injective ν := fun t₁ t₂ h => e.injective (Subtype.ext h)
  have hνmem : ∀ t, ν t ∈ good := fun t => hsub (e t).2
  -- the Lagrange curve tuple through the nodes
  set V : Fin (k + 1) → F[X] := fun t => P (ν t) with hV
  have hVdeg : ∀ t, (V t).natDegree < deg := fun t => (hP (ν t) (hνmem t)).1
  refine ⟨lagrangeCurve ν V, lagrangeCurve_natDegree_lt hdeg ν hVdeg, ?_⟩
  -- every good scalar is forced onto the curve
  intro z hz
  set W : Finset ι :=
    ((Finset.univ : Finset (Fin (k + 1))).inf fun t => S (ν t)) ∩ S z with hW
  -- the (k + 2)-fold intersection is large
  have hWcard : deg ≤ W.card := by
    have hsumle := sum_card_le_inf_card_add (fun t => S (ν t)) (S z)
      (Finset.univ : Finset (Fin (k + 1)))
    rw [Finset.card_univ, Fintype.card_fin, ← hn, ← hW] at hsumle
    have hsumge : (k + 1) * t₀ ≤ ∑ t : Fin (k + 1), (S (ν t)).card := by
      have h := Finset.card_nsmul_le_sum Finset.univ
        (fun t : Fin (k + 1) => (S (ν t)).card) t₀ (fun t _ => hScard (ν t) (hνmem t))
      rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
      exact h
    have hzcard : t₀ ≤ (S z).card := hScard z hz
    have hwin' : (k + 1) * n + deg ≤ (k + 2) * t₀ := hwin
    have hexp : (k + 2) * t₀ = (k + 1) * t₀ + t₀ := by ring
    omega
  -- the curve matches the fold on the intersection
  have hvan : ∀ i ∈ W,
      (P z - ∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) * lagrangeCurve ν V j).eval
        (domain i) = 0 := by
    intro i hi
    obtain ⟨hiinf, hiz⟩ := Finset.mem_inter.mp hi
    -- node agreements at i
    have hPt : ∀ t : Fin (k + 1), (V t).eval (domain i) =
        ∑ j : Fin (k + 1), ν t ^ (j : ℕ) * u j i := by
      intro t
      have hmem : i ∈ S (ν t) := by
        have hle : (Finset.univ : Finset (Fin (k + 1))).inf (fun t => S (ν t)) ≤ S (ν t) :=
          Finset.inf_le (Finset.mem_univ t)
        exact hle hiinf
      exact hSagree (ν t) (hνmem t) i hmem
    -- the curve evaluates to the fold at z
    have hcurve : (∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) *
        lagrangeCurve ν V j).eval (domain i) = ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i := by
      rw [lagrangeCurve_eval ν hνinj V z, Polynomial.eval_finset_sum]
      calc ∑ t : Fin (k + 1),
            (Polynomial.C ((Lagrange.basis Finset.univ ν t).eval z) * V t).eval (domain i)
          = ∑ t : Fin (k + 1), (Lagrange.basis Finset.univ ν t).eval z *
              ∑ j : Fin (k + 1), ν t ^ (j : ℕ) * u j i := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Polynomial.eval_mul, Polynomial.eval_C, hPt t]
        _ = ∑ t : Fin (k + 1), ∑ j : Fin (k + 1),
              ((Lagrange.basis Finset.univ ν t).eval z * ν t ^ (j : ℕ)) * u j i := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ j : Fin (k + 1), ∑ t : Fin (k + 1),
              ((Lagrange.basis Finset.univ ν t).eval z * ν t ^ (j : ℕ)) * u j i :=
            Finset.sum_comm
        _ = ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.sum_mul, lagrange_monomial_reproduction ν hνinj z j]
    -- the decode at z matches the fold at z
    have hPz : (P z).eval (domain i) = ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i :=
      hSagree z hz i hiz
    rw [Polynomial.eval_sub, hPz, hcurve, sub_self]
  -- root counting closes
  have hdegg : (P z - ∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) *
      lagrangeCurve ν V j).degree < deg := by
    rcases eq_or_ne (P z - ∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) *
        lagrangeCurve ν V j) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe deg
    · rw [← Polynomial.natDegree_lt_iff_degree_lt h0]
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ((hP z hz).1) ?_)
      have hle : (∑ j : Fin (k + 1), Polynomial.C (z ^ (j : ℕ)) *
          lagrangeCurve ν V j).natDegree ≤ deg - 1 := by
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        exact Nat.le_sub_one_of_lt (lagrangeCurve_natDegree_lt hdeg ν hVdeg j)
      omega
  have hzero := eq_zero_of_degree_lt_of_vanishes_on (domain := domain) hdegg W hWcard hvan
  exact sub_eq_zero.mp hzero

/-! ## §3 — deliverable (a): the producer glue -/

/-- **THE GLUE — `UnifiedProducer` on the unique-decoding window** (deliverable (a)): the
single production target of `UnifiedExtractionTarget` (both #304 cores + the closed-boundary
keystone) holds unconditionally on `curveUDWindow k deg n δ`.  The `CurveFamilyData` is the
Lagrange curve at centre `0` with the `k + 1` pinned coefficient polynomials. -/
theorem unifiedProducer_of_window {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ) :
    UnifiedExtractionTarget.UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F)
      domain δ := by
  intro u hcount P hP
  obtain ⟨a, _hadeg, haPz⟩ :=
    exists_curve_tuple_of_window hdeg hwin u
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) hcount P hP
  refine ⟨{ x₀ := 0
            n := k + 1
            hn := by omega
            c := fun t => if h : t < k + 1 then a ⟨t, h⟩ else 0
            hPz := ?_ }⟩
  intro z hz
  rw [haPz z hz]
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => (z - 0) ^ t • (if h : t < k + 1 then a ⟨t, h⟩ else 0)) (k + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dif_pos j.isLt, sub_zero, Polynomial.smul_eq_C_mul]

/-! ## §4 — deliverable (b): the closed-boundary keystone on the window -/

/-- **The closed-boundary Johnson-endpoint keystone from the window alone** (deliverable (b)):
`δ_ε_correlatedAgreementCurves` at `δ = 1 − √ρ` with the explicit positive error
`max (errorBound (cell radius)) ((n+1)/|F|)`, from the single window hypothesis at `δ` (the
cell-radius window is the same window: `curveUDWindow` only sees `⌊δ·n⌋`, and the cell radius
is floor-matched with `δ`).

HONESTY (regime): for `k ≥ 1` the window at `δ = 1 − √ρ` is satisfiable only in the
high-rate corner where ceiling/floor slack absorbs `(1−√ρ)(k+1−√ρ)·n` — e.g. `deg = n`
(`δ = 0`) or `⌊δ·n⌋ = 0` with `deg ≥` roughly `n − (k+2)`.  The theorem asserts nothing
outside the stated hypotheses. -/
theorem correlatedAgreementCurves_johnsonClosed_of_window
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg_le : deg ≤ Fintype.card ι)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := max (errorBound (BoundaryHalfState.boundaryCellRadius (Fintype.card ι) δ)
          deg domain)
        (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F)) := by
  have hdeg : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hwinCell : curveUDWindow k deg (Fintype.card ι)
      (BoundaryHalfState.boundaryCellRadius (Fintype.card ι) δ) :=
    (curveUDWindow_floor_congr
      (BoundaryHalfState.floor_boundaryCellRadius_mul hn δ)).mp hwin
  exact UnifiedExtractionTarget.correlatedAgreementCurves_johnsonClosed_of_producer
    hk hδeq hsqrt_le hdeg_le
    (unifiedProducer_of_window hdeg hwinCell)
    (unifiedProducer_of_window hdeg hwin)

/-! ## §5 — the strict residual family on the window (the #301 checking-bridge feed) -/

/-- The large-sector strict residual on the window, from the producer. -/
theorem strictCoeffPolysLargeResidual_of_window {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ) :
    ProximityGap.StrictCoeffPolysLargeResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  UnifiedExtractionTarget.strictCoeffPolysLargeResidual_of_producer
    (unifiedProducer_of_window hdeg hwin)

/-- The full strict §5 residual on the window: large sector by the producer, small sector by
Lagrange interpolation (`strictCoeffPolysResidual_of_large`). -/
theorem strictCoeffPolysResidual_of_window {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ) :
    ProximityGap.StrictCoeffPolysResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  ProximityGap.strictCoeffPolysResidual_of_large
    (strictCoeffPolysLargeResidual_of_window hdeg hwin)

/-- **Correlated agreement for affine curves on the window, strict radius**: at any
`δ < 1 − √ρ` satisfying the width-`k` window, with error `errorBound δ deg domain`.

HONESTY (regime): deep inside the window (`δ ≲ (1−ρ)/(k+2)`, `k ≥ 1`) the supplied residual
is consumed only through its `(1−ρ)/2 < δ` hypothesis, which is then false — the conclusion
is carried by the front door's internal dichotomy.  The two hypotheses are simultaneously
non-trivial only near the high-rate corner.  The non-vacuous content of the window glue is
`unifiedProducer_of_window` itself. -/
theorem correlatedAgreement_affine_curves_of_window
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hwin : curveUDWindow k deg (Fintype.card ι) δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_window (Nat.pos_of_ne_zero (NeZero.ne deg)) hwin
        hk u hprob hJ hδ P hP)

/-! ## §6 — the zero-error corner: the window at every width -/

/-- **The zero-error corner**: if `⌊δ·n⌋ = 0` and `deg ≤ n`, the window holds at every width
`k` — so the **full** `∀ k` residual family (the shape the STIR checking bridge consumes)
is produced.  (`⌊δ·n⌋ = 0` is the `δ < 1/n` corner: proximity data at radius `δ` is exact
agreement.) -/
theorem curveUDWindow_all_of_floor_eq_zero {deg n : ℕ} {δ : ℝ≥0}
    (hfloor : Nat.floor (δ * n) = 0) (hdeg_le : deg ≤ n) :
    ∀ k : ℕ, curveUDWindow k deg n δ := by
  intro k
  unfold curveUDWindow
  rw [hfloor, Nat.sub_zero]
  have hexp : (k + 2) * n = (k + 1) * n + n := by ring
  omega

/-- The full positive-width strict residual family in the zero-error corner — the exact
`hCA` shape of the STIR checking bridge (`stirCheckingCABridge`), produced genuinely (no
small-field vacuity): every instance routes through `unifiedProducer_of_window`. -/
theorem strictCoeffPolys_all_of_floor_eq_zero {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hfloor : Nat.floor (δ * (Fintype.card ι : ℝ≥0)) = 0)
    (hdeg_le : deg ≤ Fintype.card ι) :
    ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual
        (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  fun k _hk => strictCoeffPolysResidual_of_window hdeg
    (curveUDWindow_all_of_floor_eq_zero hfloor hdeg_le k)

end UnifiedProducerWindowGlue

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.UnifiedProducerWindowGlue.curveUDWindow_floor_congr
#print axioms ArkLib.UnifiedProducerWindowGlue.floor_agreement_card_of_relHammingDist_le
#print axioms ArkLib.UnifiedProducerWindowGlue.exists_curve_tuple_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.unifiedProducer_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.correlatedAgreementCurves_johnsonClosed_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.strictCoeffPolysLargeResidual_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.strictCoeffPolysResidual_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.correlatedAgreement_affine_curves_of_window
#print axioms ArkLib.UnifiedProducerWindowGlue.curveUDWindow_all_of_floor_eq_zero
#print axioms ArkLib.UnifiedProducerWindowGlue.strictCoeffPolys_all_of_floor_eq_zero
