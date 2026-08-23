/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandPairRank

/-!
# The far-pair rank bound — high-overlap stratum (#389, route 2)

Route 2 of the sub-Johnson supply wall (issue #389) is the *unconditional second
moment of the coherent-core value map*; the engine
`ProximityGap.Ownership.capacity_failure_bandwidth` already stratifies the pair
count by core overlap.  Two strata are fully controlled:

* the **small-overlap** stratum `|T ∩ T'| ≤ k` carries rank exactly `2m + 1`
  (`ProximityGap.PairRank.pair_coherence_kernel_card`);
* the **diagonal** `T = T'` carries rank exactly `m` (`card_coherent_eq`).

The remaining **high-overlap, off-diagonal** stratum `k < |T ∩ T'| < k+m+1` is the
*degeneracy obstacle*: the probe-measured rank law `2m+1 − max(0,|T∩T'|−k)`
predicts a rank strictly between `m` and `2m`, but the capstone currently bounds
it only by the trivial `m` (it simply drops the second core).  This file isolates
the genuinely provable content of that stratum.

What is proven here, all axiom-clean:

* `pairValDiff_sub` / `band_pairValDiff_surjective_of_indep` — the `m+1`
  conditions «`T`-band ∧ value-difference» are subtraction-linear, and they are
  **jointly surjective exactly when** the value-difference functional is not
  pinned to zero on the `T`-coherent subspace (`PairValIndependent`).  This is the
  precise, named, characterization of the degeneracy locus.
* `pair_rank_ge_m_succ_of_indep` — **the high-overlap rank bound**: for *any* two
  distinct cores (no overlap hypothesis whatsoever) whose pair is **non-degenerate**
  (`PairValIndependent`), the joint kernel of the `m+1` conditions satisfies

      `#kernel · q^(m+1) = q^M`,

  i.e. rank `≥ m+1`, strictly beating the trivial diagonal bound `m` that the
  capstone uses for the whole high-overlap stratum.  The unconditional
  diagonal/small-overlap strata are the proven lemmas above; the *only* residual
  is `PairValIndependent` on the degeneracy locus `k < |T∩T'| < k+m+1`.
* `pairValIndependent_of_small_overlap` — the small-overlap stratum supplies the
  non-degeneracy hypothesis (extracted from the proven joint surjectivity), so
  the *only* uncovered stratum is the high-overlap degeneracy locus.

**Honest scope.**  The pinning of `PairValIndependent` on the full degeneracy
locus — equivalently, the exact rank `2m+1 − (|T∩T'|−k)` there — is the named open
residual of route 2.  This brick proves the conditional rank gain and pins the
obstacle to exactly that hypothesis; it does not close the sub-Johnson wall.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.FarPairRank

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The value-difference functional -/

/-- The value-difference functional of the pinned `coeff k` of the two cores. -/
noncomputable def valDiff (dom : Fin n ↪ F) (k : ℕ) (T T' : Finset (Fin n))
    {M : ℕ} (c : Fin M → F) : F :=
  (coreInterp dom T (genPoly c)).coeff k - (coreInterp dom T' (genPoly c)).coeff k

theorem valDiff_sub (dom : Fin n ↪ F) (k : ℕ) (T T' : Finset (Fin n)) {M : ℕ}
    (x y : Fin M → F) :
    valDiff dom k T T' (x - y)
      = valDiff dom k T T' x - valDiff dom k T T' y := by
  unfold valDiff
  rw [coreInterp_genPoly_sub, coreInterp_genPoly_sub, Polynomial.coeff_sub,
    Polynomial.coeff_sub]
  ring

/-! ## The `m+1` condition family -/

open Classical in
/-- The `m+1` conditions «`T`-band coefficients ∧ value-difference», indexed by
`Fin m ⊕ Unit`. -/
noncomputable def bandValFamily (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    {M : ℕ} : (Fin m ⊕ Unit) → (Fin M → F) → F := fun j c =>
  match j with
  | Sum.inl j => (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ))
  | Sum.inr _ => valDiff dom k T T' c

theorem bandValFamily_sub (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    {M : ℕ} (j : Fin m ⊕ Unit) (x y : Fin M → F) :
    bandValFamily dom k m T T' j (x - y)
      = bandValFamily dom k m T T' j x - bandValFamily dom k m T T' j y := by
  rcases j with j | u
  · show (coreInterp dom T (genPoly (x - y))).coeff (k + 1 + (j : ℕ))
        = (coreInterp dom T (genPoly x)).coeff (k + 1 + (j : ℕ))
          - (coreInterp dom T (genPoly y)).coeff (k + 1 + (j : ℕ))
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
  · exact valDiff_sub dom k T T' x y

/-! ## The non-degeneracy hypothesis (the named degeneracy-locus residual) -/

open Classical in
/-- **The pair non-degeneracy hypothesis.**  Over the `T`-coherent subspace (the
generators meeting `T`'s `m` band conditions with target `0`), the
value-difference functional `valDiff` is *surjective* onto `F`.  This is the
exact condition under which the `T`-band conditions and the value difference are
**jointly** surjective; its failure is the degeneracy locus
`k < |T∩T'| < k+m+1` that the probe rank law `2m+1 − (|T∩T'|−k)` measures.

For small overlap `|T∩T'| ≤ k` it holds (the value difference is even surjective
on a *finer* subspace, by `pair_conditions_surjective`); on the diagonal `T = T'`
it fails identically (`valDiff = 0`). -/
def PairValIndependent (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    (M : ℕ) : Prop :=
  ∀ a : Fin m → F, ∀ tv : F, ∃ c : Fin M → F,
    (∀ j : Fin m, (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = a j)
      ∧ valDiff dom k T T' c = tv

open Classical in
/-- Under `PairValIndependent`, the `m+1` conditions are jointly surjective. -/
theorem band_pairValDiff_surjective_of_indep (dom : Fin n ↪ F) (k m : ℕ)
    {T T' : Finset (Fin n)} {M : ℕ}
    (hindep : PairValIndependent dom k m T T' M) :
    ∀ t : (Fin m ⊕ Unit) → F,
      ∃ c : Fin M → F, ∀ j, bandValFamily dom k m T T' j c = t j := by
  intro t
  obtain ⟨c, hband, hval⟩ := hindep (fun j => t (Sum.inl j)) (t (Sum.inr ()))
  refine ⟨c, fun j => ?_⟩
  rcases j with j | u
  · exact hband j
  · exact hval

/-! ## The high-overlap rank bound -/

open Classical in
/-- **THE FAR-PAIR HIGH-OVERLAP RANK BOUND (non-degenerate stratum).**  For any
two cores `T, T'` whose pair is non-degenerate (`PairValIndependent`) — in
particular any off-diagonal high-overlap pair `k < |T∩T'| < k+m+1` outside the
degeneracy locus — the joint kernel of the `m+1` conditions «`T`-coherence ∧
value-match» cuts the generator space by **exactly** `q^(m+1)`:

  `#{c | IsCoherent T ∧ coreInterp T coeff_k = coreInterp T' coeff_k} · q^(m+1) = q^M`.

This is rank `≥ m+1`, **strictly** beating the trivial diagonal bound `m` that
`capacity_failure_bandwidth` currently applies to the entire high-overlap
stratum.  The unconditional small-overlap (`pair_coherence_kernel_card`) and
diagonal (`card_coherent_eq`) strata are proven; the *only* residual is
`PairValIndependent` on the degeneracy locus. -/
theorem pair_rank_ge_m_succ_of_indep (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} {M : ℕ}
    (hindep : PairValIndependent dom k m T T' M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (m + 1) = (Fintype.card F) ^ M := by
  classical
  have h := card_kernel_eq_of_surjective (bandValFamily dom k m T T')
    (bandValFamily_sub dom k m T T')
    (band_pairValDiff_surjective_of_indep dom k m hindep)
  have hcardι : Fintype.card (Fin m ⊕ Unit) = m + 1 := by
    simp [Fintype.card_sum]
  rw [hcardι] at h
  rw [← h]
  congr 2
  refine Finset.filter_congr fun c _ => ?_
  constructor
  · rintro ⟨h1, h2⟩ j
    rcases j with j | u
    · exact h1 j
    · show valDiff dom k T T' c = (0 : F)
      unfold valDiff
      rw [h2, sub_self]
  · intro h
    refine ⟨fun j => h (Sum.inl j), ?_⟩
    have := h (Sum.inr ())
    show (coreInterp dom T (genPoly c)).coeff k
        = (coreInterp dom T' (genPoly c)).coeff k
    have hv : valDiff dom k T T' c = 0 := this
    unfold valDiff at hv
    exact sub_eq_zero.mp hv

/-! ## The small-overlap stratum supplies `PairValIndependent` -/

open Classical in
/-- **The small-overlap stratum is non-degenerate.**  For `|T∩T'| ≤ k` and
`M ≥ 2(k+m+1)`, `PairValIndependent` holds — extracted from the proven joint
surjectivity `pair_conditions_surjective` (which is even stronger: it controls
both bands and the value difference).  Hence
`pair_rank_ge_m_succ_of_indep` recovers (a coarsening of) the proven exact
`2m+1` count here, and the *only* uncovered stratum is the high-overlap locus. -/
theorem pairValIndependent_of_small_overlap (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hover : (T ∩ T').card ≤ k) {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    PairValIndependent dom k m T T' M := by
  intro a tv
  obtain ⟨c, hca, -, hcv⟩ :=
    pair_conditions_surjective dom hT hT' hover hM a (fun _ => 0) tv
  exact ⟨c, hca, hcv⟩

end ProximityGap.FarPairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarPairRank.valDiff_sub
#print axioms ProximityGap.FarPairRank.bandValFamily_sub
#print axioms ProximityGap.FarPairRank.band_pairValDiff_surjective_of_indep
#print axioms ProximityGap.FarPairRank.pair_rank_ge_m_succ_of_indep
#print axioms ProximityGap.FarPairRank.pairValIndependent_of_small_overlap
