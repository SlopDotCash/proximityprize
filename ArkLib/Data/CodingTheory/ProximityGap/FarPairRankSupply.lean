/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairCoherenceCount
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandPairRank

/-!
# The far-pair rank law, all strata (#389, route 2): the degeneracy locus is empty

The high-overlap stratum `k < |T∩T'|` of the deep-band second moment — recorded
as the *degeneracy obstacle* of route 2 and handled only conditionally
(`PairValIndependent`, `FarPairRankBound.lean`) — is resolved here EXACTLY and
unconditionally:

* `high_overlap_interp_eq` — **coincidence is forced**: two coherent cores
  overlapping in more than `k` points have EQUAL interpolants (both have degree
  `≤ k` and agree on `> k` nodes), so the pinned-value match costs nothing on
  this stratum.
* `card_pair_coherent_high_eq` — **the exact high-overlap count**: the joint
  event «both cores coherent ∧ values match» is exactly «the values on `T ∪ T'`
  come from one degree-`≤ k` polynomial», i.e. the `|T∪T'| − (k+1)` union-band
  conditions; hence

    `#{c : both coherent ∧ match} · q^{|T∪T'| − (k+1)} = q^M` — EXACT.

  Together with the proven small-overlap count (`card_pair_coherent_eq`, rank
  `2m+1`) this is the COMPLETE rank law `rank = 2m + 1 − max(0, o − k)` on every
  stratum: there are NO degenerate pairs, and the named residual
  `PairValIndependent` is bypassed entirely (probe:
  `scripts/probes/probe_farpair_rank.py` — exhaustive at F5, rank-verified at
  F97/F12289 on all strata).
* `capacity_failure_bandwidth_refined` — **the refined bandwidth law**: feeding
  the exact stratified counts through the second-moment engine gives, at every
  band radius, a stack with

    `C(n,k+m+1) · q ≤ #badSet · (C(n,k+m+1)
        + Σ_{j=k+1}^{k+m+1} C(k+m+1,j) · C(n,k+m+1−j) · q^{j−k})` —

  each overlap stratum `j` now pays only its true rank price `q^{j−k}` instead
  of the blanket `q^{m+1}` of `capacity_failure_bandwidth`.  The failure zone
  `#badSet ≥ q/2` extends to essentially the exact second-moment convergence
  range `C(n,k+m+1) ≳ q^{m+1}` (probe section C: previously vacuous instances
  such as RS[F₁₂₂₈₉, n=64, k=15], m=3 now certify thousands of bad scalars).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- A coherent core's interpolant has degree at most `k`: the band coefficients
vanish by coherence, everything above by the interpolation degree bound. -/
theorem coherent_interp_natDegree_le (dom : Fin n ↪ F) {k m : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {Q : F[X]}
    (hcoh : IsCoherent dom k m T Q) :
    (coreInterp dom T Q).natDegree ≤ k := by
  have hvs : Set.InjOn dom T := fun a _ b _ h => dom.injective h
  have hIdeg : (coreInterp dom T Q).degree
      < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [coreInterp, ← hT]
    exact Lagrange.degree_interpolate_lt _ hvs
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases Nat.lt_or_ge N (k + m + 1) with h | h
  · have hj : N - (k + 1) < m := by omega
    have hcoeff := hcoh ⟨N - (k + 1), hj⟩
    have hb' : k + 1 + (N - (k + 1)) = N := by omega
    rwa [hb'] at hcoeff
  · refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    exact lt_of_lt_of_le hIdeg (by exact_mod_cast h)

omit [Fintype F] [NeZero n] in
open Classical in
/-- **Coincidence is forced on the high-overlap stratum**: two coherent cores
overlapping in more than `k` points have EQUAL interpolants — both have degree
`≤ k` and agree on more than `k` nodes.  The degeneracy locus of route 2 is
empty: the value-match condition is not an independent constraint here. -/
theorem high_overlap_interp_eq (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1)
    (hT' : T'.card = k + m + 1) (hover : k < (T ∩ T').card) {Q : F[X]}
    (hcoh : IsCoherent dom k m T Q) (hcoh' : IsCoherent dom k m T' Q) :
    coreInterp dom T Q = coreInterp dom T' Q := by
  have h1 := coherent_interp_natDegree_le dom hT hcoh
  have h2 := coherent_interp_natDegree_le dom hT' hcoh'
  have hzero : coreInterp dom T Q - coreInterp dom T' Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := (T ∩ T').image (fun i => dom i)) ?_ ?_
    · have hcard : ((T ∩ T').image (fun i => dom i)).card = (T ∩ T').card :=
        Finset.card_image_of_injective _ dom.injective
      rw [hcard]
      have hlt : ((k : ℕ) : WithBot ℕ) < (((T ∩ T').card : ℕ) : WithBot ℕ) := by
        exact_mod_cast hover
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt
          (le_trans Polynomial.degree_le_natDegree (by exact_mod_cast h1)) hlt
      · exact lt_of_le_of_lt
          (le_trans Polynomial.degree_le_natDegree (by exact_mod_cast h2)) hlt
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hiT, hiT'⟩ := Finset.mem_inter.mp hi
      have hvsT : Set.InjOn dom T := fun a _ b _ h => dom.injective h
      have hvsT' : Set.InjOn dom T' := fun a _ b _ h => dom.injective h
      rw [eval_sub, coreInterp, coreInterp,
        Lagrange.eval_interpolate_at_node _ hvsT hiT,
        Lagrange.eval_interpolate_at_node _ hvsT' hiT', sub_self]
  exact sub_eq_zero.mp hzero

open Classical in
/-- **THE EXACT HIGH-OVERLAP PAIR COUNT** (the complete far-pair rank law's
remaining stratum): for cores overlapping in MORE than `k` points, the joint
event «both coherent ∧ values match» is exactly «the values on `T ∪ T'` come
from a single degree-`≤ k` polynomial», i.e. the `|T∪T'| − (k+1)` union-band
conditions, which are jointly surjective.  Hence

  `#{c : both coherent ∧ match} · q^{|T∪T'| − (k+1)} = q^M` — EXACT,

unconditionally: no `PairValIndependent` hypothesis, no degenerate pairs.
With `card_pair_coherent_eq` (small overlap, rank `2m+1`) this realizes the
probe rank law `rank = 2m + 1 − max(0, |T∩T'| − k)` on every stratum. -/
theorem card_pair_coherent_high_eq (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1)
    (hT' : T'.card = k + m + 1) (hover : k < (T ∩ T').card)
    {M d : ℕ} (hM : 2 * (k + m + 1) ≤ M) (hu : (T ∪ T').card = k + 1 + d) :
    (Finset.univ.filter (fun c : Fin M → F =>
        (IsCoherent dom k m T (coeffFamily M c)
          ∧ IsCoherent dom k m T' (coeffFamily M c))
        ∧ (coreInterp dom T (coeffFamily M c)).coeff k
            = (coreInterp dom T' (coeffFamily M c)).coeff k)).card
      * (Fintype.card F) ^ d = (Fintype.card F) ^ M := by
  have hvsU : Set.InjOn dom ((T ∪ T' : Finset (Fin n)) : Set (Fin n)) :=
    fun a _ b _ h => dom.injective h
  have hUM : (T ∪ T').card ≤ M := by
    have h := Finset.card_union_le T T'
    rw [hT, hT'] at h
    omega
  -- the union-band condition family
  set φ : Fin d → (Fin M → F) → F := fun j c =>
    (coreInterp dom (T ∪ T') (coeffFamily M c)).coeff (k + 1 + (j : ℕ)) with hφ
  -- subtraction-linearity
  have hsub : ∀ (j : Fin d) (x y : Fin M → F),
      φ j (x - y) = φ j x - φ j y := by
    intro j x y
    show (coreInterp dom (T ∪ T') (coeffFamily M (x - y))).coeff
        (k + 1 + (j : ℕ)) = _ - _
    rw [coeffFamily_sub]
    have hI : coreInterp dom (T ∪ T') (coeffFamily M x - coeffFamily M y)
        = coreInterp dom (T ∪ T') (coeffFamily M x)
          - coreInterp dom (T ∪ T') (coeffFamily M y) := by
      rw [coreInterp, coreInterp, coreInterp]
      have hvals : (fun i => (coeffFamily M x - coeffFamily M y).eval (dom i))
          = (fun i => (coeffFamily M x).eval (dom i))
            - (fun i => (coeffFamily M y).eval (dom i)) := by
        funext i
        simp [eval_sub]
      rw [hvals, map_sub]
    rw [hI, coeff_sub]
  -- joint surjectivity: prescribe the union interpolant directly
  have hsurj : ∀ t : Fin d → F, ∃ c : Fin M → F, ∀ j, φ j c = t j := by
    intro t
    set Q : F[X] := ∑ j : Fin d, C (t j) * X ^ (k + 1 + (j : ℕ)) with hQ
    have hQdeg : Q.natDegree ≤ k + d := by
      rw [hQ]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      calc (C (t j) * X ^ (k + 1 + (j : ℕ))).natDegree
          ≤ (C (t j)).natDegree
              + (X ^ (k + 1 + (j : ℕ)) : F[X]).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ k + d := by
            rw [natDegree_C, natDegree_X_pow]
            have := j.2
            omega
    have hQdeg' : Q.natDegree < M := by omega
    refine ⟨fun j => Q.coeff (j : ℕ), fun j => ?_⟩
    show (coreInterp dom (T ∪ T')
      (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff (k + 1 + (j : ℕ)) = t j
    rw [coeffFamily_reconstruct M hQdeg']
    rw [coreInterp_of_degree_lt dom (by
      rw [hu]
      calc Q.degree ≤ (Q.natDegree : WithBot ℕ) :=
            Polynomial.degree_le_natDegree
        _ < ((k + 1 + d : ℕ) : WithBot ℕ) := by exact_mod_cast by omega)]
    rw [hQ, Polynomial.finset_sum_coeff]
    calc ∑ i : Fin d, (C (t i) * X ^ (k + 1 + (i : ℕ))).coeff (k + 1 + (j : ℕ))
        = ∑ i : Fin d, (if i = j then t i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coeff_C_mul, coeff_X_pow]
          by_cases h2 : i = j
          · subst h2
            simp
          · rw [if_neg (by
              intro hji
              exact h2 (Fin.ext (by omega))), if_neg h2, mul_zero]
      _ = t j := by
          rw [Finset.sum_ite_eq' Finset.univ j (fun i => t i)]
          simp
  -- the exact kernel count
  have h := ProximityGap.PairRank.card_kernel_eq_of_surjective φ hsub hsurj
  rw [Fintype.card_fin] at h
  -- the kernel IS the joint event
  have hfeq : (Finset.univ.filter (fun c : Fin M → F =>
        (IsCoherent dom k m T (coeffFamily M c)
          ∧ IsCoherent dom k m T' (coeffFamily M c))
        ∧ (coreInterp dom T (coeffFamily M c)).coeff k
            = (coreInterp dom T' (coeffFamily M c)).coeff k))
      = @Finset.filter _ (fun c : Fin M → F => ∀ j, φ j c = 0)
          (fun c => Fintype.decidableForallFintype) Finset.univ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- both coherent ⟹ the union values come from one deg ≤ k polynomial
      rintro ⟨⟨hcoh, hcoh'⟩, -⟩
      have hPeq := high_overlap_interp_eq dom hT hT' hover hcoh hcoh'
      have hPdeg : (coreInterp dom T (coeffFamily M c)).natDegree ≤ k :=
        coherent_interp_natDegree_le dom hT hcoh
      have hagree : ∀ i ∈ T ∪ T', (coeffFamily M c).eval (dom i)
          = (coreInterp dom T (coeffFamily M c)).eval (dom i) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hiT | hiT'
        · have hvsT : Set.InjOn dom T := fun a _ b _ h => dom.injective h
          rw [coreInterp]
          exact (Lagrange.eval_interpolate_at_node
            (fun i => (coeffFamily M c).eval (dom i)) hvsT hiT).symm
        · have hvsT' : Set.InjOn dom T' := fun a _ b _ h => dom.injective h
          rw [hPeq, coreInterp]
          exact (Lagrange.eval_interpolate_at_node
            (fun i => (coeffFamily M c).eval (dom i)) hvsT' hiT').symm
      have hUI : coreInterp dom (T ∪ T') (coeffFamily M c)
          = coreInterp dom T (coeffFamily M c) := by
        rw [coreInterp, interpolate_congr_on dom (T ∪ T') hagree]
        exact (Lagrange.eq_interpolate hvsU (by
          calc (coreInterp dom T (coeffFamily M c)).degree
              ≤ ((coreInterp dom T (coeffFamily M c)).natDegree : WithBot ℕ) :=
                Polynomial.degree_le_natDegree
            _ < (((T ∪ T').card : ℕ) : WithBot ℕ) := by
                rw [hu]
                exact_mod_cast (by omega :
                  (coreInterp dom T (coeffFamily M c)).natDegree < k + 1 + d))).symm
      intro j
      show (coreInterp dom (T ∪ T') (coeffFamily M c)).coeff (k + 1 + (j : ℕ)) = 0
      rw [hUI]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · -- the union interpolant has deg ≤ k ⟹ both coherent ∧ match
      intro hker
      have hUdeg0 : (coreInterp dom (T ∪ T') (coeffFamily M c)).degree
          < (((T ∪ T').card : ℕ) : WithBot ℕ) := by
        rw [coreInterp]
        exact Lagrange.degree_interpolate_lt _ hvsU
      have hUdeg : (coreInterp dom (T ∪ T') (coeffFamily M c)).natDegree ≤ k := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases Nat.lt_or_ge N (k + 1 + d) with h2 | h2
        · have hj : N - (k + 1) < d := by omega
          have hcoeff : (coreInterp dom (T ∪ T') (coeffFamily M c)).coeff
              (k + 1 + (N - (k + 1))) = 0 := hker ⟨N - (k + 1), hj⟩
          have hb' : k + 1 + (N - (k + 1)) = N := by omega
          rwa [hb'] at hcoeff
        · refine Polynomial.coeff_eq_zero_of_degree_lt ?_
          refine lt_of_lt_of_le hUdeg0 ?_
          rw [hu]
          exact_mod_cast h2
      -- the per-core interpolants both equal the union interpolant
      have hcore : ∀ (S : Finset (Fin n)), S.card = k + m + 1 → S ⊆ T ∪ T' →
          coreInterp dom S (coeffFamily M c)
            = coreInterp dom (T ∪ T') (coeffFamily M c) := by
        intro S hScard hSsub
        have hvsS : Set.InjOn dom S := fun a _ b _ h => dom.injective h
        have hagree : ∀ i ∈ S, (coeffFamily M c).eval (dom i)
            = (coreInterp dom (T ∪ T') (coeffFamily M c)).eval (dom i) := by
          intro i hi
          rw [coreInterp]
          exact (Lagrange.eval_interpolate_at_node
            (fun i => (coeffFamily M c).eval (dom i)) hvsU (hSsub hi)).symm
        rw [coreInterp, interpolate_congr_on dom S hagree]
        exact (Lagrange.eq_interpolate hvsS (by
          rw [hScard]
          calc (coreInterp dom (T ∪ T') (coeffFamily M c)).degree
              ≤ ((coreInterp dom (T ∪ T') (coeffFamily M c)).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
            _ < ((k + m + 1 : ℕ) : WithBot ℕ) := by
                exact_mod_cast (by omega :
                  (coreInterp dom (T ∪ T') (coeffFamily M c)).natDegree
                    < k + m + 1))).symm
      have hIT := hcore T hT Finset.subset_union_left
      have hIT' := hcore T' hT' Finset.subset_union_right
      refine ⟨⟨fun jj => ?_, fun jj => ?_⟩, ?_⟩
      · show (coreInterp dom T (coeffFamily M c)).coeff (k + 1 + (jj : ℕ)) = 0
        rw [hIT]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · show (coreInterp dom T' (coeffFamily M c)).coeff (k + 1 + (jj : ℕ)) = 0
        rw [hIT']
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [hIT, hIT']
  rw [hfeq]
  exact h

open Classical in
/-- **THE REFINED CAPACITY-FAILURE BANDWIDTH LAW**: the second-moment engine
with the COMPLETE far-pair rank law — every overlap stratum `j` pays its exact
rank price `q^{j−k}` instead of the blanket `q^{m+1}`.  At every band radius
some stack satisfies

  `C(n,k+m+1) · q ≤ #badSet · (C(n,k+m+1)
      + Σ_{j=k+1}^{k+m+1} C(k+m+1,j) · C(n,k+m+1−j) · q^{j−k})`,

so `#badSet ≥ q/2` on essentially the exact second-moment convergence range
`C(n,k+m+1) ≥ Σ_j C(k+m+1,j)·C(n,k+m+1−j)·q^{j−k}` — strictly extending the
failure bandwidth of `capacity_failure_bandwidth`. -/
theorem capacity_failure_bandwidth_refined (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1) * Fintype.card F
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (n.choose (k + m + 1)
            + ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
                (k + m + 1).choose j * n.choose (k + m + 1 - j)
                  * (Fintype.card F) ^ (j - k)) := by
  set q := Fintype.card F with hq
  set M := 2 * (k + m + 1) with hM
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set Nm := Pm.card with hNm
  have hNmval : Nm = n.choose (k + m + 1) := by
    rw [hNm, hPm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos Nm with hNm0 | hNmpos
  · exact ⟨0, by rw [← hNmval, hNm0]; simp⟩
  set S := ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
    (k + m + 1).choose j * n.choose (k + m + 1 - j) * q ^ (j - k) with hS
  have hqpow : (Fintype.card F) ^ m * (Fintype.card F) ^ m * Fintype.card F
      = q ^ (2 * m + 1) := by
    rw [hq, ← pow_add, ← pow_succ]
    congr 1
    omega
  -- per-stack data
  set coh : (Fin M → F) → Finset (Finset (Fin n)) := fun c =>
    Pm.filter (fun T => IsCoherent dom k m T (coeffFamily M c)) with hcoh
  set w : (Fin M → F) → Finset (Fin n) → F := fun c T =>
    (coreInterp dom T (coeffFamily M c)).coeff k with hw
  set prs : (Fin M → F) → ℕ := fun c =>
    ((Pm ×ˢ Pm).filter (fun p =>
      (IsCoherent dom k m p.1 (coeffFamily M c)
        ∧ IsCoherent dom k m p.2 (coeffFamily M c))
      ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
          = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card with hprs
  set bad : (Fin M → F) → Finset F := fun c =>
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (coeffFamily M c).eval (dom i)) (fun i => (dom i) ^ k) γ)
    with hbad
  -- ── the exact first moment ──
  have hfirst : (∑ c : Fin M → F, (coh c).card) * q ^ m = Nm * q ^ M := by
    have hswap : ∑ c : Fin M → F, (coh c).card
        = ∑ T ∈ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            IsCoherent dom k m T (coeffFamily M c))).card := by
      simp only [hcoh, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap, Finset.sum_mul]
    calc ∑ T ∈ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            IsCoherent dom k m T (coeffFamily M c))).card * q ^ m
        = ∑ T ∈ Pm, q ^ M := by
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTcard : T.card = k + m + 1 :=
            (Finset.mem_powersetCard.mp hT).2
          rw [hq]
          exact card_coherent_eq dom hTcard (by omega)
      _ = Nm * q ^ M := by rw [Finset.sum_const, smul_eq_mul, hNm]
  -- ── the stratified second moment, now with the exact rank on EVERY stratum ──
  have hsecond : (∑ c : Fin M → F, prs c) * q ^ (2 * m + 1)
      ≤ Nm * Nm * q ^ M
        + ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
            Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j))
              * q ^ (M + (j - k)) := by
    have hswap : ∑ c : Fin M → F, prs c
        = ∑ p ∈ Pm ×ˢ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            (IsCoherent dom k m p.1 (coeffFamily M c)
              ∧ IsCoherent dom k m p.2 (coeffFamily M c))
            ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
                = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card := by
      simp only [hprs, Finset.card_filter]
      rw [Finset.sum_comm]
    -- per-pair: the exact rank price of the pair's overlap stratum
    have hperpair : ∀ p ∈ Pm ×ˢ Pm,
        (Finset.univ.filter (fun c : Fin M → F =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card
          * q ^ (2 * m + 1)
        ≤ if (p.1 ∩ p.2).card ≤ k then q ^ M
          else q ^ (M + ((p.1 ∩ p.2).card - k)) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hc1 : p.1.card = k + m + 1 := (Finset.mem_powersetCard.mp hp1).2
      have hc2 : p.2.card = k + m + 1 := (Finset.mem_powersetCard.mp hp2).2
      by_cases hcap : (p.1 ∩ p.2).card ≤ k
      · rw [if_pos hcap]
        have h := card_pair_coherent_eq dom hc1 hc2 hcap
          (M := M) (le_of_eq hM.symm)
        rw [hqpow] at h
        rw [← hq] at h
        exact le_of_eq h
      · rw [if_neg hcap]
        have hcap' : k < (p.1 ∩ p.2).card := Nat.lt_of_not_le hcap
        have hocap : (p.1 ∩ p.2).card ≤ k + m + 1 := by
          calc (p.1 ∩ p.2).card ≤ p.1.card :=
                Finset.card_le_card Finset.inter_subset_left
            _ = k + m + 1 := hc1
        have huv := Finset.card_union_add_card_inter p.1 p.2
        rw [hc1, hc2] at huv
        have hd : (p.1 ∪ p.2).card
            = k + 1 + (2 * (k + m + 1) - (p.1 ∩ p.2).card - (k + 1)) := by
          have hub : k + m + 1 ≤ (p.1 ∪ p.2).card := by
            calc k + m + 1 = p.1.card := hc1.symm
              _ ≤ (p.1 ∪ p.2).card :=
                  Finset.card_le_card Finset.subset_union_left
          omega
        have h := card_pair_coherent_high_eq dom hc1 hc2 hcap'
          (M := M) (le_of_eq hM.symm) hd
        rw [← hq] at h
        have hsplit : 2 * m + 1
            = (2 * (k + m + 1) - (p.1 ∩ p.2).card - (k + 1))
              + ((p.1 ∩ p.2).card - k) := by omega
        calc (Finset.univ.filter _).card * q ^ (2 * m + 1)
            = (Finset.univ.filter _).card
                * q ^ (2 * (k + m + 1) - (p.1 ∩ p.2).card - (k + 1))
                * q ^ ((p.1 ∩ p.2).card - k) := by
              rw [mul_assoc, ← pow_add, ← hsplit]
          _ = q ^ M * q ^ ((p.1 ∩ p.2).card - k) := by rw [h]
          _ = q ^ (M + ((p.1 ∩ p.2).card - k)) := by rw [← pow_add]
          _ ≤ q ^ (M + ((p.1 ∩ p.2).card - k)) := le_rfl
    -- the per-stratum pair count
    have hstr : ∀ j ∈ Finset.Icc (k + 1) (k + m + 1),
        ((Pm ×ˢ Pm).filter (fun p => (p.1 ∩ p.2).card = j)).card
          ≤ Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j)) := by
      intro j hj
      have hsumform : ((Pm ×ˢ Pm).filter
          (fun p => (p.1 ∩ p.2).card = j)).card
          = ∑ T ∈ Pm, (Pm.filter (fun T' => (T ∩ T').card = j)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.card_filter]
      rw [hsumform]
      calc ∑ T ∈ Pm, (Pm.filter (fun T' => (T ∩ T').card = j)).card
          ≤ ∑ T ∈ Pm, (k + m + 1).choose j * n.choose (k + m + 1 - j) := by
            refine Finset.sum_le_sum fun T hT => ?_
            have hTcard : T.card = k + m + 1 :=
              (Finset.mem_powersetCard.mp hT).2
            -- T' at overlap j contains a j-subset of T plus free points
            have hcover : Pm.filter (fun T' => (T ∩ T').card = j)
                ⊆ (T.powersetCard j).biUnion
                  (fun Sj => Pm.filter (fun T' => Sj ⊆ T')) := by
              intro T' hT'
              obtain ⟨hT'mem, hoj⟩ := Finset.mem_filter.mp hT'
              obtain ⟨Sj, hSsub, hScard⟩ :=
                Finset.exists_subset_card_eq (le_of_eq hoj.symm)
              refine Finset.mem_biUnion.mpr ⟨Sj, ?_, ?_⟩
              · exact Finset.mem_powersetCard.mpr
                  ⟨hSsub.trans Finset.inter_subset_left, hScard⟩
              · exact Finset.mem_filter.mpr
                  ⟨hT'mem, hSsub.trans Finset.inter_subset_right⟩
            calc (Pm.filter (fun T' => (T ∩ T').card = j)).card
                ≤ ((T.powersetCard j).biUnion
                    (fun Sj => Pm.filter (fun T' => Sj ⊆ T'))).card :=
                  Finset.card_le_card hcover
              _ ≤ ∑ Sj ∈ T.powersetCard j,
                  (Pm.filter (fun T' => Sj ⊆ T')).card :=
                  Finset.card_biUnion_le
              _ ≤ ∑ Sj ∈ T.powersetCard j, n.choose (k + m + 1 - j) := by
                  refine Finset.sum_le_sum fun Sj hSj => ?_
                  have hScard : Sj.card = j :=
                    (Finset.mem_powersetCard.mp hSj).2
                  calc (Pm.filter (fun T' => Sj ⊆ T')).card
                      ≤ ((Finset.univ : Finset (Fin n)).powersetCard
                          (k + m + 1 - j)).card := by
                        refine Finset.card_le_card_of_injOn
                          (fun T' => T' \ Sj) ?_ ?_
                        · intro T' hT'
                          obtain ⟨hT'mem, hST'⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp hT')
                          have hT'card : T'.card = k + m + 1 :=
                            (Finset.mem_powersetCard.mp hT'mem).2
                          rw [Finset.mem_coe, Finset.mem_powersetCard]
                          refine ⟨Finset.subset_univ _, ?_⟩
                          rw [Finset.card_sdiff_of_subset hST', hT'card,
                            hScard]
                        · intro a ha b hb hab
                          obtain ⟨-, hSa⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp ha)
                          obtain ⟨-, hSb⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp hb)
                          replace hab : a \ Sj = b \ Sj := hab
                          calc a = (a \ Sj) ∪ Sj :=
                                (Finset.sdiff_union_of_subset hSa).symm
                            _ = (b \ Sj) ∪ Sj := by rw [hab]
                            _ = b := Finset.sdiff_union_of_subset hSb
                      _ = n.choose (k + m + 1 - j) := by
                          rw [Finset.card_powersetCard, Finset.card_univ,
                            Fintype.card_fin]
              _ = (k + m + 1).choose j * n.choose (k + m + 1 - j) := by
                  rw [Finset.sum_const, Finset.card_powersetCard, hTcard,
                    smul_eq_mul]
        _ = Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j)) := by
            rw [Finset.sum_const, smul_eq_mul, hNm]
    -- assemble the strata
    rw [hswap, Finset.sum_mul]
    calc ∑ p ∈ Pm ×ˢ Pm, (Finset.univ.filter _).card * q ^ (2 * m + 1)
        ≤ ∑ p ∈ Pm ×ˢ Pm, (if (p.1 ∩ p.2).card ≤ k then q ^ M
            else q ^ (M + ((p.1 ∩ p.2).card - k))) :=
          Finset.sum_le_sum hperpair
      _ = ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => (p.1 ∩ p.2).card ≤ k), q ^ M
          + ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => ¬ (p.1 ∩ p.2).card ≤ k),
              q ^ (M + ((p.1 ∩ p.2).card - k)) := Finset.sum_ite _ _
      _ ≤ Nm * Nm * q ^ M
          + ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
              Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j))
                * q ^ (M + (j - k)) := by
          refine Nat.add_le_add ?_ ?_
          · rw [Finset.sum_const, smul_eq_mul]
            refine Nat.mul_le_mul_right _ ?_
            calc ((Pm ×ˢ Pm).filter (fun p => (p.1 ∩ p.2).card ≤ k)).card
                ≤ (Pm ×ˢ Pm).card := Finset.card_filter_le _ _
              _ = Nm * Nm := by rw [Finset.card_product, hNm]
          · -- fiber the high-overlap pairs by their exact overlap
            have hmaps : ∀ p ∈ (Pm ×ˢ Pm).filter
                (fun p => ¬ (p.1 ∩ p.2).card ≤ k),
                (p.1 ∩ p.2).card ∈ Finset.Icc (k + 1) (k + m + 1) := by
              intro p hp
              obtain ⟨hpm, hbig⟩ := Finset.mem_filter.mp hp
              obtain ⟨hp1, -⟩ := Finset.mem_product.mp hpm
              have hc1 : p.1.card = k + m + 1 :=
                (Finset.mem_powersetCard.mp hp1).2
              have hle : (p.1 ∩ p.2).card ≤ k + m + 1 := by
                calc (p.1 ∩ p.2).card ≤ p.1.card :=
                      Finset.card_le_card Finset.inter_subset_left
                  _ = k + m + 1 := hc1
              rw [Finset.mem_Icc]
              omega
            rw [← Finset.sum_fiberwise_of_maps_to hmaps
              (fun p => q ^ (M + ((p.1 ∩ p.2).card - k)))]
            refine Finset.sum_le_sum fun j hj => ?_
            have hconst : ∀ p ∈ ((Pm ×ˢ Pm).filter
                (fun p => ¬ (p.1 ∩ p.2).card ≤ k)).filter
                  (fun p => (p.1 ∩ p.2).card = j),
                q ^ (M + ((p.1 ∩ p.2).card - k)) = q ^ (M + (j - k)) := by
              intro p hp
              rw [(Finset.mem_filter.mp hp).2]
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
            refine Nat.mul_le_mul_right _ ?_
            calc (((Pm ×ˢ Pm).filter (fun p => ¬ (p.1 ∩ p.2).card ≤ k)).filter
                  (fun p => (p.1 ∩ p.2).card = j)).card
                ≤ ((Pm ×ˢ Pm).filter
                    (fun p => (p.1 ∩ p.2).card = j)).card := by
                  refine Finset.card_le_card ?_
                  intro p hp
                  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
                  exact Finset.mem_filter.mpr
                    ⟨(Finset.mem_filter.mp hp1).1, hp2⟩
              _ ≤ Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j)) :=
                  hstr j hj
  -- ── per-stack Cauchy–Schwarz over value fibers ──
  have hperCS : ∀ c : Fin M → F, (coh c).card ^ 2 ≤ (bad c).card * prs c := by
    intro c
    set img := (coh c).image (w c) with himg
    have hprsfib : prs c = ∑ v ∈ img, ((coh c).filter
        (fun T => w c T = v)).card ^ 2 := by
      show ((Pm ×ˢ Pm).filter (fun p =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card = _
      have hpairs : (Pm ×ˢ Pm).filter (fun p =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)
          = img.biUnion (fun v =>
            ((coh c).filter (fun T => w c T = v))
              ×ˢ ((coh c).filter (fun T => w c T = v))) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image, hcoh, hw, himg]
        constructor
        · rintro ⟨⟨h1, h2⟩, ⟨hcoh1, hcoh2⟩, heq2⟩
          exact ⟨(coreInterp dom p.1 (coeffFamily M c)).coeff k,
            ⟨p.1, ⟨h1, hcoh1⟩, rfl⟩,
            ⟨⟨h1, hcoh1⟩, rfl⟩, ⟨h2, hcoh2⟩, heq2.symm⟩
        · rintro ⟨v, -, ⟨⟨h1, hcoh1⟩, hv1⟩, ⟨h2, hcoh2⟩, hv2⟩
          exact ⟨⟨h1, h2⟩, ⟨hcoh1, hcoh2⟩, hv1.trans hv2.symm⟩
      rw [hpairs, Finset.card_biUnion (fun v hv v' hv' hne => by
        show Disjoint
          (((coh c).filter (fun T => w c T = v))
            ×ˢ ((coh c).filter (fun T => w c T = v)))
          (((coh c).filter (fun T => w c T = v'))
            ×ˢ ((coh c).filter (fun T => w c T = v')))
        rw [Finset.disjoint_left]
        rintro p hp hp'
        obtain ⟨h1, -⟩ := Finset.mem_product.mp hp
        obtain ⟨h1', -⟩ := Finset.mem_product.mp hp'
        exact hne (((Finset.mem_filter.mp h1).2).symm.trans
          (Finset.mem_filter.mp h1').2))]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Finset.card_product, sq]
    have hcohfib : (coh c).card = ∑ v ∈ img, ((coh c).filter
        (fun T => w c T = v)).card := by
      exact Finset.card_eq_sum_card_fiberwise fun T hT =>
        Finset.mem_image_of_mem _ hT
    have hCS : (coh c).card ^ 2 ≤ img.card * prs c := by
      rw [hprsfib, hcohfib]
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) img 1
        (fun v => ((coh c).filter (fun T => w c T = v)).card)
    have himgbad : img.card ≤ (bad c).card := by
      have h1 : img.card = (img.image (fun x => -x)).card :=
        (Finset.card_image_of_injective _ neg_injective).symm
      rw [h1]
      refine Finset.card_le_card ?_
      intro γ hγ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hT
      have hTcard : T.card = k + m + 1 :=
        (Finset.mem_powersetCard.mp hTmem).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mcaEvent_of_coherent dom hk hhi hTcard hTc⟩
    calc (coh c).card ^ 2 ≤ img.card * prs c := hCS
      _ ≤ (bad c).card * prs c := Nat.mul_le_mul_right _ himgbad
  -- ── the family-level Cauchy–Schwarz ──
  have hfamCS : (∑ c : Fin M → F, (coh c).card) ^ 2
      ≤ q ^ M * ∑ c : Fin M → F, (coh c).card ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ)
      (Finset.univ : Finset (Fin M → F)) 1 (fun c => (coh c).card)
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq] using h
  -- ── the maximizing stack ──
  obtain ⟨cstar, -, hcstar⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin M → F)) (fun c => (bad c).card)
    Finset.univ_nonempty
  set β := (bad cstar).card with hβ
  have hβbound : ∀ c : Fin M → F, (bad c).card ≤ β :=
    fun c => hcstar c (Finset.mem_univ c)
  -- ── assemble ──
  have hp2M : q ^ (2 * M) = q ^ M * q ^ M := by
    rw [← pow_add]
    congr 1
    omega
  have hp2m1 : q ^ (2 * m + 1) = q ^ m * q ^ m * q := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hsumS : ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
      Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j))
        * q ^ (M + (j - k))
      = q ^ M * (Nm * S) := by
    rw [hS, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [pow_add]
    ring
  have hkey : Nm * Nm * q ^ (2 * M) * q
      ≤ β * (q ^ (2 * M) * (Nm * (Nm + S))) := by
    calc Nm * Nm * q ^ (2 * M) * q
        = ((Nm * q ^ M) * (Nm * q ^ M)) * q := by rw [hp2M]; ring
      _ = (((∑ c : Fin M → F, (coh c).card) * q ^ m)
            * ((∑ c : Fin M → F, (coh c).card) * q ^ m)) * q := by
          rw [hfirst]
      _ = ((∑ c : Fin M → F, (coh c).card) ^ 2) * q ^ (2 * m + 1) := by
          rw [sq, hp2m1]
          ring
      _ ≤ (q ^ M * ∑ c : Fin M → F, (coh c).card ^ 2) * q ^ (2 * m + 1) :=
          Nat.mul_le_mul_right _ hfamCS
      _ ≤ (q ^ M * ∑ c : Fin M → F, β * prs c) * q ^ (2 * m + 1) := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
          refine Finset.sum_le_sum fun c _ => ?_
          calc (coh c).card ^ 2 ≤ (bad c).card * prs c := hperCS c
            _ ≤ β * prs c := Nat.mul_le_mul_right _ (hβbound c)
      _ = q ^ M * β * ((∑ c : Fin M → F, prs c) * q ^ (2 * m + 1)) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ q ^ M * β * (Nm * Nm * q ^ M
          + ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
              Nm * ((k + m + 1).choose j * n.choose (k + m + 1 - j))
                * q ^ (M + (j - k))) :=
          Nat.mul_le_mul_left _ hsecond
      _ = q ^ M * β * (Nm * Nm * q ^ M + q ^ M * (Nm * S)) := by
          rw [hsumS]
      _ = β * (q ^ (2 * M) * (Nm * (Nm + S))) := by
          rw [hp2M]
          ring
  -- cancel the positive factor Nm · q^{2M}
  have hkey2 : (Nm * q) * (Nm * q ^ (2 * M))
      ≤ (β * (Nm + S)) * (Nm * q ^ (2 * M)) := by
    calc (Nm * q) * (Nm * q ^ (2 * M))
        = Nm * Nm * q ^ (2 * M) * q := by ring
      _ ≤ β * (q ^ (2 * M) * (Nm * (Nm + S))) := hkey
      _ = (β * (Nm + S)) * (Nm * q ^ (2 * M)) := by ring
  have hq1 : 0 < q := by
    rw [hq]
    exact Fintype.card_pos
  have hfinal : Nm * q ≤ β * (Nm + S) :=
    Nat.le_of_mul_le_mul_right hkey2
      (Nat.mul_pos hNmpos (pow_pos hq1 _))
  -- conclude
  refine ⟨coeffFamily M cstar, ?_⟩
  show n.choose (k + m + 1) * q
    ≤ (bad cstar).card
      * (n.choose (k + m + 1)
        + ∑ j ∈ Finset.Icc (k + 1) (k + m + 1),
            (k + m + 1).choose j * n.choose (k + m + 1 - j) * q ^ (j - k))
  rw [← hNmval, ← hS, ← hβ]
  exact hfinal

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.coherent_interp_natDegree_le
#print axioms ProximityGap.Ownership.high_overlap_interp_eq
#print axioms ProximityGap.Ownership.card_pair_coherent_high_eq
#print axioms ProximityGap.Ownership.capacity_failure_bandwidth_refined
