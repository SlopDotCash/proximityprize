/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarPairRankBound

/-!
# The degeneracy-locus rank — deep-overlap stratum (#389, route 2)

The third Lean brick of the second-moment route through the sub-Johnson supply
wall.  `DeepBandPairRank.lean` controls the **small-overlap** strata
(`|T∩T'| ≤ k`, full rank `2m+1`) and `FarPairRankBound.lean` proves a
*conditional* rank gain off the degeneracy locus.  This file isolates the
**deep-overlap (degeneracy) stratum** `k < |T∩T'| =: j < k+m+1` itself, where the
probe-measured rank law `2m+1 − (j−k)` predicts a rank **strictly between** the
trivial diagonal bound `m` and the full `2m+1`.

Probe `probe_pair_coherence_rank.py` (re-run 2026-06-12): on the deep stratum the
rank is **exactly** `2m+1 − (j−k)` with **zero variance** — every pair at overlap
`j` has precisely that rank.  A companion structural probe
(`/tmp/probe_deep_struct.py`, six exhaustive instances `p∈{13,17}`, `k∈{2,3}`,
`m∈{1,2}`) confirms the mechanism: the `T`-band conditions are always rank `m`,
and the residual `(T'-band ∧ value-diff)` family, *restricted to the `T`-coherent
subspace*, has rank exactly `m+1 − (j−k)`.

## What is proven here (all axiom-clean)

* `coreInterp_degree_lt`, `coherent_coreInterp_degree_le`, `coreInterp_eval_eq`
  — the three structural facts about the `T`-core interpolant: it has degree
  `< |T|`; **coherence collapses its degree to `≤ k`**; and it reproduces `Q` on
  every node of `T`.
* `deep_pairCoherence_forces_coreInterp_eq` — **THE DEGENERACY MECHANISM**, fully
  unconditional.  On the deep stratum (`k+1 ≤ |T∩T'|`), every *pair-coherent*
  generator (`T`-coherent, `T'`-coherent, equal pinned values) forces

      `coreInterp dom T (genPoly c) = coreInterp dom T' (genPoly c)`,

  i.e. the two core interpolants **coincide identically**.  This is exactly why
  the rank drops: both interpolants are degree-`≤ k` and agree on the `j > k`
  shared nodes, so they are equal — the value-difference functional and the
  `T'`-band conditions collapse into the span of the `T`-coherence conditions.
  This is the precise, machine-checked content of "the value functional partially
  collapses into the span of `T`'s band conditions".
* `DeepPairValIndependent` + `deep_pair_rank_eq_of_indep` — **THE EXACT
  DEGENERACY-LOCUS RANK**, by the kernel engine `card_kernel_eq_of_surjective`.
  Conditional on the named, probe-matched deep non-degeneracy hypothesis
  `DeepPairValIndependent` (joint surjectivity of the reduced
  `2m+1 − (j−k)`-condition family that survives the collapse), the pair-coherence
  kernel satisfies

      `#kernel · q^(2m+1 − (j−k)) = q^M`,

  i.e. the rank is **exactly** `2m+1 − (j−k)` — the probe law, on the nose.  This
  hands the capstone a known, bounded *correction* term (rank `2m+1 − (j−k)`
  instead of the trivial `m`), not a wall.

## Honest scope (the residual, named precisely)

The companion probes establish that **no fixed, uniform `(2m+1 − (j−k))`-element
sub-family is surjective on every deep pair** — at overlap `j = k+m` the
value-difference functional collapses into the `T`-band span for *some* pairs and
not others (e.g. `k=3, m=1`: `T-band ⊕ vdiff` is surjective for some pairs,
deficient for others, both at `j = k+1`).  Hence the surjectivity witness is
**per-pair**, and pinning `DeepPairValIndependent` unconditionally is exactly the
finite rank-nullity computation over the coefficient space that is the named open
residual of this stratum.  This brick proves the *mechanism* (the interpolant
collapse) unconditionally, and proves the *exact rank* conditional on the
probe-matched non-degeneracy — completing the rank stratification down to that one
named, finite, linear-algebra hypothesis.  It does not close the sub-Johnson wall.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.DegeneracyRank

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank ProximityGap.FarPairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Structural facts about the core interpolant -/

/-- The `T`-core interpolant of any polynomial has degree `< |T|`. -/
theorem coreInterp_degree_lt (dom : Fin n ↪ F) (T : Finset (Fin n)) (Q : F[X]) :
    (coreInterp dom T Q).degree < (T.card : WithBot ℕ) := by
  have hvs : Set.InjOn (⇑dom) T := fun a _ b _ h => dom.injective h
  rw [coreInterp]
  exact Lagrange.degree_interpolate_lt _ hvs

/-- **Coherence collapses the interpolant degree.**  If `T` has size `k+m+1` and
`Q` is `T`-coherent (interpolant coefficients in degrees `k+1,…,k+m` all vanish),
then the `T`-core interpolant has degree `< k+1`, i.e. degree `≤ k`. -/
theorem coherent_coreInterp_degree_le (dom : Fin n ↪ F) {k m : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {Q : F[X]}
    (hcoh : IsCoherent dom k m T Q) :
    (coreInterp dom T Q).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro b hb
  have hbk : k + 1 ≤ b := by exact_mod_cast hb
  rcases Nat.lt_or_ge b (k + m + 1) with h2 | h2
  · -- inside the band: coherence kills it
    have hj : b - (k + 1) < m := by omega
    have hcoeff := hcoh ⟨b - (k + 1), hj⟩
    have hb' : k + 1 + ((⟨b - (k + 1), hj⟩ : Fin m) : ℕ) = b := by
      show k + 1 + (b - (k + 1)) = b; omega
    rw [hb'] at hcoeff
    exact hcoeff
  · -- above the interpolant degree
    refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    refine lt_of_lt_of_le (coreInterp_degree_lt dom T Q) ?_
    rw [hT]
    exact_mod_cast h2

/-- The `T`-core interpolant reproduces `Q` on every node of `T`. -/
theorem coreInterp_eval_eq (dom : Fin n ↪ F) (T : Finset (Fin n)) (Q : F[X])
    {i : Fin n} (hi : i ∈ T) :
    (coreInterp dom T Q).eval (dom i) = Q.eval (dom i) := by
  have hvs : Set.InjOn (⇑dom) T := fun a _ b _ h => dom.injective h
  rw [coreInterp]
  exact Lagrange.eval_interpolate_at_node _ hvs hi

/-! ## The degeneracy mechanism: the two interpolants coincide -/

/-- **THE DEGENERACY MECHANISM (unconditional).**  On the deep-overlap stratum
`k+1 ≤ |T∩T'|`, with both cores of size `k+m+1`, every pair-coherent generator
`c` — i.e. `T`-coherent, `T'`-coherent, and with equal pinned `coeff k` values —
forces the two core interpolants to **coincide identically**:

    `coreInterp dom T (genPoly c) = coreInterp dom T' (genPoly c)`.

Proof: coherence collapses both interpolants to degree `≤ k`; both interpolate the
same generator polynomial `genPoly c`, hence agree with each other on the `j ≥ k+1`
shared nodes `T ∩ T'`; two degree-`≤ k` polynomials agreeing on `≥ k+1` points are
equal.  (The equal-value hypothesis is *not even needed* for the identity — it is
subsumed — which is itself the source of the rank deficiency: the value-difference
condition is automatically implied.) -/
theorem deep_pairCoherence_forces_coreInterp_eq (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} {c : Fin M → F}
    (hcohT : IsCoherent dom k m T (genPoly c))
    (hcohT' : IsCoherent dom k m T' (genPoly c)) :
    coreInterp dom T (genPoly c) = coreInterp dom T' (genPoly c) := by
  have hvsI : Set.InjOn (⇑dom) ↑(T ∩ T') := fun a _ b _ h => dom.injective h
  -- both interpolants have degree ≤ k, hence < |T ∩ T'|
  have hdegT : (coreInterp dom T (genPoly c)).degree < ((T ∩ T').card : WithBot ℕ) := by
    refine lt_of_lt_of_le (coherent_coreInterp_degree_le dom hT hcohT) ?_
    exact_mod_cast hdeep
  have hdegT' : (coreInterp dom T' (genPoly c)).degree < ((T ∩ T').card : WithBot ℕ) := by
    refine lt_of_lt_of_le (coherent_coreInterp_degree_le dom hT' hcohT') ?_
    exact_mod_cast hdeep
  -- they agree on every node of T ∩ T' (both reproduce genPoly c there)
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (T ∩ T') hvsI hdegT hdegT' ?_
  intro i hi
  rw [coreInterp_eval_eq dom T (genPoly c) (Finset.mem_inter.mp hi).1,
    coreInterp_eval_eq dom T' (genPoly c) (Finset.mem_inter.mp hi).2]

/-- **Corollary: the value-difference is automatically zero on the deep
pair-coherent stratum.**  Since the interpolants coincide, the pinned values agree
for free — the value-difference functional `valDiff` contributes no independent
condition.  This is the rank deficiency, made explicit. -/
theorem deep_pairCoherence_valDiff_eq_zero (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} {c : Fin M → F}
    (hcohT : IsCoherent dom k m T (genPoly c))
    (hcohT' : IsCoherent dom k m T' (genPoly c)) :
    valDiff dom k T T' c = 0 := by
  unfold valDiff
  rw [deep_pairCoherence_forces_coreInterp_eq dom hT hT' hdeep hcohT hcohT', sub_self]

/-! ## Value-redundancy: the pair-coherence kernel is the two-band kernel -/

open Classical in
/-- **VALUE-REDUNDANCY (unconditional).**  On the deep-overlap stratum
`k+1 ≤ |T∩T'|`, the pinned-value condition is *redundant*: the pair-coherence set
(`T`-coherent ∧ `T'`-coherent ∧ equal pinned values) coincides with the pure
two-band set (`T`-coherent ∧ `T'`-coherent).  Indeed, once both cores are
coherent, the mechanism `deep_pairCoherence_forces_coreInterp_eq` makes the two
interpolants identical, so their `coeff k` are equal *for free*.  This is the
exact source of the rank deficiency: the value-difference functional carries no
independent linear condition on the deep stratum. -/
theorem deep_pairCoherence_eq_twoBand (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k))
      = (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c))) := by
  classical
  refine Finset.filter_congr fun c _ => ?_
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have := deep_pairCoherence_forces_coreInterp_eq dom hT hT' hdeep h1 h2
    rw [this]

/-! ## The exact rank on the degeneracy locus (kernel engine) -/

open Classical in
/-- **The deep-stratum non-degeneracy hypothesis** (the named residual).  On the
deep overlap `j = |T∩T'|` with `d := j − k` collapsed dimensions, the *two-band*
condition family — the `T`-band (`m` conditions) together with the `m − d`
*surviving* `T'`-band coordinates (selected by `surv`) — is **jointly
surjective** onto `F^(2m − d)` AND has the dropped `d` `T'`-band coordinates in
its span (so its kernel equals the full two-band kernel).  Equivalently: the
surviving family is a *spanning subset* of full rank `2m − d = 2m+1 − (j−k) − 1`…

Concretely we bundle the two pieces the per-pair rank-nullity computation
supplies: (i) `surjective` — joint surjectivity of the surviving `2m − d`
conditions; (ii) `implies_full` — the dropped `T'`-band coordinates vanish on the
surviving kernel.  The probe measures `rank{T-band, T'-band} = 2m+1 − (j−k)` with
zero variance, equivalently `2m − d` independent surviving band conditions whose
kernel is the full two-band kernel; this hypothesis names exactly that finite,
per-pair, full-rank fact. -/
structure DeepPairValIndependent (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    (M : ℕ) (surv : Fin (m + 1 - ((T ∩ T').card - k)) → Fin m) : Prop where
  surjective :
    ∀ t : (Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k))) → F,
      ∃ c : Fin M → F,
        (∀ j : Fin m,
          (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = t (Sum.inl j)) ∧
        (∀ j : Fin (m + 1 - ((T ∩ T').card - k)),
          (coreInterp dom T' (genPoly c)).coeff (k + 1 + ((surv j : Fin m) : ℕ))
            = t (Sum.inr j))
  implies_full :
    ∀ c : Fin M → F,
      (∀ j : Fin m, (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = 0) →
      (∀ j : Fin (m + 1 - ((T ∩ T').card - k)),
        (coreInterp dom T' (genPoly c)).coeff (k + 1 + ((surv j : Fin m) : ℕ)) = 0) →
      IsCoherent dom k m T' (genPoly c)

open Classical in
/-- The reduced surviving two-band family, indexed by `Fin m ⊕ Fin (m-d)`. -/
noncomputable def deepFamily (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    {M : ℕ} (surv : Fin (m + 1 - ((T ∩ T').card - k)) → Fin m) :
    (Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k))) → (Fin M → F) → F :=
  fun j c =>
    match j with
    | Sum.inl j => (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ))
    | Sum.inr j =>
        (coreInterp dom T' (genPoly c)).coeff (k + 1 + ((surv j : Fin m) : ℕ))

theorem deepFamily_sub (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    {M : ℕ} (surv : Fin (m + 1 - ((T ∩ T').card - k)) → Fin m)
    (j : Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k))) (x y : Fin M → F) :
    deepFamily dom k m T T' surv j (x - y)
      = deepFamily dom k m T T' surv j x - deepFamily dom k m T T' surv j y := by
  rcases j with j | j
  · show (coreInterp dom T (genPoly (x - y))).coeff (k + 1 + (j : ℕ))
        = (coreInterp dom T (genPoly x)).coeff (k + 1 + (j : ℕ))
          - (coreInterp dom T (genPoly y)).coeff (k + 1 + (j : ℕ))
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
  · show (coreInterp dom T' (genPoly (x - y))).coeff (k + 1 + ((surv j : Fin m) : ℕ))
        = (coreInterp dom T' (genPoly x)).coeff (k + 1 + ((surv j : Fin m) : ℕ))
          - (coreInterp dom T' (genPoly y)).coeff (k + 1 + ((surv j : Fin m) : ℕ))
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]

open Classical in
theorem deepFamily_surjective_of_indep (dom : Fin n ↪ F) (k m : ℕ)
    {T T' : Finset (Fin n)} {M : ℕ}
    {surv : Fin (m + 1 - ((T ∩ T').card - k)) → Fin m}
    (hindep : DeepPairValIndependent dom k m T T' M surv) :
    ∀ t : (Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k))) → F,
      ∃ c : Fin M → F, ∀ j, deepFamily dom k m T T' surv j c = t j := by
  intro t
  obtain ⟨c, hT, hT'⟩ := hindep.surjective t
  refine ⟨c, fun j => ?_⟩
  rcases j with j | j
  · exact hT j
  · exact hT' j

open Classical in
/-- **THE EXACT DEGENERACY-LOCUS RANK.**  On the deep-overlap stratum
`k+1 ≤ |T∩T'| ≤ k+m` (off-diagonal), conditional on the named deep
non-degeneracy `DeepPairValIndependent`, the pair-coherence kernel satisfies

    `#{c | IsCoherent T ∧ IsCoherent T' ∧ coeff_k I_T = coeff_k I_{T'}}
        · q^(2m+1 − (|T∩T'|−k)) = q^M`,

i.e. the rank is **exactly** `2m+1 − (|T∩T'|−k)` — the probe law, on the nose.
Two facts combine: (1) `deep_pairCoherence_eq_twoBand` — the value condition is
redundant, so the pair-coherence set equals the two-band set, *unconditionally*;
(2) the surviving family (full `T`-band `m` conditions plus the `m + 1 − d`
surviving `T'`-band coordinates, `d := |T∩T'| − k`) is jointly surjective and has
the dropped `T'`-band coordinates in its span (the named hypothesis
`DeepPairValIndependent`), so its kernel is exactly the two-band kernel.  Its
index card is `m + (m + 1 − d) = 2m + 1 − d`, matching the probe rank
`2m+1 − (j−k)` measured with zero variance.  (The probe's "`+1`" over the naive
`2m − d` two-band-row count is real: on the deep stratum the two `m`-band families
share only `d − 1` dependencies, not `d`, so their joint rank is `2m + 1 − d`; the
value row is the redundant one.) -/
theorem deep_pair_rank_eq_of_indep (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    {M : ℕ} {surv : Fin (m + 1 - ((T ∩ T').card - k)) → Fin m}
    (hindep : DeepPairValIndependent dom k m T T' M surv) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (2 * m + 1 - ((T ∩ T').card - k)) = (Fintype.card F) ^ M := by
  classical
  have hd1 : 1 ≤ (T ∩ T').card - k := by omega
  have hdm : (T ∩ T').card - k ≤ m := by omega
  have h := card_kernel_eq_of_surjective (deepFamily dom k m T T' surv)
    (deepFamily_sub dom k m T T' surv)
    (deepFamily_surjective_of_indep dom k m hindep)
  have hcardι :
      Fintype.card (Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k)))
        = 2 * m + 1 - ((T ∩ T').card - k) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  rw [hcardι] at h
  rw [deep_pairCoherence_eq_twoBand dom hT hT' hdeep, ← h]
  congr 2
  refine Finset.filter_congr fun c _ => ?_
  constructor
  · -- two-band coherent ⟹ in the surviving-family kernel
    rintro ⟨h1, h2⟩ j
    rcases j with j | j
    · exact h1 j
    · change (coreInterp dom T' (genPoly c)).coeff (k + 1 + ((surv j : Fin m) : ℕ)) = (0 : F)
      exact h2 (surv j)
  · -- surviving-family kernel ⟹ two-band coherent (via implies_full)
    intro hker
    have hcohT : IsCoherent dom k m T (genPoly c) := fun j => hker (Sum.inl j)
    refine ⟨hcohT, ?_⟩
    refine hindep.implies_full c hcohT ?_
    intro j
    exact hker (Sum.inr j)

end ProximityGap.DegeneracyRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DegeneracyRank.coreInterp_degree_lt
#print axioms ProximityGap.DegeneracyRank.coherent_coreInterp_degree_le
#print axioms ProximityGap.DegeneracyRank.coreInterp_eval_eq
#print axioms ProximityGap.DegeneracyRank.deep_pairCoherence_forces_coreInterp_eq
#print axioms ProximityGap.DegeneracyRank.deep_pairCoherence_valDiff_eq_zero
#print axioms ProximityGap.DegeneracyRank.deep_pairCoherence_eq_twoBand
#print axioms ProximityGap.DegeneracyRank.deepFamily_sub
#print axioms ProximityGap.DegeneracyRank.deepFamily_surjective_of_indep
#print axioms ProximityGap.DegeneracyRank.deep_pair_rank_eq_of_indep
