/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DegeneracyLocusRank

/-!
# Deep-stratum rank, unconditional lower bound (#389, route 2)

`DegeneracyLocusRank.lean` proves the **exact** deep-stratum rank
`2m+1 − (j−k)` *conditional* on the bundled non-degeneracy hypothesis
`DeepPairValIndependent` (joint surjectivity of the full `2m+1−(j−k)`-element
surviving two-band family).  This file removes the heavy hypothesis as far as it
can be removed, replacing it by the **minimal single-coordinate residual** and
proving everything around it **unconditionally**.

## What is proven here (all axiom-clean)

* `tband_surjective` — **UNCONDITIONAL.**  On *any* core `T` of size `k+m+1`
  (no overlap, no second-core, no degeneracy hypothesis whatsoever) and generator
  space `F^M` with `M ≥ k+m+1`, the `m` `T`-band conditions
  `coeff (k+1+j) (coreInterp T)` are **jointly surjective** onto `F^m`.  The
  construction is the bare Lagrange lift `Q := interpolate T (Σ aⱼ X^{k+1+j})`,
  with no patch — the overlap-`≤ k` restriction of `pair_conditions_surjective`
  is *not* needed when only `T` is constrained.

* `deep_pair_rank_ge_m` — **UNCONDITIONAL.**  Hence the pair-coherence
  (= two-band) kernel obeys `#kernel · q^m ≤ q^M`, i.e. rank `≥ m`, on the whole
  deep stratum with no hypothesis.  (This is the capstone's trivial bound, but
  re-derived from the explicit surjective `T`-band family rather than from
  dropping the second core.)

* `SurvivingTPrimeCoord` — **the minimal residual**, a *single-functional*
  hypothesis: there exists one surviving `T'`-band coordinate `d : Fin m` such
  that the `(m+1)`-element family «`m` `T`-band conditions ∧ that one `T'`-band
  coordinate» is jointly surjective onto `F^{m+1}`.  The structural probe
  (`/tmp/probe3.py`, six exhaustive instances `p∈{13,17,19}`, `k∈{2,3}`,
  `m∈{1,2,3}`) shows such a coordinate **always exists** on every deep pair —
  `0/N` pairs lacked one — so this residual is genuinely *minimal*: it is the
  non-vanishing of a single linear functional, not the full `(2m+1−(j−k))`-row
  surjectivity bundled by `DeepPairValIndependent`.

* `deep_pair_rank_ge_m_succ` — **rank `≥ m+1` from the single-coordinate
  residual.**  Conditional on `SurvivingTPrimeCoord` (and *nothing else* — no
  overlap bound, no value-redundancy input beyond the proven mechanism), the
  two-band kernel obeys

      `#kernel · q^(m+1) ≤ q^M`,

  i.e. rank `≥ m+1`, strictly beating the trivial diagonal/capstone bound `m`
  for *every* deep pair, conditional only on a *single* surviving functional.

## Honest scope (what genuinely remains, named precisely)

`SurvivingTPrimeCoord` is the irreducible per-pair fact.  The probe shows it
**holds for every deep pair**, but the witness coordinate `d` is *pair-dependent*
— there is **no fixed `d`** that works uniformly (at overlap `j = k+m` the `k+1`
coordinate collapses into the `T`-band span for some pairs and survives for
others, both at the same `j`; `/tmp/probe2.py`).  So pinning
`SurvivingTPrimeCoord` unconditionally is exactly a *single*-functional
non-vanishing that must be decided per pair — a strict reduction of the
`DeepPairValIndependent` residual (full `2m−(j−k)+1`-row surjectivity) down to
**one** linear functional.  This brick:

  * removes the heavy hypothesis from the `rank ≥ m` half **entirely**
    (unconditional), and
  * reduces the `rank ≥ m+1` half from a `(2m+1−(j−k))`-dimensional surjectivity
    to a **single** surviving-coordinate existence.

It does not close the sub-Johnson wall.

## SUPERSEDED (high-overlap stratum): the residual `SurvivingTPrimeCoord` is *not needed*

`deep_pair_rank_ge_m_succ` is stated on the **high-overlap** stratum `k+1 ≤ |T∩T'|`
(`hdeep`) and buys `rank ≥ m+1` only *conditionally* on `SurvivingTPrimeCoord`.  That same
stratum is resolved **unconditionally and exactly** by `FarPairRankSupply.lean`
(`high_overlap_interp_eq` / `card_pair_coherent_high_eq`, committed alongside this file):
forced coincidence of the two coherent interpolants gives the exact count

    `#{both coherent ∧ values match} · q^{|T∪T'| − (k+1)} = q^M`,

and with `|T∪T'| = 2(k+m+1) − o` the exponent is `k+2m+1 − o ≥ m+1` for every
`o ∈ [k+1, k+m]` — so `#kernel · q^(m+1) ≤ q^M` holds with **no hypothesis**, strictly
beating the conditional bound here.  (At the edge `o = k+m+1` the cores coincide, `T = T'`,
where `SurvivingTPrimeCoord` is unsatisfiable and the conditional statement is vacuous.)

Hence `SurvivingTPrimeCoord` is a **dead residual**: solvers should NOT invest in pinning it.
What this file still contributes unconditionally and irredundantly is the *low*-overlap half
— `tband_surjective` / `deep_pair_rank_ge_m` (the bare Lagrange-lift surjectivity of the
`T`-band family) — which underpins, rather than competes with, the complete rank law
`rank = 2m + 1 − max(0, o − k)`.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.DeepStratumUncond

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank ProximityGap.FarPairRank
  ProximityGap.DegeneracyRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Unconditional surjectivity of the `T`-band conditions -/

open Classical in
/-- **UNCONDITIONAL surjectivity of the `m` `T`-band conditions.**  For any single
core `T` of size `k+m+1` and `M ≥ k+m+1`, the band coefficients
`coeff (k+1+j) (coreInterp T (genPoly c))`, `j : Fin m`, are jointly surjective
onto `F^m`.  No overlap or second core is involved: build the prescribed
interpolant `p = Σ aⱼ X^{k+1+j}` (degree `< k+m+1`) and lift it through the `≤ M`
nodes of `T` — its `T`-core interpolant is `p` exactly. -/
theorem tband_surjective (dom : Fin n ↪ F) {k m : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {M : ℕ} (hM : k + m + 1 ≤ M)
    (a : Fin m → F) :
    ∃ c : Fin M → F,
      ∀ j : Fin m, (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = a j := by
  classical
  have hinj : ∀ s : Finset (Fin n), Set.InjOn (⇑dom) s :=
    fun s x _ y _ h => dom.injective h
  set p : F[X] := ∑ j : Fin m, C (a j) * X ^ (k + 1 + (j : ℕ)) with hp
  have hpdeg : p.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hp, Finset.univ_eq_empty, Finset.sum_empty, degree_zero]
      exact WithBot.bot_lt_coe _
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (k + m + 1))]
    intro j _
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (by omega : k + 1 + (j : ℕ) < k + m + 1)
  have hpcoeff : ∀ d : ℕ, p.coeff d
      = ∑ j : Fin m, if k + 1 + (j : ℕ) = d then a j else 0 := by
    intro d
    rw [hp, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne d (k + 1 + (j : ℕ)) with h | h
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
  have hpband : ∀ j : Fin m, p.coeff (k + 1 + (j : ℕ)) = a j := by
    intro j
    rw [hpcoeff, Finset.sum_eq_single j]
    · simp
    · intro j' _ hne
      rw [if_neg (by intro h; exact hne (Fin.ext (by omega)))]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- lift p through T
  set Q : F[X] := Lagrange.interpolate T (⇑dom) (fun i => p.eval (dom i)) with hQdef
  have hQdeg : Q.degree < (M : WithBot ℕ) := by
    refine lt_of_lt_of_le ?_ (by exact_mod_cast hT ▸ hM : (T.card : WithBot ℕ) ≤ (M : WithBot ℕ))
    exact_mod_cast Lagrange.degree_interpolate_lt _ (hinj T)
  set c : Fin M → F := fun j => Q.coeff (j : ℕ) with hc
  have hgen : genPoly c = Q := genPoly_coeff_eq hQdeg
  have hQT : ∀ i ∈ T, Q.eval (dom i) = p.eval (dom i) := by
    intro i hi
    rw [hQdef, Lagrange.eval_interpolate_at_node _ (hinj T) hi]
  have hIT : coreInterp dom T Q = p := by
    rw [coreInterp]
    have h1 : Lagrange.interpolate T (⇑dom) (fun i => Q.eval (dom i))
        = Lagrange.interpolate T (⇑dom) (fun i => p.eval (dom i)) :=
      Lagrange.interpolate_eq_of_values_eq_on _ _ hQT
    rw [h1]
    exact (Lagrange.eq_interpolate (hinj T) (by rw [hT]; exact hpdeg)).symm
  exact ⟨c, fun j => by rw [hgen, hIT]; exact hpband j⟩

/-! ## The `T`-band condition family, indexed by `Fin m` -/

open Classical in
/-- The `m` `T`-band conditions as a `Fin m`-indexed family on `F^M`. -/
noncomputable def tbandFamily (dom : Fin n ↪ F) (k m : ℕ) (T : Finset (Fin n))
    {M : ℕ} : Fin m → (Fin M → F) → F :=
  fun j c => (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ))

theorem tbandFamily_sub (dom : Fin n ↪ F) (k m : ℕ) (T : Finset (Fin n))
    {M : ℕ} (j : Fin m) (x y : Fin M → F) :
    tbandFamily dom k m T j (x - y)
      = tbandFamily dom k m T j x - tbandFamily dom k m T j y := by
  show (coreInterp dom T (genPoly (x - y))).coeff (k + 1 + (j : ℕ))
      = (coreInterp dom T (genPoly x)).coeff (k + 1 + (j : ℕ))
        - (coreInterp dom T (genPoly y)).coeff (k + 1 + (j : ℕ))
  rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]

/-! ## Unconditional rank `≥ m` on the whole deep stratum -/

open Classical in
/-- **UNCONDITIONAL rank `≥ m`.**  On the deep stratum, with both cores of size
`k+m+1`, the pair-coherence (= two-band) kernel obeys `#kernel · q^m ≤ q^M`.
Proof: the two-band set is a *subset* of the `T`-coherent set, whose exact card is
`q^(M−m)` by the unconditional `T`-band surjectivity.  No degeneracy hypothesis. -/
theorem deep_pair_rank_ge_m (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} (hM : k + m + 1 ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ m ≤ (Fintype.card F) ^ M := by
  classical
  -- exact card of the T-coherent set via the surjective T-band family
  have hker := card_kernel_eq_of_surjective (tbandFamily dom k m T)
    (tbandFamily_sub dom k m T)
    (fun t => by
      obtain ⟨c, hc⟩ := tband_surjective dom hT hM t
      exact ⟨c, fun j => hc j⟩)
  rw [Fintype.card_fin] at hker
  -- two-band ⊆ tband-kernel
  have hsub : (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k))
      ⊆ (Finset.univ.filter (fun c : Fin M → F =>
          ∀ j, tbandFamily dom k m T j c = 0)) := by
    intro c hc
    obtain ⟨h1, _, _⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => h1 j⟩
  calc _ ≤ (Finset.univ.filter (fun c : Fin M → F =>
              ∀ j, tbandFamily dom k m T j c = 0)).card
            * (Fintype.card F) ^ m := by
          exact Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ = (Fintype.card F) ^ M := by
          convert hker using 4

/-! ## The minimal single-coordinate residual -/

open Classical in
/-- **The minimal deep-stratum residual** (single surviving `T'`-band coordinate).
There exists one coordinate `d : Fin m` such that the `(m+1)`-element family — the
`m` `T`-band conditions together with the *single* `T'`-band coordinate `d` — is
jointly surjective onto `F^{m+1}`.  The structural probe shows such a `d` exists
on *every* deep pair (`0/N` pairs lacked one), but the witness is **per-pair**
(no fixed `d` works at overlap `j = k+m`).  This is a strict reduction of
`DeepPairValIndependent`: a *single* surviving functional, not the full
`(2m+1−(j−k))`-row surjectivity. -/
def SurvivingTPrimeCoord (dom : Fin n ↪ F) (k m : ℕ) (T T' : Finset (Fin n))
    (M : ℕ) : Prop :=
  ∃ d : Fin m, ∀ t : (Fin m ⊕ Unit) → F, ∃ c : Fin M → F,
    (∀ j : Fin m, (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = t (Sum.inl j))
      ∧ (coreInterp dom T' (genPoly c)).coeff (k + 1 + (d : ℕ)) = t (Sum.inr ())

open Classical in
/-- The `(m+1)`-element family «`m` `T`-band ∧ one `T'`-coord `d`», on `Fin m ⊕ Unit`. -/
noncomputable def survFamily (dom : Fin n ↪ F) (k : ℕ) {m : ℕ} (T T' : Finset (Fin n))
    (d : Fin m) {M : ℕ} : (Fin m ⊕ Unit) → (Fin M → F) → F :=
  fun j c =>
    match j with
    | Sum.inl j => (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ))
    | Sum.inr _ => (coreInterp dom T' (genPoly c)).coeff (k + 1 + (d : ℕ))

theorem survFamily_sub (dom : Fin n ↪ F) (k : ℕ) {m : ℕ} (T T' : Finset (Fin n))
    (d : Fin m) {M : ℕ} (j : Fin m ⊕ Unit) (x y : Fin M → F) :
    survFamily dom k T T' d j (x - y)
      = survFamily dom k T T' d j x - survFamily dom k T T' d j y := by
  rcases j with j | u
  · show (coreInterp dom T (genPoly (x - y))).coeff (k + 1 + (j : ℕ))
        = (coreInterp dom T (genPoly x)).coeff (k + 1 + (j : ℕ))
          - (coreInterp dom T (genPoly y)).coeff (k + 1 + (j : ℕ))
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
  · show (coreInterp dom T' (genPoly (x - y))).coeff (k + 1 + (d : ℕ))
        = (coreInterp dom T' (genPoly x)).coeff (k + 1 + (d : ℕ))
          - (coreInterp dom T' (genPoly y)).coeff (k + 1 + (d : ℕ))
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]

/-! ## Rank `≥ m+1` from the single-coordinate residual -/

open Classical in
/-- **rank `≥ m+1` FROM THE SINGLE-COORDINATE RESIDUAL.**  On the deep stratum,
conditional only on `SurvivingTPrimeCoord` (one surviving `T'`-band coordinate),
the pair-coherence (= two-band) kernel obeys

    `#kernel · q^(m+1) ≤ q^M`,

i.e. rank `≥ m+1`, strictly beating the trivial capstone bound `m`.  Proof: the
surviving `(m+1)`-element family is jointly surjective (its kernel has exact card
`q^(M−(m+1))`), and the two-band set is *contained* in that kernel (a two-band
generator is `T`-coherent, so meets the `m` band conditions, and is `T'`-coherent,
so its single `T'`-coordinate vanishes too).  Subset ⟹ the count bound. -/
theorem deep_pair_rank_ge_m_succ (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ}
    (hindep : SurvivingTPrimeCoord dom k m T T' M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (m + 1) ≤ (Fintype.card F) ^ M := by
  classical
  obtain ⟨d, hsurj⟩ := hindep
  -- the surviving family is surjective
  have hsurjF : ∀ t : (Fin m ⊕ Unit) → F,
      ∃ c : Fin M → F, ∀ j, survFamily dom k T T' d j c = t j := by
    intro t
    obtain ⟨c, hb, hv⟩ := hsurj t
    refine ⟨c, fun j => ?_⟩
    rcases j with j | u
    · exact hb j
    · exact hv
  have hker := card_kernel_eq_of_surjective (survFamily dom k T T' d)
    (survFamily_sub dom k T T' d) hsurjF
  have hcardι : Fintype.card (Fin m ⊕ Unit) = m + 1 := by
    simp [Fintype.card_sum]
  rw [hcardι] at hker
  -- two-band ⊆ surviving-family kernel
  have hsub : (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k))
      ⊆ (Finset.univ.filter (fun c : Fin M → F =>
          ∀ j, survFamily dom k T T' d j c = 0)) := by
    intro c hc
    obtain ⟨h1, h2, -⟩ := (Finset.mem_filter.mp hc).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
    rcases j with j | u
    · exact h1 j
    · show (coreInterp dom T' (genPoly c)).coeff (k + 1 + (d : ℕ)) = (0 : F)
      exact h2 d
  calc _ ≤ (Finset.univ.filter (fun c : Fin M → F =>
            ∀ j, survFamily dom k T T' d j c = 0)).card
            * (Fintype.card F) ^ (m + 1) := by
          exact Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ = (Fintype.card F) ^ M := by
          convert hker using 3

end ProximityGap.DeepStratumUncond

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeepStratumUncond.tband_surjective
#print axioms ProximityGap.DeepStratumUncond.tbandFamily_sub
#print axioms ProximityGap.DeepStratumUncond.deep_pair_rank_ge_m
#print axioms ProximityGap.DeepStratumUncond.survFamily_sub
#print axioms ProximityGap.DeepStratumUncond.deep_pair_rank_ge_m_succ
