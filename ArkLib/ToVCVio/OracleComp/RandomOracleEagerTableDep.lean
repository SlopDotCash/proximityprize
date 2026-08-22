/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Lazy random oracle equals eager full-table sampling — dependent-range oracle specs

VCVio's `RandomOracle.EagerTable` proves the lazy-vs-eager random-oracle equivalence only for the
constant-range oracle `D →ₒ R`. This file generalizes it to an **arbitrary** oracle specification
`spec : OracleSpec ι`, whose range `spec.Range q` may depend on the query `q`. Running an
`OracleComp spec α` under the lazy random oracle (`OracleSpec.randomOracle`,
i.e. `uniformSampleImpl.withCaching`) from the empty cache has the same output distribution as the
eager strategy: sample a *full dependent* answer table `g : (q : spec.Domain) → spec.Range q`
uniformly, then evaluate the computation deterministically against `g`.

The proof mirrors the constant-range argument: the lazy oracle samples a fresh uniform value on
first query and caches it for consistency, so caching only ever affects *repeated* queries. Since
every fresh table entry is uniform and independent, lazily sampling on demand is distributionally
identical to pre-sampling the whole table. The new workhorse is the **dependent marginalization**
lemma `evalDist_uniformSample_bind_update_dep`: overwriting one coordinate of a uniform dependent
function table with a fresh independent uniform draw is measure preserving (the `t`-marginal
independence of the uniform product distribution).

This is the form required to reformulate a state-restoration / Fiat-Shamir challenge oracle (whose
range `pSpec.Challenge i` depends on the challenge round) as a pre-sampled challenge table.

## Main results

* `evalDist_uniformSample_bind_update_dep` — dependent marginalization (single-coordinate resample).
* `evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep` — cache-parametrized form.
* `evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep` — the empty-cache equivalence.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

section Marginalization

variable {ι : Type} {R : ι → Type} [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] [∀ i, SampleableType (R i)]
  [SampleableType (∀ i, R i)]

/-- **Dependent marginalization: overwriting one coordinate of a uniform dependent function table
is measure-preserving.**

Drawing `u` uniformly from `R t`, then a full dependent table `g : ∀ i, R i` uniformly, and
returning `Function.update g t u` yields the same distribution as drawing the table directly. This
is the `t`-marginal independence of the uniform (product) distribution on `∀ i, R i`. It is the
dependent-range analogue of `OracleComp.evalDist_uniformSample_bind_update`. -/
lemma evalDist_uniformSample_bind_update_dep (t : ι) :
    𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (Function.update g t u)] =
      𝒟[$ᵗ (∀ i, R i)] := by
  classical
  haveI : Nonempty (∀ i, R i) := ⟨fun i => Classical.arbitrary (R i)⟩
  refine evalDist_ext fun h => ?_
  rw [probOutput_uniformSample (∀ i, R i) h,
    HasEvalSPMF.probOutput_bind_eq_sum_fintype]
  have hinner : ∀ u : R t,
      Pr[= h | (do let g ← $ᵗ (∀ i, R i); pure (Function.update g t u))]
        = (if u = h t then
            (Fintype.card (R t) : ℝ≥0∞) * (Fintype.card (∀ i, R i) : ℝ≥0∞)⁻¹ else 0) := by
    intro u
    have hmap : (do let g ← $ᵗ (∀ i, R i); pure (Function.update g t u))
        = (fun g => Function.update g t u) <$> ($ᵗ (∀ i, R i)) := by rw [bind_pure_comp]
    rw [hmap, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample (∀ i, R i)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun g : ∀ i, R i => h = Function.update g t u).card : ℝ≥0∞)
          = if u = h t then (Fintype.card (R t) : ℝ≥0∞) else 0 := by
      by_cases hu : u = h t
      · have hset : (Finset.univ.filter fun g : ∀ i, R i => h = Function.update g t u)
            = Finset.univ.image (fun r : R t => Function.update h t r) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hg
            refine ⟨g t, ?_⟩
            rw [eq_comm, Function.update_eq_iff] at hg
            obtain ⟨_, hg2⟩ := hg
            funext x
            by_cases hx : x = t
            · subst hx; simp
            · simp [Function.update_of_ne hx, hg2 x hx]
          · rintro ⟨r, rfl⟩
            rw [eq_comm, Function.update_eq_iff]
            exact ⟨by simp [hu], fun x hx => by simp [Function.update_of_ne hx]⟩
        rw [hset, Finset.card_image_of_injective _
          (fun r₁ r₂ hr => by simpa using congrFun hr t), Finset.card_univ, if_pos hu]
      · have hempty : (Finset.univ.filter fun g : ∀ i, R i => h = Function.update g t u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro g _ hg
          rw [eq_comm, Function.update_eq_iff] at hg
          exact hu hg.1
        rw [hempty, Finset.card_empty, Nat.cast_zero, if_neg hu]
    rw [hcard]; by_cases hu : u = h t <;> simp [hu]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (h t)]
  rw [if_pos (Finset.mem_univ _), probOutput_uniformSample (R t), ← mul_assoc,
      ENNReal.inv_mul_cancel, one_mul]
  · simp [Fintype.card_ne_zero]
  · exact ENNReal.natCast_ne_top _

/-- Post-composed dependent marginalization: drawing a fresh uniform `u`, then a full dependent
uniform table `g`, and evaluating `ψ` on `Function.update g t u` matches evaluating `ψ` on a
directly drawn uniform table. -/
lemma evalDist_uniformSample_bind_update_map_dep {α : Type} (t : ι) (ψ : (∀ i, R i) → α) :
    𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (ψ (Function.update g t u))] =
      𝒟[do let g ← $ᵗ (∀ i, R i); pure (ψ g)] := by
  have hL : (do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (ψ (Function.update g t u))) =
      ψ <$> (do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (Function.update g t u)) := by
    simp [map_bind, bind_pure_comp]
  have hR : (do let g ← $ᵗ (∀ i, R i); pure (ψ g)) = ψ <$> ($ᵗ (∀ i, R i)) := by
    simp [bind_pure_comp]
  rw [hL, hR, evalDist_map, evalDist_map, evalDist_uniformSample_bind_update_dep t]

/-- **Reading a uniform dependent table at one coordinate is a fresh uniform sample.** Drawing a
uniform full table `g : ∀ i, R i` and post-processing its value `g t` at a fixed coordinate `t` has
the same distribution as drawing `g t` fresh. This is the per-coordinate marginal-projection form of
the marginalization lemma — the building block for peeling one challenge out of a pre-sampled
challenge table (the read is replaced by a fresh sample independent of the rest of `g`). -/
lemma evalDist_uniformTable_read_eq_uniform {α : Type} (t : ι) (F : R t → α) :
    𝒟[do let g ← $ᵗ (∀ i, R i); pure (F (g t))] = 𝒟[do let u ← $ᵗ (R t); pure (F u)] := by
  rw [← evalDist_uniformSample_bind_update_map_dep t (fun g => F (g t))]
  simp only [Function.update_self]
  refine evalDist_ext fun x => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun u => ?_
  congr 1
  rw [probOutput_bind_const]
  simp

end Marginalization

section EagerTable

variable {ι : Type} {spec : OracleSpec ι}

/-- The total dependent answer table obtained by overlaying a `QueryCache` on top of a full
dependent function table: cached entries take priority, uncached coordinates fall through to `g`. -/
@[reducible] def tableExtendingDep (c : spec.QueryCache) (g : (q : spec.Domain) → spec.Range q) :
    (q : spec.Domain) → spec.Range q :=
  fun q => (c q).getD (g q)

section
variable [DecidableEq spec.Domain]

/-- Overlaying `c.cacheQuery t u` on `g` is the `t`-update of overlaying `c` on `g`. -/
lemma tableExtendingDep_cacheQuery (c : spec.QueryCache)
    (g : (q : spec.Domain) → spec.Range q) (t : spec.Domain) (u : spec.Range t) :
    tableExtendingDep (c.cacheQuery t u) g = Function.update (tableExtendingDep c g) t u := by
  funext t'
  by_cases ht : t' = t
  · subst ht; simp [tableExtendingDep, QueryCache.cacheQuery]
  · simp [tableExtendingDep, QueryCache.cacheQuery_of_ne _ _ ht, Function.update_of_ne ht]

/-- When `t` is uncached, updating the overlaid table at `t` equals overlaying the cache on the
updated full table. -/
lemma tableExtendingDep_update_of_none (c : spec.QueryCache)
    (g : (q : spec.Domain) → spec.Range q)
    {t : spec.Domain} (hc : c t = none) (u : spec.Range t) :
    Function.update (tableExtendingDep c g) t u = tableExtendingDep c (Function.update g t u) := by
  funext t'
  by_cases ht : t' = t
  · subst ht; simp [tableExtendingDep, hc]
  · simp [tableExtendingDep, Function.update_of_ne ht]

end

/-- Overlaying the empty cache leaves a full dependent table unchanged. -/
lemma tableExtendingDep_empty (g : (q : spec.Domain) → spec.Range q) :
    tableExtendingDep (∅ : spec.QueryCache) g = g := by
  funext t; simp [tableExtendingDep]

section
variable [DecidableEq ι] [DecidableEq spec.Domain] [Fintype spec.Domain]
  [∀ q, Fintype (spec.Range q)] [∀ q, Nonempty (spec.Range q)]
  [∀ q, SampleableType (spec.Range q)] [SampleableType ((q : spec.Domain) → spec.Range q)]

/-- **Lazy random oracle equals eager full-table sampling — dependent-spec, cache-parametrized.**

Running `oa` under the lazy random oracle starting from cache `c` yields the same output
distribution as: sample a full dependent table `g : (q : spec.Domain) → spec.Range q` uniformly,
then evaluate `oa` deterministically against the table overlaying `c` on `g`. This is the induction
vehicle: the cache `c` is generalized so the `query`/`bind` step can recurse through `cacheQuery`. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep
    {α : Type} (oa : OracleComp spec α) (c : spec.QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ ((q : spec.Domain) → spec.Range q);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g)) oa)] := by
  classical
  haveI : Nonempty ((q : spec.Domain) → spec.Range q) := ⟨fun q => Classical.arbitrary _⟩
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    have hlhs : (simulateQ randomOracle (pure a : OracleComp spec α)).run' c
        = (pure a : ProbComp α) := by
      rw [simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, c) : ProbComp (α × _)) = pure a
      rw [map_pure]
    rw [hlhs]
    simp only [evalWithAnswerFn_pure]
    symm
    refine evalDist_ext fun x => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ ((q : spec.Domain) → spec.Range q)) (by simp), one_mul]
  | query_bind t k ih =>
    have hred :
        (simulateQ randomOracle (liftM (spec.query t) >>= k)).run' c
          = ((randomOracle (spec := spec) t).run c) >>=
            fun p : spec.Range t × spec.QueryCache =>
              (simulateQ randomOracle (k p.1)).run' p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      change Prod.fst <$> (((randomOracle (spec := spec) t).run c) >>= fun p =>
        (simulateQ randomOracle (k p.1)).run p.2) = _
      rw [map_bind]; rfl
    have heval : ∀ g : (q : spec.Domain) → spec.Range q,
        evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g)) (liftM (spec.query t) >>= k)
          = evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g))
              (k (tableExtendingDep c g t)) := by
      intro g
      rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g))
        (k (simulateQ (QueryImpl.ofFn (tableExtendingDep c g)) (liftM (spec.query t)))) = _
      rw [simulateQ_spec_query]; rfl
    rw [hred]
    simp_rw [heval]
    rcases hc : c t with _ | u
    · rw [show ((randomOracle (spec := spec) t).run c) =
            (fun u => (u, c.cacheQuery t u)) <$> ($ᵗ (spec.Range t)) from
            QueryImpl.withCaching_run_none _ hc]
      rw [show (((fun u => (u, c.cacheQuery t u)) <$> ($ᵗ (spec.Range t))) >>=
              fun p : spec.Range t × spec.QueryCache =>
                (simulateQ randomOracle (k p.1)).run' p.2)
            = (($ᵗ (spec.Range t)) >>= fun u =>
                (simulateQ randomOracle (k u)).run' (c.cacheQuery t u)) from by
        rw [map_eq_bind_pure_comp]; simp [bind_assoc]]
      set ψ : ((q : spec.Domain) → spec.Range q) → α := fun g' =>
        evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g')) (k (tableExtendingDep c g' t))
        with hψ
      have hfun : ∀ u : spec.Range t, (fun g : (q : spec.Domain) → spec.Range q =>
            evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep (c.cacheQuery t u) g)) (k u))
          = fun g : (q : spec.Domain) → spec.Range q => ψ (Function.update g t u) := by
        intro u
        funext g
        simp only [hψ]
        rw [tableExtendingDep_cacheQuery, ← tableExtendingDep_update_of_none c g hc u]
        simp only [Function.update_self]
      trans 𝒟[do let u ← $ᵗ (spec.Range t); let g ← $ᵗ ((q : spec.Domain) → spec.Range q);
                  pure (ψ (Function.update g t u))]
      · rw [evalDist_bind, evalDist_bind]
        refine congrArg _ (funext fun u => ?_)
        rw [ih u (c.cacheQuery t u), bind_pure_comp, bind_pure_comp, hfun u]
      · exact evalDist_uniformSample_bind_update_map_dep (ι := spec.Domain) (R := spec.Range) t ψ
    · rw [show ((randomOracle (spec := spec) t).run c) = (pure (u, c) : ProbComp _) from
            QueryImpl.withCaching_run_some _ hc]
      rw [pure_bind, ih u c]
      refine congrArg _ ?_
      refine congrArg _ (funext fun g => ?_)
      congr 1
      have : tableExtendingDep c g t = u := by simp [tableExtendingDep, hc]
      rw [this]

/-- **Lazy random oracle equals eager full-table sampling — dependent-spec form.**

Running an `OracleComp spec α` under the lazy random oracle from the empty cache yields the same
output distribution as: sample a full dependent answer table uniformly, then evaluate the
computation deterministically against it. The dependent-range generalization of
`OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`. -/
theorem evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep
    {α : Type} (oa : OracleComp spec α) :
    𝒟[(simulateQ randomOracle oa).run' ∅] =
      𝒟[do let g ← $ᵗ ((q : spec.Domain) → spec.Range q);
            pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep oa ∅]
  refine congrArg _ ?_
  refine congrArg _ (funext fun g => ?_)
  rw [tableExtendingDep_empty]

end

end EagerTable

end OracleComp
