/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The supply instance (#371): explainable cores of agreement-capped words

The two provable halves of the `ExplainableCoreSupply` question:

* `explainable_cores_card_of_agreement_le` — **the agreement-capped supply**:
  if every codeword agrees with `w` on at most `A` points, then

    **`#(explainable (k+m+1)-cores of w) · C(k+m+1, k) ≤ C(n,k) · C(A−k, m+1)`.**

  Pair-counting: every `k`-subset of an explainable core determines its
  explaining codeword (the unique degree-`<k` interpolant), so the core's
  remaining `m+1` points lie in that one codeword's agreement set.

* `near_scalar_unique` — **the near-line dichotomy**: for a strongly far
  direction, at most ONE scalar has its line within agreement `> (n+k)/2` of
  the code (two such lines would overlap in `> k` agreement points, where the
  direction itself becomes explainable).

Honesty note (the remaining wall): combining these with the witness-mass law
closes the deep-band count whenever the resulting binomial inequality is
nonvacuous — which covers small-parameter ranges but NOT the production
regime, where the agreement cap forced by `near_scalar_unique`
(`A ≈ (n+k)/2`) leaves `C(n,k)·C(A−k,m+1)` of the same order as the witness
mass.  Improving the supply below Johnson agreement is quantitatively the
list-decoding wall — the known coupling of `δ*` to the 25-year-open problem.
The supply-side mathematics ABOVE that wall is now fully proven.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The agreement-capped supply instance**: explainable cores of a word whose
codeword agreements are all ≤ `A` pack against `k`-subset determination. -/
theorem explainable_cores_card_of_agreement_le (dom : Fin n ↪ F)
    {k m : ℕ} (hk : 1 ≤ k) {w : Fin n → F} {A : ℕ}
    (hA : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ A) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card * (k + m + 1).choose k
      ≤ n.choose k * (A - k).choose (m + 1) := by
  set expl := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => ExplainableOn dom k w T) with hexpl
  -- the pair set: (core, k-subset of it)
  set PP := expl.sigma (fun T => T.powersetCard k) with hPP
  have hPPcard : PP.card = expl.card * (k + m + 1).choose k := by
    rw [hPP, Finset.card_sigma]
    calc ∑ T ∈ expl, (T.powersetCard k).card
        = ∑ T ∈ expl, (k + m + 1).choose k := by
          refine Finset.sum_congr rfl fun T hT => ?_
          obtain ⟨hTmem, -⟩ := Finset.mem_filter.mp hT
          have hTcard : T.card = k + m + 1 :=
            (Finset.mem_powersetCard.mp hTmem).2
          rw [Finset.card_powersetCard, hTcard]
      _ = expl.card * (k + m + 1).choose k := by
          rw [Finset.sum_const, smul_eq_mul]
  -- fiber the pairs over the k-subset
  have hfiber : PP.card = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (PP.filter (fun p => p.2 = s)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hp2
    obtain ⟨hTmem, -⟩ := Finset.mem_filter.mp hp1
    have hTsub : p.1 ⊆ Finset.univ := Finset.subset_univ _
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans hTsub, hcard⟩
  -- each fiber is bounded by the agreement geometry
  have hperfiber : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (PP.filter (fun p => p.2 = s)).card ≤ (A - k).choose (m + 1) := by
    intro s hs
    have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    -- the unique interpolant of w on s
    set cs : Fin n → F :=
      fun i => (Lagrange.interpolate s (⇑dom) (fun i => w i)).eval (dom i)
      with hcs
    have hvs : Set.InjOn dom s := fun a _ b _ h => dom.injective h
    have hcsdeg : (Lagrange.interpolate s (⇑dom) (fun i => w i)).degree
        < (k : ℕ) := by
      have h := Lagrange.degree_interpolate_lt (r := fun i => w i) hvs
      rwa [hscard] at h
    have hcsag : ∀ i ∈ s, cs i = w i := by
      intro i hi
      rw [hcs]
      exact Lagrange.eval_interpolate_at_node _ hvs hi
    -- any explaining codeword of a core containing s IS the interpolant
    have hforce : ∀ (T : Finset (Fin n)), s ⊆ T →
        ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        (∀ i ∈ T, c i = w i) → ∀ i, c i = cs i := by
      intro T hsT c hcC hcag i
      obtain ⟨P, hPdeg, rfl⟩ := hcC
      have hzero : P - Lagrange.interpolate s (⇑dom) (fun i => w i) = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (s := s.image (fun i => dom i)) ?_ ?_
        · have hcard2 : (s.image (fun i => dom i)).card = k := by
            rw [Finset.card_image_of_injective _ dom.injective, hscard]
          rw [hcard2]
          exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
            (max_lt hPdeg hcsdeg)
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          have hwi : P.eval (dom i) = w i := hcag i (hsT hi)
          have h2 : (Lagrange.interpolate s (⇑dom)
              (fun i => w i)).eval (dom i) = w i :=
            Lagrange.eval_interpolate_at_node _ hvs hi
          rw [eval_sub, hwi, h2, sub_self]
      have h3 : P = Lagrange.interpolate s (⇑dom) (fun i => w i) :=
        sub_eq_zero.mp hzero
      rw [hcs, h3]
    -- inject the fiber into the (m+1)-subsets of the interpolant's agreement
    refine le_trans (Finset.card_le_card_of_injOn
      (t := ((agreeSet cs w) \ s).powersetCard (m + 1))
      (fun p => p.1 \ s) ?_ ?_) ?_
    · -- maps into the (m+1)-subsets of agreeSet(cs, w) \ s
      intro p hp
      obtain ⟨hpPP, hps⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hpPP
      obtain ⟨hTmem, hTexpl⟩ := Finset.mem_filter.mp hp1
      have hTcard : p.1.card = k + m + 1 :=
        (Finset.mem_powersetCard.mp hTmem).2
      have hsT : s ⊆ p.1 := by
        rw [← hps]
        exact (Finset.mem_powersetCard.mp hp2).1
      obtain ⟨c, hcC, hcag⟩ := hTexpl
      have hcis := hforce p.1 hsT c hcC hcag
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      constructor
      · intro i hi
        obtain ⟨hiT, hins⟩ := Finset.mem_sdiff.mp hi
        rw [Finset.mem_sdiff]
        refine ⟨?_, hins⟩
        rw [agreeSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hcis i]
        exact hcag i hiT
      · rw [Finset.card_sdiff_of_subset hsT, hTcard, hscard]
        omega
    · -- injective: the core is recovered as (T \ s) ∪ s
      intro p hp p' hp' heq2
      obtain ⟨hpPP, hps⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp'PP, hp's⟩ := Finset.mem_filter.mp hp'
      have hsT : s ⊆ p.1 := by
        rw [← hps]
        exact (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hpPP).2).1
      have hsT' : s ⊆ p'.1 := by
        rw [← hp's]
        exact (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp'PP).2).1
      replace heq2 : p.1 \ s = p'.1 \ s := heq2
      have h1 : p.1 = p'.1 := by
        calc p.1 = (p.1 \ s) ∪ s := (Finset.sdiff_union_of_subset hsT).symm
          _ = (p'.1 \ s) ∪ s := by rw [heq2]
          _ = p'.1 := Finset.sdiff_union_of_subset hsT'
      have h2 : p.2 = p'.2 := by rw [hps, hp's]
      exact Sigma.ext h1 (by rw [h2])
    · -- the target counts (m+1)-subsets of a set of size ≤ A − k
      rw [Finset.card_powersetCard]
      refine Nat.choose_le_choose _ ?_
      have hags : s ⊆ agreeSet cs w := by
        intro i hi
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hcsag i hi⟩
      have hcsmem : cs ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
        ⟨Lagrange.interpolate s (⇑dom) (fun i => w i), hcsdeg, rfl⟩
      have h := hA cs hcsmem
      rw [Finset.card_sdiff_of_subset hags, hscard]
      omega
  -- assemble
  calc expl.card * (k + m + 1).choose k = PP.card := hPPcard.symm
    _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (PP.filter (fun p => p.2 = s)).card := hfiber
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (A - k).choose (m + 1) := Finset.sum_le_sum hperfiber
    _ = n.choose k * (A - k).choose (m + 1) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]

open Classical in
/-- **The near-line dichotomy**: for a strongly far direction, at most one
scalar's line comes within agreement `> (n+k)/2` of the code. -/
theorem near_scalar_unique (dom : Fin n ↪ F) {k : ℕ}
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k)
    {A : ℕ} (hAbig : n + k < 2 * A) {γ γ' : F} (hne : γ ≠ γ')
    {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hag : A ≤ (agreeSet c (fun i => u₀ i + γ * u₁ i)).card)
    (hag' : A ≤ (agreeSet c' (fun i => u₀ i + γ' * u₁ i)).card) :
    False := by
  -- the two agreement sets overlap in more than k points
  set S := agreeSet c (fun i => u₀ i + γ * u₁ i) with hS
  set S' := agreeSet c' (fun i => u₀ i + γ' * u₁ i) with hS'
  have hinter : k < (S ∩ S').card := by
    have h1 : (S ∪ S').card ≤ n := by
      calc (S ∪ S').card ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    have h2 := Finset.card_union_add_card_inter S S'
    omega
  -- on the overlap, the direction is explained by a codeword
  set d : Fin n → F := fun i => (γ - γ')⁻¹ • (c i - c' i) with hd
  have hdC : d ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ hc hc')
  have hdag : S ∩ S' ⊆ agreeSet d u₁ := by
    intro i hi
    obtain ⟨hiS, hiS'⟩ := Finset.mem_inter.mp hi
    have h1 : c i = u₀ i + γ * u₁ i := by
      have := (Finset.mem_filter.mp hiS).2
      exact this
    have h2 : c' i = u₀ i + γ' * u₁ i := by
      have := (Finset.mem_filter.mp hiS').2
      exact this
    rw [agreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hd]
    show (γ - γ')⁻¹ * (c i - c' i) = u₁ i
    rw [h1, h2]
    have hγne : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  have := hμ d hdC
  have hle : (S ∩ S').card ≤ (agreeSet d u₁).card :=
    Finset.card_le_card hdag
  omega

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.explainable_cores_card_of_agreement_le
#print axioms ProximityGap.Ownership.near_scalar_unique
