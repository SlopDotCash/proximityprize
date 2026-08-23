/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CrossingCountBound
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import Mathlib.Algebra.Order.Chebyshev

/-!
# The mean-degree law down to Johnson, by Cauchy–Schwarz (#389)

The deep-band supply route (landed: `MeanDegreeDeepBand.lean` at `2n² ≤ t²(t−1)`,
`MeanDegreeGeneral.lean` at `2s·cap·C(n,s)·(n−s) ≤ t²(t−s)·C(t,s)`) proves the
mean-degree law `Σ_c a_c ≤ 2n` on deep thresholds `t ≳ n^{2/3}`-scale.  This file
widens the proven range to its true boundary: replacing Bonferroni with
Cauchy–Schwarz on the crossing identity closes the law down to **exactly the Johnson
agreement** `t² > s·n`, for arbitrary set systems, with no branch analysis, no pencil
exclusion, and no cap hypothesis:

> **`crossing_double_count_general_local`** — pairwise `≤ s` intersections:
> `Σ_x d_x(d_x−1) ≤ s·L(L−1)` (the general-`s` form of the landed
> `crossing_double_count`).

> **`mean_degree_master`** — with each set of size `≥ t` and `u = Σ_{A∈S} |A|`:
> `u·t² ≤ n·s·u + n·t²` — chaining `u² ≤ n·Σd²` (Cauchy–Schwarz), the crossing
> count, and `L·t ≤ u`.

> **`mean_degree_sharp`** — the division-free sharp form
> `u·(t² − s·n) ≤ n·t²`, i.e. `u ≤ n·t²/(t² − s·n)` whenever `t² > s·n`.

> **`mean_degree_law`** — for `t² ≥ 2·s·n`: **`Σ_{A∈S} |A| ≤ 2n`** — the measured
> constant, proven for every band at or above `t = √(2sn)`.

> **`rs_agreement_mean_degree_law`** / **`rs_agreement_family_card_le`** — the RS
> instantiation (`s = k−1`, pairwise discharge by `rsCode_pairwise_agreeSet_card_le`):
> for any word `w`, the agreement sets of distinct codewords with `≥ t` agreement
> satisfy `Σ_c |agreeSet c w| ≤ 2n` and `#family · t ≤ 2n` once `t² ≥ 2(k−1)n`.

**Sharpness.** At `t² ≈ s·n` the bound blows up, and must: projective planes
(`n = q²+q+1` points, `L = n` lines, `t = q+1`, `s = 1`) give `Σ|A| = n(q+1) ≈ n^{3/2}`
at `t² ≈ n`.  So below Johnson the mean-degree law is FALSE for set systems and any
proof must couple the word — the remaining open range of issue #389's statement is
exactly the sub-Johnson strip `t² < 2(k−1)n`, nothing above it.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {n : ℕ} [NeZero n]

open Classical in
/-- **The general crossing double-count**: for a family pairwise intersecting in
`≤ s` points, `Σ_x d_x(d_x−1) ≤ s·L(L−1)`. -/
theorem crossing_double_count_general_local {S : Finset (Finset (Fin n))} {s : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s) :
    ∑ x : Fin n, ((S.filter (fun A => x ∈ A)).card
        * ((S.filter (fun A => x ∈ A)).card - 1))
      ≤ s * (S.card * (S.card - 1)) := by
  classical
  have hpoint : ∀ x : Fin n, (S.filter (fun A => x ∈ A)).card
      * ((S.filter (fun A => x ∈ A)).card - 1)
      = (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
          (fun p => x ∈ p.1 ∧ x ∈ p.2)).card := by
    intro x
    have h1 : (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
        (fun p => x ∈ p.1 ∧ x ∈ p.2))
        = (((S.filter (fun A => x ∈ A)) ×ˢ (S.filter (fun A => x ∈ A))).filter
            (fun p => p.1 ≠ p.2)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      tauto
    rw [h1, offdiag_card]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  have hswap : (∑ x : Fin n, (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
      (fun p => x ∈ p.1 ∧ x ∈ p.2)).card)
      = ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), (p.1 ∩ p.2).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have : (p.1 ∩ p.2).card
        = ((Finset.univ : Finset (Fin n)).filter (fun x => x ∈ p.1 ∧ x ∈ p.2)).card := by
      congr 1
      ext x
      simp [Finset.mem_inter]
    rw [this, Finset.card_filter]
  rw [hswap]
  calc ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), (p.1 ∩ p.2).card
      ≤ ∑ _p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), s := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpmem, hne⟩ := Finset.mem_filter.mp hp
        rcases Finset.mem_product.mp hpmem with ⟨h1, h2⟩
        exact hpair p.1 h1 p.2 h2 hne
  _ = ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card * s := by
        rw [Finset.sum_const, smul_eq_mul]
  _ = s * (S.card * (S.card - 1)) := by rw [offdiag_card, mul_comm]

open Classical in
/-- **The degree-sum exchange**: `Σ_x d_x = Σ_{A∈S} |A|`. -/
theorem degree_sum_exchange (S : Finset (Finset (Fin n))) :
    ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card = ∑ A ∈ S, A.card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.card_filter]
  congr 1
  exact Finset.filter_univ_mem A

open Classical in
/-- **The master inequality**: a family of `≥ t`-sets in `[n]`, pairwise intersecting
in `≤ s` points, with `u = Σ_{A∈S} |A|`, satisfies `u·t² ≤ n·s·u + n·t²`.

Chain: Cauchy–Schwarz `u² ≤ n·Σ_x d_x²`, the crossing count
`Σ_x d_x(d_x−1) ≤ s·L(L−1)`, and the bootstrap `L·t ≤ u`. -/
theorem mean_degree_master {S : Finset (Finset (Fin n))} {s t : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s)
    (hsize : ∀ A ∈ S, t ≤ A.card) :
    (∑ A ∈ S, A.card) * t ^ 2
      ≤ n * s * (∑ A ∈ S, A.card) + n * t ^ 2 := by
  classical
  set d : Fin n → ℕ := fun x => (S.filter (fun A => x ∈ A)).card with hd
  set u : ℕ := ∑ A ∈ S, A.card with hu
  set L : ℕ := S.card with hL
  have hdu : ∑ x : Fin n, d x = u := degree_sum_exchange S
  -- bootstrap: L·t ≤ u
  have hLt : L * t ≤ u := by
    calc L * t = ∑ _A ∈ S, t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ A ∈ S, A.card := Finset.sum_le_sum hsize
  -- Cauchy–Schwarz: u² ≤ n·Σ d²
  have hCS : u ^ 2 ≤ n * ∑ x : Fin n, d x ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := d)
    rw [hdu] at h
    simpa [Finset.card_univ, Fintype.card_fin] using h
  -- pointwise square split: d² = d(d−1) + d
  have hsq : ∀ x : Fin n, d x ^ 2 = d x * (d x - 1) + d x := by
    intro x
    cases hdx : d x with
    | zero => simp
    | succ e => simp only [Nat.succ_sub_one]; ring
  have hsum_sq : ∑ x : Fin n, d x ^ 2
      = (∑ x : Fin n, d x * (d x - 1)) + u := by
    rw [Finset.sum_congr rfl (fun x _ => hsq x), Finset.sum_add_distrib, hdu]
  have hcross : ∑ x : Fin n, d x * (d x - 1) ≤ s * (L * (L - 1)) :=
    crossing_double_count_general_local hpair
  -- crossing mass dominated by u²: t²·L(L−1) ≤ (L·t)² ≤ u²
  have hcrossu : t ^ 2 * (L * (L - 1)) ≤ u ^ 2 := by
    calc t ^ 2 * (L * (L - 1)) ≤ t ^ 2 * (L * L) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ = (L * t) ^ 2 := by ring
    _ ≤ u ^ 2 := Nat.pow_le_pow_left hLt 2
  -- the chain, then cancel u
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · simp [hu0]
  have key : u * (u * t ^ 2) ≤ u * (n * s * u + n * t ^ 2) := by
    calc u * (u * t ^ 2) = u ^ 2 * t ^ 2 := by ring
    _ ≤ (n * ∑ x : Fin n, d x ^ 2) * t ^ 2 := Nat.mul_le_mul_right _ hCS
    _ = n * t ^ 2 * (∑ x : Fin n, d x * (d x - 1)) + n * t ^ 2 * u := by
        rw [hsum_sq]; ring
    _ ≤ n * t ^ 2 * (s * (L * (L - 1))) + n * t ^ 2 * u := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hcross) _
    _ = n * s * (t ^ 2 * (L * (L - 1))) + n * t ^ 2 * u := by ring
    _ ≤ n * s * u ^ 2 + n * t ^ 2 * u := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hcrossu) _
    _ = u * (n * s * u + n * t ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left key hupos

open Classical in
/-- **The sharp form**: `u·(t² − s·n) ≤ n·t²` — i.e. `u ≤ n·t²/(t² − s·n)` whenever
`t² > s·n`; the bound blows up exactly at the Johnson agreement `t² = s·n`, where
projective planes witness `u ≈ n^{3/2}`. -/
theorem mean_degree_sharp {S : Finset (Finset (Fin n))} {s t : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s)
    (hsize : ∀ A ∈ S, t ≤ A.card) :
    (∑ A ∈ S, A.card) * (t ^ 2 - s * n) ≤ n * t ^ 2 := by
  have hm := mean_degree_master hpair hsize
  set u : ℕ := ∑ A ∈ S, A.card
  calc u * (t ^ 2 - s * n) = u * t ^ 2 - u * (s * n) := by
        rw [Nat.mul_sub]
  _ ≤ n * t ^ 2 := by
        refine Nat.sub_le_iff_le_add.mpr ?_
        calc u * t ^ 2 ≤ n * s * u + n * t ^ 2 := hm
        _ = n * t ^ 2 + u * (s * n) := by ring
  -- (the `Nat.sub` truncation makes the statement unconditional: below Johnson the
  -- left factor is `0` and the bound is vacuous, as it must be)

open Classical in
/-- **THE MEAN-DEGREE LAW, down to Johnson**: a family of `≥ t`-sets in `[n]`,
pairwise intersecting in `≤ s` points, with `t² ≥ 2·s·n`, satisfies
`Σ_{A∈S} |A| ≤ 2n`. -/
theorem mean_degree_law {S : Finset (Finset (Fin n))} {s t : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s)
    (hsize : ∀ A ∈ S, t ≤ A.card)
    (ht : 0 < t) (hJ : 2 * (s * n) ≤ t ^ 2) :
    ∑ A ∈ S, A.card ≤ 2 * n := by
  have hm := mean_degree_master hpair hsize
  set u : ℕ := ∑ A ∈ S, A.card
  -- 2·u·t² ≤ 2·n·s·u + 2·n·t² ≤ u·t² + 2·n·t² ⟹ u·t² ≤ 2·n·t² ⟹ u ≤ 2n
  have h1 : 2 * (n * s * u) ≤ u * t ^ 2 := by
    calc 2 * (n * s * u) = u * (2 * (s * n)) := by ring
    _ ≤ u * t ^ 2 := Nat.mul_le_mul_left _ hJ
  have h2 : 2 * (u * t ^ 2) ≤ u * t ^ 2 + 2 * (n * t ^ 2) := by
    calc 2 * (u * t ^ 2) ≤ 2 * (n * s * u + n * t ^ 2) :=
          Nat.mul_le_mul_left _ hm
    _ = 2 * (n * s * u) + 2 * (n * t ^ 2) := by ring
    _ ≤ u * t ^ 2 + 2 * (n * t ^ 2) := Nat.add_le_add_right h1 _
  have h3 : u * t ^ 2 ≤ (2 * n) * t ^ 2 := by
    have h2' : u * t ^ 2 + u * t ^ 2 ≤ u * t ^ 2 + 2 * (n * t ^ 2) := by
      calc u * t ^ 2 + u * t ^ 2 = 2 * (u * t ^ 2) := by ring
      _ ≤ u * t ^ 2 + 2 * (n * t ^ 2) := h2
    calc u * t ^ 2 ≤ 2 * (n * t ^ 2) := Nat.le_of_add_le_add_left h2'
    _ = (2 * n) * t ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h3 (pow_pos ht 2)

section RSInstantiation

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The RS agreement-family mean-degree law**: for any word `w` and any family `C`
of codewords of `rsCode dom k` each agreeing with `w` on `≥ t` points, with
`t² ≥ 2(k−1)n`: `Σ_c |agreeSet c w| ≤ 2n`.  The pairwise `≤ k−1` intersection is
discharged by `rsCode_pairwise_agreeSet_card_le` through
`agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c'`. -/
theorem rs_agreement_mean_degree_law (dom : Fin n ↪ F) {k t : ℕ} (hk : 1 ≤ k)
    {w : Fin n → F} {C : Finset (Fin n → F)}
    (hC : ∀ c ∈ C, c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hsize : ∀ c ∈ C, t ≤ (agreeSet c w).card)
    (ht : 0 < t) (hJ : 2 * ((k - 1) * n) ≤ t ^ 2) :
    ∑ c ∈ C, (agreeSet c w).card ≤ 2 * n := by
  classical
  rcases Finset.eq_empty_or_nonempty C with hCe | ⟨c₀, hc₀⟩
  · simp [hCe]
  -- k ≤ t (so equal agreement sets force equal codewords)
  have hkt : k ≤ t := by
    have htn : t ≤ n := le_trans (hsize c₀ hc₀)
      (le_trans (Finset.card_le_univ _) (by simp))
    rcases Nat.eq_zero_or_pos (k - 1) with hk1 | hk1
    · omega
    · have h1 : 2 * ((k - 1) * t) ≤ 2 * ((k - 1) * n) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ htn)
      have h2 : (2 * (k - 1)) * t ≤ t * t := by
        calc (2 * (k - 1)) * t = 2 * ((k - 1) * t) := by ring
        _ ≤ t ^ 2 := le_trans h1 hJ
        _ = t * t := sq t
      have h3 : 2 * (k - 1) ≤ t := Nat.le_of_mul_le_mul_right h2 ht
      omega
  -- membership unfolding for the Ownership agreeSet
  have hmem : ∀ (c : Fin n → F) (i : Fin n), i ∈ agreeSet c w ↔ c i = w i := by
    intro c i
    simp [agreeSet]
  -- the agreement-set family
  have hinjOn : Set.InjOn (fun c => agreeSet c w) ↑C := by
    intro c hc c' hc' he
    have he' : agreeSet c w = agreeSet c' w := he
    refine explainable_core_explainer_unique dom (w := w) (T := agreeSet c w)
      (le_trans hkt (hsize c hc)) (hC c hc) (hC c' hc') ?_ ?_
    · intro i hi
      exact (hmem c i).mp hi
    · intro i hi
      rw [he'] at hi
      exact (hmem c' i).mp hi
  set Sfam := C.image (fun c => agreeSet c w) with hSfam
  have hsum : ∑ A ∈ Sfam, A.card = ∑ c ∈ C, (agreeSet c w).card :=
    Finset.sum_image (fun c hc c' hc' he => hinjOn hc hc' he)
  rw [← hsum]
  refine mean_degree_law (s := k - 1) (t := t) ?_ ?_ ht hJ
  · intro A hA B hB hne
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hB
    have hcc' : c ≠ c' := fun h => hne (by rw [h])
    have hsub : agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c' := by
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hi
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 ⊢
      exact h1.trans h2.symm
    exact le_trans (Finset.card_le_card hsub)
      (rsCode_pairwise_agreeSet_card_le dom hk (hC c hc) (hC c' hc') hcc')
  · intro A hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    exact hsize c hc

open Classical in
/-- **The Johnson-type list bound, for free**: under the same hypotheses,
`#C · t ≤ 2n`. -/
theorem rs_agreement_family_card_le (dom : Fin n ↪ F) {k t : ℕ} (hk : 1 ≤ k)
    {w : Fin n → F} {C : Finset (Fin n → F)}
    (hC : ∀ c ∈ C, c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hsize : ∀ c ∈ C, t ≤ (agreeSet c w).card)
    (ht : 0 < t) (hJ : 2 * ((k - 1) * n) ≤ t ^ 2) :
    C.card * t ≤ 2 * n := by
  classical
  calc C.card * t = ∑ _c ∈ C, t := by rw [Finset.sum_const, smul_eq_mul]
  _ ≤ ∑ c ∈ C, (agreeSet c w).card := Finset.sum_le_sum hsize
  _ ≤ 2 * n := rs_agreement_mean_degree_law dom hk hC hsize ht hJ

/-- **The mean-degree law**, as a named parametric Prop (the issue-thread conjecture):
every word's capped large-agreement family satisfies `Σ_c |agreeSet c w| ≤ 2n`.

Proven above Johnson (`meanDegreeLaw_above_johnson`); REFUTED below Johnson at
`q = Θ(n)` (`MeanDegreeLawRefuted.lean`: a machine-checked countermodel at
`q = n = 19`, `k = 2`, `t = 4`, `cap = 6`). -/
def MeanDegreeLaw (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {n' : ℕ} [NeZero n'] (dom : Fin n' ↪ F) (k t cap : ℕ) : Prop :=
  ∀ (w : Fin n' → F) (C : Finset (Fin n' → F)),
    (∀ c ∈ C, c ∈ (rsCode dom k : Submodule F (Fin n' → F))) →
    (∀ c ∈ C, t ≤ (agreeSet c w).card ∧ (agreeSet c w).card ≤ cap) →
    ∑ c ∈ C, (agreeSet c w).card ≤ 2 * n'

open Classical in
/-- **The law holds above Johnson**, any cap: `t² ≥ 2(k−1)n ⟹ MeanDegreeLaw`. -/
theorem meanDegreeLaw_above_johnson (dom : Fin n ↪ F) {k t : ℕ} (cap : ℕ)
    (hk : 1 ≤ k) (ht : 0 < t) (hJ : 2 * ((k - 1) * n) ≤ t ^ 2) :
    MeanDegreeLaw F dom k t cap := fun _w _C hC hcap =>
  rs_agreement_mean_degree_law dom hk hC (fun c hc => (hcap c hc).1) ht hJ

end RSInstantiation

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.crossing_double_count_general_local
#print axioms ProximityGap.PairRank.degree_sum_exchange
#print axioms ProximityGap.PairRank.mean_degree_master
#print axioms ProximityGap.PairRank.mean_degree_sharp
#print axioms ProximityGap.PairRank.mean_degree_law
#print axioms ProximityGap.PairRank.rs_agreement_mean_degree_law
#print axioms ProximityGap.PairRank.rs_agreement_family_card_le
#print axioms ProximityGap.PairRank.meanDegreeLaw_above_johnson
