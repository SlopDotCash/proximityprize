/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds

/-!
# GG25 random-RS MCA up to capacity — checked failure-probability accounting (issue #99)

The front door `CodingTheory.random_rs_mca` (ABF26 Theorem 4.15 / GG25 Theorem 5.15) states that
over a uniformly sampled size-`n` evaluation domain `L ⊆ F`, the random Reed–Solomon code
`RS[F, L, k]` has MCA error at the capacity-near radius `1 - k/n - η` bounded by `bound`, except
with probability at most `failure`:

```
Pr_{L ← uniformSizeSubsetOfLe F n hn}[¬ goodDomain L] ≤ failure
```

The genuinely external GG25 content is the *probability estimate* — the line-stitching /
list-decoding argument that supplies concrete `bound` and `failure` values. This module does NOT
prove that estimate. It formalizes the in-tree, fully-checked **uniform-PMF
counting → failure-probability accounting** that the front door's `failure` term needs, mirroring
the checked-reduction pattern already used for T4.14
(`frs_epsMCA_capacity_gg25_of_residuals`).

Main results:

* `randomRSMCA_pr_eq_badCount_div`: the front-door failure probability equals
  `(#bad domains) / C(|F|, n)` (exact, over the uniform size-`n` subset distribution).
* `random_rs_mca_of_badCount`: if the bad-domain count divided by `C(|F|, n)` is `≤ failure`,
  the front-door Prop `random_rs_mca` holds.
* `random_rs_mca_of_allGood`: if every size-`n` domain is good, the failure probability is `0`,
  so `random_rs_mca` holds for any `failure`.
* `random_rs_mca_of_prob_bound`: the trivial Prop wrapper isolating the external GG25 estimate.

All declarations are axiom-clean (`#print axioms` below).
-/

open scoped ENNReal NNReal ProbabilityTheory

namespace CodingTheory

open Probability ProximityGap
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The per-domain "good" predicate underlying `random_rs_mca`: the capacity-near MCA error of
the Reed–Solomon code on the embedded size-`n` domain is at most `bound`. -/
noncomputable def randomRSMCAGood
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (η : ℝ) (bound : ENNReal) (L : SizeSubset F n) : Prop :=
  epsMCA (F := F) (A := F)
      ((ReedSolomon.code (SizeSubset.toEmbedding L) k : Set (L → F)))
      ((1 - (k : ℝ) / (n : ℝ) - η).toNNReal) ≤ bound

/-- The front door `random_rs_mca` is *definitionally* the failure-probability inequality for the
`randomRSMCAGood` predicate over the uniform size-`n` domain distribution. -/
theorem random_rs_mca_def
    (n k : ℕ) (η : ℝ) (bound failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F) :
    random_rs_mca F n k η bound failure hn_pos hn ↔
      Pr_{ let L ← uniformSizeSubsetOfLe F n hn }[
        ¬ randomRSMCAGood F n k η bound L] ≤ failure := by
  rfl

/-- **Exact failure probability as a uniform bad-domain count.**

Over the uniform size-`n` domain distribution, the probability that a domain is *not* good equals
the number of bad size-`n` domains divided by `C(|F|, n)`. This is the substantive
counting → probability bridge; it has no external content. -/
theorem randomRSMCA_pr_eq_badCount_div
    (n k : ℕ) (η : ℝ) (bound : ENNReal)
    (hn : n ≤ Fintype.card F) :
    Pr_{ let L ← uniformSizeSubsetOfLe F n hn }[
      ¬ randomRSMCAGood F n k η bound L] =
      ((Finset.univ.filter
          (fun L : SizeSubset F n => ¬ randomRSMCAGood F n k η bound L)).card : ENNReal)
        / ((Fintype.card F).choose n : ENNReal) := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator]
  -- The tsum over the Fintype `SizeSubset F n` collapses to a Finset sum.
  rw [tsum_fintype]
  -- Every point mass equals `(C(|F|,n))⁻¹`.
  have hpt : ∀ L : SizeSubset F n,
      uniformSizeSubsetOfLe F n hn L = ((Fintype.card F).choose n : ENNReal)⁻¹ :=
    fun L => uniformSizeSubsetOfLe_apply hn L
  simp_rw [hpt]
  -- Factor the constant point mass out of the indicator sum.
  rw [← Finset.mul_sum]
  -- Collapse the indicator sum to the cardinality of the bad-domain filter.
  rw [Finset.sum_boole]
  rw [div_eq_mul_inv, mul_comm]

/-- **Checked reduction: bad-domain count bound ⇒ front door.**

If the number of bad size-`n` domains divided by `C(|F|, n)` is at most `failure`, then the
front-door Prop `random_rs_mca` holds. The hypothesis `hcount` is exactly the
counting form of the GG25 probability estimate; this lemma supplies the uniform-PMF accounting. -/
theorem random_rs_mca_of_badCount
    (n k : ℕ) (η : ℝ) (bound failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hcount :
      ((Finset.univ.filter
          (fun L : SizeSubset F n => ¬ randomRSMCAGood F n k η bound L)).card : ENNReal)
        / ((Fintype.card F).choose n : ENNReal) ≤ failure) :
    random_rs_mca F n k η bound failure hn_pos hn := by
  rw [random_rs_mca_def, randomRSMCA_pr_eq_badCount_div]
  exact hcount

/-- **Checked corollary: every domain good ⇒ zero failure ⇒ front door for any `failure`.** -/
theorem random_rs_mca_of_allGood
    (n k : ℕ) (η : ℝ) (bound failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hgood : ∀ L : SizeSubset F n, randomRSMCAGood F n k η bound L) :
    random_rs_mca F n k η bound failure hn_pos hn := by
  classical
  rw [random_rs_mca_def, randomRSMCA_pr_eq_badCount_div]
  have hempty :
      (Finset.univ.filter
          (fun L : SizeSubset F n => ¬ randomRSMCAGood F n k η bound L)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro L _
    simpa using hgood L
  rw [hempty]
  simp

/-- **Prop wrapper isolating the external GG25 probability estimate.**

Taking the GG25 failure-probability bound as a hypothesis discharges `random_rs_mca` trivially.
This is the clean boundary between the formalized accounting (above) and the unformalized
line-stitching / list-decoding estimate that supplies `bound` and `failure`. -/
theorem random_rs_mca_of_prob_bound
    (n k : ℕ) (η : ℝ) (bound failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hprob :
      Pr_{ let L ← uniformSizeSubsetOfLe F n hn }[
        ¬ randomRSMCAGood F n k η bound L] ≤ failure) :
    random_rs_mca F n k η bound failure hn_pos hn := by
  rw [random_rs_mca_def]
  exact hprob

end CodingTheory

#print axioms CodingTheory.randomRSMCA_pr_eq_badCount_div
#print axioms CodingTheory.random_rs_mca_of_badCount
#print axioms CodingTheory.random_rs_mca_of_allGood
#print axioms CodingTheory.random_rs_mca_of_prob_bound
