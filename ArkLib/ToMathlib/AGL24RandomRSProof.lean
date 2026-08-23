/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# AGL24 random Reed-Solomon near-capacity list decoding — first-moment residual plumbing

This file builds the **random Reed-Solomon first-moment residual** infrastructure for ABF26
Theorem 3.6 ([AGL24 Thm 1.1], issue #95), mirroring the already-landed GLMRSW22 random-linear
endpoint (`randomLinearLambdaLowerEvent` / `randomLinearLambdaLowerProbability` /
`randomLinearLambdaLowerFirstMomentResidual` + the `exists_*_of_probability_pos` reductions in
`ListDecoding/Bounds.lean`).

The front-door statement `CodingTheory.random_rs_list_decoding` records the faithful probability
space (a uniformly sampled size-`n` evaluation domain `L ⊆ F`, via `uniformSizeSubsetOfLe`) and
the near-capacity list-decoding target.  Here we:

* `randomRSListDecodingEvent` — the per-sampled-domain **success** event: the random RS code on the
  sampled domain `L` is list-decodable up to the near-capacity radius `1 - k/n - η` with list size
  `≤ listBound`.
* `randomRSBadDomainEvent` — its negation, the **bad-domain** event whose probability AGL24 bounds.
* `randomRSBadDomainProbability` — `Pr[bad-domain]` under `uniformSizeSubsetOfLe`.
* `random_rs_list_decoding_of_badDomainProbability_bound` — the in-tree **reduction** from the
  exact bad-domain probability bound `Pr[bad-domain] ≤ failure` to the existing front-door
  `random_rs_list_decoding` Prop.
* `randomRSBadDomainCountBound` — the remaining AGL24 first-moment obligation after the
  probability-space accounting is discharged: a pure bad-domain counting inequality over
  size-`n` domains.
* `random_rs_list_decoding_of_badDomainCountBound` — the in-tree **reduction** from that pure
  count-bound obligation to the front-door statement.

This does **not** prove the AGL24 first-moment counting bound itself; it pins the missing paper
input to the pure `randomRSBadDomainCountBound` inequality and proves the probability and front-door
reductions in-tree.  Everything here is axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ListDecodable

section RandomReedSolomonResidual

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The AGL24 **success** event for one sampled size-`n` evaluation domain `L ⊆ F`: the random
Reed-Solomon code `RS[F, L, k]` is list-decodable at the near-capacity radius `1 - k/n - η`
with list size `≤ listBound`. -/
noncomputable def randomRSListDecodingEvent
    (n k listBound : ℕ) (η : ℝ) (L : Probability.SizeSubset F n) : Prop := by
  classical
  exact
    Lambda
      ((ReedSolomon.code (Probability.SizeSubset.toEmbedding L) k : Set (L → F)))
      (1 - (k : ℝ) / (n : ℝ) - η) ≤ (listBound : ℕ∞)

/-- The AGL24 **bad-domain** event: the sampled domain `L` *fails* the near-capacity
list-decoding bound.  This is exactly the negation of `randomRSListDecodingEvent`. -/
noncomputable def randomRSBadDomainEvent
    (n k listBound : ℕ) (η : ℝ) (L : Probability.SizeSubset F n) : Prop :=
  ¬ randomRSListDecodingEvent (F := F) n k listBound η L

/-- Probability of the bad-domain event under a uniformly sampled size-`n` evaluation domain. -/
noncomputable def randomRSBadDomainProbability
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (hn : n ≤ Fintype.card F) : ENNReal := by
  classical
  exact
    Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
      randomRSBadDomainEvent (F := F) n k listBound η L]

/-- The bad-domain probability is exactly the front-door failure probability inside
`random_rs_list_decoding`.  Bridges the named `randomRSBadDomainEvent`/`...Probability` surface to
the literal `Pr_{…}[¬ …]` expression in the existing front-door definition. -/
theorem randomRSBadDomainProbability_eq_front_door
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (hn : n ≤ Fintype.card F) :
    randomRSBadDomainProbability F n k listBound η hn =
      Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
        letI : DecidablePred (Membership.mem L) := Classical.decPred _
        letI : Fintype L := Subtype.fintype (Membership.mem L)
        ¬ (Lambda
            ((ReedSolomon.code (Probability.SizeSubset.toEmbedding L) k : Set (L → F)))
            (1 - (k : ℝ) / (n : ℝ) - η) ≤ (listBound : ℕ∞))] := by
  rfl

/-- **In-tree reduction (issue #346).** The exact AGL24 bad-domain probability bound
`Pr[bad-domain] ≤ failure` discharges the existing front-door `random_rs_list_decoding`
proposition.

This is the random-RS analogue of `exists_code_of_randomLinearLambdaLowerFirstMomentResidual` for
the GLMRSW22 endpoint: the front-door reduction is proven in-tree and the remaining AGL24 content
is pushed below the probability-space layer by `randomRSBadDomainCountBound`. -/
theorem random_rs_list_decoding_of_badDomainProbability_bound
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hprob : randomRSBadDomainProbability F n k listBound η hn ≤ failure) :
    random_rs_list_decoding F n k listBound η failure hn_pos hn := by
  -- `random_rs_list_decoding` unfolds (definitionally, modulo the `by classical; exact`) to the
  -- literal `Pr[¬ Lambda-bound] ≤ failure`; `hprob` is exactly that, repackaged through the
  -- bad-domain probability bridge.
  rw [randomRSBadDomainProbability_eq_front_door] at hprob
  simpa [random_rs_list_decoding] using hprob

/-- Direct probability-bound wrapper for the AGL24 random-RS front door.

This is the public `random_rs_list_decoding` analogue of the GG25 MCA
`random_rs_mca_of_prob_bound` wrapper: the external paper estimate is supplied as the exact
bad-domain probability bound over `uniformSizeSubsetOfLe`, while the front-door packaging is
checked in-tree. -/
theorem random_rs_list_decoding_of_prob_bound
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hprob :
      Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
        randomRSBadDomainEvent (F := F) n k listBound η L] ≤ failure) :
    random_rs_list_decoding F n k listBound η failure hn_pos hn := by
  classical
  exact random_rs_list_decoding_of_badDomainProbability_bound F n k listBound η failure hn_pos hn
    (by
      simpa [randomRSBadDomainProbability] using hprob)

end RandomReedSolomonResidual

/-! ## The counting layer: the residual with its probability space discharged

Mirroring the GG25 accounting (`randomRSMCA_pr_eq_badCount_div` in `GG25RandomRSMCAProof.lean`),
the uniform-PMF layer of the AGL24 residual is provable in-tree: the bad-domain probability *is*
the bad-domain count divided by `C(|F|, n)`.  The genuinely external AGL24 content therefore
moves one layer deeper, to a pure counting inequality with no probability in the statement:

  `#{bad size-n domains} / C(|F|, n) ≤ failure`. -/

section CountingLayer

open scoped Classical

/-- **Exact bad-domain probability as a uniform count.**  Over the uniform size-`n` domain
distribution, `Pr[bad-domain]` equals the number of bad size-`n` domains divided by
`C(|F|, n)`.  Pure accounting; no external content. -/
theorem randomRSBadDomainProbability_eq_badCount_div
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (hn : n ≤ Fintype.card F) :
    randomRSBadDomainProbability F n k listBound η hn =
      ((Finset.univ.filter
          (fun L : Probability.SizeSubset F n =>
            randomRSBadDomainEvent (F := F) n k listBound η L)).card : ENNReal)
        / ((Fintype.card F).choose n : ENNReal) := by
  classical
  have h : randomRSBadDomainProbability F n k listBound η hn =
      Pr_{ let L ← Probability.uniformSizeSubsetOfLe F n hn }[
        randomRSBadDomainEvent (F := F) n k listBound η L] := rfl
  rw [h, ProbabilityTheory.Pr_eq_tsum_indicator, tsum_fintype]
  have hpt : ∀ L : Probability.SizeSubset F n,
      Probability.uniformSizeSubsetOfLe F n hn L
        = ((Fintype.card F).choose n : ENNReal)⁻¹ :=
    fun L => Probability.uniformSizeSubsetOfLe_apply hn L
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_mul_inv, mul_comm]

/-- **The remaining AGL24 first-moment obligation for issue #346.**  At fixed field, length,
degree, list bound, and gap, the number of bad size-`n` evaluation domains is at most a
`failure` fraction of all size-`n` domains.

This is the paper-level counting estimate from [AGL24, Thm. 1.1] after ArkLib discharges the
uniform PMF accounting in `randomRSBadDomainProbability_eq_badCount_div`.  It is deliberately a
counting statement with no probability space and no theorem-shaped placeholder. -/
def randomRSBadDomainCountBound
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal) : Prop :=
  ((Finset.univ.filter
      (fun L : Probability.SizeSubset F n =>
        randomRSBadDomainEvent (F := F) n k listBound η L)).card : ENNReal)
    / ((Fintype.card F).choose n : ENNReal) ≤ failure

/-- The exact bad-domain probability bound follows from the pure AGL24 bad-domain count bound.
The PMF accounting is discharged in-tree; what remains is the named counting input
`randomRSBadDomainCountBound`. -/
theorem randomRSBadDomainProbability_bound_of_badDomainCountBound
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal) (hn : n ≤ Fintype.card F)
    (hcount : randomRSBadDomainCountBound F n k listBound η failure) :
    randomRSBadDomainProbability F n k listBound η hn ≤ failure := by
  rw [randomRSBadDomainProbability_eq_badCount_div]
  simpa [randomRSBadDomainCountBound] using hcount

/-- **Front door from the bad-domain count**: the named counting inequality alone discharges
`random_rs_list_decoding`, with the probability-space accounting verified in-tree. -/
theorem random_rs_list_decoding_of_badDomainCountBound
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal)
    (hn_pos : 0 < n) (hn : n ≤ Fintype.card F)
    (hcount : randomRSBadDomainCountBound F n k listBound η failure) :
    random_rs_list_decoding F n k listBound η failure hn_pos hn :=
  random_rs_list_decoding_of_badDomainProbability_bound F n k listBound η failure hn_pos hn
    (randomRSBadDomainProbability_bound_of_badDomainCountBound
      F n k listBound η failure hn hcount)

end CountingLayer

/-! ## Axiom audit -/

#print axioms randomRSListDecodingEvent
#print axioms randomRSBadDomainEvent
#print axioms randomRSBadDomainProbability
#print axioms randomRSBadDomainProbability_eq_front_door
#print axioms random_rs_list_decoding_of_badDomainProbability_bound
#print axioms random_rs_list_decoding_of_prob_bound
#print axioms random_rs_list_decoding
#print axioms randomRSBadDomainProbability_eq_badCount_div
#print axioms randomRSBadDomainCountBound
#print axioms randomRSBadDomainProbability_bound_of_badDomainCountBound
#print axioms random_rs_list_decoding_of_badDomainCountBound

end CodingTheory
