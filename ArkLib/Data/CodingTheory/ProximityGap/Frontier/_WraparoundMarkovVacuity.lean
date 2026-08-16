/-
# The wraparound union/Markov bad-prime bound is vacuous below the average (#444)

This is the precise Lane-3 constraint rung that links the *proven average control* of the wraparound
(`_WraparoundNormDivisibility`: the per-relation prime-divisor count is bounded **independently of `p`**,
so the **average** wraparound `(∑_p W_p)/#primes` is `O(n^{2r}·φ(n)·log r / #primes)`) to its **failure
to control the supremum** (`_OverdispersionObstructsVariance`: a single heavy prime spoils the variance).

The bridge is elementary but had not been locked in-kernel as a stated constraint: the only tool that
turns the *summed* incidence into a *per-prime* exclusion is the union/Markov bound

  `#{ j ∈ S : W j ≥ T } ≤ (∑_{j∈S} W j) / T`,

and this bound is **vacuous** (it does not exclude even one prime) for every threshold `T` at or below
the **average** `(∑ W)/|S|`, because then its right-hand side is `≥ |S|`.  At prize scale the relevant
threshold (`W_prize ~ n·log(p/n)`) sits *orders of magnitude below* the average wraparound (probe
`probe_markov_vacuity.py`: avg/Wprize `≈ 21, 262, 3360, 44800` for `n = 8,16,32,64` at `β = 4`, the gap
*growing* in `n`), so the union route over the norm-divisibility incidence cannot isolate the worst prime.

Two axiom-clean facts:
* `markov_count_le` — the real finite Markov bound `T·#{W ≥ T} ≤ ∑ W` for nonnegative `W`, `T > 0`.
* `markov_bound_vacuous_below_mean` — if `0 < T ≤ mean`, the Markov right-hand side `(∑ W)/T ≥ |S|`,
  so the union bound is vacuous: it cannot exclude any prime.

This is a **constraint lemma (no-go bookkeeping)**: it formalizes WHY average-control does not transfer to
sup-control through the union bound.  No CORE, cancellation, completion, anti-concentration, or capacity
claim is made.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ArkLib.ProximityGap.WraparoundMarkovVacuity

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The mean of the wraparound `W` over the finite set `S` of admissible primes. -/
noncomputable def mean (S : Finset ι) (W : ι → ℝ) : ℝ := (∑ j ∈ S, W j) / S.card

/-- **Finite Markov inequality (multiplicative form).**  For a nonnegative weight `W` and threshold
`T > 0`, the heavy set `{ j ∈ S : T ≤ W j }` satisfies `T · #{heavy} ≤ ∑_{j∈S} W j`.  This is the only
mechanism by which the *summed* wraparound incidence yields a *per-prime* exclusion count. -/
theorem markov_count_le (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hW : ∀ j ∈ S, 0 ≤ W j) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j := by
  classical
  set H := S.filter (fun j => T ≤ W j) with hHdef
  have hHS : H ⊆ S := filter_subset _ _
  -- On the heavy set, each weight is at least `T`, so `T·#H ≤ ∑_{H} W`.
  have hlow : T * (H.card : ℝ) ≤ ∑ j ∈ H, W j := by
    have : ∑ _j ∈ H, T ≤ ∑ j ∈ H, W j := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact (mem_filter.mp hj).2
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- The heavy sub-sum is at most the full sum, since `W ≥ 0` off `H`.
  have hsub : ∑ j ∈ H, W j ≤ ∑ j ∈ S, W j :=
    Finset.sum_le_sum_of_subset_of_nonneg hHS (fun j hjS _ => hW j hjS)
  exact le_trans hlow hsub

/-- **The union/Markov bad-prime bound is vacuous at or below the average.**  If `0 < T ≤ mean S W`
(the threshold is no larger than the average wraparound) and the index set is nonempty, then the Markov
right-hand side `(∑ W)/T` is at least `|S|`.  Hence the union bound `#{heavy} ≤ (∑W)/T` cannot exclude
*any* prime — it permits every prime to be heavy.  This is exactly why a controlled *average* (bounded
`∑ W`) certifies nothing about the *supremum* at any prize-scale threshold below the average. -/
theorem markov_bound_vacuous_below_mean (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T) (hTmean : T ≤ mean S W) :
    (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T := by
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  -- From `T ≤ (∑ W)/|S|` and `|S| > 0`: `T · |S| ≤ ∑ W`.
  have hTS : T * (S.card : ℝ) ≤ ∑ j ∈ S, W j := by
    have h := mul_le_mul_of_nonneg_right hTmean (le_of_lt hcard)
    -- h : T * |S| ≤ (mean) * |S|
    rwa [mean, div_mul_cancel₀ _ (ne_of_gt hcard)] at h
  -- Divide by `T > 0`: `|S| ≤ (∑ W)/T`.
  rw [le_div_iff₀ hT]
  linarith [hTS]

/-- **Combined statement: average-control does not certify any prime below the average.**  Whenever the
threshold `T` is at or below the average wraparound, the Markov-excluded count bound is at least the total
number of admissible primes, so it leaves the heavy set unconstrained: the supremum is not controlled by
the (proven) average bound through the union route. -/
theorem average_control_does_not_bound_sup
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T) (hW : ∀ j ∈ S, 0 ≤ W j)
    (hTmean : T ≤ mean S W) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j
      ∧ (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ⟨markov_count_le S W T hW, markov_bound_vacuous_below_mean S W T hne hT hTmean⟩

end ArkLib.ProximityGap.WraparoundMarkovVacuity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_count_le
#print axioms ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_bound_vacuous_below_mean
#print axioms ArkLib.ProximityGap.WraparoundMarkovVacuity.average_control_does_not_bound_sup
