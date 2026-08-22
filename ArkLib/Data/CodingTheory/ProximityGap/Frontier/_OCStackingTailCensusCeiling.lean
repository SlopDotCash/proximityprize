/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# LANE OC-TAIL (#466, 2026-07-10): the CROSS-PRIME stacking-census tail ceiling —
  depth-3 stacked violators are FINITE in the tail, with an explicit
  `poly(n)/log P` cardinality bound (axiom-clean double-count theorem).

## Position in the campaign

After OC-ORBIT (r369 piece (a): a depth-3 exact-Wick violation needs `K = n/16` simultaneous
primitive orbits), OC-PIECEB (the per-prime height-norm certificate `p^{v_p} ∣ N(r)`,
`0 < N(r) ≤ 6^{n/2}` for char-p-only relations), and OC-EQUI (Galois equidistribution: the
single-embedding stacking count is WLOG — transversality carries nothing extra), the surviving
piece-(b) object is the SINGLE-EMBEDDING STACKING CENSUS: how many pool relations can vanish
simultaneously at one embedding of one prime.

This lane runs the SAME norm certificate ACROSS DISTINCT PRIMES — a direction none of
OC-ORBIT/PIECEB/EQUI (nor FS15–FS18, which work per-window with a union bound) used:

* a fixed candidate `r` with `0 < N(r) ≤ H^φ` can vanish at at most `log_P(H^φ)` DISTINCT
  primes `p ≥ P`, because the product of those primes divides `N(r)` (pairwise-coprime
  distinct primes), so `P^t ≤ N(r) ≤ H^φ`;
* a violator prime consumes `≥ K` distinct candidates from the incidence pool (piece (a));
* double-counting the candidate×prime incidence relation therefore gives, for EVERY finite
  set `V` of violator primes in the tail `[P, ∞)`:

  `|V| · K ≤ |Cand| · log_P(H^φ)` — uniform in `V`, hence the violator set is FINITE.

At the census cell (`H = 6`, `φ = n/2`, `K = n/16`, `|Cand| ≤ C(n/2,6)·2^6`) this reads: for
every fixed `n`, the TOTAL number of primes `p ≥ P` admitting a depth-3 stacked exact-Wick
violation is at most `16·|Cand|·(n/2)·log 6/(n·log P) = O(n^6/log P)` — over the whole
infinite tail, not per window. Fraction of violators in `[P, 2P]` is `O(n^6 log P/P)`:
density → 0 for `P ≫ n^6` — matching r370's observation that stacking is easy just above
`n^3` and decays with β; the crossover the counting heuristic predicts is β ≈ 6.

## What this does and does NOT say (honesty)

* It is a FINITENESS/DENSITY-ZERO theorem for the depth-3 stacked-violator PRIME SET at fixed
  `n` — the first tail-uniform (not per-window) quantitative form in-tree. It complements
  FS10/FS14–FS18 (almost-all-prime ladders): the mechanism here is the cross-prime
  divisor-product argument, not a per-prime union bound; and the `K = n/16` division is new
  (piece (a) enters as the per-violator incidence floor).
* It CANNOT discharge the explicit prize field: G64 proved the FS almost-all-prime ladder is
  forced exceptional at the nominal prize field by depth six — exceptional-set avoidance is a
  mapped non-route to the prize. This lane's value is census control on the piece-(b) object
  (the violator set is thin and explicitly finite in the tail), not a prize path.
* The interface hypotheses (norm nonzero-and-bounded for char-p-only candidates; incidence ⟹
  prime divides the norm certificate; violator ⟹ `K` incidences) are exactly OC-PIECEB's
  certificate identity + OC-ORBIT's orbit law, probe-verified again here
  (`probe_466_oc_stacking_tail_census.py`: certificate ⟺ embedding-vanishing exact at every
  cell; max cross-prime multiplicity within the `log_P(6^m)` ceiling; violator census within
  the ceiling). CORE remains OPEN / ON-BGK.

## What is proved (all axiom-clean)

* `incidence_double_count` : the exact candidate×prime incidence double count.
* `pow_card_le_of_primes_dvd` : distinct primes `≥ P` dividing `N ≠ 0` number at most
  `log_P N` (via `P^t ≤ ∏ primes ≤ N`).
* `filter_card_le_log` : per-candidate cross-prime multiplicity ceiling.
* `stacking_violator_tail_ceiling` : the capstone `|V| · K ≤ |Cand| · Nat.log P (H^φ)`.
* `violatorSet_finite` : the set of stacked-violator primes in the tail is FINITE.
* `depth3_tail_ceiling` : the census-cell instantiation `H = 6`, `φ = n/2`, `K = n/16`.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling

/-- Exact double count of the candidate×prime incidence relation: summing per-prime
candidate counts over any prime set equals summing per-candidate prime counts. -/
theorem incidence_double_count {α β : Type*}
    (Cand : Finset α) (V : Finset β) (Inc : α → β → Prop) [∀ a p, Decidable (Inc a p)] :
    ∑ p ∈ V, (Cand.filter (fun a => Inc a p)).card
      = ∑ a ∈ Cand, (V.filter (fun p => Inc a p)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- Distinct primes `≥ P` all dividing a nonzero integer `N` satisfy `P^(their number) ≤ N`:
their product is a divisor of `N` (distinct primes are pairwise coprime) and dominates
`P^count` termwise. This is the cross-prime use of the norm certificate. -/
theorem pow_card_le_of_primes_dvd {N P : ℕ} (hN : N ≠ 0)
    (S : Finset ℕ) (hprime : ∀ q ∈ S, Nat.Prime q) (hge : ∀ q ∈ S, P ≤ q)
    (hdvd : ∀ q ∈ S, q ∣ N) :
    P ^ S.card ≤ N := by
  have hprod_dvd : (∏ q ∈ S, q) ∣ N :=
    Finset.prod_primes_dvd N (fun q hq => (hprime q hq).prime) hdvd
  calc P ^ S.card ≤ ∏ q ∈ S, q := Finset.pow_card_le_prod S _ P hge
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hprod_dvd

/-- Per-candidate cross-prime multiplicity ceiling: a candidate whose norm certificate is
nonzero and at most `H^φ` is incident to at most `Nat.log P (H^φ)` primes `≥ P`. -/
theorem filter_card_le_log {N P H φ : ℕ} (hP : 2 ≤ P) (hH : 1 ≤ H) (hN : N ≠ 0)
    (hNle : N ≤ H ^ φ)
    (S : Finset ℕ) (hprime : ∀ q ∈ S, Nat.Prime q) (hge : ∀ q ∈ S, P ≤ q)
    (hdvd : ∀ q ∈ S, q ∣ N) :
    S.card ≤ Nat.log P (H ^ φ) := by
  have hpow : P ^ S.card ≤ H ^ φ :=
    le_trans (pow_card_le_of_primes_dvd hN S hprime hge hdvd) hNle
  exact Nat.le_log_of_pow_le (by omega) hpow

/-- **Capstone: the stacking-violator tail ceiling.** If every candidate carries a nonzero
norm certificate `≤ H^φ`, every incidence forces the prime (which is `≥ P`) to divide that
certificate, and every violator prime has at least `K` incident candidates, then for ANY
finite violator set `V` in the tail:

`|V| · K ≤ |Cand| · log_P(H^φ)`.

Uniform in `V` — the violator set cannot grow with the window. -/
theorem stacking_violator_tail_ceiling {α : Type*}
    (Cand : Finset α) (V : Finset ℕ) (Inc : α → ℕ → Prop) [∀ a p, Decidable (Inc a p)]
    (Nrm : α → ℕ) (P H φ K : ℕ) (hP : 2 ≤ P) (hH : 1 ≤ H)
    (hN0 : ∀ a ∈ Cand, Nrm a ≠ 0)
    (hNle : ∀ a ∈ Cand, Nrm a ≤ H ^ φ)
    (hInc : ∀ a ∈ Cand, ∀ p ∈ V, Inc a p → Nat.Prime p ∧ P ≤ p ∧ p ∣ Nrm a)
    (hviol : ∀ p ∈ V, K ≤ (Cand.filter (fun a => Inc a p)).card) :
    V.card * K ≤ Cand.card * Nat.log P (H ^ φ) := by
  have h1 : V.card * K ≤ ∑ p ∈ V, (Cand.filter (fun a => Inc a p)).card := by
    calc V.card * K = ∑ _p ∈ V, K := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hviol
  have h2 := incidence_double_count Cand V Inc
  have h3 : ∀ a ∈ Cand, (V.filter (fun p => Inc a p)).card ≤ Nat.log P (H ^ φ) := by
    intro a ha
    refine filter_card_le_log hP hH (hN0 a ha) (hNle a ha) _ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqV, hqI⟩ := Finset.mem_filter.mp hq
      exact (hInc a ha q hqV hqI).1
    · intro q hq
      obtain ⟨hqV, hqI⟩ := Finset.mem_filter.mp hq
      exact (hInc a ha q hqV hqI).2.1
    · intro q hq
      obtain ⟨hqV, hqI⟩ := Finset.mem_filter.mp hq
      exact (hInc a ha q hqV hqI).2.2
  have h4 : ∑ a ∈ Cand, (V.filter (fun p => Inc a p)).card
      ≤ Cand.card * Nat.log P (H ^ φ) := by
    calc ∑ a ∈ Cand, (V.filter (fun p => Inc a p)).card
        ≤ ∑ _a ∈ Cand, Nat.log P (H ^ φ) := Finset.sum_le_sum h3
      _ = Cand.card * Nat.log P (H ^ φ) := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- **Finiteness of the stacked-violator prime set.** Under the tail interface (incidence
anywhere in the tail forces primality, `≥ P`, and division of the candidate's certificate),
the set of ALL primes with `≥ K` stacked candidates is FINITE — for every fixed `n`, only
finitely many primes in the whole infinite tail admit a depth-3 stacked violation. -/
theorem violatorSet_finite {α : Type*}
    (Cand : Finset α) (Inc : α → ℕ → Prop) [∀ a p, Decidable (Inc a p)]
    (Nrm : α → ℕ) (P H φ K : ℕ) (hP : 2 ≤ P) (hH : 1 ≤ H) (hK : 0 < K)
    (hN0 : ∀ a ∈ Cand, Nrm a ≠ 0)
    (hNle : ∀ a ∈ Cand, Nrm a ≤ H ^ φ)
    (hInc : ∀ a ∈ Cand, ∀ p : ℕ, Inc a p → Nat.Prime p ∧ P ≤ p ∧ p ∣ Nrm a) :
    {p : ℕ | K ≤ (Cand.filter (fun a => Inc a p)).card}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨V, hVsub, hVcard⟩ :=
    hinf.exists_subset_card_eq (Cand.card * Nat.log P (H ^ φ) / K + 1)
  have hviol : ∀ p ∈ V, K ≤ (Cand.filter (fun a => Inc a p)).card := by
    intro p hp
    exact hVsub hp
  have hceil := stacking_violator_tail_ceiling Cand V Inc Nrm P H φ K hP hH hN0 hNle
    (fun a ha p _ hI => hInc a ha p hI) hviol
  rw [hVcard] at hceil
  have hlt : Cand.card * Nat.log P (H ^ φ) <
      (Cand.card * Nat.log P (H ^ φ) / K + 1) * K :=
    (Nat.div_lt_iff_lt_mul hK).mp (Nat.lt_succ_self _)
  exact absurd hceil (Nat.not_le.mpr hlt)

/-- The census-cell instantiation: heights `H = 6`, degree `φ = n/2`, orbit floor
`K = n/16` (r369 piece (a)). For every finite depth-3 violator set `V` in the tail `[P, ∞)`:
`|V| · (n/16) ≤ |Cand| · log_P(6^{n/2})` — the explicit `O(n^6/log P)` violator ceiling. -/
theorem depth3_tail_ceiling {α : Type*}
    (Cand : Finset α) (V : Finset ℕ) (Inc : α → ℕ → Prop) [∀ a p, Decidable (Inc a p)]
    (Nrm : α → ℕ) (P n : ℕ) (hP : 2 ≤ P)
    (hN0 : ∀ a ∈ Cand, Nrm a ≠ 0)
    (hNle : ∀ a ∈ Cand, Nrm a ≤ 6 ^ (n / 2))
    (hInc : ∀ a ∈ Cand, ∀ p ∈ V, Inc a p → Nat.Prime p ∧ P ≤ p ∧ p ∣ Nrm a)
    (hviol : ∀ p ∈ V, n / 16 ≤ (Cand.filter (fun a => Inc a p)).card) :
    V.card * (n / 16) ≤ Cand.card * Nat.log P (6 ^ (n / 2)) :=
  stacking_violator_tail_ceiling Cand V Inc Nrm P 6 (n / 2) (n / 16) hP (by omega)
    hN0 hNle hInc hviol

end ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.incidence_double_count
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.pow_card_le_of_primes_dvd
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.filter_card_le_log
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.stacking_violator_tail_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.violatorSet_finite
#print axioms
  ArkLib.ProximityGap.Frontier.OCStackingTailCensusCeiling.depth3_tail_ceiling
