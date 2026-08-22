/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusCapForcedBelow
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AlignmentSupply
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# The deployed census-weld budget is INFEASIBLE at the deep central band (#444)

The census-domination weld (`CensusDominationWeld.lean`) pins the deployed
`δ* = 1 − r/2^μ` GRANTING two things:

* the named Prop **`CensusDomination dom k a₀ K`** — every stack has at most `K` alignable
  `a`-sets at every band `a ≥ a₀` (`CensusDominationWeld.CensusDomination`); and
* the deployed budget **`K / p ≤ ε*`**, i.e. `K ≤ ε*·p` (the `hK` hypothesis of
  `kkh26_deltaStar_pin_of_censusDomination`).

The necessity companion `CensusCapForcedBelow.censusDomination_cap_ge_choose` forces, from a
SINGLE `γ`-aligned set `A` with a non-degenerate `(k+1)`-tuple, the lower bracket

  `C(|A| − (k+1), a − (k+1)) ≤ K`   at every band `a ∈ [k+1, |A|]`.

and `KKH26AlignmentSupply.kkh26_fibreUnion_aligned_nondegenerate` REALIZES such a set: for
the KKH26 line at code dimension `k = (r−2)m+1` on the smooth `n = s·m` domain, every
`r`-subset of the `m`-power subgroup yields a `γ`-aligned set `A` of size exactly `r·m`
carrying a non-degenerate `(k+1)`-tuple.

**What is new here.**  This file WELDS the necessity floor against the supply realizer and
then against the deployed `K`-budget, at the DEEP CENTRAL band.  With `|A| = r·m` and
`k+1 = (r−2)m+2`, the residual window has width `|A| − (k+1) = 2m − 2`; choosing the
central band `a = (r−1)m + 1` gives `a − (k+1) = m − 1`, so the necessity floor is exactly
the **central binomial coefficient**

  `C(2m − 2, m − 1) = centralBinom (m − 1)`,

which is `≥ 4^{m−1}/(2(m−1))` — EXPONENTIAL in the multiplicity `m`.  Hence:

* `census_cap_ge_centralBinom` (the welded floor): for the KKH26 supply at any `r`-subset
  `T`, every `K` witnessing the per-stack census bound at the central band must dominate
  `centralBinom (m − 1)`;
* `not_censusDomination_of_budget_lt_centralBinom` (the infeasibility): if the deployed
  budget `K` is below `centralBinom (m − 1)`, the named Prop `CensusDomination` at the
  central band is FALSE for the KKH26 stack — so the weld's two hypotheses are jointly
  UNSATISFIABLE there.

**Honest scope.**  This is NOT a CORE closure and NOT a refutation of the prize.  It is a
precise constraint-lemma on the DEPLOYED census weld: the named `CensusDomination` Prop, at
the deep central band, requires a budget `K ≥ centralBinom (m−1) = 2^{Θ(m)}`, which is
EXPONENTIAL in the multiplicity, whereas the prize calibration `ε*·q ≈ n` makes `K ≤ ε*·p`
only POLYNOMIAL.  So the census normal form **cannot be invoked at the deep central band**
in the high-multiplicity slice `centralBinom (m−1) > K` — it must live at the Johnson-scale
agreement radius `a ≈ √(kn) ≫ (r−1)m+1`, exactly the honest reading recorded in
`Frontier/CountLaneNotSecondOrder.lean` and `DeepBandSupplyExponential.lean` (where the
SIBLING `ExplainableCoreSupply` object was shown exponential at the deep band).  This is the
matching result for the DISTINCT `alignableSets`/`CensusDomination` object the weld actually
uses, carried all the way to the weld's deployed `K`-budget — which neither sibling file
does.  It makes no capacity / beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched).
The central binomial is exponential ⟹ the deep band is the WRONG radius, NOT that the prize
is impossible.  Probe: `scripts/probes/probe_census_cap_exceeds_budget.py` (the threshold is
sharp — feasible for `m = 2`, infeasible from `m ≥ ~½ log₂ n`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

* Issue #444 (the prize CORE; the count/census face).
* `CensusDominationWeld.lean` (the deployed `δ*` pin from `CensusDomination` + `K/p ≤ ε*`),
  `Frontier/CensusCapForcedBelow.lean` (the necessity floor `C(…) ≤ K`),
  `KKH26AlignmentSupply.lean` (the supply realizer),
  `DeepBandSupplyExponential.lean` / `Frontier/CountLaneNotSecondOrder.lean` (the sibling
  exponential floor on `ExplainableCoreSupply`).
-/

open Finset Polynomial

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- **The welded central-band floor.**  Instantiating the necessity floor
(`censusDomination_cap_ge_choose`) on the KKH26 supply set
(`kkh26_fibreUnion_aligned_nondegenerate`, of size `r·m` at code dimension
`k = (r−2)m+1` on the smooth `n = s·m` domain) at the central band `a = (r−1)m+1`: any `K`
witnessing the per-stack alignable census bound at that band must dominate the central
binomial `centralBinom (m − 1) = C(2m−2, m−1)`. -/
theorem census_cap_ge_centralBinom
    {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) {n : ℕ} [NeZero n] (hn : n = s * m)
    {g : ZMod p} (hg : orderOf g = n)
    {T : Finset (ZMod p)} (hTsub : T ⊆ (Finset.range s).image (fun j => (g ^ m) ^ j))
    {r : ℕ} (hr2 : 2 ≤ r) (hTcard : T.card = r)
    {K : ℕ}
    (hcap : (alignableSets (smoothDom g n hg) ((r - 2) * m + 1) ((r - 1) * m + 1)
        (fun i => (g ^ (i : ℕ)) ^ (r * m)) (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m))).card
      ≤ K) :
    Nat.centralBinom (m - 1) ≤ K := by
  classical
  -- unpack the supply realizer
  obtain ⟨A, hAcard, hAlign, t, htinj, htmem, hnd⟩ :=
    kkh26_fibreUnion_aligned_nondegenerate (p := p) hs hm hn hg hTsub hr2 hTcard
  -- the central band and basic arithmetic facts
  set k : ℕ := (r - 2) * m + 1 with hkdef
  set a : ℕ := (r - 1) * m + 1 with hadef
  -- k + 1 ≤ a : (r-2)m + 2 ≤ (r-1)m + 1  ⇔  m ≥ 1
  have hka : k + 1 ≤ a := by
    rw [hkdef, hadef]
    have hstep : (r - 2) * m + m = (r - 1) * m := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  -- a ≤ A.card = r·m : (r-1)m + 1 ≤ r·m  ⇔  1 ≤ m
  have hAa : a ≤ A.card := by
    rw [hAcard, hadef]
    have hstep : (r - 1) * m + m = r * m := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  -- the residual window width: A.card − (k+1) = 2m − 2
  have hwidth : A.card - (k + 1) = 2 * m - 2 := by
    rw [hAcard, hkdef]
    have hrm : (r - 2) * m + 2 * m = r * m := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  -- the central index: a − (k+1) = m − 1
  have hcentre : a - (k + 1) = m - 1 := by
    rw [hadef, hkdef]
    have hstep : (r - 2) * m + m = (r - 1) * m := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  -- the necessity floor at the central band
  have hfloor := censusDomination_cap_ge_choose (smoothDom g n hg)
    (k := k) (a := a)
    (fun i => (g ^ (i : ℕ)) ^ (r * m)) (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m))
    (A := A) (K := K) hAa hka hAlign htinj htmem hnd hcap
  -- rewrite the binomial into the central binomial
  rw [hwidth, hcentre] at hfloor
  -- C(2m−2, m−1) = C(2(m−1), m−1) = centralBinom (m−1)
  have hbridge : (2 * m - 2).choose (m - 1) = Nat.centralBinom (m - 1) := by
    rw [Nat.centralBinom]
    congr 1
    omega
  rwa [hbridge] at hfloor

open Classical in
/-- **The deployed census budget is infeasible at the deep central band.**  If the deployed
budget `K` is strictly below the central binomial `centralBinom (m − 1)` (which is forced by
the prize calibration `K ≤ ε*·p ≈ n` once `m ≥ ~½ log₂ n`), then the named Prop
`CensusDomination` of the weld — at the central band `a = (r−1)m+1` for the KKH26 stack —
is FALSE.  Equivalently: the weld's two hypotheses (`CensusDomination` and `K/p ≤ ε*`) are
jointly UNSATISFIABLE at the deep central band whenever `centralBinom (m−1) > K`. -/
theorem not_censusDomination_of_budget_lt_centralBinom
    {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) {n : ℕ} [NeZero n] (hn : n = s * m)
    {g : ZMod p} (hg : orderOf g = n)
    {T : Finset (ZMod p)} (hTsub : T ⊆ (Finset.range s).image (fun j => (g ^ m) ^ j))
    {r : ℕ} (hr2 : 2 ≤ r) (hTcard : T.card = r)
    {K : ℕ} (hbudget : K < Nat.centralBinom (m - 1)) :
    ¬ CensusDomination (smoothDom g n hg) ((r - 2) * m + 1) ((r - 1) * m + 1) K := by
  classical
  intro hdom
  -- specialise the named Prop to the KKH26 stack at the central band `a = a₀`; its filter
  -- IS `alignableSets` (definitionally the same filter), giving the cap hypothesis
  have hcap : (alignableSets (smoothDom g n hg) ((r - 2) * m + 1) ((r - 1) * m + 1)
      (fun i => (g ^ (i : ℕ)) ^ (r * m)) (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m))).card
      ≤ K :=
    hdom (fun i => (g ^ (i : ℕ)) ^ (r * m)) (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m))
      ((r - 1) * m + 1) (le_refl _)
  have hfloor := census_cap_ge_centralBinom hs hm hn hg hTsub hr2 hTcard hcap
  omega

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.census_cap_ge_centralBinom
#print axioms ProximityGap.Ownership.not_censusDomination_of_budget_lt_centralBinom
