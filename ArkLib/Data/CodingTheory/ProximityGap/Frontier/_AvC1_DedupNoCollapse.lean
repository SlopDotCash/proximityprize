/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (Av-C1 frontier — dedup-across-directions does NOT collapse the
distinct-gamma union)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Av-C1 — the deduplicated distinct-γ UNION does NOT collapse to near-linear (#444)

## ROUTE C re-attack (the affine-escape hypothesis)

The "distinct-γ" object for the prize is, at a fixed agreement level `s`, the union over all
`Θ(n²)` monomial far-directions `R = (a,b)` of the bad-γ sets
`Γ_R = { γ ∈ 𝔽_p : x^a + γ·x^b agrees with a deg<k poly on ≥ s points of μ_n }`.

A previous round measured the **per-direction-summed** count `∑_R |Γ_R| ~ n^{3.88}`.
The C1 ESCAPE HYPOTHESIS: the orbits across directions OVERLAP so heavily that the true
deduplicated union `|⋃_R Γ_R|` collapses to `≤ c·n` (near-linear), which would reopen the
off-BGK affine escape (union under budget `= n` ⇒ δ* pinned below the wall).

## VERDICT: REFUTED by exact integer computation (`scripts/rust-pg`, bin `unionmeas`).

At the binding depth `s = k+2`, `ρ = 1/4` (`k = n/4`), non-Fermat prime `p ≡ 1 (mod n)`:

| n  |  ∑_R |Γ_R| (SUM) |  |⋃_R Γ_R| (UNION) | MAX_R |Γ_R| | budget n |
|----|------------------|-------------------|-------------|----------|
|  8 |             120  |              21   |          9  |        8 |
| 16 |            1952  |             361   |         89  |       16 |
| 20 |            9904  |            1597   |        359  |       20 |
| 24 |           34712  |            6135   |       1153  |       24 |

* `UNION/SUM` ratio is **constant ≈ 0.17** across all `n` ⇒ dedup removes only a CONSTANT
  factor (~5.7×), it does NOT change the growth exponent.
* log-log slope of UNION ≈ slope of SUM (≈ 5.2 over n=8..24, ≈ 7 over n≥16): the exponents
  TRACK each other. The union grows super-linearly with the SAME exponent as the sum.
* Already the single worst direction `MAX_R |Γ_R|` exceeds the budget super-linearly
  (`MAX/n = 1.1, 5.6, 18, 48` for `n=8,16,20,24`).

So `|⋃_R Γ_R| ≥ MAX_R |Γ_R| ≫ n`: the union is bounded BELOW by the worst single direction,
which already blows the budget. Dedup across directions cannot rescue it. C1 escape closed.

## What this brick proves (the structural core)

The only set-theoretic fact dedup gives you is `|⋃_R Γ_R| ≥ |Γ_R|` for every direction `R`
(a union dominates each member). Combined with the measured fact that some direction `R*`
already has `|Γ_{R*}| > n` (budget), the union exceeds the budget — NO amount of cross-direction
overlap can collapse it. This brick formalizes that monotonicity backbone over `Finset`, the
exact mechanism by which the C1 hypothesis is refuted: dedup is dominated below by `MAX`, and
`MAX > budget` is the witnessed numeric input.
-/

namespace ArkLib.ProximityGap.Frontier.AvC1

open Finset

/-- A union of finsets dominates any single member: `Γ_R ⊆ ⋃_R Γ_R`. -/
theorem subset_biUnion_of_mem {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (Γ : ι → Finset α) {R : ι} (hR : R ∈ s) :
    Γ R ⊆ s.biUnion Γ :=
  Finset.subset_biUnion_of_mem Γ hR

/-- **Dedup is dominated below by any single direction.** The deduplicated distinct-γ union
`|⋃_R Γ_R|` is at least the size `|Γ_R|` of any one direction `R`. This is the entire
set-theoretic content available to the C1 escape: cross-direction overlap can only shrink the
union toward `MAX`, never below it. -/
theorem card_biUnion_ge_member {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (Γ : ι → Finset α) {R : ι} (hR : R ∈ s) :
    (Γ R).card ≤ (s.biUnion Γ).card :=
  Finset.card_le_card (subset_biUnion_of_mem s Γ hR)

/-- **C1 escape refuted (abstract form).** If even a SINGLE direction `R*` has a bad-γ set
larger than the budget (`budget < |Γ_{R*}|`, the witnessed numeric fact `MAX > n`), then the
deduplicated union over ALL directions also exceeds the budget. No deduplication / overlap
across the `Θ(n²)` directions can collapse the union under budget. -/
theorem dedup_union_exceeds_budget {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (Γ : ι → Finset α) (budget : ℕ)
    {R : ι} (hR : R ∈ s) (hMax : budget < (Γ R).card) :
    budget < (s.biUnion Γ).card :=
  lt_of_lt_of_le hMax (card_biUnion_ge_member s Γ hR)

/-- **Quantified instance at the measured binding point `n = 16`, `s = k+2 = 6`.**
The witnessed worst direction is `R* = (9,15)` with `|Γ_{R*}| = 89`, budget `= n = 16`.
Since `16 < 89`, the deduplicated union (measured `|⋃| = 361`) likewise exceeds budget,
independent of any cross-direction overlap. (`Γ`, `s` are arbitrary; only the two numeric
inequalities — membership of the worst direction and `budget < its card` — are used, exactly
mirroring the exact-integer `unionmeas` output.) -/
theorem dedup_union_exceeds_budget_n16 {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (Γ : ι → Finset α) {Rstar : ι}
    (hR : Rstar ∈ s) (hcard : (Γ Rstar).card = 89) :
    16 < (s.biUnion Γ).card := by
  apply dedup_union_exceeds_budget s Γ 16 hR
  rw [hcard]; norm_num

#print axioms subset_biUnion_of_mem
#print axioms card_biUnion_ge_member
#print axioms dedup_union_exceeds_budget
#print axioms dedup_union_exceeds_budget_n16

end ArkLib.ProximityGap.Frontier.AvC1
