# δ\* #466 — SYZ22: the reduced strip bridge (identification + pair-doubling), 2026-07-11

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ22StripBridge.lean`
(axiom-clean: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `axiom`, no
`native_decide`).

## What SYZ22 does

SYZ21 landed the MDS shortening dimension `shortening_dim α k U :
finrank (dualAnnihilator (range (evalOnS α k U))) = |U| − k` fully in-tree, and flagged three
residuals to a concrete `SuperadditiveUnion` instance: (i) identification of G87's syndrome-pair
witness functionals with the punctured-code annihilator functionals, (ii) pair-doubling, (iii)
sunflower/packing realizability. SYZ22 discharges (i) and (ii) as theorems and pins (iii) as the
*sole* remaining residual.

### (i) IDENTIFICATION — DISCHARGED

`block_source_dim` / `block_source_dim_eq_shortening`. G87 (`_G87McaEventSyndromeBridge`)
builds its per-witness block of parity functionals as **duals of the quotient**
`(S→F) ⧸ range(evalOnS α k S)` — the syndrome quotient of the code *punctured to `S`*.
SYZ22 proves this source space has dimension exactly `|S| − k` (`= max(0,|S|−k)`), and that this
**equals** `shortening_dim` of the `S`-anchored punctured code. So the `t − k` functionals G87
constructs from a witness `(S,c)` are exactly a basis of `dualAnnihilator(range(evalOnS α k S))`
— the parity checks supported inside `S` **are** the dual codewords of the punctured code. The
"abstract-H ⟺ punctured-annihilator" step is now a theorem, not a probe reduction.
Proof: `Subspace.dual_finrank_eq` + `finrank_quotient_add_finrank` + SYZ21's `punctureDim_*`.

### (ii) PAIR-DOUBLING — DISCHARGED

`doubled_shortening_dim`:
`finrank ((dualAnnihilator (range evalOnS)) × (dualAnnihilator (range evalOnS))) = 2(|U| − k)`.
The syndrome-pair space is a direct sum of two copies of the syndrome quotient; a `U`-anchored
annihilating functional doubles (`ℓ∘fst`, `ℓ∘snd` independent). This is exactly the target of
`SuperadditiveUnion.union_span_rank = 2(|U| − k)` and of `finrank_syndromePair = 2(n − k)`.
Proof: `Module.finrank_prod` + `shortening_dim`.

### (iii) REALIZABILITY — remains the ONLY residual; NOT eliminated from the safety path

The task hypothesis was that realizability is unneeded for the safety (upper-bound) direction.
**On careful audit this is not correct**, and SYZ22 records the honest situation:

- `span_ceiling` (= SYZ20 `plantable_span_cap` specialised) gives the **upper** bound
  `finrank(span synFunctionals) + 1 ≤ 2(n − k)` unconditionally — a functional family
  annihilating a nonzero syndrome cannot span past `2(n − k) − 1`.
- To convert this into a **union budget** `|U| ≤ n − 1` (which is what feeds SYZ20's/SYZ21's
  knapsack count bound) one needs the matching **lower** bound
  `finrank(span synFunctionals) ≥ 2(|U| − k)` — i.e. that the union functionals actually
  *realise* the full doubled shortening space. Two upper bounds do not chain; the budget needs
  the realized rank.

Parts (i)/(ii) prove this lower bound is **attainable** (the ambient `U`-anchored space has
exactly dimension `2(|U|−k)`, and each G87 block is a full-rank `t−k` slice of it). What is
*not* proven is that a **specific over-budget family fills it** — the sunflower packing /
SYZ18 distinct-support realizability. SYZ22 records the honest conditional
`strip_budget_of_realizability` (= SYZ20 `union_card_le`): given the `SuperadditiveUnion`
equality (realizability), `|U| ≤ n−1` follows, and then the SYZ21 combined-coverage knapsack
(`knapsack_closes_strip_n64`, unconditional ℕ computation, `< 64` at `t ∈ {43,44,45}`) bounds
the bad count strictly below the survival budget.

## Final δ\* verdict (VERBATIM, honest)

**No new unconditional δ\* statement.** SYZ22 upgrades (i) identification and (ii) pair-doubling
from probe reductions to axiom-clean theorems, but the production **strip closure**, and hence
the `δ\* ≥ 1/3 − lattice` floor-jump and the resulting two-sided pin at rate `1/2`, remain
**conditional on realizability** — i.e. on `SuperadditiveUnion` being instantiable at the
production shape (`n = 2^30, k = 2^29`). The unconditional δ\* status is unchanged by this file
(floor unchanged; the pin is still gated on the sunflower/packing lower bound).

What *is* now unconditional and in-tree toward the pin:
- `shortening_dim = |U|−k` (SYZ21);
- G87 block ≅ `|S|−k`-dim shortening space, i.e. the identification (SYZ22 (i));
- pair space = `2(|U|−k)` doubled shortening (SYZ22 (ii));
- span ceiling `≤ 2(n−k)−1` (SYZ20/SYZ22);
- knapsack count `< B` at `n = 32, 64` given the budget (SYZ21/SYZ22).

The single open link between these and the pin is the realizability lower bound
`finrank(span) ≥ 2(|U|−k)` for over-budget families (sunflower packing, SYZ18 control).

## Theorems (all axiom-clean)

`block_source_dim`, `block_source_dim_eq_shortening`, `doubled_shortening_dim`,
`doubled_eq_two_mul_single`, `span_ceiling`, `strip_budget_of_realizability`,
`knapsack_closes_strip_n64`.
