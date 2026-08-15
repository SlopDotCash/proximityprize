# Issue #466 G136 (part 0): the anchor constant 3 is sharp

Date: 2026-07-11 (UTC). `Frontier/_G136AnchorConstantSharp.lean`, axiom-clean, 0 sorryAx.

## Result

`three_sq_sub_three_le_addREnergy`: for any negation-closed `G` (with `0 ∉ G`, `2 ≠ 0`),

    3·#G² − 3·#G ≤ E₂(G),

by the three explicit pairwise-disjoint families: identity `(x,y;x,y)` (n²), swap
`(x,y;y,x)`, x≠y (n²−n), and the zero-sum plane `(x,−x;z,−z)`, z ∉ {x,±x} (n²−2n), with
exact cardinalities `card_famId`/`card_famSwap`/`card_famZero`.

`coefficient_two_budget_fails_at_production`: at `#G = 2^30` and every `q ≥ 2^158`, the
same lower bound already gives

    q·(2·#G²) + #G⁴ < q·E₂(G),

so any rung-2 production anchor with Wick coefficient `2` is impossible even after spending
the full DC allowance. This is a calibrated consumer of the zero-sum-plane obstruction, not a
new anchor proof.

## Significance

First Lean piece of the cyclotomic accident programme: the production rung-2 anchor
`q·E₂ ≤ 3q·n² + n⁴` is TIGHT — the constant 3 cannot be improved for μ_{2^30} (−1 ∈ H),
and the accident-free value E₂ = 3n²−3n (verified exactly at all tested p ≥ 73) is the
exact minimum for negation-closed sets. The remaining G136 parts (2-power Mann
classification, accident law, sharp production criterion) now have their baseline pinned.

CORE remains OPEN.
