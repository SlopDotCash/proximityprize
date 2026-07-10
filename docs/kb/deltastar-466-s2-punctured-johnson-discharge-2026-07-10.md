# S2: within-Johnson discharge of `PuncturedListBudget` — the open band is pinned to exactly beyond-Johnson (2026-07-10)

Status: axiom-clean partial discharge + boundary pin landed; the beyond-Johnson band remains THE open core (Johnson-equivalent-hard per hlow-map §3).

## Claim

`Frontier/_S2PuncturedJohnsonDischarge.lean` (namespace `ProximityGap.PuncturedJohnsonDischarge`):

- `lineAppearingCodewords_card_le_of_punctured_johnson`: on any line whose direction has a
  nonempty zero set, with `z = #directionZeroSet u₁`, `s = #directionSupportSet u₁`,
  `A = a − s`, if the squared Johnson condition
  `(ℓ+1)·(A − z/q)² > N·(N + ℓ·((k−1) − z/q))`, `N = z(1−1/q)`,
  holds, then `#lineAppearingCodewords ≤ ℓ`.
- `puncturedListBudget_of_johnson`: uniformly over safe, non-support-eligible lines whose
  parameters satisfy the window, `PuncturedListBudget dom k a ℓ` — the only surviving object on
  the line-list PRIMARY surface after LANE S1 refuted the coupled choose-sum.
- `johnson_condition_sanity`: concrete satisfiable instance of the condition.

Only `1 ≤ k`, `0 < z`, `1 < q` are assumed — the `k ≤ z` restriction-injectivity hypothesis
turned out to be unnecessary (the proof indexes the appearing family directly and feeds pairwise
punctured agreement `≤ k−1` from `rsCode_pairwise_agreeSet_card_le` into
`card_le_of_johnson_sq` on `ι := ↥Z`).

## Mechanism

R2B's zero-agreement floor (`sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords`)
puts every appearing codeword within punctured agreement `A = a − s` of the FIXED center
`u₀|_Z` (on the zero set the line word is constant in γ). Pairwise punctured agreements of
distinct RS codewords are `≤ k−1`. The in-tree agreement-Johnson bound
(`CodeGeometry.card_le_of_johnson_sq`) then caps the family size at the explicit `ℓ`.

## Consequence

The `hlow`/low-profile production obligation is now discharged unconditionally on the
within-Johnson side of the punctured parameters (essentially `(a−s)² ≳ z(k−1)` with `1/q`
corrections), with consumers already wired
(`largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget` →
`mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit`). The surviving open residual on this
lane is machine-pinned to exactly the beyond-Johnson band `(a−s)² ≲ z(k−1)` — the same
beyond-Johnson list-size problem as far branch H1 (hlow-map §3), i.e. the BGK core.

## Honest scope

Seals the tractable side of the split and pins the boundary; does not touch the prize wall.
Issue #466 S2. Axiom audit `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
