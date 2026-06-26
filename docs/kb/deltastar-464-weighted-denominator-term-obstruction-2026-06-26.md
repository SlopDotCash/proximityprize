# DeltaStar #464: weighted denominator term obstruction

Date: 2026-06-26.

Status: obstruction surface, not a floor proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

`codewordSupportDivWeight` is the current scalar-sharp denominator baseline for the singleton
defect route:

```text
sum_{c appearing} #support(u1)/(a - #zeroAgreement(c,u0,u1)).
```

The new obstruction file does not improve that sum.  It makes one failure mode explicit: if one
appearing codeword already has a denominator term large enough that

```text
2B < puncturedWeight + #support(u1)/(a - #zeroAgreement(c,u0,u1)),
```

then the uniform weighted denominator budget cannot hold.

## Lean Surface

`LineListCodewordSupportDivArithmeticObstruction.lean` adds:

```lean
codewordSupportDivWeight_term_le
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_profile_term_gt
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_support_lower_term_gt
```

The first theorem is the bookkeeping fact: each appearing-codeword term is bounded by the
weighted denominator sum.  The three refuters turn a concrete term, an exact support/zero-profile,
or a lower support bound into failure of
`UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted`.

## Critical Point

This is only a one-way certificate.  It is not an exact scanner for failure of the full
denominator sum.  Many moderate terms can push

```text
puncturedWeight + codewordSupportDivWeight
```

over `2B` even when no single term does.  So the route still needs a theorem controlling either
profile concentration across appearing codewords or a genuinely pairwise scalar relation.

## Consequence

Any proof attempt that treats individual denominator terms as harmless can now be tested against
this explicit one-term obstruction.  If a concrete profile satisfies the inequality above, the
weighted denominator baseline is already impossible on that line; progress has to happen before
that profile is admitted or by a sharper theorem than `codewordSupportDivWeight`.
