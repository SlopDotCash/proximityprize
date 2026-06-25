# Issue #464: profile compression forces large fibers

Date: 2026-06-25.

Status: **counting guardrail**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackProfileCompressionTradeoff.lean
```

records the cardinality pressure behind any finite stack profile.

For a profile map

```lean
profile : WordStack A (Fin 2) iota -> P
```

Lean proves:

```lean
stackUniverse_card_le_profileCard_mul_fiberCap
exists_large_profileFiber_of_profileCard_mul_lt_stackUniverse
cardA_pow_le_profileCard_mul_fiberCap
exists_large_profileFiber_of_profileCard_mul_lt_exp
profileFiber_card_le_one_of_injective
stackUniverse_card_le_profileCard_of_injective
not_injective_profile_of_profileCard_lt_stackUniverse
```

The core statement is:

```text
if every profile fiber has size <= K,
then #WordStack <= #P * K.
```

Since

```text
#WordStack(A, Fin 2, iota) = |A|^(2*|iota|),
```

any profile with `#P*K < |A|^(2|iota|)` must have a fiber larger than `K`.

The injective-profile lemmas pin the opposite end: an injective profile has fibers of size at most
one, so its profile space must be at least as large as the entire stack universe.  Therefore any
profile that is genuinely smaller than the stack universe is necessarily non-injective and must
merge distinct stacks.

## Critical Consequence

A small binder, adjacent-pattern, monomial, or floor-localization profile cannot cover the stack
universe with uniformly small fibers.  If the profile count is small, at least one profile fiber is
enormous.

That does not refute the profile route.  It says exactly where the real theorem lives:

```text
inside each large fiber, prove the true bad-scalar maximizer is controlled.
```

Together with `_StackProfileFiberMax.lean`, this gives the profile route's honest burden:

```text
small #P buys compression only by creating large fibers;
large fibers are acceptable only if their exact maximizers are structurally forced.
```

So a proposed profile proof should be red-teamed in two passes:

```text
1. Does #P actually compress the stack universe?
2. If yes, what theorem controls the huge profile fibers it necessarily creates?
```

Without an answer to (2), profile compression is only relabeling the worst-case stack problem.
