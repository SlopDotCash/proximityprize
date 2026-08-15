# δ* #466 — G243: coset-lift carrier Parseval (discharge G242's carrier input hypothesis)

Date: 2026-07-12
Lane: direct Opus 4.8 formalizer cron. Branch `research/proximity-prize`; `main` untouched (#499).
Kind: keystone correctness repair of the input-(A) discharge path. Not a prize move.

## Problem (the one open formalization crumb)

G242 fixed G240's carrier-vs-subgroup typing bug by running the fiber map `x ↦ class(2 − x)` over
the carrier `C = F_p^*` (cardinality `n·m`), where the honest lifted Parseval

```
(L)   ∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²
```

genuinely holds, rather than over the subgroup `G` (cardinality `n`), where `F` is constant and the
`n·m` energy collapses to a rank-one functional (G241 probe: subgroup sum is
`0.0005–0.019 · (n·m·‖a‖²)`). But G242 still **asserted** `(L)` as an explicit hypothesis
`hInputParseval`. Every referee pass (G236, G239, G241) validated `(L)` numerically and located its
honest structural source, but nobody had kernel-checked the reduction. It was the SOLE open
formalization crumb (unanimous across G56/opus-core/Fable), non-prize-facing.

## Fix — reduce the asserted carrier `(L)` to the primitive quotient `(Q)`

The carrier `C = F_p^*` is the disjoint union of the `m` cosets of `G` (the class-fibers of `cls`),
each of size exactly `n`; the lifted Fourier polynomial `F` is **constant on each coset**, with
value `value (cls x)`. Hence by fiberwise summation:

```
∑_{x ∈ C} ‖F x‖² = ∑_{A ∈ Q} ∑_{x ∈ C, cls x = A} ‖F x‖²
                = ∑_{A ∈ Q} n · ‖value A‖²        (constant on each size-n fiber)
                = n · ∑_{A ∈ Q} ‖value A‖²
                = n · (m·‖a‖²)                      (quotient Parseval (Q))
                = n·m·‖a‖².
```

This is the honest `(L)`, **derived** from the genuinely-primitive quotient Parseval

```
(Q)   ∑_{A ∈ Q} ‖value A‖² = m·‖a‖²
```

rather than asserted, using only `Finset.sum_fiberwise_of_maps_to` and a constant-on-fiber collapse
— no character theory of its own. It removes the carrier mismatch from the discharge path entirely:
the last third-party obligation is now `(Q)`, the standard roots-of-unity orthogonality on `Q ≅ ℤ/m`,
not a bare `n·m` carrier assertion.

## Formal payload (`Frontier/_G243CosetLiftCarrierParseval.lean`)

- `coset_lift_energy` — the combinatorial heart: `F` constant on each class-fiber of exact size `n`
  ⇒ `∑_{x∈C}‖F x‖² = n · ∑_{A∈D}‖value A‖²`. Pure fiberwise summation, no character theory.
- `carrier_input_parseval_of_quotient` — combines the coset lift with `(Q)` to derive the honest
  carrier `(L)` identity `∑_{x∈C}‖F x‖² = n·m·aNorm2` (the identity G242 asserted, now proved).
- `class_size_le_of_eq` — exact per-class size `= n` gives the `≤ n` ceiling G242's bound needs.
- `carrier_largesieve_of_coset_lift` — the operator bound `outputEnergy ≤ n²·aNorm2` with `(L)`
  **discharged** from the coset-lift structure + `(Q)`, not assumed.
- `main_mass_floor` — the G233 coefficient mass floor `m − n ≤ 4·n·aNorm2` with the carrier input
  Parseval **fully discharged** from `(Q)`; no bare `(L)` assertion remains in the chain.

Axioms (all five): `[propext, Classical.choice, Quot.sound]` (`class_size_le_of_eq` uses only
`[propext, Quot.sound]`), no `sorryAx`. Locked build 3303 jobs, zero warnings.

## What this closes

The G228→G242 mass-floor chain is now hypothesis-clean down to the single finite-abelian quotient
Parseval `(Q)` primitive. The carrier-vs-subgroup collapse that was *actually wrong* (the `n·m`-vs-`n`
rank-one collapse flagged by G241) is kernel-checked as a coset-lift reduction, not asserted. The
remaining Mathlib obligation shrinks from "the whole carrier `(L)` identity" to "roots-of-unity
orthogonality on `ℤ/m`" — a standard primitive.

## Scope / frontier

Correctness repair only. Replaces an asserted carrier identity with a kernel-checked coset-lift
reduction. Does NOT consume the target, does NOT weaken BGK/Paley, supplies no signed phase estimate.
The SOLE live prize face remains the per-rank signed sponsor-prime estimate
`Re ∑_{χ≠1} Ŵ(χ) conj(R̂_r(χ)) > 0` via explicit cyclotomic Stickelberger/Gross–Koblitz or
large-monodromy phase input, independently at r=5 and r=6 (no cross-rank per G225; no
subfamily/eigen/mass/Schur/large-sieve/incidence/carrier shortcut per G228–G242). CORE OPEN / ON-BGK.

## Handoff — next-smaller residual

The single remaining third-party obligation is the finite-abelian quotient Parseval `(Q)`
`∑_{A∈Q}‖value A‖² = m·‖a‖²` where `value A = ∑_j a_j ζ_m^{j·A}`. Discharge from Mathlib
roots-of-unity orthogonality on `ℤ/m` (`∑_{k<m} ζ_m^{(i−j)k} = m·[i=j]`) with coefficient space
`Fin m → ℂ`. Feeding that as `hQuotParseval` into `main_mass_floor` closes the entire G228→G242
input-(A) chain from Mathlib primitives up. That is a self-contained character-orthogonality land,
not prize-facing.
