# δ* / #466 — G168: scaling coset-confinement of minimal zero-sum supports (2026-07-11)

## Provenance

The Fable referee (2026-07-11 06:35 UTC, `arklib-fable-critic.md`) refereed Shaw's G165
scaling-ladder (`ac6b62994`, comment 4943005346) and **explicitly ranked the coset-stabilizer lemma
as the single decisive next proof for the formalizer**, with a finite group-theory mechanism:

> If `g` has multiplicative order `d > 1` and `g · S = S`, then `S` is a union of the multiplicative
> cosets `x⟨g⟩`. The sum of any nontrivial finite subgroup of `F_p^*` is 0, so each coset `x⟨g⟩` is
> itself a zero-sum subset. Minimality then forbids proper zero-sum subsets, so `S` must be a single
> coset: `s = d = ord(g)`, and the stabilizer is exactly `⟨g⟩`.

The opus-core lane concurrently landed G167 (`_G167NegationStabilizerCollapse.lean`, `e3f9843b1`),
which handles only the **negation** special case `d = 2` (`g = -1`), giving `S.card = 2`. G168 is the
**general order-`d` ladder statement** of which G167 is the `d = 2` instance.

## Theorem (axiom-clean, over any field `K`)

`Frontier/_G168ScalingCosetConfinement.lean`, namespace
`ArkLib.ProximityGap.Frontier.G168ScalingCosetConfinement`.

Definitions:
- `IsZeroSumSupport S` — `S` nonempty, `0 ∉ S`, `∑ S = 0`.
- `IsMinimalZeroSumSupport S` — every nonempty `T ⊆ S` with `∑ T = 0` is all of `S`.
- `scalingOrbit x g d := (range d).image (fun i => x * g ^ i)` — the coset `{x·gⁱ : i < d}`.

Theorems:
- `geom_sum_eq_zero_of_pow_eq_one : g ^ d = 1 → g ≠ 1 → ∑_{i<d} gⁱ = 0`
  (the finite-subgroup sum-is-zero fact, via `geom_sum_mul` factoring `gᵈ - 1 = 0` in a field).
- `sum_scalingOrbit_eq_zero` — a coset `{x·gⁱ}` for a nontrivial `d`-th root of unity sums to
  `x·(∑ gⁱ) = 0`, so it is itself a zero-sum set.
- `card_scalingOrbit` — an injective (distinct-power) orbit has exactly `d` elements.
- **`card_eq_order_of_scaling_fixes`** (core): if a distinct `d`-element coset `{x·gⁱ}` of a
  nontrivial `d`-th root of unity is contained in a minimal zero-sum support `S`, then `S` equals
  that coset and `S.card = d`.
- `no_scaling_fix_of_card_ne` — free-action corollary: if `S.card ≠ d` there is no such fixing
  order-`d` orbit inside `S`.
- `card_eq_two_of_neg_scaling` — the `d = 2`, `g = -1` specialisation recovering G167's collapse.

Axiom audit (`#print axioms`, all six): `{propext, Classical.choice, Quot.sound}` only. No `axiom`,
`sorry`, `native_decide`, or goal weakening.

## Meaning

Exactly identifies the fixed sector of a single order-`d` scaling on minimal zero-sum supports and
**forces the support size to equal that order**: a minimal zero-sum support admitting a fixing
order-`d` scaling is a single multiplicative coset of exactly `d` elements. Consequences for the
ladder census:
- the accident sector of the `2`-Sylow scaling action is concentrated on support sizes equal to the
  order of some fixing element (dyadic `s = 2^j` at production `H = 2^30`);
- every size not equal to any fixing order is a free `H`-orbit, so `2^k ∣ N_s` there.

This upgrades G167's negation-only classification (`d = 2`) to the full order-`d` ladder Fable
requested. It is a **congruence / structural classification, not a magnitude bound**: it does not
bound `N_s` in size and does not touch the BGK/Paley barrier that binds the free-orbit magnitudes at
production depth. **CORE remains OPEN / ON-BGK.** With this capstone the congruence arc of G165/G167
is complete; the only remaining prize-facing object is a *magnitude* bound on the free minimal-zero-sum
support counts, which is exactly where BGK still binds.

## Probe

`scripts/probes/probe_466_g168_scaling_coset_confinement.py` (PASS; `p = 7, 11, 13, 17, 41, 97`):
- geometric-sum vanishing `∑_{i<d} gⁱ = 0` for every element of order `d > 1`, and every coset
  `x⟨g⟩` verified zero-sum with `|x⟨g⟩| = d`;
- every minimal zero-sum support fixed by an order-`d` scaling has `|S| = d` and equals a single
  coset. (Across these cells the only fixed supports are the `d = 2` antipodal pairs, consistent with
  G167; the theorem is proven for general `d`.)

## Relation to prior ledger

- Sharpens/generalises `[466-G167-negation-stabilizer-collapse]` (the `d = 2` instance).
- Consistent with the G165 ladder honest boundary: congruence, not magnitude; BGK still binds.
