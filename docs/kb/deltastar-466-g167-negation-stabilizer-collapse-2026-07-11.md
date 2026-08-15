# δ* / #466 — G167: negation-stabilizer collapse of minimal zero-sum supports

**Date:** 2026-07-11
**Lane:** arklib-opus-core (direct Opus 4.8 CORE)
**Status:** axiom-clean structural theorem landed; CORE remains OPEN / ON-BGK.

## One-line

The only minimal zero-sum support in `F_p^*` with a nontrivial 2-power scaling stabilizer is a
`{x, -x}` antipodal pair; every other size is a free orbit.

## Context

G165 (Klein-orbit `4 | genericPrimitiveCorePairs`, mod-4 residue on the signed-fixed sector) and the
Fable scaling-ladder referee extended the negation residue to a full mod-`2^k` ladder via the cyclic
2-Sylow `H ≤ F_p^*` acting by scaling on the *minimal zero-sum supports*. The Fable coset-stabilizer
**sketch** proposed a classification in which dyadic sizes `s ∈ {2,4,8,…}` carry nontrivial
stabilizers with `c_s` minimal order-`s` cosets each, giving `N_s ≡ c_s·(2^k/s) (mod 2^k)`.

## Result (sharper than the sketch)

Exact enumeration (`p = 17, 41, 97`, all minimal zero-sum supports up to size 5–6) shows the dyadic
part of the sketch is empty: **the only minimal zero-sum support with any nontrivial 2-power
stabilizer is `{x, -x}`, stabilized only by `-1`.** Equivalently:

> `S` minimal zero-sum and `S = -S` (char `≠ 2`)  ⟹  `S.card = 2` and `S = {x, -x}`.

### Mechanism — the subcoset obstruction the sketch missed

A nontrivial 2-power scaling `u` of order `d ≥ 2` satisfies `u^{d/2} = -1` (the unique element of
multiplicative order two in a field). So `u·S = S` already forces `-1·S = S`, i.e. `S = -S`. A
negation-symmetric set of nonzero field elements (char `≠ 2`) is a disjoint union of two-element
antipodal pairs `{x, -x}`, and each such pair is *itself* zero-sum (a nontrivial finite subgroup of
`F_p^*` sums to `0`; `Mathlib.sum_subgroup_units_eq_zero`). Minimality forbids a proper nonempty
zero-sum subset, so `S` is exactly one pair. A coset of a subgroup of order `d ≥ 4` is never minimal
because it contains the order-2 subcoset `{x, -x}`.

## Consequences

- The primitive-residue **accident sector is exactly the size-two supports**.
- For every `s ≠ 2`, `-1` (and any 2-power scaling group containing it, up to the full `H`) acts
  **fixed-point-freely**, so `2^k ∣ N_s`.
- For `s = 2`, `N_2 = (p-1)/2` is divisible by `2^{k-1}` only (the enumeration correctly reports
  `2^k ∤ N_2`).
- This is a **congruence, not a magnitude bound**; it cannot move the production census scale. BGK/
  Paley still binds on the magnitude of `N_s` and the free-orbit counts.

## Payload

- `Frontier/_G167NegationStabilizerCollapse.lean` — axiom-clean over any field of char `≠ 2`.
  Theorems: `sum_antipodal_pair`, `card_antipodal_pair`, `ne_neg_self_of_ne_zero`,
  `neg_mem_of_neg_invariant`, `card_eq_two_of_neg_invariant`,
  `no_neg_invariant_support_of_card_ne_two`. Axioms `{propext, Classical.choice, Quot.sound}`.
- `scripts/probes/probe_466_g167_negation_stabilizer_collapse.py` — PASS.

## Honest scope

Structural finite-field group-action theorem classifying the fixed-point sector of negation on
minimal zero-sum supports. No magnitude bound; does not touch the BGK barrier. CORE open.
