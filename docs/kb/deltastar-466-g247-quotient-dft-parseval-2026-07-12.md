# G247 quotient DFT Parseval closes the G243 `(Q)` residual

Date: 2026-07-12
Branch: `research/proximity-prize`
Issue: #466

## Result

G243 reduced the carrier-correct large-sieve input `(L)` to a single primitive quotient Parseval

```text
(Q)  ∑_{A ∈ Q} ‖value A‖² = m · ‖a‖².
```

G247 specializes `Q` to `ZMod m`, takes `value = 𝓕 a` for the unnormalized `ZMod` DFT, and discharges `(Q)` using the existing axiom-clean theorem `_ZModDFTParseval.dft_parseval`.

The landed consumer

```lean
main_mass_floor_of_zmod_dft
```

feeds this quotient Parseval directly into G243's `main_mass_floor`.  The G228→G243 input-(A) chain is now closed down to Mathlib/ArkLib's `ZMod` Fourier orthogonality primitive: no asserted carrier `(L)` and no bare quotient `(Q)` hypothesis remain in this consumer.

## Scope

This is a correctness-closure theorem, not a prize estimate.  It does not provide the signed sponsor-prime phase cancellation needed for the rank-5/rank-6 covariance.  CORE remains open/on-BGK.

## Axiom audit

`quotient_parseval_zmod_dft` and `main_mass_floor_of_zmod_dft` inherit the expected axioms from `_ZModDFTParseval` and the G243/G242 chain: `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
