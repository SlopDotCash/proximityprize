# Issue #464: Full-Field Noisy-Character Transfer Gate

Date: 2026-06-25

Status: transfer obstruction for Kopparty's arXiv:2601.07137 noisy-character recovery theorem;
not a prize proof.

Source checked: https://arxiv.org/abs/2601.07137.  The paper recovers a low-degree polynomial from
noisy values of a character composition on the full field `F_q`; the degree regime is `o(q^(1/2))`
and the error tolerance is a constant fraction of the `q` field positions.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FullFieldNoisyCharacterTransferGate.lean`

## Point

The Kopparty/noisy-character style paper is a full-field polynomial recovery theorem.  Its natural
consumer hypotheses are global: enough agreement or samples over all of `F_q`, plus a degree range.

For #464, the data live only on the dyadic subgroup `mu_n`.  At the prize scale `q >= n^4`, even
perfect knowledge on `mu_n` has global density

```text
n / q <= 1 / n^3.
```

The degree condition may be harmless: if the relevant degree is `d <= n` and `q >= n^2`, then
`d <= sqrt(q)`.  The problem is the global-density transfer, not the polynomial degree.

## Lean Gate

The key consumer theorem is:

```lean
fullField_noisyCharacter_transfer_gate :
  d <= n ->
  0 < n ->
  n^2 <= q ->
  n^4 <= q ->
  globalAgreement <= subgroupDensity n q ->
  1 / n^3 < tau ->
  d <= Real.sqrt q /\ not (tau <= globalAgreement)
```

So any full-field theorem whose agreement threshold is above `n^-3` cannot be triggered merely
from subgroup-supported observations, even when the degree side is inside the theorem's range.

## Consequence For #464

Full-field noisy-character recovery does not transfer to the subgroup period without an additional
extension theorem that upgrades sparse `mu_n` information into full-field agreement.  Such an
extension theorem would itself have to encode the missing equidistribution/cancellation input, so
this route currently relocates the wall rather than breaching it.
