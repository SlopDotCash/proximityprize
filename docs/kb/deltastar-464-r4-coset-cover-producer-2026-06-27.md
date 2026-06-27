# #464 R4 coset-cover producer and direct-attack triage — 2026-06-27

Status: **producer contract landed, no delta-star closure**.

## What was tried

The dossier's best non-BGK direct lane is R4: symmetric-function/coset
rigidity for the bad-scalar image.  In the clean reduced case, the bad scalar
is a symmetric readout such as `gamma = -e1(S)` under constraints like
`e2(S)=0`; dilation forces realized bad scalars to come in cyclotomic cosets.
If every stack's bad scalars met only `O(1)` such cosets, the incidence bound
would be `O(n)` and would feed the existing `WorstCaseIncidenceBounded`
consumer directly.

I stress-tested the tempting Mann/Lam-Leung proof idea.  It does explain why
dyadic vanishing sums break into antipodal pieces, but the existing exact probe
`probe_444_n13_d2_e2_recursion_profile.py` already shows this is not enough:
the `e2=0,e1!=0` lane has structural width-5 rows outside the two-singleton
recursion.  So "all bad sets are paired blocks plus tiny tails" is not a proof
of R4.

I also checked the genuinely wild explicit-formula/zero-density lane already
formalized in `_AmbWildLeap.lean`.  It does escape the hypotheses of the two
standard no-go cages, but the zero count reintroduces the same gap unless one
proves a uniform zero-density/pair-correlation estimate.  That is a new analytic
front, not a closure.

## Lean addition

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R4CosetCoverProducer.lean`

Main declarations:

- `BadScalarCover`: for every stack, bad scalars are contained in at most `K`
  finite pieces of size at most `S`.
- `badScalarSet_card_le_of_cover`: finite union bound, `#bad <= K*S`.
- `worstCaseIncidenceBounded_of_badScalarCover`: the cover discharges
  `OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ (K*S)`.
- `worstCaseIncidence_pin_of_badScalarCover`: if `(K*S)/q <= epsilon*`, then
  `δ <= mcaDeltaStar C epsilon*`.

Validation:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R4CosetCoverProducer.lean
```

Result: OK, axiom audit only reports the usual `propext` line.

## Net

The direct proof is now sharply phrased: prove the actual R4 rigidity theorem
that supplies `BadScalarCover` with `K=O(1)` and `S=O(n)` at the prize radius.
Mann pairing alone is too narrow; the explicit-formula route relocates the wall.
The surviving concrete target is still a q-independent symmetric-function
coset-cover theorem, not another moment or SDP estimate.
