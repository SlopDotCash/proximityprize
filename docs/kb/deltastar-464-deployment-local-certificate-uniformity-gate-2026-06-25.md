# DeltaStar #464: Deployment-Local Certificate Uniformity Gate

## Artifact

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DeploymentLocalCertificateUniformityGate.lean`

## Point

Deployment-local or finite certificates are useful evidence, but the #464 consumer needs a
uniform theorem over the target instance family.  A checked base panel, checked field list, or
fixed deployment subgroup cannot by logic alone imply an all-scale statement.

The Lean gate records the exact contract:

- `CertifiedOn S Good`: `Good` has been checked on the local/finite set `S`.
- `UniformGood Good`: `Good` holds for every target instance.
- `CoveredByCertified S Good`: every target instance reduces to a checked one in a way preserving
  `Good`.

It proves the negative model:

```lean
finite_nat_certificates_not_force_uniform :
  not (forall Good : Nat -> Prop, CertifiedOn S Good -> UniformGood Good)
```

and the positive replacement:

```lean
uniformGood_of_certifiedOn_and_cover :
  CertifiedOn S Good -> CoveredByCertified S Good -> UniformGood Good
```

## Consequence

Finite deployment checks should be routed as local evidence unless accompanied by a cover,
propagation, or action-orbit substitution theorem.  The missing analytic/formal input is not more
local certificates by themselves; it is the theorem showing that every target instance is covered
by the certified family.

## Status

Negative/guardrail, axiom-clean.  No closure of the proximity gap is claimed.
