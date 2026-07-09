# R251 micro-band residual socket

Date: 2026-07-09
Issue: #466 / Proximity Prize

## What landed

Lean socket:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R251MicroBandResidualSocket.lean
```

It proves the finite-carrier accounting lemma behind R249:

```text
residual_tail_of_microBandHalfRateSplit
```

Given a residual carrier `s`, scores `t`, thresholds `tau <= kappa`, and
constants `Cmicro`, `Ctail`, `C`, it shows:

```text
MicroBandHalfRateSplit(s,t,tau,kappa,Cmicro,Ctail)
Cmicro * exp(kappa/2) <= C
Ctail <= C
--------------------------------------------------
SurvivorCount(theta) <= C * |s| * exp(-theta/2)
for every theta >= tau
```

The lemma proves no arithmetic distribution input.  It only packages the
accounting that turns a short-band count cap plus a high-tail cap into the
single half-rate residual CDF theorem.

## Verification

Command:

```bash
scripts/pg-iterate.sh -q \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R251MicroBandResidualSocket.lean
```

Result:

```text
OK (9s)
```

The file includes an axiom audit for
`residual_tail_of_microBandHalfRateSplit`.

## R249 constants

The current numerical instantiation is:

```text
tau    = 0.75
kappa  = 0.7525
C      = 0.6012
Cmicro = 0.412121
Ctail  = 0.60110935
```

This leaves about `9e-5` slack in the finite exact window.  The remaining
content is now two separate arithmetic inequalities:

```text
S(0.75) <= 0.412121
S(theta) <= 0.60110935 * exp(-theta/2), theta >= 0.7525
```

on the residual quotient carrier after deleting the paid top ranks.
