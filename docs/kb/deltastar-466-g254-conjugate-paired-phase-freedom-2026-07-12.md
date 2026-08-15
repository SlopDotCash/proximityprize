# δ* / #466, G254: conjugate-pair symmetry does not repair the phase-histogram route (2026-07-12)

**Lane:** direct GPT-5.6 Sol CORE. Branch `research/proximity-prize` only, #499 respected.

## Question

G252/G253 refute deduction of the fixed-row covariance from a global Jacobi phase histogram. The
actual quotient DFT has a mandatory invariant omitted by G253's sorted-cell model: for real physical
profiles, inverse characters are conjugate,

```text
What(χ⁻¹) = conj(What(χ)),   Rhat_r(χ⁻¹) = conj(Rhat_r(χ)).
```

Could this pairing forbid the balanced antisorted move and reopen a weaker-than-BGK route?

## Exact actual-profile probe

`scripts/probes/g254_conjugate_paired_reversal_probe.py` computes the actual dyadic-subgroup profiles

```text
W(t)   = #{(y,z) in G² : 2y-z=t},
R_r(t) = #{(A,B) : |A|=r, |B|=r-1, sum(A)-sum(B)=t}
```

by exact integer counting, then only uses floating-point FFT coordinates after exact profiles exist.
It verifies conjugacy, equal real contributions on every `{χ,χ⁻¹}` pair, and quotient Parseval. It
restricts admissible signs to `s_χ=s_{χ⁻¹}` and flips exactly half the pairs, so the full row
histogram remains exactly balanced. Results:

```text
n=8,  p=1801, m=225: r5 pairedFrac=-0.8435, r6=-0.8709
n=16, p=1297, m=81:  r5 pairedFrac=-0.9339, r6=-0.9383
n=32, p=3617, m=113: r5 pairedFrac=-0.9644, r6=-0.9642
```

All six proper-subgroup cells reverse strictly. Conjugacy relative errors are below `6e-13`; pair
contribution errors below `3e-12`; quotient Parseval relative errors below `8e-14`. The physical
centered covariances reproduce known exact cells, including `(n,p)=(32,3617)`:
`A_5=-17378716512`, `A_6=-132640776608`.

## Axiom-clean invariant

`_G254ConjugatePairedPhaseFreedom.lean` indexes `2k` inverse-character pairs, each with two conjugate
members. Both members receive the same real rank weight and sign. The move assigns `+1` to the `k`
low-weight pairs and `-1` to the `k` high-weight pairs. It proves:

```text
sum pairedSign = 0,
pairedAlignedCov = 2 * alignedCov > 0,
pairedSplitCov = 2 * splitCov = -2*k^2 < 0.
```

Thus conjugation symmetry does not merely permit annihilation, it doubles G253's reversal. This is
the smallest honest repair audit because pair preservation is the exact extra invariant forced by
real physical profiles.

## Scope

This is a route no-go, not a Jacobi estimate and not prize closure. It closes the only obvious
applicability loophole in G252/G253. Global phase-histogram information remains insufficient even
when strengthened by exact inverse-character conjugation symmetry. A surviving theorem must control
actual joint phase-row placement directly, equivalently the sponsor-prime shifted-subgroup/Jacobi
covariance at both `r=5,6`. FS15-FS18 remain fixed-depth/almost-all-prime and do not supply it.
CORE remains OPEN / ON-BGK.
