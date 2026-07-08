# R232: Fermat spike rank profile

Issue: #466. Date: 2026-07-08.

## Question

R230 and R231 left a specific obstruction to the quotient-tail route: rare
high-threshold quotient spikes can spend too much of the quarter-MGF budget.
This round asks whether those spikes are a broad 2-adic saturation phenomenon
or a narrow generalized-Fermat resonance.

## Spike-rank profile

Command:

```text
python3 scripts/probes/probe_r230_spike_rank_profile.py \
  --chunk 8192 \
  --case 64:238081:r230-worst \
  --case 256:202753:r231-C-witness
```

Selected rows:

```text
n=64  p=65537   M=1024  mgf1/4=3.2624  topX=29.776
  top contributions: r1=1.670 r2=1.731 r4=1.831 r8=1.891 r16=1.982
  barrier excess:    r1=2.050 r2=-8.365 r4=-7.437 r8=-8.777

n=64  p=238081  M=3720  mgf1/4=1.6149  topX=21.943
  top contributions: r1=0.065 r2=0.128 r4=0.182 r8=0.209 r16=0.239
  barrier excess:    r1=-10.943 r2=-8.271 r4=-10.344 r8=-12.449

n=256 p=202753  M=792   mgf1/4=1.3912  topX=10.095
  top contributions: r1=0.016 r2=0.028 r4=0.051 r8=0.088 r16=0.129
  barrier excess:    r1=-16.604 r2=-14.690 r4=-12.674 r8=-10.733
```

The worst R231 budget row is nearly a one-spike event: the largest quotient
orbit alone contributes `1.67` toward the target `2`, and the top 16 orbits
already contribute `1.982`.  The R230 multi-spike witness is not comparable;
its top 16 orbits contribute only `0.239`.

## Fermat-family check

Command:

```text
python3 scripts/probes/probe_466_fermat_family.py
```

Aggregate saturated-vs-control result:

```text
worst coset == mu_n: SAT 2/34 = 0.059, CTL 0/34 = 0.000
mu_n coset in top 1%: SAT 0.088, CTL 0.088
C inflation: mean ratio 1.0145, median 1.0011, frac>=1.15 0.029
decision: FAMILY-ARTIFACT by the lane thresholds
```

So broad 2-adic saturation is not enough to explain the obstruction.

The generalized-Fermat subfamily is different.  For primes of the form
`p = B^(n/2) + 1`, the identity period has the exact geometric cosine form

```text
eta_1 = sum_{j < n/2} 2 cos(2*pi*B^j/p) = n - c_B + o(1).
```

The probe verified this closed form on all tested generalized-Fermat rows.
The in-window endpoint `n=32, p=65537 = 2^16 + 1` has:

```text
eta0 = M = 25.2108
C = 1.6140
mu_n is the worst coset
```

The note in the probe remains important: the next `B=2` tower candidate for
`n=64` would use `F_5 = 2^32 + 1`, which is composite.  Thus the strongest
visible one-spike resonance appears finite in the current prime window.

## Interpretation

The negative low-band and trimmed-tail results should not be read as evidence
against quotient methods in general.  They isolate two different top-spike
regimes:

- a narrow generalized-Fermat one-spike resonance, with an explicit geometric
  cosine formula;
- broader multi-spike rows, where the top ranks are individually cheap but
  still force crude survival envelopes to overspend.

A plausible next theorem is therefore not a uniform top-spike reserve.  It is
a structure-sensitive split:

1. classify or finitely enumerate generalized-Fermat identity-coset resonances;
2. prove a rank-barrier inequality for non-resonant quotient spectra;
3. handle the remaining multi-spike rows by a direct rank-sum or second-moment
   budget rather than by an all-threshold survival envelope.

No prize closure is claimed.  This round records a sharper obstruction map and
rules out treating 2-adic saturation itself as the exceptional family.
