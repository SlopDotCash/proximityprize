# δ* #466 — random-phase bulk control comparison (2026-07-08)

## Hypothesis

R173/R174 suggested the dyadic bulk might be explained by random-walk behavior
of sums of unit phases.  R175 compares exact dyadic coset spectra against
random sums of `n` independent unit phases, normalized by mean square.

Probe: `scripts/probes/probe_r175_random_phase_bulk_control.py`.

## Result

```text
n=64 p=16778497
  dyadic q50=0.461 q75=1.333 q90=2.718 S1=0.319 S2=0.159 S4=0.045
         max=27.584 mgf=1.1541 grid=1.1984 r170=0.5470
  random q50=0.696 q75=1.393 q90=2.299 S1=0.370 S2=0.136 S4=0.017
         max=11.550 mgf=1.1426 grid=1.1817 r170=0.6327

n=128 p=268437889
  dyadic q50=0.458 q75=1.326 q90=2.710 S1=0.318 S2=0.158 S4=0.045
         max=23.688 mgf=1.1543 grid=1.1987 r170=0.5442
  random q50=0.696 q75=1.387 q90=2.298 S1=0.369 S2=0.135 S4=0.018
         max=12.065 mgf=1.1428 grid=1.1819 r170=0.6311

n=256 p=16777729
  dyadic q50=0.456 q75=1.325 q90=2.708 S1=0.319 S2=0.158 S4=0.045
         max=16.587 mgf=1.1544 grid=1.1988 r170=0.5459
  random q50=0.695 q75=1.390 q90=2.286 S1=0.369 S2=0.134 S4=0.019
         max=11.912 mgf=1.1428 grid=1.1820 r170=0.6311
```

## Verdict

The dyadic spectrum is not simply random phases.

Compared to random unit-phase sums, dyadic periods have:

* more very-small values, shifting the median down from `≈0.696` to `≈0.46`;
* fewer values just above `T=1`;
* a heavier moderate/high tail (`S4≈0.045` versus `≈0.018`);
* only a small R168 MGF penalty (`≈ +0.0115`).

Proof implication:

```text
Do not try to prove R170 by importing a generic random-walk concentration
theorem.  The dyadic arithmetic distribution is more polarized: extra mass near
zero compensates for a heavier tail.
```

The useful survivor is an MGF/cancellation view: the high-tail penalty is small
enough that the finite-grid certificate still has large slack.  A proof may
need to exploit a conservation law or recurrence that forces the extra high
tail to be paid for by extra near-zero cosets.
