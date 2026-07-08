# δ* #466 — dyadic spike tails and top-coset concentration (2026-07-08)

## Hypothesis

R63 refuted universal dyadic moment-ratio monotonicity.  R64/R65 tested the
next weaker route:

```text
Dyadic Gauss-period spectra may have local super-Wick windows, but those
windows are bounded, recover after a finite moment range, and are carried by
very few exceptional cosets.
```

Probes:

* `scripts/probes/probe_r64_dyadic_spike_tail.py`
* `scripts/probes/probe_r65_dyadic_top_coset_concentration.py`

## R64: spike height and recovery

Exact coset spectra across adversarial and nearby admissible dyadic primes:

```text
n   p          q        v2  fail                 peak        recover
----------------------------------------------------------------------------------
32  32993      1031     5   R1<2 (0.211)         R8=5.5034    R15
64  264769     4137     6   R3<4 (0.0617)        R8=1.679     R12
64  265921     4155     6   R4<5 (0.0081)        R1=1         R2
64  16778497   262164   8   R4<5 (0.0491)        R13=4.2167   R21
128 2101249    16416    12  R4<5 (0.00309)       R1=1         R2
128 268438657  2097177  7   -                    R1=1         R2
256 16777729   65538    9   -                    R1=1         R2
```

Selected spectra:

```text
n=32 p=32993:
  R1=1 R2=1.2107 R3=1.6442 R4=2.3329 R5=3.2513 R6=4.2506
  R7=5.0813 R8=5.5034 R9=5.4002 R10=4.8204 R11=3.9358
  R12=2.9562 R13=2.0537 R14=1.3262 R15=0.7996 R16=0.45195

n=64 p=16778497:
  R1=1 R2=0.9843 R3=0.96446 R4=0.96333 R5=1.0124 R6=1.1493
  R7=1.4103 R8=1.8163 R9=2.3539 R10=2.9642 R11=3.5493
  R12=3.9973 R13=4.2167 R14=4.1643 R15=3.8558 R16=3.3549
```

## R65: top-coset concentration

The super-Wick windows are driven by a tiny exceptional tail.

```text
n=32 p=32993 peak=R8=5.50341 xmax/sigma2=17.6363
  counts >=2:160 >=4:56 >=8:9 >=12:3 >=16:1 >=20:0
  peak-share top1:0.8138 top2:0.9175 top4:0.9769 top8:0.9892

n=64 p=264769 peak=R8=1.67898 xmax/sigma2=18.0304
  counts >=2:656 >=4:176 >=8:15 >=12:3 >=16:1 >=20:0
  peak-share top1:0.7933 top2:0.8763 top4:0.9417 top8:0.9661

n=64 p=16778497 peak=R13=4.21667 xmax/sigma2=27.5838
  counts >=2:41555 >=4:11712 >=8:1064 >=12:118 >=16:22 >=20:2 >=24:2
  peak-share top1:0.6124 top2:0.9506 top4:0.9623 top8:0.9751
```

Controls with peak at `R1` have large high-threshold tails too, but those tails
do not dominate the low moments:

```text
n=64 p=16777601 peak=R1=1 xmax/sigma2=23.1947
  counts >=2:41606 >=4:11695 >=8:1107 >=12:94 >=16:9 >=20:2
  peak-share top1:0.0001 top2:0.0002 top4:0.0003 top8:0.0006

n=128 p=268437889 peak=R1=1 xmax/sigma2=23.6882
  counts >=2:330664 >=4:95115 >=8:9352 >=12:954 >=16:108 >=20:14
  peak-share top1:0.0000 top2:0.0000 top4:0.0000 top8:0.0001
```

## Verdict

The monotonicity route is dead, but R64/R65 leave a viable replacement:

```text
Prove a dyadic Gauss-period order-statistic bound:
  the number of cosets with |η_b|^2 / σ^2 above threshold T is small enough
  that the exceptional tail cannot violate the prize moment envelope.
```

The proof target should not be phrased as `R_{r+1} ≤ R_r`.  It should be a
tail-count or Lorenz-curve theorem for the normalized coset magnitudes.  The
key empirical feature is concentration: in the bad windows, one or two cosets
carry most of the peak moment, while recovery follows once the double
factorial beats those top masses.

Adversarial calibration points:

```text
(n,p,T,count) = (64,16778497,24,2), (64,16778497,16,22),
                (32,32993,16,1), (32,32993,12,3).
```

Any closing theorem must allow these exceptional cosets while bounding their
number and maximum size.
