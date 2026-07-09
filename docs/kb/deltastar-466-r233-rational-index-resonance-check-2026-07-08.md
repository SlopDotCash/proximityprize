# R233: rational-index resonance check

Status: quick negative/partial evidence.

## Question

After R232 refuted the low-order quotient-character explanation, the next
candidate was:

```text
large spikes occur when the top quotient index j has j/M unusually close to a
small-denominator rational a/q.
```

This would be useful because it might turn top-spike control into a Diophantine
counting lemma.

## Scratch command

For `n=64`, prime rows `p = 64 M + 1`, and `500 <= M < 5000`, compute the
top index `j`, best rational approximation with `q <= 32`, and the scaled
error

```text
M * |j/M - a/q|.
```

The scaled error is used because unscaled error automatically shrinks with
large `M`.

## Observations

Top direct-MGF failures:

```text
M=1024 p=65537  mgf=3.262 X=29.776 scaledErr=0.000 frac=0/1
M=3193 p=204353 mgf=2.632 X=32.121 scaledErr=3.050 frac=17/20
M=757  p=48449  mgf=2.239 X=24.992 scaledErr=0.435 frac=18/23
M=990  p=63361  mgf=2.002 X=24.556 scaledErr=1.000 frac=17/30
```

But nearby or strong passing rows also have good small-denominator hints:

```text
M=1030 p=65921  mgf=1.934 X=23.600 scaledErr=0.211 frac=1/19
M=522  p=33409  mgf=1.865 X=21.551 scaledErr=0.071 frac=25/28
M=3760 p=240641 mgf=1.612 X=23.000 scaledErr=0.828 frac=14/29
M=1702 p=108929 mgf=1.579 X=20.043 scaledErr=0.452 frac=16/31
```

And some high absolute spikes with safe MGF have poor rational proximity:

```text
M=4050 p=259201 mgf=1.621 X=23.855 scaledErr=17.000 frac=1/1
M=2227 p=142529 mgf=1.871 X=25.814 scaledErr=27.594 frac=1/32
```

## Interpretation

Small-denominator proximity is not a clean classifier for MGF failure.  It may
help describe individual resonances, but a theorem of the form

```text
top spikes only occur near small-denominator j/M
```

is false or too weak for the prize route.

The evidence keeps pointing to a rank-weighted anti-concentration statement:
large top spikes are allowed, but their cumulative weighted mass

```text
sum_{r < R} exp(X_(r)/4) / M
```

must be controlled.  The classifier probably needs both phase-alignment size
and carrier size, not just order or rational approximation of the quotient
index.
