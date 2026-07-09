# R234 finite exception taxonomy for top-five route

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R233 identified one dramatic finite obstruction to the top-five budget cap:

```text
n=128, p=65537, M=512
```

R234 checks whether this is isolated or part of a family, and whether the
top-five route should start at `n >= 256`.

## Target Certificate

Parameters inherited from R231/R233:

```text
trim = 5
tau = 0.75
K = 0
C = 0.60110935
step = 0.03125
```

## n = 128 window

Command:

```bash
python3 scripts/probes/probe_r233_top5_budget_cap.py \
  --medium-min-a 7 --medium-max-a 7 --medium-max-index 4096 \
  --min-index 512 --cache-dir /tmp/proximity-r233-n128 --top 40
```

Summary:

```text
cases=565
worst_total=2.701602
worst row: n=128 p=65537 M=512
```

Top failures:

```text
n=128 p=65537  M=512   total=2.701602 topStair=0.988894 maxX=24.486519
n=128 p=231169 M=1806  total=2.0754   topStair=0.3627   maxX=24.389
```

The rest of the reported top-40 rows have positive slack.  The `p=65537`
Fermat row is the monster; `p=231169` is a smaller same-lane failure.

## n = 256 window

Command:

```bash
python3 scripts/probes/probe_r233_top5_budget_cap.py \
  --medium-min-a 8 --medium-max-a 8 --medium-max-index 4096 \
  --min-index 512 --cache-dir /tmp/proximity-r233-n256 --top 25
```

Summary:

```text
cases=532
worst_total=1.907978
slack=0.092022
worst row: n=256 p=583169 M=2278
worst_top_stair=0.195472
maxX=23.915111
```

Thus n=256 already has comfortable margin under the R231/R233 certificate in
this exact window.

## Interpretation

The top-five route should be framed with a finite/asymptotic split:

```text
finite exceptional lane: n <= 128, with explicit handling of p=65537 and p=231169;
main lane: n >= 256, top-five budget cap plus residual tail.
```

This is substantially cleaner than the earlier survival-envelope attempts.  The
main theorem target can now start at `n >= 256`, while the low-n rows can be
handled by finite direct certificates or separate structured-prime lemmas.
