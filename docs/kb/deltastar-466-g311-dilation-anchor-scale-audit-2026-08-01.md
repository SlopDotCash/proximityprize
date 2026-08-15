# G311: coefficient-1 dilation anchor fails at certified large field scale

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G297 proved that the coefficient-1 cyclotomic anchor does not transport to the coefficient-2 CORE
kernel. On the small cell `mu_16 <= F_113^*`, the exact values are:

```text
r=5: A1=-2977296, A2=+1727120
r=6: A1= +152176, A2=  -77440
```

G311 checks the same finite question at certified mission-scale field size. Proth theorem certifies

```text
p = 111*2^128 + 1
```

prime with witness `5`. For `n=16`, the probe computes the adjacent-rank rows at `r=5,6` by two
independent exact implementations: sparse row/kernel querying and direct subset-pair enumeration.
Both implementations return:

```text
r=5: A1=-2035138560, A2=+12132759625789254812263498506989117214991787712
r=6: A1=-8954609664, A2=+40205630224372760716789501328599919806465162752
```

Thus the coefficient-1 anchor has the opposite sign from the coefficient-2 target at the large
Proth-prime scale for both ranks checked. The sign-transport shortcut remains dead in this toy-order
large-field audit.

## Scope

This is a finite scale audit of G297, not a production theorem. It uses `n=16`, not `n=2^30`, and it
does not prove any logarithmic-depth or worst-case-over-frequency bound. It only says that the
coefficient-1-to-coefficient-2 sign transport obstruction survives the field-size discipline in this
checked toy order.

## Artifact

- Probe: `scripts/probes/g311_dilation_anchor_scale_audit.py`
- Output: platform temp directory `arklib-reports/g311_dilation_anchor_scale_audit.out`
