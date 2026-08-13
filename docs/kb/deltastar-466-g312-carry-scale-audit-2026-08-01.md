# G312: integer-carry localization is scale-sensitive

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G278 showed that, on its small/medium checked cells, the adjacent-rank CORE alignment does not
localize cleanly into carry zero or nonzero carry buckets. G312 repeats that exact carry decomposition
at certified large field size for the toy order `n=16`.

First, the probe reproduces the published G278 cell `p=433,n=16`:

```text
r=5: A=+3425440, J=4708000, need=4700090
r=6: A=+52032,   J=20680512, need=20680392
```

Both ranks have nonzero carry spread, and carry zero alone is below the gate.

Then Proth theorem certifies

```text
p = 111*2^128 + 1
```

prime with witness `5`, and `p > 16*2^128`. At this prime, for `n=16`, two exact implementations
agree: the integer-carry census and direct modular subset-pair enumeration. The carry profile flips:

```text
r=5: A=+12132759625789254812263498506989117214991787712, J=321216,  carries={0:321216}
r=6: A=+40205630224372760716789501328599919806465162752, J=1064448, carries={0:1064448}
```

So the G278 small-field spread-carry obstruction is scale-sensitive in this checked toy order. At the
certified large field, all counted mass lies in carry zero for both adjacent ranks.

## Scope

This is a finite scale audit, not a production theorem. It uses `n=16`, not `n=2^30`, and it does not
prove any logarithmic-depth or worst-case-over-frequency estimate. It says only that the small-field
carry-localization no-go cannot be read as field-size-stable evidence without checking the large
field regime.

## Artifact

- Probe: `scripts/probes/g312_carry_scale_audit.py`
- Output: platform temp directory `arklib-reports/g312_carry_scale_audit.out`
