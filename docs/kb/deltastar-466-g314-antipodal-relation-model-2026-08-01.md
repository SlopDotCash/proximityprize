# G314: antipodal-pair model explains the certified all-rank table

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G313 found that at the certified Proth prime

```text
p = 111*2^128 + 1
```

with toy order `n=16`, the coefficient-1 weighted kernel has zero adjacent-rank alignment at every
rank `r=1..15`, while coefficient 2 has positive alignment at every rank.

G314 explains the exact dot table by a finite antipodal-pair model. Write the 16th roots as eight
pairs `{e_j, -e_j}`. For each ordered kernel pair `(y,z)`, and for each antipodal root pair, count
only local selections of the `r`-subset `A` and the `(r-1)`-subset `B` that balance the signed
coordinate in

```text
coefficient*y - z - sum(A) + sum(B) = 0.
```

This pure combinatorial model returns:

```text
coefficient 1: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
coefficient 2: [16, 576, 8064, 64064, 321216, 1064448, 2369472, 3544608,
                3544608, 2369472, 1064448, 321216, 64064, 8064, 576]
```

The exact finite-field computation at `p=111*2^128+1,n=16` matches these model dot values at every
rank `r=1..15`. Direct subset-pair enumeration also agrees for the live ranks `r=5,6`.

The same model does not match the small G297 cell `p=113,n=16`: at ranks `5,6`, the field dots are
much larger and even reverse signs relative to the large-scale behavior. Thus the small-cell signs
include extra finite-field relations; the certified large-scale toy cell is governed exactly by the
antipodal-pair relation table.

## Scope

This remains a finite toy-order audit. It explains the `n=16` certified-scale table but does not
prove the production `n=2^30` case. The useful next question is whether this antipodal-pair normal
form persists, approximately or exactly, at larger toy orders and at the live rank window.

## Artifact

- Probe: `scripts/probes/g314_antipodal_relation_model.py`
- Output: platform temp directory `arklib-reports/g314_antipodal_relation_model.out`
