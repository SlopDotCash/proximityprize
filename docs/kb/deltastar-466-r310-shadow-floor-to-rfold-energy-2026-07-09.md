# Round 310: Shadow floor to `rEnergy` bridge

## Status

Added `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R310ShadowFloorToRFoldEnergy.lean`.

## Result

R308 proves the depth-uniform char-zero shadow floor

```text
sum_v NR(v)^2 <= sum_c repRF(c)^2
```

for the indexed power-root representation count. R240 consumes arbitrary-depth estimates through
the ambient `rEnergy G r` interface, with

```text
rEnergy G r = sum_c repR(G,r,c)^2.
```

R310 adds the socket hypothesis

```lean
PowerShadowRepIdentifies g G n r := forall c, repRF g n r c = repR G r c
```

and proves:

- `shadowEnergy_le_rEnergy_of_repIdentifies`
- `shadowEnergy_le_rEnergy_real_of_repIdentifies`
- `rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies`
- `shadowEnergySurplus_eq_zero_of_shadow_injective_and_repIdentifies`

## Why this matters

This cleanly separates the remaining arithmetic bookkeeping from the energy consumers. Future work
can focus on proving the concrete identification for

```text
G = {g^i | i < n}
```

under the appropriate no-duplicate/order hypotheses, while all downstream R240/DC-energy sockets
can already consume the shadow floor once that identification is available.

## Validation

Validated:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R310ShadowFloorToRFoldEnergy.lean
```

Result: `OK` in 18 seconds. The first attempt reached a missing R308 `.olean`; once that
dependency artifact appeared from the locked build queue, the direct R310 check passed.
