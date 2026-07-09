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

R310 adds the concrete power-root set

```lean
powerRootSet g n := Finset.univ.image (fun i : Fin n => g ^ (i : Nat))
```

the socket hypothesis

```lean
PowerShadowRepIdentifies g G n r := forall c, repRF g n r c = repR G r c
```

and proves:

- `powerTuple_mem_piFinset`
- `exists_unique_powerTuple_of_mem_piFinset`
- `repR_eq_filter_card`
- `repRF_eq_repR_powerRootSet`
- `powerShadowRepIdentifies_powerRootSet`
- `pow_inj_below_order`
- `power_index_injective_of_orderOf`
- `powerShadowRepIdentifies_powerRootSet_of_orderOf`
- `shadowEnergy_le_rEnergy_of_repIdentifies`
- `shadowEnergy_le_rEnergy_real_of_repIdentifies`
- `shadowEnergy_le_rEnergy_powerRootSet_of_orderOf`
- `shadowEnergy_le_rEnergy_real_powerRootSet_of_orderOf`
- `rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies`
- `rEnergy_powerRootSet_eq_shadowEnergy_of_orderOf_and_shadow_injective`
- `shadowEnergySurplus_eq_zero_of_shadow_injective_and_repIdentifies`

## Why this matters

This discharges the finite-set bookkeeping layer. Under injectivity of the first `n` powers,
the indexed R308 count is definitionally transported to the ambient R240 count for

```text
G = {g^i | i < n}
```

R310 also proves that `orderOf g = n` plus `g != 0` supplies that injectivity. Thus all downstream
R240/DC-energy sockets can consume the R308 shadow floor for the exact-order concrete power-root
set. The remaining arithmetic input for equality rather than a floor is R308 shadow injectivity,
i.e. control of genuine bounded-height cyclotomic collisions.

## Validation

Validated:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R310ShadowFloorToRFoldEnergy.lean
```

Result: `OK` in 18 seconds. The first attempt reached a missing R308 `.olean`; once that
dependency artifact appeared from the locked build queue, the direct R310 check passed.

Follow-up validation after adding the concrete power-root representation bridge:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R310ShadowFloorToRFoldEnergy.lean
```

Result: `OK` in 34 seconds.

Follow-up validation after adding exact-order injectivity consumers:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R310ShadowFloorToRFoldEnergy.lean
```

Result: `OK` in 29 seconds.
