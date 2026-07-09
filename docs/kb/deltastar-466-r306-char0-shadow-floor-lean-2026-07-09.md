# #466 R306 — the char-0 shadow floor, machine-checked (r305 classification formalized in Lean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R306Depth3CharZeroFloor.lean`
(real locked build, all 4 theorems axiom-clean [propext, Classical.choice, Quot.sound]).

For `n = 2m` and any `g : F` with `g^m = −1` (the Φ_n = x^m + 1 relation, F any field):

- `evalVec_vecOf` / `gsum_eq_evalVec_tripleVec`: every triple's field-level 3-sum
  `g^a + g^b + g^c` FACTORS through its exact integer shadow vector in `ℤ^m`
  (the r305 construction, now a theorem);
- `rep3F_eq_sum_N3`: the field-level fiber count is the pushforward of the char-0
  histogram `N₃` along shadow evaluation;
- `shadow_energy_le_depth3_energy` (**the floor**): `Σ_v N₃(v)² ≤ Σ_{c:F} rep₃(c)²` —
  the depth-3 energy of ANY field instance is at least the char-0 shadow energy,
  unconditionally. The difference is exactly the r305 collision mass ("excess") ≥ 0.

This is the Lean foundation for consuming the r305 census: the floor half is now proven;
the excess half (= what the good-prime lane must exclude) is the exactly-characterized
census object. Next consumers: (a) tie `Σ N₃²` to the #464 closed form `15n³−45n²+40n`
at n = 2^k; (b) an injectivity criterion (`evalVec` injective on `keys` ⟹ excess = 0 ⟹
E₃ = char-0 exactly) as the formal good-prime condition. CORE OPEN.
