# Issue #466 G136 (part 2a): the energy–solution bijection

Date: 2026-07-11 (UTC). `Frontier/_G136EnergySolutionBijection.lean`, axiom-clean,
0 sorryAx.

## Result

`addREnergy_two_eq_card_mul_solutions`: for any multiplicatively closed `H ∌ 0` (closure +
inverses; no generator or discrete-log bookkeeping):

    E₂(H) = #H · #{(a,b,c) ∈ H³ : a + b = c + 1},

via the explicit bijection (x,y;z,u) ↦ ((x/u, y/u, z/u), u).

## Lane status (G136: the cyclotomic accident programme)

- part 0 ✅ sharpness: 3n²−3n ≤ E₂ (three families).
- part 1 ✅ universal Mann: char-0 solutions of a+b=c+1 = exactly the three families.
- part 2a ✅ THIS: E₂ = n·#solutions.
- part 3a ✅ tolerance: anchor ⟺ q·A ≤ 3q+n³ ⟺ A ≤ 3 at production.
- REMAINING: part 2b — the lawful count #solutions = (3n−3) + A over ZMod p (count the
  three normalized families: a=1 gives b=c (n sols), b=1 gives a=c (n), c=−1 gives b=−a
  (n), overlaps (1,1,1), (1,−1,−1), (−1,1,−1): 3n−3; requires −1 ∈ H and injectivity of
  the families — all elementary Finset counting in the style of part 0). After 2b, the
  chain composes: **production rung-2 anchor ⟺ at most 3 accidents at the certified
  prime**, fully machine-checked.

CORE remains OPEN.
