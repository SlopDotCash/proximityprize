# Issue #466 G136 (production instantiation): the concrete rung-2 equivalence at μ_{2^30}

Date: 2026-07-11 (UTC). `Frontier/_G136ProductionInstantiation.lean`, axiom-clean,
0 sorryAx.

## Result

`production_rung2_anchor_iff_accidents`: for a primitive 2^30-th root of unity ω in a
finite field with > 2^90 elements (both certified prize primes qualify):

    q·E₂({ω^k : k < 2^30}) ≤ 3·q·(2^30)² + (2^30)⁴  ⟺  #accidents ≤ 3.

All closure hypotheses (card = 2^30, 1 ∈ H, 0 ∉ H, ·-closed, ⁻¹-closed, −1 = ω^{2^29})
discharged from `IsPrimitiveRoot` alone, reusing the in-tree
`primitiveRoot_pow_eq_iff`/`primitiveRoot_pow_half` bricks.

## G136 programme: COMPLETE at rung 2 (six files, all axiom-clean)

sharpness → universal Mann → energy–solution bijection → lawful count → tolerance pin →
abstract capstone → concrete production instantiation. The production rung-2 anchor is
now literally: "the certified prime admits ≤ 3 accidents in μ_{2^30}" — a finite
Diophantine fact, expected count 2^{-68}, attackable by cyclotomic divisibility rather
than exponential sums. Extension surface: rungs 3–10 via 2t-term conjugate-trick Manns.

CORE remains OPEN — the accident counts are the wall.
