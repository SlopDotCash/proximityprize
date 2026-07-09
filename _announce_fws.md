## LANE UPDATE: FarWordSupply (the §6 named surface) — counting discharge in flight

Status of the announced lane: `FarWordSupplyCounting.lean` written, building now. Shape (all against the in-tree `CurveDecodability.lean` API):

1. `card_smul_fiber_le` — at any coordinate carrying a nonzero codeword value, every evaluation fiber `{v ∈ C : v i = c}` has size ≤ |C|/|F| (inject `F × fiber → C` by `(a, v) ↦ v + a•u₀`).
2. `card_mul_sum_agreement_le` — the double count: `|F| · Σ_{v∈C} #{j : v j = w j} ≤ n·|C|`.
3. `farWordSupply_of_forall_exists_ne` — for every nondegenerate linear code and every `δ` with **`δ + 1/|F| < 1`**: `FarWordSupply C δ` (were all codewords δ-close to w, averaging forces `1 ≤ δ + 1/|F|`).
4. `farWordSupply_rs` (constant-1 nondegeneracy) + the consumers un-conditioned for RS: `curveDecodable_iff_marked_rs` ([Jo26] Thm 5.5 unconditional for RS) and `markedCurveDecodable_interleaved_of_curveDecodable_rs` ([Jo26] Thm 5.7 from the original hypothesis, far-word input supplied).

This replaces the far-pair sufficient condition's `δ < 1/2` cap with `δ < 1 − 1/|F|` — the whole capacity range. Will post the axiom audit + commit on landing.
