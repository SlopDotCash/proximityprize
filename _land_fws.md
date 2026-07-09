## LANDED: FarWordSupply discharged by counting (`FarWordSupplyCounting.lean`, commit e5d63b113, 7/7 axiom-clean)

The §6 named surface `FarWordSupply` ([Jo26] Lemma 5.4's counting input, `CurveDecodability.lean`) is closed for the codes that matter:

- **`farWordSupply_of_forall_exists_ne`** — every linear code with no degenerate coordinate supplies δ-far codewords for **all δ with δ + 1/|F| < 1**. Proof: the fiber bound (`card_smul_fiber_le`: `(a, v) ↦ v + a•u₀` injects `F × {v ∈ C : v i = c}` into C, so every evaluation fiber is ≤ |C|/|F|) + the agreement double count (`card_mul_sum_agreement_le`: `|F|·Σ_{v∈C} #{j : v j = w j} ≤ n·|C|`) + averaging (all-close would force 1 ≤ δ + 1/|F|).
- **`farWordSupply_rs`** — RS at every k ≥ 1 (constant-1 nondegeneracy), so the in-tree far-pair route's δ < 1/2 cap is replaced by the **whole capacity range** at cryptographic field sizes.
- Consumers un-conditioned for RS: **`curveDecodable_iff_marked_rs`** ([Jo26] Thm 5.5 as an unconditional equivalence for RS) and **`markedCurveDecodable_interleaved_of_curveDecodable_rs`** ([Jo26] Thm 5.7 from the original hypothesis, far-word input supplied). Any future GG25-style curve-decodability result for explicit smooth RS now imports marked form + interleaving transfer with zero conditional baggage in this range.

Honest scope note (in-file): 1 − 1/|F| is the averaging threshold, not a per-code optimum; some sub-1 threshold is necessary in general (zero code). What the consumers need — coverage of δ ≤ 1 − ρ for RS — is what it gives.

The §6 debt table now reads: `FarWordSupply` ✅ closed (this); `TZPrimeSupply` (analytic NT external, priced), `JohnsonDischargeStatement` (GS aggregation), GKL24 witness-cover ×4, CS25 refutation inputs ×2, paper-interface residuals — still open.
