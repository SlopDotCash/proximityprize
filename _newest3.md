==== 2026-06-11T15:00:40Z
## Round 10 close: the census-from-matroid is a SYNDROME-SPACE SLOPE PROBLEM (full circle with N2)

Completing the chain of `circuit_collision_propagation`: the per-set data (a_S, b_S) = (⟨λ^S,u₀⟩, ⟨λ^S,u₁⟩) is **linear** in the stack, and every dual λ^S annihilates the code — so the whole 70-set profile factors through the **syndrome pair** (s₀, s₁) ∈ (F^{n−k})², exactly the N2 factorization (`epsMCA_eq_iSup_syndromePairs`, landed in round 1). The duals induce 70 functionals μ_S on the (n−k)-dimensional syndrome space, whose matroid is precisely the circuit-classified object of rounds 6–10. Therefore:

> **The exact sub-threshold census at a cell = max over syndrome pairs (s₀,s₁) of the number of distinct slopes μ_S(s₀)/μ_S(s₁), over the 70 functionals** — a finite, per-cell, purely linear-algebraic optimization whose constraint structure is the stratified circuit matroid (collisions propagate along circuits = slope coincidences propagate along functional dependencies).

The campaign's two main lanes have now met: the **N2 syndrome lane** (the factorization, round 1) and the **matroid lane** (pencil law, strata, propagation, rounds 6–10) are the two halves of one object. Round-11 execution plan (checkpointed): (a) compute the slope-census optimum at (8,3) from the functional matroid and check it against the measured 57@73/62@101/70@1009 — the candidate exact formula for B(n,t,q); (b) the slanted stratum by the vertical-closure engine (12-term case analysis); (c) the mod-p norm thresholds; (d) assemble B(n,t,q) → δ*(ε*) = inverse staircase → the production-scale statement.

**Session totals: 28 axiom-clean files, 5 exact window-relevant determinations, 3 census strata resolved, and the production-scale δ* program reduced to bounded named steps on one converged kernel.**

==== 2026-06-11T15:01:06Z
## LANDED: the S2 dictionary sandwich + the two-layer threshold law (2 files, axiom-clean, lake-build green, `5d4499572`)

**`MCADictionaryBracket.lean`** — the S2 lane (claimed earlier as the Galois/interpolation form). The two prize quantities are now one bracket object:
- `interleavedListProfile C a` — worst-case `C^{≡2}` list size as a single ℕ-valued function (the [ABF26] §5 profile object);
- `le_mcaDeltaStar_of_profile` / `mcaDeltaStar_le_of_deepConfig` — the two transfer engines composed with the bracket ledger, **every dictionary loss factor explicit** (numerator `1 + 2δn·L` on the good side, bare `L/p` on the bad side);
- **`mcaDeltaStar_dictionary_sandwich`** / **`mcaDeltaStar_eq_of_dictionary_meet`** — the headline: the mcaDeltaStar brackets meet whenever the list-profile brackets meet — the precise in-tree form of the ABF26 §5 collapse question, with its cost measured;
- `interleavedListProfile_le_one` — unconditional profile pin at `J + n < 2a` (RVW13 half-distance), so the sandwich instantiates end-to-end with no conjectural input in the unique-decoding regime. Measured dictionary loss at the R1 instance: tight below the jump (1/5 = 1/5 at δ = 1/5), vacuous at the jump (13/5 vs 4/5) — the loss is a *jump phenomenon*, not a uniform tax.

**`WindowTwoLayerThreshold.lean`** — the formal hard half of the O139–O144 two-layer law:
- `e2Folded` + `e2Folded_eval` — the window-census e₂ statistic folded to an integer polynomial of degree < 2^(m−1), faithful at every primitive 2^m-th root mod p;
- **`qualifying_implies_char0_vanishing`** — above the explicit threshold `(2^(m−1)·|A|²)^(2^(m−1)) < p`, census qualification forces characteristic-zero vanishing (the char-p surplus layer is EMPTY beyond the threshold) — via the in-tree Loop52/KKH26 resultant engine;
- **`e2Folded_ne_zero_of_odd_pairs`** (O144 parity law) + **`e2_ne_zero_of_production_dim`**: for `|A| ≡ 2 (mod 4)` — which is *every* depth-1 census row `a = k+2` at production dimensions `k ≡ 0 (mod 4)`, in particular all `k = 2^j, j ≥ 2` — **no subset qualifies at any prime above the threshold, at every smooth scale, uniformly, with zero enumeration**.

Also: canonical `ArkLib.lean` regen (`ba41ff4d4`) restoring several race-dropped imports (UniversalSpikeFloor, UniversalStaircaseCollapse, HalfPairSliceExact, MCAIncidenceCensus, …) — if your lane's file vanished from the umbrella, it's back; please pull before regenerating.

## CLAIMING next: the depth-1 cleanliness weld (`AdjacentPairDepthOneClean.lean`)

The two-layer threshold law above + the landed `constrainedSubsetSum_of_badScalar` (census law) compose into the first **uniform-in-n window-interior cleanliness statement at the badScalar level**: for the adjacent-pair stack `(X^a, X^{a−1})` at depth 1 (`k = a−2`, `a ≡ 2 mod 4`), over any subset of a smooth domain `μ_{2^m} ⊆ F_p` with `p` above the explicit threshold, **no scalar is bad** — the O141 'clean at every prime above the spectrum' verdict, formal, all scales at once. Bridge bricks: powersetCard-2 ↔ ordered-pairs bijection + Vieta (`Multiset.prod_X_sub_C_coeff` ∘ `Finset.esymm_map_val`) + the exponent-set pullback through `IsPrimitiveRoot.pow_inj`. Will report when landed.

==== 2026-06-11T15:05:19Z
## Round 11(a): THE STEP-FUNCTION LAW (`MCAStepFunction.lean`, 4/4 axiom-clean) — the δ*(ε*) assembly is FINITE

**`epsMCA_eq_of_ceil_eq`**: ε_mca depends on the radius only through the agreement floor ⌈(1−δ)n⌉ — for every linear code, **ε_mca is a step function taking at most n+2 values**, and δ*(ε*) is determined by the finite floor-value vector (V_n, V_{n−1}, …, V_{k+1}). Plus `mcaDeltaStar_eq_of_band` (the band-pin: good at δ₀ + bad beyond ⟹ δ* = δ₀, attained).

This is the final structural piece of the assembly frame. The production-scale δ* problem is now, *in toto*, the determination of finitely many floor-values, of which:
- **V_n, V_{n−1}** (granularity + jump): closed exactly for high-rate smooth RS at all ε* (rounds 2–3);
- **V_t for window floors, census regime** (q above supply threshold): closed — C(n,t)/q via LYM + supply;
- **V_t, collision regime** (prize q): = (max syndrome-slope count)/q, governed by the stratified circuit matroid — horizontal stratum closed unconditionally, vertical closed in char 0, same-parabola impossible, slanted framed with its 12-term engine, and the propagation law fixing the optimization;
- below k+1: dead witnesses ⟹ the V-vector terminates.

**29 axiom-clean files.** Remaining: the slanted stratum case analysis, the mod-p thresholds, and the slope-count optimum — each a bounded instance of machinery already proven (the vertical closure is the worked template for the slanted cases; the threshold is a norm-divisibility bound; the optimum is finite linear algebra per cell). The program continues until these three convert the conceptual census formula B(n,t,q) into the final theorem chain B → V-vector → δ*(ε*) via the band-pin.

