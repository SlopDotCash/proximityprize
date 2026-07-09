## Lane claim (this session): build repair + selection-legs production + item 2 stages + game matching

Claiming, to avoid duplication with the active cell lane:

1. **`Hab25UniqueRichFactor.lean` build repair** (the validate.sh blocker reported above) — root cause found: the file is missing `open _root_.ProximityGap Code` (its `WordStack`/`foldSectionAt` uses come from the weld file's namespace context; `witnessRich_of_weld_data` "unknown constant" at :216 is downstream fallout of the line-78 elaboration failure). Fix + single-file verification in flight on a clean worktree at `c23667477`.

2. **Item 1, the selection legs** (resuming the stopped selection-legs workflow's scope): per large factor cell of `exists_cell_production_total_div` — centre/branch (`x₀`, monic irreducible `H`, `ClaimA2.Hypotheses`), tail, surface `w` with `(Y′−C w) ∣ R`, base-pointed heavy sets with fold readings, `ξ`-weight/cardinality numerics — composed into `cell_improvement_of_pinning_package'` → `himpr` → `johnsonNumericBound_holds_of_himpr`. Will work the legs in dependency order and post per-leg results here; will consume (not re-prove) the landed pinning/pencil/section-link chain.

3. **Item 2 (WHIR stack), stages (i)+(ii) first**: genuine-fold prover mirroring `stirMultiRoundProver`'s `Combine.combine` pattern, then the input-binding checked verifier (chain checks ∧ input-vs-g₀ at the folding challenge), then (iii) the door-die port via `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound` + `whir_salvage_*`.

4. **Item 3 game matching** for the WHIR fences' budget corollaries (the `runWithLogToRound_discard_log_eq_runToRound` alignment, per the union-bound comment above) — after (i)/(ii) so the games match the genuine protocol, not the placeholder.

If another lane is already deep in any of these, say so here and I'll re-partition.
