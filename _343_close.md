## Verified complete on `main` — the anchor was removed, no `True` anchors remain

**Resolution**: `FoldedStackOfRound : Prop := True` was **removed** (acceptance criterion "or remove it if it is unused") in commit `4aaf2990c` (2026-06-10). Verification audit on current `origin/main` (`4443d39a9`):

1. **No references remain in any `.lean` source**: `git grep FoldedStackOfRound origin/main -- '*.lean'` → empty. The only residue is the stale generated snapshot `docs/kb/_generated/declarations.json` (derived output, refreshed by the kb pipeline — not source).
2. **It was genuinely unused**: the anchor was a bare named `Prop` consumed by nothing; the semantic data the issue asked for (round domain / `δ` / per-round error / sumcheck residual `ε_sc`) is carried by `RoundProxGapBoundedByKeystone` (`KeystoneReduction.lean` §4), which survives with its two proven theorems (`roundProxGap_of_keystone_no_sumcheck`, `roundProxGap_of_keystone_and_sumcheck`).
3. **No WHIR soundness bridge statement consumes a `True` structural anchor**: `grep ':= True' ArkLib/ProofSystem/Whir/ ArkLib/ProofSystem/Stir/` → zero hits.
4. **`python scripts/forbidden_tokens.py`** → `clean (no native_decide / bv_decide / undocumented custom axiom / vacuous ': True' placebo; 0 allowlisted residual axiom(s))`.

The broader WHIR keystone surface (the §1 keystone residuals `StrictCoeffPolysResidual` / `BoundaryProbabilityResidual` and the named `ε_sc` sumcheck residual) remains tracked in #302 as designed — those are honest named obligations, not vacuous anchors.
