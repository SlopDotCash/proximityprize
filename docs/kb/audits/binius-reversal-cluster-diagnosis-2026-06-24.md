# Fold reversal-cluster diagnosis — #313 (2026-06-24, triple-witnessed)

Concrete handoff artifact for the Binius `Steps/Fold.lean` reversal cluster
(build errors **1129, 1201, 1355, 1359**). Produced by cold compiler trace +
two independent source-reading agents (not census-trust). The 306 lemma was a
mis-grade that fell to 3 lines; **this cluster is NOT** — it is a genuine
fold-order-vs-statement-order re-derivation, verified below.

## The exact mismatch (from the live compiler, gate build exit 1)

| err | proof builds (`afterSlice`/`beforeSlice`, Fold 1071-1080) | consumer expects (via `incrementalBadEventExistsProp`) |
|-----|-----------------------------------------------------------|--------------------------------------------------------|
| 1129 | `fun cId ↦ Fin.snoc challenges r_i' ⟨j·ϑ+cId⟩` (**raw**)   | `foldOrderChallenges (Fin.snoc …) ⟨…⟩` (**wrapped**)   |
| 1201 | `challenges ⟨j·ϑ+cId⟩` (**raw**)                          | `foldOrderChallenges challenges ⟨…⟩` (**wrapped**)     |
| 1355 | raw `Fin.snoc` (`getLastOraclePositionIndex` variant)     | wrapped                                                |
| 1359 | **has** wrapped `foldOrderChallenges …`                    | expects **raw** (the *inverse* direction)              |

## Root cause (signatures, three-witness confirmed)

- `incrementalFoldingBadEvent … (r_challenges : Fin k → L)` — takes a **raw** function (`Compliance.lean:219`).
- `incrementalBadEventExistsProp` passes `fun cId ↦ foldOrderChallenges challenges ⟨curIdx+cId⟩` — **wrapped**, `Fin.rev`-reversed (`Relations.lean:410`).
- `foldOrderChallenges challenges = fun j ↦ challenges (Fin.rev j)` (`Basic.lean:49`); `getFoldingChallenges i ch k h = fun cId ↦ foldOrderChallenges ch ⟨k+cId⟩` (`Basic.lean:1169`).
- `afterSlice`/`beforeSlice` (`Fold.lean:1071-1080`) are rebuilt in **statement order** (raw `Fin.snoc`/direct index, no `Fin.rev`).

So the lemma reconstructs the challenge slices in statement order while the
surrounding `incrementalBadEventExistsProp` obligations are in fold order
(`Fin.rev`). 1129/1201/1355 need raw→wrapped; 1359 is the inverse — **no single
redefinition of `afterSlice`/`beforeSlice` satisfies all four.**

## The reachable fix (for the maintainer / a future interactive pass)

Re-derive `afterSlice`/`beforeSlice` (and the HEqs `h_afterSlice_heq`/
`h_beforeSlice_heq`, `h_challenges`, `hj_after_full`/`hj_before_full`, and the
`h_not_fresh`/`h_before_false` consumers) in **fold order**, bridging raw↔wrapped
through a `Fin.rev` snoc-reindexing identity.

**★ CENSUS CORRECTION (cold-verified 2026-06-24, two witnesses: repo grep +
source-reading agent):** the keystone the prior census repeatedly cited —
`foldOrderChallenges_snoc`, claimed "proven in Basic.lean, compiles, banked" — **does
NOT exist** anywhere in ArkLib or its deps. Only `foldOrderChallenges_cons`
(`Basic.lean:54`, the *cons→snoc* direction, the WRONG direction for this bridge)
exists. So the reversal fix must FIRST author the missing snoc-reindexing lemma,
THEN do the multi-point re-derivation — strictly harder than the census assumed.
This is maintainer-grade proof engineering, not a one-liner.

## Strategic note — DO NOT grind this solo (lewis-strategy)

The cone gate is **all-or-nothing** and is *also* blocked by QueryPhase **370**
(`iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask`, ill-stated:
`i : Fin r` fed to `Fin ℓ`-typed `qMap_total_fiber_repr_coeff`/
`extractMiddleFinMask` — needs maintainer design intent, 512 consumers). So even
a **perfect** reversal-cluster fix moves the gate by **zero** while risking the
banked Fold state. The reversal cluster + 370 are both maintainer-gated; the
honest solo floor is gate **21** (this session: 22→21 via the 306 fix). See
memory `issue-313-binius-cone-cold-census` DAY-78.
