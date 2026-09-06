# Issue 2: Guruswami–Sudan library boundary

`GSFactorExtract.lean` and `BivariateVanishing.lean` contain reusable algebra,
including factor extraction from multiplicity bounds and the resulting list-size
bound. They now live in `ArkLib/Data/CodingTheory/GuruswamiSudan/` as
`FactorExtraction.lean` and `BivariateVanishing.lean`. Declaration namespaces,
theorem statements, and proofs are unchanged. Consumers import the new paths.

The historical issue #2 assessment that `GSFactorExtract` has only campaign
consumers is no longer true: `GuruswamiSudan/ListSizeBound.lean` imports it,
and the Guruswami–Sudan umbrella imports that list-size theorem. Moving that
entire dependency chain into Research would remove genuine library machinery.
Rehoming the reusable algebra first keeps the intended library/research boundary.

A comments-aware import preflight on commit
`577b06b6d3e6857bcea8bb5b159c947f144807e7` found 390 modules transitively
importing eleven explicit campaign seeds (Lattice2 and its four children,
GSFactorExtract, CapacityBounds, Hab25ConjectureGlue, and three Whir campaign
modules). Of these, 170 were outside ProximityGap. This count identifies a
review surface, not a classification of every affected module as research.

After rehoming the two algebra modules, the ten remaining seeds reach 213
modules, only 26 outside ProximityGap. This set still requires classification;
the ProximityGap umbrella should lose campaign imports rather than move wholesale.

This change is based on the Frontier split in PR #188. It does not complete
the remaining campaign moves, corpus distillation, or issue #2. Regenerate
both library import roots after staging moved modules, and validate both
library targets before integration. Focused compilation of both moved modules and the downstream `ListSizeBound`
consumer passed under Lean 4.30.0-rc2. Full consumer-graph and repository
validation remain pending.

An import-based audit of all 29 lemmas and theorems in the three checked files
passed with only standard Lean axioms. Source hashes and per-declaration results
are recorded in [`gs-library-boundary-2026-09-06.json`](../kb/audits/gs-library-boundary-2026-09-06.json).
