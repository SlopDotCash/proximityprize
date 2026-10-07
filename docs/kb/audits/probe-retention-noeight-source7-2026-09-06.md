# Corrected source-root search retention review

Retain `scripts/probes/probe_noeight_source7_root_coupled_lines.py`. After correcting its inverse-Vandermonde orientation, the full default seed-20260710 search completed 100000 sampled affine row pairs and exited 0. The best raw outsider count is 17, but that sample has joint core nine and violates the required cap. The best sample with joint core at most seven has five outsiders. No residual-shaped candidate was found.

The companion JSON preserves the corrected source hash, complete output, received rows and explicit decoded-polynomial witnesses. The interpolation correction and independent exhaustive polynomial comparison are documented in [the regression audit](noeight-source7-interpolation-fix-2026-09-06.md). Older results from the transposed implementation are not verified by this replay.

The sampled pairs are drawn through legal outsiders with a biased distribution of error sizes. Exhaustive interpolation makes each evaluated score exact, but does not make the affine-line search exhaustive. Five is a lower bound attained by this search, not a universal maximum, and failure to find a residual-shaped candidate does not prove the production residual.

This original unreferenced-source review advances the corrected aggregate to 76 of 92 reviewed, with 16 remaining.
