/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Abort Analysis for Duplex-Sponge Fiat-Shamir

This module provides the theoretical framework for analyzing abort events in the simulator
for Duplex-Sponge Fiat-Shamir (DSFS) transformation. We analyze the conditions under which
the simulation of the duplex sponge oracle using the random oracle and random permutation
aborts, following Section 5.7 of Chiesa-Orrù [CO25].

Specifically, we characterize the relationship between the occurrence of bad events (such as
capacity collisions or permutation inconsistencies) and simulator failure:
- **Lemma 5.17**: Under the condition that the combined bad event $E(\text{tr})$ does not occur,
  the standard trace generator $\text{StdTrace}(\text{tr})$ is guaranteed not to abort.
- **Lemma 5.18**: If the bad event $E(\text{tr}_{\mathcal{A}})$ does not occur during the execution
  of the adversary $\mathcal{A}$, the query simulator $\mathcal{A}^{\text{D2SQuery}}$ does not
  abort.
- **Claim 5.19**: If the inversion event $E_{\text{inv}}(\text{tr}, s)$, permutation consistency
  event $E_{\text{prp}}(\text{tr})$, and backtracking fork event $E_{\text{fork}}(\text{tr}, s)$ do
  not occur, then $\text{backTrack}(\text{tr}, s)$ succeeds without error
  (i.e., does not output $\text{err}$).
- **Claim 5.20**: If the permutation consistency event $E_{\text{prp}}(\text{tr})$ does not occur,
  the lookahead procedure $\text{lookAhead}(\text{tr}.p, s, i)$ is guaranteed not to fail with an
  error for any sponge state $s$ and challenge round $i$.
-/
