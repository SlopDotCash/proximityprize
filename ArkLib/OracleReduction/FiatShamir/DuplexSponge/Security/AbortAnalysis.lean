/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Abort Analysis for Duplex-Sponge Fiat-Shamir (placeholder)

**Status: placeholder module with no declarations.** This file currently consists of the import
of `Security/BadEvents.lean` and this docstring only. None of Lemmas 5.17–5.18 or Claims
5.19–5.20 below is stated or proved in this module; the list records the intended content.
(Fragments of the Claim 5.19 argument are used, on the honest surface, in `ForkPaper.lean` and
`ForkPaperFork.lean`; those files do not state the abort lemmas themselves.)

Intended content: analyze abort events in the simulator for the Duplex-Sponge Fiat-Shamir (DSFS)
transformation, i.e. the conditions under which the simulation of the duplex sponge oracle using
the random oracle and random permutation aborts, following Section 5.7 of Chiesa-Orrù [CO25].

Specifically, the planned statements relate the occurrence of bad events (such as capacity
collisions or permutation inconsistencies) to simulator failure:
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
