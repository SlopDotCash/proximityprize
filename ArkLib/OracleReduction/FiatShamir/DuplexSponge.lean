/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.AbortAnalysis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBound
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBoundPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BudgetCover
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaAssembly
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaHybrids
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HonestConsistency
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HonestConsistencyPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ConsistencyPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ConsistencyPaperCascade
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ForkFalse
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ForkPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HashHalf
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HashPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TimePFalse
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.EagerFalse
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsCoincidence
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RunCollapse
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Soundness
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.State

/-!
# Duplex sponge Fiat–Shamir (umbrella)

This module imports a curated subset of the leaves under
`ArkLib/OracleReduction/FiatShamir/DuplexSponge/` (the core definitions and the main security
modules listed above, together with whatever those import transitively). It does **not** import
every leaf: many `Security/Lemma*`, lazy-carrier, salted and correspondence modules are not
imported directly (and need not be reachable transitively), so
`lake build ArkLib.OracleReduction.FiatShamir.DuplexSponge` is not guaranteed to compile the
full subtree; build `ArkLib` for that.

Names from the imported modules (and their transitive imports) are available to any file that
imports this umbrella, but this umbrella is not a maintained or stable public API: downstream
code should usually import the specific leaf modules it depends on (or `ArkLib`).
-/
