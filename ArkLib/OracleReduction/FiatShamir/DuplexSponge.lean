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

This module imports every leaf under `ArkLib/OracleReduction/FiatShamir/DuplexSponge/` so that
`lake build ArkLib.OracleReduction.FiatShamir.DuplexSponge` compiles the full subtree.

Downstream code should usually import specific leaf modules (or `ArkLib`) rather than relying on
this file for names, since `import` does not re-export child modules.
-/
