/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HonestConsistency

/-!
# #316 — Duplex-Sponge Fiat-Shamir: discharge of the M2a honest bad-event residual

This module previously carried a verbatim copy of the declarations now living in
`ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HonestConsistency` (both files
declared the same `DuplexSpongeFS.Sponge316` namespace members, which made any module
transitively importing both fail to elaborate with an "environment already contains …"
error).  The content is identical, so this file is now a thin re-export of the canonical
`HonestConsistency` module: every declaration it used to provide (`lemma5_12_honest`,
`hasInvEntry_implies_E`, the capacity/anchor predicates, …) remains accessible in the same
namespace through this import.
-/
