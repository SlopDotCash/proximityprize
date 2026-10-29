/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.VectorIOR

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound

/-!
# Vector Interactive Oracle Reductions

We define vector interactive oracle reductions (V-IOR) and vector interactive oracle proofs
(V-IOPs), as special cases IORs/IOPs where all messages and oracle statements are vectors over some
alphabet. We also define their proximity versions, V-IORP and V-IOPP, which exhibit a gap between
the relation for completeness and the relation for soundness.

This is the original formulation of IOPs in [BCS16]. Many IOPs of interest in the literature are of
this form, and so we isolate this special case for ease of notation and reasoning.

We also define complexity measures for V-IORs, such as proof length and verifier's query complexity.

-/

namespace ProtocolSpec

namespace VectorSpec

variable {n : ℕ}

variable {A : Type} {vPSpec : VectorSpec n}

end VectorSpec

end ProtocolSpec

variable {n : ℕ} {ι : Type}

variable {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n} {A : Type}
  [SampleableType A]

open scoped NNReal

namespace VectorIOR

variable {StmtIn WitIn StmtOut WitOut : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [∀ i, OracleInterface (OStmtIn i)] {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

-- `VectorIOR.IsSecure` (completeness + rbr knowledge soundness bundle) was deleted in the
-- 2026-06-10 proof-debt audit: zero instances and zero consumers anywhere in the tree.
-- Reintroduce it from `VectorIOP.IsSecureWithGap`'s shape if a genuine consumer appears.

end VectorIOR

namespace VectorIOP

variable {Statement Witness : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)]

-- `VectorIOP.IsSecure` (gap-free completeness + rbr knowledge soundness bundle) was deleted in
-- the 2026-06-10 proof-debt audit: zero instances and zero consumers anywhere in the tree.
-- The live interface is `IsSecureWithGap` below (specialize `completeRelation = soundRelation`
-- to recover the gap-free notion).

end VectorIOP
