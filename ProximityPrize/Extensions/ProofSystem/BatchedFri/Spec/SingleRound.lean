/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Extensions.OracleReduction.Basic
import ArkLib.ProofSystem.Fri.RoundConsistency
import ProximityPrize.Extensions.ProofSystem.Fri.Spec.SingleRound
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Linear
import CompPoly.Univariate.ToPoly.Impl

/-!
# The Batched FRI protocol

  We describe the Batched FRI oracle reduction as a random linear combination round,
  and the FRI oracle reduction.

 -/

namespace BatchedFri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Fri NNReal Domain

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree", for `s = 1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `m` the number of polynomials batched
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (m : ℕ)
variable {ω : SmoothCosetFftDomain n F}


namespace BatchingRound

-- DEFINITION COMPLETED (2026-06-04): batching-round input relation. The batched-FRI input is a
-- collection of `m + 1` purported codewords on the full domain `ω`, each committed to its own
-- low-degree witness polynomial (degree `< 2 ^ (∑ s) * d`). Following [BCIKS20 §8]/[FRI1216], the
-- well-formed-input relation asserts every batched oracle is the honest evaluation of its witness
-- polynomial on `ω`. (No `δ`: the relation is stated on the witnessed polynomials directly; the
-- subsequent proximity claim is carried by the FRI round-0 relation after batching — see
-- `outputRelation`, which composes with `Fri.Spec.FoldPhase.inputRelation`.)
-- The generic upstream `batchSpec S` supplies the message/challenge interfaces and the
-- inherited finiteness/nonemptiness instances. Its challenge type is the supplied `S`.

end BatchingRound

end Spec

end BatchedFri
