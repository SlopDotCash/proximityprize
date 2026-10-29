/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Fri.Spec.General

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.General
import ProximityPrize.Extensions.ProofSystem.Fri.Spec.SingleRound

/-!
# FRI Protocol Specification (General)

The general (multi-round) FRI protocol over a non-binary field, built by sequentially composing
single folding rounds. Defines the input and output proximity relations (`inputRelation`,
`outputRelation`), the folding protocol spec (`pSpecFold`), the per-round reduction
(`reductionFold`), and the full composed `reduction`.
-/

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal Domain

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ)
variable {ω : SmoothCosetFftDomain n F}

/- Input/Output relations for the FRI protocol. -/
end Spec

end Fri
