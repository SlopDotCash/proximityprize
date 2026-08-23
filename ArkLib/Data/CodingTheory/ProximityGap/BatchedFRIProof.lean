/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.ProtocolCountingBricks

/-!
# Batched FRI Joint Proximity (Issue #14)

The batched-FRI joint-proximity residual — the bound on the probability that a random linear
combination of functions is `δ`-close to a Reed–Solomon code while the individual functions are
not jointly close — is tracked **honestly** as the named proposition
`ProximityGap.Issue14.BatchedFRIJointProximityKernel` (an open `def : Prop` in `Issue14Kernels`).

Its proof is the beyond-list-decoding-radius mass bound and is **not** in tree. This module
intentionally contains **no** `theorem` discharging it: an earlier `breakthrough`/`Resolution`
theorem whose proof was an unfilled hole was removed, because it laundered the open residual into
an unproved-axiom dependency while claiming a breakthrough. Downstream developments should consume
`BatchedFRIJointProximityKernel` as an explicit hypothesis until the underlying list-decoding bound
is actually proved.

This module does expose the proved query-round counting complement used by the Batched FRI
frontier: the number of length-`t` query tuples that leave the good set in at least one coordinate
is `|ι|^t - |G|^t`.
-/

namespace ProximityGap
namespace Issue14

/-- Query-round counting complement: the number of query tuples that leave the good set in at
least one coordinate is the total number of query tuples minus the all-good tuples. -/
theorem query_tuple_someQueryOut_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (t : ℕ) :
    (Finset.univ.filter (fun q : Fin t → ι => ¬ ∀ j, q j ∈ G)).card
      = Fintype.card ι ^ t - G.card ^ t := by
  exact card_someQueryOut_eq G t

end Issue14
end ProximityGap
