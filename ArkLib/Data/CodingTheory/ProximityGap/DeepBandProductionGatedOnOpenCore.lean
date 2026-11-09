/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSubJohnsonSharpRate

/-!
# Conditional production deep-band bad-set count (#389)

The boundary-pinning files (`DeepBandProductionSubJohnson`,
`…General`, `…SharpRate`) proved the in-tree above-Johnson discharge provably
inapplicable across the production regime — but those vacuity statements were
standalone arithmetic, consumed nowhere.  This file makes them **load-bearing**:
it wires them into #389's actual conclusion, the deep-band bad-scalar count.

The consumer chain is in-tree and axiom-clean:
`SubJohnsonListBound → ExplainableCoreSupply` (`explainableCoreSupply_of_listBound`)
→ the bad-set count (`deep_band_badSet_card_of_supply`).  The capstone composes
them at `m = 0` and conjoins the sharp-rate vacuity, yielding the precise statement:

> In the first production band (rate `≤ k/(k+4)`), the open core
> `SubJohnsonListBound` **alone** produces the bad-set count
> `C(n,k+1) ≤ #badSet · |F|⁰ · (L·C(A,k+1))`, **and** the in-tree above-Johnson
> route that would otherwise supply this bound is provably unavailable
> (`¬ n(k−1) < (k+1)²`).

`subJohnsonListBound_supply_budget` shows that every input to this consumer
satisfies `C(n,k+1) ≤ L·C(A,k+1)`. The displayed inequality at `m = 0` can
therefore force at most one bad scalar. A smaller supply budget requires a
restriction on received words or a bound directly on coherent fibers.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- In the first deep band (`m = 0`) at rate `≤ k/(k+4)` (`5 ≤ k`, `k + 4 ≤ n`),
`SubJohnsonListBound dom k 0 L A` gives the bad-scalar count. The in-tree
above-Johnson discharge is inapplicable in this band. -/
theorem production_badSet_gated_on_open_core (dom : Fin n ↪ F) {k : ℕ}
    (hk5 : 5 ≤ k) (hn : k + 4 ≤ n) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + 0 + 1 : ℕ) : ℝ≥0))
    {L A : ℕ} (hLB : SubJohnsonListBound dom k 0 L A) :
    (∃ Q₀ : F[X],
        n.choose (k + 0 + 1)
          ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
              (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
            * (Fintype.card F) ^ 0 * (L * A.choose (k + 0 + 1)))
      ∧ ¬ n * (k - 1) < (k + 0 + 1) ^ 2 := by
  have hk : 1 ≤ k := by omega
  refine ⟨?_, firstBand_aboveJohnson_vacuous_sharp hk5 hn⟩
  exact deep_band_badSet_card_of_supply dom hk hhi (explainableCoreSupply_of_listBound dom hLB)

end ProximityGap.Ownership
