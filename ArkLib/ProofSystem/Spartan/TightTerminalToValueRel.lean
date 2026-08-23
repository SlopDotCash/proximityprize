/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ToMathlib.SpartanBricks

/-!
# The tight terminal lands in the semantic value relation (#352)

The D1 obstruction recorded at `composedCompletenessWithClaimValueRelStatement` was that the
broad composed chain's `relOut` is `univ`, so the semantic value relation cannot be reached
by monotonicity.  The TIGHT chain does not have that defect: its terminal currency
`tightFinalRelOut` carries the second-terminal identity `e₂ = eval r_y (secondSCVP …)`,
and the in-tree endpoint bridge
(`secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue`) converts that identity
into exactly the membership demanded by `finalCheckWithClaimValueRelIn`.  This file lands
the transport:

* `tightTerminalToFinalClaim` — the statement/oracle reshaping from the tight terminal
  type to the `FinalClaimStatement`/`FinalOracleStatement` pair (the carried target, the
  challenge, the target-dropped statement; oracles unchanged — `AfterLinearCombination`
  IS `AfterSecondSumcheck` reducibly);
* **`valueRel_of_tightFinalRelOut`** — membership transport: a tight-terminal pair in
  `tightFinalRelOut` reshapes into `finalCheckWithClaimValueRelIn`.

Consequence for #352: `composedCompletenessWithClaimValueRelStatement` for the concrete
`Rc := composedPIOPTightPure_Rc ▷ (0-round reshaping lens)` reduces to the tight chain's
completeness at `tightFinalRelOut` (the landed `…_of_leaves` apex + the leaf suite) plus
the standard 0-round lens-completeness plumbing — the semantic-vs-`univ` gap itself is
CLOSED by this transport.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace Spartan.Spec.Bricks

open MvPolynomial

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-- **The terminal reshaping**: tight terminal pair ⟶ `FinalClaimStatement` pair.  The
carried target is the first component; the final statement is the challenge with the
target-dropped mid statement; the oracles are unchanged. -/
@[reducible]
def tightTerminalToFinalClaim
    (x : Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i) :=
  ((x.1.1.1, (x.1.1.2, dropFirstTarget pp x.1.2)), x.2)

/-- **Membership transport (#352, the semantic gap closed)**: the tight terminal relation
lands in the semantic value relation through the reshaping — the second-terminal identity
becomes `target = finalExpectedClaimValue` by the endpoint bridge. -/
theorem valueRel_of_tightFinalRelOut
    (x : (Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)
    (hx : x ∈ tightFinalRelOut (R := R) pp) :
    ((tightTerminalToFinalClaim pp x.1, ()) :
        (FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit)
      ∈ finalCheckWithClaimValueRelIn R pp := by
  obtain ⟨hval, -⟩ := hx
  show x.1.1.1.1 = finalExpectedClaimValue R pp (x.1.1.1.2, dropFirstTarget pp x.1.1.2)
    x.1.2
  rw [hval]
  exact secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue R pp
    (x.1.1.1.2, dropFirstTarget pp x.1.1.2) x.1.2

end

end Spartan.Spec.Bricks

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Spartan.Spec.Bricks.valueRel_of_tightFinalRelOut
