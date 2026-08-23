/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSLambdaSubJohnson
import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# The sub-Johnson `Λ` bound for INTERLEAVED Reed–Solomon codes (#389)

The MCA application runs on interleaved codes (word stacks of arity `m`).  The existing
interleaved-`Λ` bounds for RS are Johnson-gated; below the Johnson radius they are vacuous.
Composing the sub-Johnson base bound `rsCode_Lambda_subJohnson_le` with the elementary product
bound `Lambda_interleaved_le_pow` (ABF26 Lemma 2.10) gives the interleaved sub-Johnson bound,
valid at **every** radius:

> **`rsCode_interleaved_Lambda_subJohnson_le`** — for `k ≤ a` and `a ≤ (1−δ)·n`,
> ```
> Λ(RS[dom,k]^{⋈ m}, δ) ≤ (C(n,k) / C(a,k))^m.
> ```

This is the interleaved list-size input to the MCA error bound, available below Johnson for
explicit RS — the actual code shape used by the proximity gap.
-/

open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ListDecodable Code InterleavedCode.ListSize

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The sub-Johnson `Λ` bound for interleaved RS.** Valid at every radius (below Johnson too),
from the base sub-Johnson bound and the elementary product bound for interleaving. -/
theorem rsCode_interleaved_Lambda_subJohnson_le (dom : Fin n ↪ F) {k a m : ℕ} {δ : ℝ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hn : 0 < Fintype.card (Fin n))
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ)) :
    Lambda (Code.interleavedCodeSet (κ := Fin m)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ
      ≤ (n.choose k / a.choose k : ℕ∞) ^ m :=
  le_trans (InterleavedCode.ListSize.Lambda_interleaved_le_pow _ δ)
    (pow_le_pow_left' (rsCode_Lambda_subJohnson_le dom hk hka hn ha) m)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_interleaved_Lambda_subJohnson_le
