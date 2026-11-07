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
interleaved-`Λ` bounds for RS are Johnson-gated: with `δ` an error (distance) radius they apply
only for `δ` below the Johnson radius (`≈ 1 − √ρ`), and give nothing for `δ` at or beyond it
(the hard regime). Here "sub-Johnson" refers to the *agreement* `(1−δ)·n` lying below the
Johnson agreement threshold, i.e. to radii beyond the Johnson radius. Composing the sub-Johnson
base bound `rsCode_Lambda_subJohnson_le` with the elementary product bound
`Lambda_interleaved_le_pow` (ABF26 Lemma 2.10) gives the interleaved sub-Johnson bound, valid at
**every** radius `δ` satisfying its agreement hypothesis:

> **`rsCode_interleaved_Lambda_subJohnson_le`** — for `k ≤ a` and `a ≤ (1−δ)·n`,
> ```
> Λ(RS[dom,k]^{⋈ m}, δ) ≤ (C(n,k) / C(a,k))^m.
> ```

This is an interleaved list-size input to the MCA error bound, available beyond the Johnson
radius (agreement below the Johnson agreement threshold) for explicit RS — the actual code shape
used by the proximity gap. It is a combinatorial bound with the stated agreement hypothesis; its
size `(C(n,k)/C(a,k))^m` need not be polynomial in `n`, so it is not a uniform polynomial
list-size bound.
-/

open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ListDecodable Code InterleavedCode.ListSize

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The sub-Johnson `Λ` bound for interleaved RS.** Valid at every radius `δ` satisfying the
agreement hypothesis `k ≤ a ≤ (1−δ)·n` (including radii beyond the Johnson radius),
from the base sub-Johnson bound and the elementary product bound for interleaving. -/
theorem rsCode_interleaved_Lambda_subJohnson_le (dom : Fin n ↪ F) {k a m : ℕ} {δ : ℝ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hn : 0 < Fintype.card (Fin n))
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ)) :
    ListDecodable.Lambda (Code.interleavedCodeSet (κ := Fin m)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ
      ≤ (n.choose k / a.choose k : ℕ∞) ^ m :=
  le_trans (InterleavedCode.ListSize.Lambda_interleaved_le_pow _ δ)
    (pow_le_pow_left' (rsCode_Lambda_subJohnson_le dom hk hka hn ha) m)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_interleaved_Lambda_subJohnson_le
