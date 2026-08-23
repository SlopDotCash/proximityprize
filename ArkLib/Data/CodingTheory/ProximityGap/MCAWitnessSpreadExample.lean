/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# A concrete maximal-MCA witness: the multi-`γ` engine fires non-vacuously (#232)

`MCAWitnessSpread.lean` proves two facts: the multi-scalar lower-bound engine
`epsMCA_ge_card_div_of_mcaEvent_set` (`|G|` bad scalars ⟹ `ε_mca ≥ |G|/|F|`), and the
structural obstruction `unique_bad_gamma_common_witness` (a *fixed* witness set admits at most
one bad scalar, so the bad scalars must use *distinct* witness sets — the list-decoding spread).

This file demonstrates that the obstruction is **realizable** and the engine is **non-vacuous**:
we exhibit an explicit linear code over which `mcaEvent` fires for *every* scalar in `F`, each
with a *distinct* witness set, hence `ε_mca = 1` (maximal).

* **Code.** `C = constCode`, the constant-functions (repetition / rate-`1/n` RS) code over
  `F = ZMod 3`, `ι = Fin 3`.
* **Line.** stack `u₀ = ![0,0,1]`, `u₁ = ![0,1,2]`, radius `δ = 1/3` (so witness sets have
  size `≥ 2`).
* **Spread.** `γ = 0` fires on `S = {0,1}`; `γ = 1` on `{0,2}`; `γ = 2` on `{1,2}` — three
  *distinct* witness sets, exactly as `unique_bad_gamma_common_witness` forces.

**Result** (`epsMCA_constCode_eq_one`): `ε_mca(C, 1/3) = 1`. This is a fully computable,
`sorry`-free, axiom-clean witness that the witness-spread lower-bound mechanism is real, and a
second structural-separation example beyond the zero code (a *nonzero* linear code with maximal
MCA error).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace ProximityGap.MCAWitnessSpread.Example

/-- The constant-functions (repetition) code over `ZMod 3` on three coordinates. It is the
rate-`1/3` Reed–Solomon code (degree-`0` polynomials). -/
def constCode : Set (Fin 3 → ZMod 3) := {v | ∀ i j, v i = v j}

/-- Every constant function is a codeword. -/
theorem const_mem_constCode (c : ZMod 3) : (fun _ => c) ∈ constCode := fun _ _ => rfl

/-- The two-row stack carrying the line `u₀ + γ·u₁`. -/
noncomputable def uStack : WordStack (ZMod 3) (Fin 2) (Fin 3) := ![![0, 0, 1], ![0, 1, 2]]

/-- The MCA size threshold at `δ = 1/3`, `n = 3`: a witness set of size `2` qualifies. -/
theorem size_ok {S : Finset (Fin 3)} (hcard : S.card = 2) :
    (S.card : ℝ≥0) ≥ (1 - (1 : ℝ≥0) / 3) * (Fintype.card (Fin 3) : ℝ≥0) := by
  rw [hcard, Fintype.card_fin, ge_iff_le]
  rw [show ((3 : ℕ) : ℝ≥0) = 3 from by norm_num, show ((2 : ℕ) : ℝ≥0) = 2 from by norm_num]
  refine le_of_eq ?_
  apply NNReal.coe_injective
  have h13 : (1 : ℝ≥0) / 3 ≤ 1 := by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 3)]; norm_num
  push_cast [NNReal.coe_sub h13]
  norm_num

/-- **Joint-disagreement from non-constancy.** If `u₁` takes two different values at coordinates
`i, j ∈ S`, then no constant codeword pair matches `(u₀, u₁)` on `S`: the second codeword would
be constant yet equal `u₁` at both `i` and `j`. -/
theorem not_pairJointAgreesOn_of_u1_noncost
    {S : Finset (Fin 3)} {u₀ u₁ : Fin 3 → ZMod 3} {i j : Fin 3}
    (hi : i ∈ S) (hj : j ∈ S) (hne : u₁ i ≠ u₁ j) :
    ¬ pairJointAgreesOn constCode S u₀ u₁ := by
  rintro ⟨v₀, _hv₀, v₁, hv₁, h⟩
  exact hne (by rw [← (h i hi).2, ← (h j hj).2]; exact hv₁ i j)

/-- A single `mcaEvent` from: a size-`2` witness set `S`, a constant value `c` that the line
`u₀ + γ·u₁` hits on all of `S`, and a non-constancy witness `u₁ i ≠ u₁ j` in `S`. -/
theorem mcaEvent_of_witness
    {γ : ZMod 3} {S : Finset (Fin 3)} {c : ZMod 3} {i j : Fin 3}
    (hcard : S.card = 2) (hi : i ∈ S) (hj : j ∈ S) (hne : (uStack 1) i ≠ (uStack 1) j)
    (hconst : ∀ s ∈ S, (uStack 0) s + γ • (uStack 1) s = c) :
    mcaEvent constCode (1/3 : ℝ≥0) (uStack 0) (uStack 1) γ := by
  refine ⟨S, size_ok hcard, ⟨(fun _ => c), const_mem_constCode c, ?_⟩,
    not_pairJointAgreesOn_of_u1_noncost hi hj hne⟩
  intro s hs; exact (hconst s hs).symm

/-- **Every scalar is bad, on a distinct witness set.** For each `γ ∈ ZMod 3`, `mcaEvent` fires
for the stack `uStack` at radius `1/3`: `γ = 0` on `{0,1}`, `γ = 1` on `{0,2}`, `γ = 2` on
`{1,2}`. -/
theorem mcaEvent_constCode_all (γ : ZMod 3) :
    mcaEvent constCode (1/3 : ℝ≥0) (uStack 0) (uStack 1) γ := by
  fin_cases γ
  · -- γ = 0, S = {0,1}, line = (0,0,1), constant value 0 on {0,1}
    exact mcaEvent_of_witness (S := {0, 1}) (c := 0) (i := 0) (j := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- γ = 1, S = {0,2}, line = (0,1,0), constant value 0 on {0,2}
    exact mcaEvent_of_witness (S := {0, 2}) (c := 0) (i := 0) (j := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- γ = 2, S = {1,2}, line = (0,2,2), constant value 2 on {1,2}
    exact mcaEvent_of_witness (S := {1, 2}) (c := 2) (i := 1) (j := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The maximal-MCA witness.** The constant code over `ZMod 3` has `ε_mca(C, 1/3) = 1`: the
multi-scalar engine fires for *all* of `F` (with three distinct witness sets), giving
`ε_mca ≥ |F|/|F| = 1`, and `ε_mca ≤ 1` always.

This is a fully computable, non-vacuous instantiation of `epsMCA_ge_card_div_of_mcaEvent_set`,
confirming that the witness-spread lower-bound mechanism is real and that the
`unique_bad_gamma_common_witness` obstruction (distinct witness sets per scalar) is realizable. -/
theorem epsMCA_constCode_eq_one :
    epsMCA (F := ZMod 3) (A := ZMod 3) constCode (1/3 : ℝ≥0) = 1 := by
  refine le_antisymm (epsMCA_le_one constCode (1/3 : ℝ≥0)) ?_
  have hge := epsMCA_ge_card_div_of_mcaEvent_set (F := ZMod 3) (A := ZMod 3)
    constCode (1/3 : ℝ≥0) uStack (Finset.univ) (fun γ _ => mcaEvent_constCode_all γ)
  have key : ((Finset.univ : Finset (ZMod 3)).card : ℝ≥0∞)
      / (Fintype.card (ZMod 3) : ℝ≥0∞) = 1 := by
    rw [Finset.card_univ]
    exact ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  rw [key] at hge
  exact hge

#print axioms epsMCA_constCode_eq_one

end ProximityGap.MCAWitnessSpread.Example
