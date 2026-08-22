/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import Mathlib.Algebra.Field.ZMod

/-!
# The black-box form of ABF26 Theorem 4.21 is *false* (statement-level refutation)

`ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean` formerly carried the legacy target proposition
`lineDecodable_imp_epsMCA_le_target` (now replaced by a theorem using `MCAForallDoubleCover`), whose docstring (the "WALL" note) explained that the
*counting reduction* of GG25 / ABF26 Theorem 4.21 cannot close the goal for a black-box
proximity parameter `a` and an unconstrained radius `δ`, and that the faithful route needs a
Guruswami–Sudan statement repair.

This file proves the stronger fact that the conclusion of the legacy `lineDecodable_imp_epsMCA_le_target` proposition did
**not** follow from its hypothesis at all: there is a concrete instance where the code is
`(δ, a, n+1)`-line-decodable yet `ε_mca(C, δ) > a / |F|`. Hence the target theorem is **not a
theorem as stated** — it requires a hypothesis repair (a proximity bound on `δ`, e.g.
`δ < (n-1)/n`, together with a nondegeneracy bound such as `1 ≤ a` or `2 ≤ n`), not merely a
cleverer leaf proof. The existing `sorry` therefore cannot be honestly discharged.

## The witness

Take `ι = Fin 1` (so `n = |ι| = 1`), `F = A = ZMod 2`, the **zero code** `C = ⊥` (whose
underlying set is `{0}`), `δ = 0`, and `a = 0`.

* **Line-decodability holds vacuously-strongly.** Any `U : F → ι → A` valued in `C = {0}`
  satisfies `U γ = 0` for all `γ`, so for the affine pair `(u₁, u₂) = (0, 0) ∈ C²` we have
  `U γ = 0 = u₁ + γ • u₂` for every `γ`; thus `Pr_γ[U γ = u₁ + γ • u₂] = 1 ≥ (n+1)/|F| = 2/2`.
  The conclusion of `LineDecodable` is *always* satisfiable here, independently of the
  hypothesis, so `LineDecodable C δ a (n+1)` holds.

* **`ε_mca` is strictly positive.** The stack `u 0 = 0`, `u 1 = 1` (the all-ones word of
  `Fin 1 → ZMod 2`) fires `mcaEvent` at `γ = 0`: the witness set `S = {0}` has
  `|S| = 1 ≥ (1-δ)·n = 1`, the zero codeword `w = 0` equals the line `u 0 + 0 • u 1 = 0` on
  `S`, and **no** codeword pair from `C = {0}` agrees with `(u 0, u 1) = (0, 1)` on `S`
  (any pair is `(0,0)` and `0 ≠ 1` at position `0`), so `¬ pairJointAgreesOn`. Hence
  `Pr_γ[mcaEvent] ≥ Pr[γ = 0] = 1/|F| > 0 = a / |F|`, and `ε_mca(C, δ) ≥ 1/|F| > a/|F|`.

The single shared "miss" of the WALL counterexample is realised here geometrically: at the
only nonzero coordinate the affine `g₀(γ) = (u₁-f₁)₀ + γ·(u₂-f₂)₀ = -(1)·γ` is identically
constrained by no second equation, so the line-decoder's `n+1`-budget — which only sees the
trivially-aligned zero pair — never pins the bad coordinate. This is exactly the off-by-one /
no-proximity-bound obstruction described in `LineDecoding.lean`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.LineDecodingRefutation

open scoped NNReal ProbabilityTheory ENNReal
open CodingTheory ProximityGap Code

/-- `2` is prime, so `ZMod 2` is a field. -/
instance primeFact_LineDecodingRefutation_1 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The concrete refuting data: `ι = Fin 1`, `F = A = ZMod 2`, `C = ⊥`, `δ = a = 0`. -/
abbrev ι : Type := Fin 1
abbrev F : Type := ZMod 2
abbrev A : Type := ZMod 2

/-- The zero code `C = ⊥`; its underlying set is `{0}`. -/
abbrev Czero : ModuleCode ι F A := (⊥ : Submodule F (ι → A))

/-- A word valued in the zero code is the zero word. -/
theorem mem_Czero_iff (x : ι → A) : x ∈ (Czero : Set (ι → A)) ↔ x = 0 := by
  simp [Czero]

/-- **Line-decodability holds for the zero code at every `(δ, a)`.**
The conclusion is satisfiable by the zero affine pair `(0,0)`, independently of the hypothesis,
because `Pr_γ[U γ = 0 + γ • 0] = Pr_γ[True] = 1 ≥ (n+1)/|F|` once `U` is valued in `C = {0}`. -/
theorem lineDecodable_Czero (δ a : ℝ≥0) :
    LineDecodable (F := F) ((Czero : Set (ι → A))) δ a ((Fintype.card ι : ℝ≥0) + 1) := by
  classical
  intro f₁ f₂ U hU _hyp
  refine ⟨0, Czero.zero_mem, 0, Czero.zero_mem, ?_⟩
  -- `U γ = 0` for all `γ` (valued in `{0}`), and `0 + γ • 0 = 0`, so the event is `True`.
  have hUzero : ∀ γ : F, (U γ = (0 : ι → A) + γ • (0 : ι → A)) = True := by
    intro γ
    have : U γ = 0 := (mem_Czero_iff (U γ)).mp (hU γ)
    simp [this]
  -- The probability of the always-true event is `1`, and `(n+1)/|F| ≤ 1`.
  have hPr_one : Pr_{let γ ← $ᵖ F}[U γ = (0 : ι → A) + γ • (0 : ι → A)] = 1 := by
    rw [ProbabilityTheory.Pr_eq_tsum_indicator]
    have : (fun γ : F => ($ᵖ F) γ *
        (if (U γ = (0 : ι → A) + γ • (0 : ι → A)) then (1 : ENNReal) else 0))
        = fun γ : F => ($ᵖ F) γ := by
      funext γ
      have hT : (U γ = (0 : ι → A) + γ • (0 : ι → A)) := by
        have := hUzero γ; simpa using this.symm ▸ trivial
      rw [if_pos hT, mul_one]
    rw [this, PMF.tsum_coe]
  rw [hPr_one]
  -- `(card ι + 1)/|F| = 2/2 = 1`.
  have hcardF : ((Fintype.card F : ℕ) : ENNReal) = (2 : ENNReal) := by
    rw [show (Fintype.card F : ℕ) = 2 from by decide]; rfl
  rw [hcardF]
  -- goal: `(↑(↑(card ι) + 1) : ENNReal) / 2 ≤ 1`
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  -- `↑((card ι : ℝ≥0) + 1) ≤ 2`
  have : (((Fintype.card ι : ℝ≥0) + 1 : ℝ≥0) : ENNReal) = (2 : ENNReal) := by
    rw [show (Fintype.card ι : ℕ) = 1 from by decide]
    push_cast
    norm_num
  rw [this]

/-- The refuting stack: `u 0 = 0`, `u 1 = 1` (the all-ones word of `Fin 1 → ZMod 2`). -/
noncomputable def ubad : WordStack A (Fin 2) ι := fun k _ => if k = 0 then 0 else 1

@[simp] theorem ubad_zero : ubad 0 = (0 : ι → A) := by
  funext i; simp [ubad]

@[simp] theorem ubad_one : ubad 1 = (fun _ => (1 : A)) := by
  funext i; simp [ubad]

/-- **`mcaEvent` fires at `γ = 0` for the stack `ubad`** (with `δ = 0`).
Witness set `S = {0}` (all of `ι = Fin 1`): `|S| = 1 ≥ (1-0)·1`; the zero codeword equals the
line `ubad 0 + 0 • ubad 1 = 0` on `S`; and no codeword pair of `C = {0}` agrees with
`(ubad 0, ubad 1) = (0, 1)` on `S`, since any pair is `(0,0)` and `0 ≠ 1`. -/
theorem mcaEvent_ubad_zero :
    mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (ubad 0) (ubad 1) (0 : F) := by
  classical
  refine ⟨{0}, ?_, ⟨0, Czero.zero_mem, ?_⟩, ?_⟩
  · -- `|S| = 1 ≥ (1 - 0) * card ι = 1`
    rw [show (Fintype.card ι : ℕ) = 1 from by decide]
    simp
  · -- the zero codeword equals the line on `S = {0}`: `0 = ubad 0 + 0 • ubad 1 = 0`
    intro i _
    simp
  · -- no joint pair on `S`
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    -- `v₁ ∈ {0}` so `v₁ = 0`, but agreement forces `v₁ 0 = ubad 1 0 = 1`, contradiction.
    have hv₁0 : v₁ = 0 := (mem_Czero_iff v₁).mp hv₁
    have hcontra := (hagree 0 (by simp)).2
    rw [hv₁0] at hcontra
    -- `hcontra : (0 : ι → A) 0 = ubad 1 0`, i.e. `0 = 1` in `ZMod 2`
    rw [ubad_one] at hcontra
    simp only [Pi.zero_apply] at hcontra
    exact absurd hcontra (by decide)

/-- **`ε_mca(C, δ) ≥ 1/|F| > 0`** for the zero code at `δ = 0`: the `ubad` stack puts mass
`≥ Pr[γ = 0] = 1/|F|` on `mcaEvent`, and `ε_mca` is the supremum over stacks. -/
theorem epsMCA_Czero_pos :
    (0 : ENNReal) < epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) := by
  classical
  -- lower-bound the inner probability for `ubad` by the single point `γ = 0`.
  have hpoint :
      (1 : ENNReal) / (Fintype.card F : ENNReal) ≤
        Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
          (ubad 0) (ubad 1) γ] := by
    rw [ProbabilityTheory.Pr_eq_tsum_indicator]
    -- the `γ = 0` term contributes `($ᵖ F) 0 * 1 = 1/|F|`.
    refine le_trans ?_ (ENNReal.le_tsum (0 : F))
    rw [if_pos mcaEvent_ubad_zero, mul_one, PMF.uniformOfFintype_apply, one_div]
  -- `1/|F| > 0` and the body is `≤ ε_mca`.
  have hbody_le : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
        (ubad 0) (ubad 1) γ] ≤ epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) := by
    unfold epsMCA
    exact le_iSup (fun u : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) γ]) ubad
  have hpos : (0 : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal) := by
    rw [show (Fintype.card F : ℕ) = 2 from by decide]
    norm_num
  exact lt_of_lt_of_le hpos (le_trans hpoint hbody_le)

/-- **The black-box ABF26 Theorem 4.21 (`lineDecodable_imp_epsMCA_le`) is false as stated.**

There is a concrete instance — the zero code `C = ⊥` over `F = ZMod 2`, `ι = Fin 1`,
`δ = a = 0` — that is `(δ, a, |ι|+1)`-line-decodable yet has `ε_mca(C, δ) > a / |F|`. So the
conclusion of the legacy `lineDecodable_imp_epsMCA_le_target` proposition did **not** follow from its hypothesis: the
theorem required a hypothesis repair exposing the Guruswami--Sudan interpolation/list-size
structure, not a leaf proof of the present form. -/
theorem lineDecodable_imp_epsMCA_le_false :
    LineDecodable (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (0 : ℝ≥0)
        ((Fintype.card ι : ℝ≥0) + 1) ∧
      ¬ (epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
          ≤ (0 : ℝ≥0) / (Fintype.card F : ENNReal)) := by
  refine ⟨lineDecodable_Czero 0 0, ?_⟩
  -- RHS `0 / |F| = 0`, and `ε_mca > 0`.
  have hrhs : ((0 : ℝ≥0) : ENNReal) / (Fintype.card F : ENNReal) = 0 := by simp
  rw [hrhs]
  exact not_le.mpr epsMCA_Czero_pos

end CodingTheory.LineDecodingRefutation
