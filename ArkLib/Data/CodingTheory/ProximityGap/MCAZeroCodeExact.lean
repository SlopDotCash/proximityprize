/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The exact MCA error of the zero code, over an arbitrary field

`MCALowerBound.lean` proves `epsMCA(zero code over ZMod 2, 0) = 1/2` (`epsMCA_C0_eq_half`),
with the upper bound resting on `badScalar_card_le_one`, which is specific to `ZMod 2` on one
coordinate (`Fin 1`, via `Subsingleton`). This file generalizes the exact value to **every**
finite field `F` and **every** nonempty index type `ι`:

  `ε_mca(⊥, 0) = 1 / |F|`.

The two ingredients, both proved here for general `(ι, F)`:

* **Lower bound** (`epsMCA_bot_ge_inv_card`): the stack `(0, 𝟙)` fires `mcaEvent` at `γ = 0`
  (witness set `S = univ`, the zero codeword on the line, and no joint pair because the second
  row is the all-ones word `𝟙 ≠ 0`); via `epsMCA_ge_inv_card_of_mcaEvent` this gives `≥ 1/|F|`.
* **Upper bound** (`badScalar_card_le_one_bot`): at radius `0` the witness set is forced to be
  all of `ι` (`|S| ≥ |ι|`), so `mcaEvent` at `γ` forces `u₀ + γ·u₁ = 0` with `u₁ ≠ 0` (else the
  zero pair `(0,0)` would witness `pairJointAgreesOn`, contradicting `mcaEvent`); picking a
  coordinate `i₀` with `u₁ i₀ ≠ 0`, two firing scalars `γ, γ'` satisfy
  `γ · u₁ i₀ = -u₀ i₀ = γ' · u₁ i₀`, so `γ = γ'` by field cancellation. Hence each stack has at
  most one bad scalar, and `Pr_γ[mcaEvent] ≤ 1/|F|`.

Combined: `ε_mca(⊥, 0) = 1/|F|`, recovering `epsMCA_C0_eq_half` at `F = ZMod 2`.

## References
- Generalizes `ProximityGap.MCALowerExample.epsMCA_C0_eq_half`.
- Issue #140 / #171 (MCA lower-bound theory).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The zero code over `F` with alphabet `F`; its underlying set is `{0}`. -/
abbrev Cbot : Set (ι → F) := ((⊥ : Submodule F (ι → F)) : Set (ι → F))

theorem mem_Cbot_iff (x : ι → F) : x ∈ (Cbot : Set (ι → F)) ↔ x = 0 := by simp [Cbot]

theorem zero_mem_Cbot : (0 : ι → F) ∈ (Cbot : Set (ι → F)) := by simp [Cbot]

/-- The refuting/witness stack: `u 0 = 0`, `u 1 = 𝟙` (the all-ones word `ι → F`). -/
noncomputable def ubad : WordStack F (Fin 2) ι := fun k _ => if k = 0 then 0 else 1

@[simp] theorem ubad_zero : ubad (ι := ι) (F := F) 0 = (0 : ι → F) := by funext i; simp [ubad]

@[simp] theorem ubad_one : ubad (ι := ι) (F := F) 1 = (fun _ => (1 : F)) := by
  funext i; simp [ubad]

/-- **`mcaEvent` fires at `γ = 0`** for the stack `ubad`, at radius `0`. -/
theorem mcaEvent_ubad :
    mcaEvent (F := F) (Cbot : Set (ι → F)) 0 (ubad 0) (ubad 1) (0 : F) := by
  classical
  refine ⟨Finset.univ, ?_, ⟨0, zero_mem_Cbot, ?_⟩, ?_⟩
  · rw [Finset.card_univ]; simp
  · intro i _; simp
  · rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hcontra := (hagree i₀ (Finset.mem_univ i₀)).2
    rw [(mem_Cbot_iff v₁).mp hv₁, ubad_one] at hcontra
    simp only [Pi.zero_apply] at hcontra
    exact absurd hcontra zero_ne_one

/-- **Lower bound:** `1/|F| ≤ ε_mca(⊥, 0)`, via the firing stack `ubad`. -/
theorem epsMCA_bot_ge_inv_card :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) 0 :=
  epsMCA_ge_inv_card_of_mcaEvent (F := F) (A := F) (Cbot : Set (ι → F)) 0 ubad 0 mcaEvent_ubad

open Classical in
/-- **Upper bound, key combinatorics:** at radius `0`, each stack has at most one bad scalar for
the zero code, over an arbitrary field and index type. -/
theorem badScalar_card_le_one_bot (u : WordStack F (Fin 2) ι) :
    (Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) 0 (u 0) (u 1) γ)
      Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, ⟨w, hwmem, hweq⟩, hno⟩ := hγ.2
  obtain ⟨S', hS', ⟨w', hwmem', hweq'⟩, _⟩ := hγ'.2
  -- At radius 0 the witness set is forced to be all of `ι`.
  have hforce : ∀ (T : Finset ι), ((1 : ℝ≥0) - 0) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) →
      T = Finset.univ := by
    intro T hT
    apply Finset.eq_univ_of_card
    have hge : (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) := by simpa using hT
    have h1 : Fintype.card ι ≤ T.card := by exact_mod_cast hge
    exact le_antisymm (Finset.card_le_univ T) h1
  have hSuniv : S = Finset.univ := hforce S hS
  have hS'univ : S' = Finset.univ := hforce S' hS'
  have hiS : ∀ i, i ∈ S := fun i => by rw [hSuniv]; exact Finset.mem_univ i
  have hiS' : ∀ i, i ∈ S' := fun i => by rw [hS'univ]; exact Finset.mem_univ i
  have hw0 : w = 0 := (mem_Cbot_iff w).mp hwmem
  have hw0' : w' = 0 := (mem_Cbot_iff w').mp hwmem'
  -- The second row is nonzero, else the zero pair would witness `pairJointAgreesOn`.
  have hu1ne : u 1 ≠ 0 := by
    intro hu1z
    apply hno
    refine ⟨0, zero_mem_Cbot, 0, zero_mem_Cbot, fun i _ => ?_⟩
    have hwi : w i = (u 0) i + γ • (u 1) i := hweq i (hiS i)
    rw [hw0, hu1z] at hwi
    simp only [Pi.zero_apply, smul_zero, add_zero] at hwi
    refine ⟨?_, ?_⟩
    · simp only [Pi.zero_apply]; exact hwi
    · simp [hu1z]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu1ne
  rw [Pi.zero_apply] at hi₀
  -- Two firing scalars pin the same `γ` at coordinate `i₀`.
  have e1 : (0 : F) = (u 0) i₀ + γ • (u 1) i₀ := by
    have := hweq i₀ (hiS i₀)
    rw [hw0] at this; simpa using this
  have e2 : (0 : F) = (u 0) i₀ + γ' • (u 1) i₀ := by
    have := hweq' i₀ (hiS' i₀)
    rw [hw0'] at this; simpa using this
  have hmul : γ • (u 1) i₀ = γ' • (u 1) i₀ := by
    have : (u 0) i₀ + γ • (u 1) i₀ = (u 0) i₀ + γ' • (u 1) i₀ := by rw [← e1, ← e2]
    exact add_left_cancel this
  rw [smul_eq_mul, smul_eq_mul] at hmul
  exact mul_right_cancel₀ hi₀ hmul

open Classical in
/-- **Exact value: `ε_mca(zero code over `F`, 0) = 1/|F|`,** for every finite field `F` and every
nonempty index type `ι`. Generalizes `MCALowerExample.epsMCA_C0_eq_half` (the `ZMod 2` case). -/
theorem epsMCA_bot_eq_inv_card :
    epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) 0 = 1 / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm ?_ epsMCA_bot_ge_inv_card
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_one_bot u

end General

/-! ## Source audit -/

#print axioms epsMCA_bot_ge_inv_card
#print axioms badScalar_card_le_one_bot
#print axioms epsMCA_bot_eq_inv_card

end ProximityGap.MCAZeroCode
