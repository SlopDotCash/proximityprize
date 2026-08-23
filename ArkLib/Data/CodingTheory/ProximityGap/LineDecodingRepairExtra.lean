/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingRepair
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Further repair progress for the refuted ABF26 Theorem 4.21 (issue #140)

`LineDecodingRepair.lean` records the first wave of honest, axiom-clean repair progress for the
*false* black-box form of `lineDecodable_imp_epsMCA_le_target`: counterexample-exclusion,
counterexample-exclusion, the exact value `ε_mca(Czero, 0) = 1/|F|` (specialised to `ZMod 2`),
and the coverage-discharge theorems.

This module extends that wave with genuinely new, axiom-clean lemmas. None of these require the
absent Guruswami–Sudan interpolation core.

## Main results

* **(C) Exact-value structure of the zero code over ANY finite field and ANY single-coordinate
  index.** The refutation file proves `ε_mca = 1/|F|` only for `ι = Fin 1, F = ZMod 2` via a
  two-element `decide`. Here `zeroCode` is the zero submodule over an *arbitrary* finite field `K`
  and an *arbitrary* `Subsingleton` index `ι` (the genuine "single coordinate" generalization),
  and:
  - `mcaEvent_zeroCode_iff` — exact characterization: the zero code's `mcaEvent` at radius `0`
    fires at `γ` iff `u₀ i₀ + γ • u₁ i₀ = 0` and the stack is nondegenerate at the unique
    coordinate (upgrades the in-tree one-directional `mcaEvent_Czero_pos0` to a biconditional);
  - `mcaEvent_zeroCode_unique` — the zero code's `mcaEvent` fires for **at most one** scalar
    over *any* field (generalizes the `ZMod 2`-only `not_mcaEvent_both` two-scalar impossibility,
    via the affine-root argument rather than a finite case split);
  - `mcaBadCount_zeroCode_le_one`, `mcaBadCount_zeroCode_lt_two` — the bad count is `≤ 1` for any
    field, so it lives in `{0, 1}`;
  - `epsMCA_zeroCode_le_inv_card` — the upper half `ε_mca(zeroCode, 0) ≤ 1/|K|` over any field.
  - `epsMCA_zeroCode_eq_inv_card` — when the ambient module is nontrivial, this upper bound is
    sharp: a nonzero constant second word gives one bad scalar, so `ε_mca(zeroCode, 0) = 1/|K|`.

* **(D) Refutation-region facts.** `not_mcaEvent_zeroCode_of_deg` (a stack that vanishes at the
  coordinate is never bad — the refutation needs a genuinely nonzero stack) and
  `mcaBadCount_zeroCode_eq_zero_of_deg` pin one edge of the region the counterexample cannot
  touch.

* **(E) Bridge to the in-tree `ZMod 2` refutation.** `mcaBadCount_Czero_le_one`,
  `epsMCA_Czero_le_inv_card_via_general` re-derive the refutation-file facts as instances of the
  general results, confirming the in-tree `epsMCA_Czero_eq_half` is the `|K| = 2` case of a
  field-generic identity.

The GS-interpolant core of the genuine T4.21 repair remains open (isolated as the
`MCAForallDoubleCover` hypothesis in `LineDecodingCoverage.lean`); these lemmas are tractable
repair-progress on the *refutation boundary* and the exact-value structure, not on that core.
-/

namespace CodingTheory.LineDecodingRepairExtra

open scoped NNReal ProbabilityTheory ENNReal
open CodingTheory ProximityGap Code

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## (C) The zero code over an arbitrary finite field and a single-coordinate index -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Subsingleton ι]
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]

/-- The zero code over `(ι → A)`: the `⊥` submodule, whose underlying set is `{0}`. -/
abbrev zeroCode : ModuleCode ι K A := (⊥ : Submodule K (ι → A))

/-- A word valued in the zero code is the zero word. -/
theorem mem_zeroCode_iff (x : ι → A) : x ∈ (zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A)) ↔
    x = 0 := by
  simp [zeroCode]

/-- The unique index of a `Subsingleton`-and-`Nonempty` `ι`. -/
private noncomputable def i₀ : ι := Classical.arbitrary ι

/-- `Fintype.card ι = 1` for a `Subsingleton`, `Nonempty` index. -/
theorem card_ι_eq_one : Fintype.card ι = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨i₀, fun y => Subsingleton.elim y i₀⟩

/-- **One direction of the zero-code `mcaEvent` characterization (necessity).** If the zero
code's `mcaEvent` fires at `γ` (radius `0`), the affine value at the unique coordinate vanishes
and the stack is nondegenerate there. General-field, general-`Subsingleton`-index version of the
in-tree `mcaEvent_Czero_pos0`. -/
theorem mcaEvent_zeroCode_pos0 {u₀ u₁ : ι → A} {γ : K}
    (h : mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ γ) :
    (u₀ i₀ + γ • u₁ i₀ = 0) ∧ (u₀ i₀ ≠ 0 ∨ u₁ i₀ ≠ 0) := by
  classical
  obtain ⟨S, hScard, ⟨w, hw, hwline⟩, hno⟩ := h
  have hw0 : w = 0 := (mem_zeroCode_iff w).mp hw
  rw [card_ι_eq_one (ι := ι)] at hScard
  have hcard1 : (1 : ℝ≥0) ≤ (S.card : ℝ≥0) := by simpa using hScard
  have hcardNat : 1 ≤ S.card := by exact_mod_cast hcard1
  have hmem : i₀ ∈ S := by
    rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨x, hx⟩
    have : x = i₀ := Subsingleton.elim x i₀
    rwa [this] at hx
  have hlin : u₀ i₀ + γ • u₁ i₀ = 0 := by
    have := hwline i₀ hmem; rw [hw0] at this; simpa using this.symm
  refine ⟨hlin, ?_⟩
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hu0, hu1⟩ := hcon
  apply hno
  refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, ?_⟩
  intro i hi
  have hi0 : i = i₀ := Subsingleton.elim i i₀
  subst hi0
  exact ⟨by simp [hu0], by simp [hu1]⟩

/-- **Other direction (sufficiency).** If the affine value at the unique coordinate vanishes and
the stack is nondegenerate there, the zero code's `mcaEvent` fires at `γ` (radius `0`). -/
theorem mcaEvent_zeroCode_of_affine_zero {u₀ u₁ : ι → A} {γ : K}
    (hlin : u₀ i₀ + γ • u₁ i₀ = 0) (hne : u₀ i₀ ≠ 0 ∨ u₁ i₀ ≠ 0) :
    mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ γ := by
  classical
  refine ⟨{i₀}, ?_, ⟨0, Submodule.zero_mem _, ?_⟩, ?_⟩
  · rw [card_ι_eq_one (ι := ι)]; simp
  · intro i hi
    have hi0 : i = i₀ := Subsingleton.elim i i₀
    subst hi0
    simpa using hlin.symm
  · rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    have hv₀0 : v₀ = 0 := (mem_zeroCode_iff v₀).mp hv₀
    have hv₁0 : v₁ = 0 := (mem_zeroCode_iff v₁).mp hv₁
    obtain ⟨ha, hb⟩ := hagree i₀ (by simp)
    rw [hv₀0] at ha; rw [hv₁0] at hb
    simp only [Pi.zero_apply] at ha hb
    rcases hne with h | h
    · exact h ha.symm
    · exact h hb.symm

/-- **Exact characterization of the zero code's `mcaEvent`.** Over any finite field and any
single-coordinate index, the zero code's `mcaEvent` at radius `0` fires at `γ` **iff** the affine
value at the unique coordinate vanishes and the stack is nondegenerate there. Upgrades the in-tree
one-directional `mcaEvent_Czero_pos0` to a biconditional, field-generic. -/
theorem mcaEvent_zeroCode_iff {u₀ u₁ : ι → A} {γ : K} :
    mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ ↔
      (u₀ i₀ + γ • u₁ i₀ = 0) ∧ (u₀ i₀ ≠ 0 ∨ u₁ i₀ ≠ 0) := by
  constructor
  · exact mcaEvent_zeroCode_pos0
  · rintro ⟨hlin, hne⟩; exact mcaEvent_zeroCode_of_affine_zero hlin hne

/-- **A concrete one-scalar bad event for any nonzero module element.** The zero first word and
constant nonzero second word fire `mcaEvent` at `γ = 0` for the zero code. This supplies the
field-generic lower half of the exact zero-code MCA value. -/
theorem mcaEvent_zeroCode_zero_of_ne {a : A} (ha : a ≠ 0) :
    mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      (0 : ι → A) (fun _ => a) (0 : K) := by
  refine mcaEvent_zeroCode_of_affine_zero (ι := ι) (K := K) (A := A) ?_ ?_
  · simp
  · right
    simpa using ha

/-- **The zero code's `mcaEvent` fires for at most one scalar — over ANY finite field.** This is
the genuine field-generic generalization of the in-tree `not_mcaEvent_both` (which only excludes
the two scalars `0, 1` of `ZMod 2` by a finite case split). The argument is purely algebraic: the
affine `u₀ i₀ + X • u₁ i₀` has at most one root unless `u₁ i₀ = 0`, and then nondegeneracy forces
`u₀ i₀ ≠ 0` so there is no root at all. -/
theorem mcaEvent_zeroCode_unique {u₀ u₁ : ι → A} {γ γ' : K}
    (h : mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ γ)
    (h' : mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ γ') :
    γ = γ' := by
  obtain ⟨hlin, hne⟩ := mcaEvent_zeroCode_pos0 h
  obtain ⟨hlin', _⟩ := mcaEvent_zeroCode_pos0 h'
  have heq : γ • u₁ i₀ = γ' • u₁ i₀ := by
    have h1 : γ • u₁ i₀ = -(u₀ i₀) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hlin
    have h2 : γ' • u₁ i₀ = -(u₀ i₀) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hlin'
    rw [h1, h2]
  have hsub : (γ - γ') • u₁ i₀ = 0 := by rw [sub_smul, heq, sub_self]
  by_contra hcon
  have hγγ' : γ - γ' ≠ 0 := sub_ne_zero.mpr hcon
  have hu1 : u₁ i₀ = 0 := by
    rcases smul_eq_zero.mp hsub with hz | hz
    · exact absurd hz hγγ'
    · exact hz
  have hu0 : u₀ i₀ = 0 := by
    have := hlin; rw [hu1, smul_zero, add_zero] at this; exact this
  rcases hne with h0 | h0
  · exact h0 hu0
  · exact h0 hu1

/-- **The zero code's bad-scalar count is at most one — over ANY finite field.** Corollary of
`mcaEvent_zeroCode_unique`: the bad-scalar set is a subsingleton. -/
theorem mcaBadCount_zeroCode_le_one {u₀ u₁ : ι → A} :
    mcaBadCount (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0) u₀ u₁
      ≤ 1 := by
  classical
  rw [mcaBadCount, Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  exact mcaEvent_zeroCode_unique hγ.2 hγ'.2

/-- **Bad-count dichotomy.** The zero code's bad count at radius `0` lives in `{0, 1}`. -/
theorem mcaBadCount_zeroCode_lt_two {u₀ u₁ : ι → A} :
    mcaBadCount (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0) u₀ u₁
      < 2 :=
  Nat.lt_succ_of_le mcaBadCount_zeroCode_le_one

/-- **`ε_mca(zeroCode, 0) ≤ 1/|K|` over an arbitrary finite field.** Generalizes the in-tree
`epsMCA_Czero_le_half` (which is `ZMod 2`-specific, derived via `not_mcaEvent_both`) to any finite
field, using the field-generic bad-count bound. -/
theorem epsMCA_zeroCode_le_inv_card :
    epsMCA (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      ≤ (1 : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  refine ENNReal.div_le_div_right ?_ _
  refine iSup_le fun u => ?_
  have hle : mcaBadCount (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A)))
      (0 : ℝ≥0) (u 0) (u 1) ≤ 1 := mcaBadCount_zeroCode_le_one
  exact_mod_cast hle

/-- **`1/|K| ≤ ε_mca(zeroCode, 0)` for nontrivial ambient modules.** A nonzero constant second
word gives a bad scalar at `γ = 0`, and `ε_mca` dominates that stack's bad-scalar probability. -/
theorem epsMCA_zeroCode_ge_inv_card [Nontrivial A] :
    (1 : ENNReal) / (Fintype.card K : ENNReal) ≤
      epsMCA (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := exists_ne (0 : A)
  let u : WordStack A (Fin 2) ι := fun k => if k = 0 then (0 : ι → A) else fun _ => a
  have hev : mcaEvent (F := K)
      ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      (u 0) (u 1) (0 : K) := by
    simpa [u] using mcaEvent_zeroCode_zero_of_ne (ι := ι) (K := K) (A := A) ha
  have hpoint :
      (1 : ENNReal) / (Fintype.card K : ENNReal) ≤
        Pr_{let γ ← $ᵖ K}[
          mcaEvent (F := K)
            ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
            (u 0) (u 1) γ] := by
    rw [pr_mcaEvent_eq_mcaBadCount_div]
    have hmem :
        (0 : K) ∈ Finset.filter
          (fun γ : K =>
            mcaEvent (F := K)
              ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
              (u 0) (u 1) γ) Finset.univ := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hev
    have hcard1 : (1 : ℕ) ≤
        (Finset.filter
          (fun γ : K =>
            mcaEvent (F := K)
              ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
              (u 0) (u 1) γ) Finset.univ).card :=
      Finset.card_pos.mpr ⟨0, hmem⟩
    gcongr
    exact_mod_cast hcard1
  refine le_trans hpoint ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack A (Fin 2) ι =>
    Pr_{let γ ← $ᵖ K}[
      mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A)))
        (0 : ℝ≥0) (u 0) (u 1) γ]) u

/-- **Exact value of the zero-code MCA error over one coordinate.** For any finite field and any
nontrivial ambient module, `ε_mca(zeroCode, 0) = 1/|K|`. -/
theorem epsMCA_zeroCode_eq_inv_card [Nontrivial A] :
    epsMCA (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      = (1 : ENNReal) / (Fintype.card K : ENNReal) :=
  le_antisymm epsMCA_zeroCode_le_inv_card
    (epsMCA_zeroCode_ge_inv_card (ι := ι) (K := K) (A := A))

/-! ## (D) Refutation-region facts: which stacks the counterexample cannot touch -/

/-- **A stack that vanishes at the coordinate is never bad for the zero code.** If
`u₀ i₀ = 0` and `u₁ i₀ = 0`, then no scalar fires `mcaEvent`: the refutation *requires* a
genuinely nonzero stack at the coordinate. -/
theorem not_mcaEvent_zeroCode_of_deg {u₀ u₁ : ι → A} {γ : K}
    (h₀ : u₀ i₀ = 0) (h₁ : u₁ i₀ = 0) :
    ¬ mcaEvent (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ γ := by
  intro h
  obtain ⟨_, hne⟩ := mcaEvent_zeroCode_pos0 h
  rcases hne with hc | hc
  · exact hc h₀
  · exact hc h₁

/-- Count form of `not_mcaEvent_zeroCode_of_deg`: a coordinate-vanishing stack contributes zero
bad scalars. -/
theorem mcaBadCount_zeroCode_eq_zero_of_deg {u₀ u₁ : ι → A}
    (h₀ : u₀ i₀ = 0) (h₁ : u₁ i₀ = 0) :
    mcaBadCount (F := K) ((zeroCode (ι := ι) (K := K) (A := A) : Set (ι → A))) (0 : ℝ≥0)
      u₀ u₁ = 0 :=
  mcaBadCount_eq_zero_of_forall_not_mcaEvent _ _ _ _ fun _ =>
    not_mcaEvent_zeroCode_of_deg h₀ h₁

end General

/-! ## (E) Bridge to the in-tree `ZMod 2` refutation -/

section Bridge

open CodingTheory.LineDecodingRefutation

/-- The in-tree refutation index `Fin 1` is a `Subsingleton`. -/
instance moduleInstance_LineDecodingRepairExtra_1 : Subsingleton (Fin 1) := inferInstance

/-- **The in-tree refutation's bad-scalar count is `≤ 1`** — re-derived as an instance of the
general field-generic `mcaBadCount_zeroCode_le_one`. The in-tree `not_mcaEvent_both` is the
`ZMod 2` shadow of this. -/
theorem mcaBadCount_Czero_le_one {u₀ u₁ : ι → A} :
    mcaBadCount (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ ≤ 1 :=
  mcaBadCount_zeroCode_le_one (ι := ι) (K := F) (A := A)

/-- **The in-tree refutation's `ε_mca(Czero, 0) ≤ 1/|F|`** — re-derived from the general result,
confirming the refutation-file `epsMCA_Czero_eq_half` (`= 1/2` over `ZMod 2`) is the `|F| = 2` case
of the field-generic identity `epsMCA_zeroCode_le_inv_card`. -/
theorem epsMCA_Czero_le_inv_card_via_general :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      ≤ (1 : ENNReal) / (Fintype.card F : ENNReal) :=
  epsMCA_zeroCode_le_inv_card (ι := ι) (K := F) (A := A)

/-- **Exact value re-confirmed via the general upper bound.** Combining the general upper half
`epsMCA_Czero_le_inv_card_via_general` with the in-tree lower half `epsMCA_Czero_ge_half` yields
`ε_mca(Czero, 0) = 1/|F|`, matching `LineDecodingRepair.epsMCA_Czero_eq_inv_card` but with the
upper bound now factored through the field-generic argument. -/
theorem epsMCA_Czero_eq_inv_card_via_general :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      = (1 : ENNReal) / (Fintype.card F : ENNReal) :=
  le_antisymm epsMCA_Czero_le_inv_card_via_general
    CodingTheory.LineDecodingRepair.epsMCA_Czero_ge_half

end Bridge

end CodingTheory.LineDecodingRepairExtra

#print axioms CodingTheory.LineDecodingRepairExtra.mcaEvent_zeroCode_zero_of_ne
#print axioms CodingTheory.LineDecodingRepairExtra.epsMCA_zeroCode_ge_inv_card
#print axioms CodingTheory.LineDecodingRepairExtra.epsMCA_zeroCode_eq_inv_card
