/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Algebra.Field.ZMod

/-!
# Coset-invariance of the MCA bad event in the direction word (#389)

The MCA bad event `mcaEvent C δ u₀ u₁ γ` depends on the direction word `u₁` **only through its
coset `u₁ + C`**: shifting `u₁` by any codeword `c ∈ C` leaves the bad event (hence the whole set
of bad scalars, hence `ε_mca`) unchanged.

    `mcaEvent C δ u₀ u₁ γ  ↔  mcaEvent C δ u₀ (u₁ − c) γ`   for every `c ∈ C`.

**Why it matters.**  This is the rigorous "WLOG `u₁` is a sparsest representative **of its own
coset**" reduction: one may replace `u₁` by any `u₁ − c`, `c ∈ C`, e.g. a minimum-weight element
of `u₁ + C`, without changing the bad set.

**What it does NOT say (audit PG-062).**  The bad set is a function of the coset `u₁ + C`, but it
is **not** a function of the single statistic `dist(u₁, C)`: different cosets with the same
distance to the code can have different bad sets.  The checked counterexample
`DistanceCounterexample.bad_event_not_determined_by_distance` below shows this over `𝔽₅`,
`n = 2`, `C = {0}`, `δ = 0`, `u₀ = e₁`: the directions `e₁` and `e₂` have equal Hamming distance
to `C`, yet `γ = −1` is an MCA event for `e₁` and not for `e₂`.  So distance-only case splits
(e.g. "far" directions for the decoupled-Johnson packing bound
`DecoupledJohnsonBound.mca_badScalars_card_mul_sub_le`, which is non-vacuous when
`A₁ = n − dist(u₁,C) < a²/n`, versus "sparse/near" directions for the high-distance
`BandCollapse` rigidity) are valid case splits on a coset invariant of `u₁`, but they do not by
themselves reduce the whole coset to its distance; any argument that treats two cosets with the
same distance as interchangeable needs a separate justification.

The proof is a coset bijection: the witness codeword transforms `w ↦ w − γ•c ∈ C`, and the joint
pair transforms `v₁ ↦ v₁ + c ∈ C` — both reversible.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal

namespace ArkLib.ProximityGap.CosetInvariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **One direction of coset-invariance** (used for both directions of the `iff`).  If `γ` is bad
for `(u₀, u₁)` and `c ∈ C`, then `γ` is bad for `(u₀, u₁ − c)`. -/
theorem mcaEvent_sub_codeword_imp
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    {c : ι → A} (hc : c ∈ C)
    (h : _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) :
    _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ (u₁ - c) γ := by
  obtain ⟨S, hScard, ⟨w, hwC, hw⟩, hnj⟩ := h
  refine ⟨S, hScard, ⟨w - γ • c, C.sub_mem hwC (C.smul_mem γ hc), ?_⟩, ?_⟩
  · -- closeness transfers: (w − γ•c) i = u₀ i + γ•(u₁ − c) i
    intro i hi
    have := hw i hi
    simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
    rw [this, smul_sub]
    abel
  · -- non-jointness transfers via v₁ ↦ v₁ + c
    rintro ⟨v₀, hv₀C, v₁, hv₁C, hagree⟩
    refine hnj ⟨v₀, hv₀C, v₁ + c, C.add_mem hv₁C hc, ?_⟩
    intro i hi
    obtain ⟨he₀, he₁⟩ := hagree i hi
    refine ⟨he₀, ?_⟩
    have : v₁ i = (u₁ - c) i := he₁
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    rw [this]; abel

/-- **Coset-invariance of the MCA bad event in the direction word.**  Shifting `u₁` by a codeword
`c ∈ C` does not change whether `γ` is MCA-bad.  Hence the bad set depends on `u₁` only through
its coset `u₁ + C`.  It is NOT determined by `dist(u₁, C)` alone: see
`DistanceCounterexample.bad_event_not_determined_by_distance`. -/
theorem mcaEvent_sub_codeword_iff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    {c : ι → A} (hc : c ∈ C) :
    _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ
      ↔ _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ (u₁ - c) γ := by
  constructor
  · exact mcaEvent_sub_codeword_imp C δ u₀ u₁ γ hc
  · intro h
    have hc' : -c ∈ C := C.neg_mem hc
    have := mcaEvent_sub_codeword_imp C δ u₀ (u₁ - c) γ hc' h
    simpa [sub_sub_cancel, sub_neg_eq_add] using this

end ArkLib.ProximityGap.CosetInvariance

/-! ## Equal distance does not determine the bad event (audit PG-062)

Over `𝔽₅` with `n = 2`, the zero code `C = {0}`, radius `δ = 0` and `u₀ = e₁ = (1, 0)`: the
directions `e₁` and `e₂ = (0, 1)` both have Hamming distance `1` to `C`, but at `γ = −1` the line
`e₁ + γ·e₁ = 0` is (vacuously) close to `C` while `(e₁, e₁)` is not jointly explained by `C`, so
`γ` is MCA-bad for `e₁`; the line `e₁ + γ·e₂ = (1, −1)` has no full-domain agreement with `0`, so
`γ` is not bad for `e₂`. (Adapted from the audit fixture `coset-distance-counterexample.lean.txt`.)
-/

namespace ArkLib.ProximityGap.CosetInvariance.DistanceCounterexample

open _root_.ProximityGap

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The zero code in `𝔽₅²`. -/
abbrev Czero : Submodule (ZMod 5) (Fin 2 → ZMod 5) := ⊥

/-- The first standard basis vector of `𝔽₅²`. -/
def e₁ : Fin 2 → ZMod 5 := ![1, 0]

/-- The second standard basis vector of `𝔽₅²`. -/
def e₂ : Fin 2 → ZMod 5 := ![0, 1]

/-- `e₁` and `e₂` are at the same Hamming distance from the zero code. -/
theorem equal_distance_to_zero :
    hammingDist e₁ (0 : Fin 2 → ZMod 5) = hammingDist e₂ (0 : Fin 2 → ZMod 5) := by
  decide

/-- `γ = −1` is an MCA event for the direction `e₁`. -/
theorem event_for_first_direction :
    mcaEvent (F := ZMod 5) (Czero : Set (Fin 2 → ZMod 5)) 0 e₁ e₁ (-1 : ZMod 5) := by
  refine ⟨Finset.univ, by norm_num, ⟨0, by simp, ?_⟩, ?_⟩
  · intro i _
    simp
  · rintro ⟨v0, hv0, v1, hv1, ha⟩
    have hv : v0 = 0 := by simpa using hv0
    have h := (ha 0 (Finset.mem_univ 0)).1
    simp [hv, e₁] at h

/-- `γ = −1` is not an MCA event for the direction `e₂`. -/
theorem no_event_for_second_direction :
    ¬ mcaEvent (F := ZMod 5) (Czero : Set (Fin 2 → ZMod 5)) 0 e₁ e₂ (-1 : ZMod 5) := by
  rintro ⟨S, hcard, ⟨v, hv, ha⟩, _⟩
  have hge : 2 ≤ S.card := by simpa using hcard
  have hle : S.card ≤ 2 := by simpa using Finset.card_le_univ S
  have hS : S = Finset.univ :=
    Finset.eq_univ_of_card S (by simpa using Nat.le_antisymm hle hge)
  have hv0 : v = 0 := by simpa using hv
  have h := ha 0 (by rw [hS]; exact Finset.mem_univ 0)
  simp [hv0, e₁, e₂] at h

/-- **The MCA bad event is not a function of `dist(u₁, C)`.**  Two directions at equal Hamming
distance from the code can have different bad events at the same scalar. -/
theorem bad_event_not_determined_by_distance :
    ∃ v w : Fin 2 → ZMod 5,
      hammingDist v (0 : Fin 2 → ZMod 5) = hammingDist w (0 : Fin 2 → ZMod 5) ∧
      mcaEvent (F := ZMod 5) (Czero : Set (Fin 2 → ZMod 5)) 0 e₁ v (-1 : ZMod 5) ∧
      ¬ mcaEvent (F := ZMod 5) (Czero : Set (Fin 2 → ZMod 5)) 0 e₁ w (-1 : ZMod 5) :=
  ⟨e₁, e₂, equal_distance_to_zero, event_for_first_direction, no_event_for_second_direction⟩

end ArkLib.ProximityGap.CosetInvariance.DistanceCounterexample

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.CosetInvariance.mcaEvent_sub_codeword_imp
#print axioms ArkLib.ProximityGap.CosetInvariance.mcaEvent_sub_codeword_iff
#print axioms
  ArkLib.ProximityGap.CosetInvariance.DistanceCounterexample.bad_event_not_determined_by_distance
