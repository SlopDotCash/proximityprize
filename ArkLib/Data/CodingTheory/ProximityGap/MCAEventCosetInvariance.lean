/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Coset-invariance of the MCA bad event in the direction word (#389)

The MCA bad event `mcaEvent C δ u₀ u₁ γ` depends on the direction word `u₁` **only through its
coset `u₁ + C`**: shifting `u₁` by any codeword `c ∈ C` leaves the bad event (hence the whole set
of bad scalars, hence `ε_mca`) unchanged.

    `mcaEvent C δ u₀ u₁ γ  ↔  mcaEvent C δ u₀ (u₁ − c) γ`   for every `c ∈ C`.

**Why it matters (the floor unification).**  This is the rigorous "WLOG `u₁` is its sparsest
representative" reduction.  The bad set depends on `u₁` only via `dist(u₁, C)`:

* the **decoupled-Johnson** packing bound (`DecoupledJohnsonBound.mca_badScalars_card_mul_sub_le`)
  is non-vacuous exactly when `u₁` is **far** from the code (`A₁ = n − dist(u₁,C) < a²/n`);
* the **high-distance `BandCollapse`** rigidity is the regime where `u₁` (after this shift) is
  **sparse**, i.e. **near** the code.

So the two unconditional floor levers cover complementary halves of `u₁`-space, welded by this one
invariance; the entire beyond-Johnson floor difficulty is localized to the crossover regime where
`u₁` is moderately close to the code (the structured / KKH26-bad-line adversary).

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
`c ∈ C` does not change whether `γ` is MCA-bad.  Hence the bad set, `ε_mca`, and `δ*` depend on
`u₁` only through its coset `u₁ + C` (equivalently, only through `dist(u₁, C)`). -/
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

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.CosetInvariance.mcaEvent_sub_codeword_imp
#print axioms ArkLib.ProximityGap.CosetInvariance.mcaEvent_sub_codeword_iff
