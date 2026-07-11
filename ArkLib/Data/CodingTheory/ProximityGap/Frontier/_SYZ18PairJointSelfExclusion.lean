/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# SYZ18: pairJoint self-exclusion — the shared-witness mechanism (#466 / #507)

## The conjecture and the honest maximum proved here

**SYZ18 conjecture** (the campaign stance inverted): at rate `1/2`, for a radius in the
strip `(Johnson ≈ 0.293, 1/3)`, any stack `(u₀, u₁)` with *more than budget-many* bad
scalars must be a syzygy configuration (`_G86RankCollapseDichotomy`, `_G87…`: the witness
constraint rows are linearly dependent), and such a configuration is *self-excluding* —
the shared algebraic structure forces the `pairJointAgreesOn` clause to fire for some of
the involved scalars, so they were never `mcaEvent`-bad.

The empirical truth test
(`scripts/probes/probe_syz18_pairjoint_self_exclusion.py`, kb note
`docs/kb/deltastar-466-syz18-pairjoint-self-exclusion-2026-07-11.md`) isolated the exact
mechanism and its scope.  This file formalizes the honest, unconditional **core** of that
mechanism — the *shared-witness* self-exclusion — which is the atomic engine the syzygy
picture is built out of, together with its direct `mcaEvent` consequence.

## Main results (all axiom-clean, over an arbitrary field)

* `shared_witness_forces_pairJoint` — **the mechanism.**  If two *distinct* scalars
  `γ₀ ≠ γ₁` each have a codeword of `C` agreeing with their respective line
  `u₀ + γ·u₁` on the *same* set `S`, then `pairJointAgreesOn C S u₀ u₁` holds: a joint
  codeword pair `(v₀, v₁)` agrees with `(u₀, u₁)` on all of `S`.  The pair is recovered
  by the classic pencil inversion `v₁ = (γ₀−γ₁)⁻¹ • (w₀ − w₁)`, `v₀ = w₀ − γ₀ • v₁`.
* `mcaEvent_witnesses_are_scalar_unique` — **self-exclusion consequence.**  A witness set
  `S` that certifies the non-agreement clause `¬ pairJointAgreesOn C S u₀ u₁` can carry a
  line-explanation `∃ w ∈ C, w = u₀ + γ·u₁ on S` for **at most one** scalar `γ`.  Hence
  two `mcaEvent`-bad scalars sharing a common witness set is impossible: distinct bad
  scalars require distinct witness sets.

The linear-algebra content is exactly the reason two ball-hits on one pencil that share an
error support collapse to a joint pair — the subspace `S(E)` of syndromes supported on the
common error support `E = Sᶜ` is closed under the difference `t_{γ₀} − t_{γ₁} =
(γ₀−γ₁)·s₁`, pushing both `s₀` and `s₁` individually into `S(E)`.
-/

namespace ProximityGap.SYZ18

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {A : Type} [AddCommGroup A] [Module F A]

/-- **The shared-witness mechanism.**  Two distinct scalars whose lines are each explained
by a codeword of `C` on the *same* set `S` force a joint codeword pair on `S`.

This is the pencil-inversion at the heart of the proximity-gap argument: from
`w₀ = u₀ + γ₀·u₁` and `w₁ = u₀ + γ₁·u₁` on `S`, the codeword
`v₁ := (γ₀ − γ₁)⁻¹ • (w₀ − w₁)` agrees with `u₁` on `S`, and `v₀ := w₀ − γ₀ • v₁`
agrees with `u₀` on `S`. -/
theorem shared_witness_forces_pairJoint
    (C : Submodule F (ι → A)) {S : Finset ι} {u₀ u₁ : ι → A} {γ₀ γ₁ : F}
    (hne : γ₀ ≠ γ₁)
    (h0 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₀ • u₁ i)
    (h1 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  obtain ⟨w₀, hw₀C, hw₀⟩ := h0
  obtain ⟨w₁, hw₁C, hw₁⟩ := h1
  have hd : γ₀ - γ₁ ≠ 0 := sub_ne_zero.mpr hne
  set c : F := (γ₀ - γ₁)⁻¹ with hc
  -- v₁ := c • (w₀ − w₁) ∈ C agrees with u₁ on S.
  set v₁ : ι → A := c • (w₀ - w₁) with hv₁
  have hv₁C : v₁ ∈ C := C.smul_mem c (C.sub_mem hw₀C hw₁C)
  have hv₁S : ∀ i ∈ S, v₁ i = u₁ i := by
    intro i hi
    have e0 : w₀ i = u₀ i + γ₀ • u₁ i := hw₀ i hi
    have e1 : w₁ i = u₀ i + γ₁ • u₁ i := hw₁ i hi
    have hsub : (w₀ - w₁) i = (γ₀ - γ₁) • u₁ i := by
      simp only [Pi.sub_apply, e0, e1]
      rw [sub_smul]
      abel
    have : v₁ i = c • ((γ₀ - γ₁) • u₁ i) := by
      simp only [hv₁, Pi.smul_apply, hsub]
    rw [this, smul_smul, hc, inv_mul_cancel₀ hd, one_smul]
  -- v₀ := w₀ − γ₀ • v₁ ∈ C agrees with u₀ on S.
  set v₀ : ι → A := w₀ - γ₀ • v₁ with hv₀
  have hv₀C : v₀ ∈ C := C.sub_mem hw₀C (C.smul_mem γ₀ hv₁C)
  have hv₀S : ∀ i ∈ S, v₀ i = u₀ i := by
    intro i hi
    have e0 : w₀ i = u₀ i + γ₀ • u₁ i := hw₀ i hi
    have hu : v₁ i = u₁ i := hv₁S i hi
    simp only [hv₀, Pi.sub_apply, Pi.smul_apply, hu, e0]
    abel
  exact ⟨v₀, hv₀C, v₁, hv₁C, fun i hi => ⟨hv₀S i hi, hv₁S i hi⟩⟩

/-- **Self-exclusion: witness sets are scalar-unique.**  If `S` certifies the
non-agreement clause `¬ pairJointAgreesOn C S u₀ u₁` (the defining clause of `mcaEvent`),
then at most one scalar `γ` can have a codeword explaining its line `u₀ + γ·u₁` on `S`.
Concretely: two distinct scalars cannot both be line-explained on the same non-agreement
witness set. -/
theorem mcaEvent_witnesses_are_scalar_unique
    (C : Submodule F (ι → A)) {S : Finset ι} {u₀ u₁ : ι → A} {γ₀ γ₁ : F}
    (hnoJoint : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (h0 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₀ • u₁ i)
    (h1 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i) :
    γ₀ = γ₁ := by
  by_contra hne
  exact hnoJoint (shared_witness_forces_pairJoint C hne h0 h1)

/-- **`mcaEvent` phrasing of self-exclusion.**  Two distinct scalars that are both
`mcaEvent`-bad *via the same witness set `S`* is impossible.  Here "bad via `S`" is the
witness content of `mcaEvent C δ u₀ u₁ γ` after fixing the event's set to `S`: a codeword
explains the line on `S`, and no joint pair agrees on `S`.  Since the non-agreement clause
depends only on `(S, u₀, u₁)` — not on `γ` — a single non-agreement witness set forces the
explaining scalar to be unique. -/
theorem no_two_bad_scalars_share_witness
    (C : Submodule F (ι → A)) {S : Finset ι} {u₀ u₁ : ι → A} {γ₀ γ₁ : F}
    (hnoJoint : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (hbad0 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₀ • u₁ i)
    (hbad1 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i)
    (hne : γ₀ ≠ γ₁) : False :=
  hne (mcaEvent_witnesses_are_scalar_unique C hnoJoint hbad0 hbad1)

end ProximityGap.SYZ18
