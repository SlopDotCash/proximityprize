/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The MCA equivariance engine (#357 S3): `mcaEvent` symmetry, orbit-sup reduction

`ε_mca` is a `⨆` over `|A|^{2n}` stacks of a probability over the line scalar `γ`. The probe
laboratory computes exact values of `ε_mca` only because the per-stack probability is constant
on the orbits of a large symmetry group. This file makes that symmetry **formal**, turning the
probes' orbit reductions into theorems and providing the scaling engine for exact-`δ*` rungs
beyond `n = 4` (R1, `MCADeltaStarExactPoint.lean`).

## The group, and the lemmas

For a linear code `C ⊆ (ι → A)` over `F`, the per-stack bad-scalar probability
`γ ↦ Pr[mcaEvent C δ u₀ u₁ γ]` is invariant under:

* **codeword translation** (`mcaEvent_translate`, `prob_mcaEvent_translate`):
  `(u₀, u₁) ↦ (u₀ + c₀, u₁ + c₁)` for codewords `c₀, c₁ ∈ C` — `mcaEvent` is preserved at
  *each* `γ` (the translation `c₀ + γ•c₁` stays in `C`);
* **scaling of the whole stack** (`mcaEvent_smul_both`, `prob_mcaEvent_smul_both`):
  `(u₀, u₁) ↦ (s•u₀, s•u₁)`, `s ≠ 0` — preserved at each `γ`;
* **scaling of the direction row** (`mcaEvent_smul_right`, `prob_mcaEvent_smul_right`):
  `u₁ ↦ s•u₁`, `s ≠ 0` — reparametrizes `γ ↦ γ·s`, so the *probability* is preserved
  (uniform measure, `prob_uniform_comp_equiv`);
* **γ-shift** (`mcaEvent_shift`, `prob_mcaEvent_shift`): `u₀ ↦ u₀ + β•u₁` — reparametrizes
  `γ ↦ β + γ`, probability preserved;
* **domain symmetry** (`mcaEvent_comp_perm_iff`, `prob_mcaEvent_comp_perm`): any permutation
  `σ` of the coordinates with `C ∘ σ = C` — preserved at each `γ`. For Reed–Solomon codes the
  multiplicative rotations of a (smooth) subgroup domain qualify (`comp_perm_mem_code`,
  `mcaEvent_rs_rotate`): `domain (σ i) = g · domain i` maps `code domain k` to itself via
  `p ↦ p ∘ (gX)`.

Consequently `ε_mca` is computable as a sup over **orbit representatives**
(`epsMCA_eq_iSup_subtype_of_reps`): any set of stacks meeting every orbit of the action
suffices. This is the engine that makes the `n = 8` exact rung kernel-feasible and
retroactively certifies the probe lab's orbit reductions.

## The R1 instance

For the `R1` code `rsC = RS[F₅, ⟨2⟩, 2]` (`MCADeltaStarExactPoint.lean`):
* `rsC_eq_code` — **the bridge**: the hand-rolled `rsC` *is* literally
  `ReedSolomon.code ⟨gdom, _⟩ 2` (red-teaming R1: its "RS" claim is now anchored to the
  project-wide RS definition);
* `gdom_rotate` / `rsC_comp_rotate_mem` / `mcaEvent_rsC_rotate` — the concrete domain
  rotation `σ = finRotate 4` (`gdom (σ i) = 2 · gdom i`) preserves `rsC` and hence
  `mcaEvent`: the A5 equivariance pin, machine-checked at the first exact-δ* instance.

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
`native_decide`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. Issue #357 (S3 in the campaign dossier).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAEquivariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Probability helpers -/

open Classical in
/-- Pointwise-equivalent events have equal probability. -/
theorem Pr_congr_iff {α : Type} (D : PMF α) {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) :
    Pr_{ let x ← D }[P x] = Pr_{ let x ← D }[Q x] :=
  le_antisymm (Pr_le_Pr_of_implies D P Q fun x => (h x).mp)
    (Pr_le_Pr_of_implies D Q P fun x => (h x).mpr)

open Classical in
/-- The uniform measure is invariant under any self-equivalence of the sample space:
`Pr[P (e γ)] = Pr[P γ]`. -/
theorem prob_uniform_comp_equiv {G : Type} [Fintype G] [Nonempty G]
    (P : G → Prop) (e : G ≃ G) :
    Pr_{ let γ ←$ᵖ G }[P (e γ)] = Pr_{ let γ ←$ᵖ G }[P γ] := by
  have hcard : (Finset.filter (fun γ => P (e γ)) Finset.univ).card
      = (Finset.filter P Finset.univ).card := by
    apply Finset.card_equiv e
    intro γ
    simp
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card, hcard]

/-- Right multiplication by a nonzero scalar, as a self-equivalence of `F` whose
forward map is *syntactically* `γ * s`. -/
def mulRightEquiv (s : F) (hs : s ≠ 0) : F ≃ F where
  toFun γ := γ * s
  invFun γ := γ * s⁻¹
  left_inv γ := by field_simp
  right_inv γ := by field_simp

/-- Left addition by a scalar, as a self-equivalence of `F` whose forward map is
*syntactically* `β + γ`. -/
def addLeftEquiv (β : F) : F ≃ F where
  toFun γ := β + γ
  invFun γ := γ - β
  left_inv γ := by ring_nf
  right_inv γ := by ring_nf

/-! ## Transport of `pairJointAgreesOn` -/

/-- Joint explainability is invariant under translating the stack by a codeword pair. -/
theorem pairJointAgreesOn_translate (C : Submodule F (ι → A)) {S : Finset ι}
    {u₀ u₁ c₀ c₁ : ι → A} (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + c₀) (u₁ + c₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ - c₀, C.sub_mem hv₀ hc₀, v₁ - c₁, C.sub_mem hv₁ hc₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    constructor
    · simp only [Pi.sub_apply, h0, Pi.add_apply]
      abel
    · simp only [Pi.sub_apply, h1, Pi.add_apply]
      abel
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ + c₀, C.add_mem hv₀ hc₀, v₁ + c₁, C.add_mem hv₁ hc₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    exact ⟨by simp only [Pi.add_apply, h0], by simp only [Pi.add_apply, h1]⟩

/-- Joint explainability is invariant under scaling the direction row by `s ≠ 0`. -/
theorem pairJointAgreesOn_smul_right (C : Submodule F (ι → A)) {S : Finset ι}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ (s • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀, hv₀, s⁻¹ • v₁, C.smul_mem _ hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    refine ⟨h0, ?_⟩
    rw [Pi.smul_apply, h1, Pi.smul_apply, smul_smul, inv_mul_cancel₀ hs, one_smul]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀, hv₀, s • v₁, C.smul_mem _ hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    exact ⟨h0, by rw [Pi.smul_apply, h1, Pi.smul_apply]⟩

/-- Joint explainability is invariant under scaling the whole stack by `s ≠ 0`. -/
theorem pairJointAgreesOn_smul_both (C : Submodule F (ι → A)) {S : Finset ι}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) :
    pairJointAgreesOn (C : Set (ι → A)) S (s • u₀) (s • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨s⁻¹ • v₀, C.smul_mem _ hv₀, s⁻¹ • v₁, C.smul_mem _ hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    constructor
    · rw [Pi.smul_apply, h0, Pi.smul_apply, smul_smul, inv_mul_cancel₀ hs, one_smul]
    · rw [Pi.smul_apply, h1, Pi.smul_apply, smul_smul, inv_mul_cancel₀ hs, one_smul]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨s • v₀, C.smul_mem _ hv₀, s • v₁, C.smul_mem _ hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    exact ⟨by rw [Pi.smul_apply, h0, Pi.smul_apply],
      by rw [Pi.smul_apply, h1, Pi.smul_apply]⟩

/-- Joint explainability is invariant under the γ-shift `u₀ ↦ u₀ + β•u₁`. -/
theorem pairJointAgreesOn_shift (C : Submodule F (ι → A)) {S : Finset ι}
    {u₀ u₁ : ι → A} (β : F) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + β • u₁) u₁ ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ - β • v₁, C.sub_mem hv₀ (C.smul_mem _ hv₁), v₁, hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    refine ⟨?_, h1⟩
    simp only [Pi.sub_apply, Pi.smul_apply, h0, h1, Pi.add_apply]
    abel
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ + β • v₁, C.add_mem hv₀ (C.smul_mem _ hv₁), v₁, hv₁, fun i hi => ?_⟩
    obtain ⟨h0, h1⟩ := hag i hi
    refine ⟨?_, h1⟩
    simp only [Pi.add_apply, Pi.smul_apply, h0, h1]

/-! ## Transport of `mcaEvent` -/

/-- **Translation equivariance (per-`γ`).** Translating the stack by a codeword pair preserves
the MCA event at every scalar: the line picks up `c₀ + γ•c₁ ∈ C`. -/
theorem mcaEvent_translate (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ c₀ c₁ : ι → A} (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w - (c₀ + γ • c₁),
      C.sub_mem hw (C.add_mem hc₀ (C.smul_mem γ hc₁)), fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_translate C hc₀ hc₁).mpr hp)⟩
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    rw [hag i hi]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add]
    abel
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w + (c₀ + γ • c₁),
      C.add_mem hw (C.add_mem hc₀ (C.smul_mem γ hc₁)), fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_translate C hc₀ hc₁).mp hp)⟩
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [hag i hi]
    simp only [smul_add]
    abel

/-- **Stack-scaling equivariance (per-`γ`).** Scaling both rows by `s ≠ 0` preserves the MCA
event at every scalar. -/
theorem mcaEvent_smul_both (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (s • u₀) (s • u₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨s⁻¹ • w, C.smul_mem _ hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_smul_both C hs).mpr hp)⟩
    rw [Pi.smul_apply, hag i hi]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    have hs2 : s⁻¹ * (γ * s) = γ := by
      rw [← mul_assoc, mul_comm s⁻¹ γ, mul_assoc, inv_mul_cancel₀ hs, mul_one]
    rw [inv_mul_cancel₀ hs, one_smul, hs2]
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨s • w, C.smul_mem _ hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_smul_both C hs).mp hp)⟩
    rw [Pi.smul_apply, hag i hi]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    rw [mul_comm s γ]

/-- **Direction-scaling reparametrization.** Scaling the direction row by `s ≠ 0` moves the
MCA event from scalar `γ` to scalar `γ·s`. -/
theorem mcaEvent_smul_right (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (s • u₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ * s) := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_smul_right C hs).mpr hp)⟩
    rw [hag i hi, Pi.smul_apply, smul_smul]
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_smul_right C hs).mp hp)⟩
    rw [hag i hi, Pi.smul_apply, smul_smul]

/-- **γ-shift reparametrization.** Shifting `u₀` by `β•u₁` moves the MCA event from scalar
`γ` to scalar `β + γ`. -/
theorem mcaEvent_shift (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} (β : F) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + β • u₁) u₁ γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (β + γ) := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_shift C β).mpr hp)⟩
    rw [hag i hi]
    simp only [Pi.add_apply, Pi.smul_apply, add_smul]
    abel
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun hp => hno ((pairJointAgreesOn_shift C β).mp hp)⟩
    rw [hag i hi]
    simp only [Pi.add_apply, Pi.smul_apply, add_smul]
    abel

/-- One direction of domain-permutation equivariance: if the stack is precomposed with a
code-preserving permutation `σ`, the MCA event transports back along `σ` (witness set
`S ↦ S.image σ`, codeword `w ↦ w ∘ σ⁻¹`). -/
theorem mcaEvent_comp_perm_mp (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {γ : F} (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ →
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
  refine ⟨S.image ⇑σ, ?_, ⟨w ∘ ⇑σ⁻¹, hσ' w hw, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective S σ.injective]
    exact hcard
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have h := hag j hj
    simpa [Function.comp] using h
  · intro hpair
    apply hno
    obtain ⟨v₀, hv₀, v₁, hv₁, hagp⟩ := hpair
    refine ⟨v₀ ∘ ⇑σ, hσ v₀ hv₀, v₁ ∘ ⇑σ, hσ v₁ hv₁, fun j hj => ?_⟩
    exact hagp (σ j) (Finset.mem_image_of_mem ⇑σ hj)

/-- **Domain-permutation equivariance (per-`γ`).** For any coordinate permutation preserving
the code (in both directions), precomposing the stack preserves the MCA event at every
scalar. -/
theorem mcaEvent_comp_perm_iff (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {γ : F} (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  constructor
  · exact mcaEvent_comp_perm_mp C σ hσ hσ'
  · intro h
    have e0 : (u₀ ∘ ⇑σ) ∘ ⇑σ⁻¹ = u₀ := by
      funext i
      simp [Function.comp, Equiv.Perm.inv_def]
    have e1 : (u₁ ∘ ⇑σ) ∘ ⇑σ⁻¹ = u₁ := by
      funext i
      simp [Function.comp, Equiv.Perm.inv_def]
    have h' : mcaEvent (F := F) (C : Set (ι → A)) δ ((u₀ ∘ ⇑σ) ∘ ⇑σ⁻¹)
        ((u₁ ∘ ⇑σ) ∘ ⇑σ⁻¹) γ := by
      rw [e0, e1]
      exact h
    refine mcaEvent_comp_perm_mp C σ⁻¹ hσ' ?_ h'
    intro w hw
    have := hσ w hw
    simpa using this

/-! ## The probability-level invariances -/

open Classical in
/-- Per-stack bad-scalar probability is invariant under codeword translation. -/
theorem prob_mcaEvent_translate (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ c₀ c₁ : ι → A} (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] :=
  Pr_congr_iff _ fun γ => mcaEvent_translate C hc₀ hc₁ γ

open Classical in
/-- Per-stack bad-scalar probability is invariant under whole-stack scaling. -/
theorem prob_mcaEvent_smul_both (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (s • u₀) (s • u₁) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] :=
  Pr_congr_iff _ fun γ => mcaEvent_smul_both C hs γ

open Classical in
/-- Per-stack bad-scalar probability is invariant under direction-row scaling (uniform
measure + the `γ·s` reparametrization). -/
theorem prob_mcaEvent_smul_right (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} {s : F} (hs : s ≠ 0) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (s • u₁) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] := by
  rw [Pr_congr_iff ($ᵖ F) (fun γ => mcaEvent_smul_right C hs γ)]
  exact prob_uniform_comp_equiv
    (fun γ => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) (mulRightEquiv s hs)

open Classical in
/-- Per-stack bad-scalar probability is invariant under the γ-shift `u₀ ↦ u₀ + β•u₁`
(uniform measure + the `β + γ` reparametrization). -/
theorem prob_mcaEvent_shift (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} (β : F) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + β • u₁) u₁ γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] := by
  rw [Pr_congr_iff ($ᵖ F) (fun γ => mcaEvent_shift C β γ)]
  exact prob_uniform_comp_equiv
    (fun γ => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) (addLeftEquiv β)

open Classical in
/-- Per-stack bad-scalar probability is invariant under code-preserving domain
permutations. -/
theorem prob_mcaEvent_comp_perm (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ : ι → A} (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] :=
  Pr_congr_iff _ fun γ => mcaEvent_comp_perm_iff C σ hσ hσ' (γ := γ)

/-! ## The orbit-sup reduction -/

open Classical in
/-- **The orbit-representative reduction.** If a set `T` of stacks meets every per-stack
probability value (e.g. a transversal of the equivariance-group orbits, by the invariance
lemmas above), then `ε_mca` is the sup over `T` alone. This is the formal engine behind the
probe lab's orbit reductions and the scaling route for exact-`δ*` rungs beyond `n = 4`. -/
theorem epsMCA_eq_iSup_subtype_of_reps (C : Set (ι → A)) (δ : ℝ≥0)
    (T : Set (WordStack A (Fin 2) ι))
    (hT : ∀ u : WordStack A (Fin 2) ι, ∃ v ∈ T,
      Pr_{ let γ ←$ᵖ F }[mcaEvent C δ (v 0) (v 1) γ]
        = Pr_{ let γ ←$ᵖ F }[mcaEvent C δ (u 0) (u 1) γ]) :
    epsMCA (F := F) C δ
      = ⨆ v : T, Pr_{ let γ ←$ᵖ F }[mcaEvent C δ ((v : WordStack A (Fin 2) ι) 0)
          ((v : WordStack A (Fin 2) ι) 1) γ] := by
  unfold epsMCA
  apply le_antisymm
  · refine iSup_le fun u => ?_
    obtain ⟨v, hvT, hve⟩ := hT u
    rw [← hve]
    exact le_iSup (fun v : T =>
      Pr_{ let γ ←$ᵖ F }[mcaEvent C δ ((v : WordStack A (Fin 2) ι) 0)
        ((v : WordStack A (Fin 2) ι) 1) γ]) ⟨v, hvT⟩
  · refine iSup_le fun v => ?_
    exact le_iSup (fun u : WordStack A (Fin 2) ι =>
      Pr_{ let γ ←$ᵖ F }[mcaEvent C δ (u 0) (u 1) γ]) (v : WordStack A (Fin 2) ι)

/-! ## Reed–Solomon domain rotations -/

/-- **RS codes are closed under multiplicative domain rotations.** If a coordinate
permutation `σ` scales the evaluation domain (`domain (σ i) = g · domain i`), then
precomposition with `σ` maps `code domain k` into itself, via `p ↦ p.comp (gX)`. -/
theorem comp_perm_mem_code {domain : ι ↪ F} {k : ℕ} (σ : Equiv.Perm ι) (g : F)
    (hg : ∀ i, domain (σ i) = g * domain i) {w : ι → F}
    (hw : w ∈ ReedSolomon.code domain k) : (w ∘ ⇑σ) ∈ ReedSolomon.code domain k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hw ⊢
  obtain ⟨p, hdeg, rfl⟩ := hw
  refine ⟨p.comp (Polynomial.C g * Polynomial.X), ?_, ?_⟩
  · rcases eq_or_ne (p.comp (Polynomial.C g * Polynomial.X)) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe k
    · have hp0 : p ≠ 0 := by
        rintro rfl
        simp at h0
      have hgle : (Polynomial.C g * Polynomial.X).natDegree ≤ 1 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le
      have hple : (p.comp (Polynomial.C g * Polynomial.X)).natDegree ≤ p.natDegree := by
        refine le_trans Polynomial.natDegree_comp_le ?_
        calc p.natDegree * (Polynomial.C g * Polynomial.X).natDegree
            ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hgle
          _ = p.natDegree := Nat.mul_one _
      have hdeg' : p.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hdeg
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (lt_of_le_of_lt hple hdeg')
  · funext i
    simp [ReedSolomon.evalOnPoints, Function.comp, Polynomial.eval_comp, hg i]

/-- **MCA-event equivariance under RS domain rotation.** For any multiplicative rotation of
the evaluation domain (`domain (σ i) = g · domain i`, `g ≠ 0`), precomposing the stack
preserves the MCA event of the RS code at every scalar. -/
theorem mcaEvent_rs_rotate (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F)
    (hg0 : g ≠ 0) (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (γ : F) (u₀ u₁ : ι → F) :
    mcaEvent (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ ↔
      mcaEvent (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ γ := by
  have hginv : ∀ i, domain (σ⁻¹ i) = g⁻¹ * domain i := by
    intro i
    have h := hg (σ⁻¹ i)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h ⊢
    rw [h, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  exact mcaEvent_comp_perm_iff (ReedSolomon.code domain k) σ
    (fun w hw => comp_perm_mem_code σ g hg hw)
    (fun w hw => comp_perm_mem_code σ⁻¹ g⁻¹ hginv hw)

/-! ## The R1 instance: bridging `rsC` to `ReedSolomon.code`, and its rotation -/

section R1Instance

open ProximityGap.MCADeltaStarExactPoint

/-- The R1 domain as an embedding. -/
def gdomEmb : Fin 4 ↪ F5 := ⟨gdom, gdom_injective⟩

/-- **The bridge (red-teaming R1):** the hand-rolled `rsC` of `MCADeltaStarExactPoint.lean`
*is* the project-wide Reed–Solomon code `code ⟨gdom,_⟩ 2`. The exact-`δ*` theorem therefore
genuinely speaks about `RS[F₅, ⟨2⟩, 2]` in the canonical sense. -/
theorem rsC_eq_code : rsC = ReedSolomon.code gdomEmb 2 := by
  ext w
  constructor
  · rintro ⟨a, b, h⟩
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    refine ⟨Polynomial.C b * Polynomial.X + Polynomial.C a, ?_, ?_⟩
    · have h1 : (Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le
      have h2 : (Polynomial.C a : Polynomial F5).natDegree = 0 := Polynomial.natDegree_C a
      have h3 := Polynomial.natDegree_add_le (Polynomial.C b * Polynomial.X)
        (Polynomial.C a : Polynomial F5)
      omega
    · funext i
      rw [h i]
      simp [ReedSolomon.evalOnPoints, gdomEmb]
      ring
  · intro hw
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hw
    obtain ⟨p, hdeg, rfl⟩ := hw
    obtain ⟨c, d, rfl⟩ :=
      Polynomial.exists_eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hdeg)
    refine ⟨d, c, fun i => ?_⟩
    simp [ReedSolomon.evalOnPoints, gdomEmb]
    ring

/-- The cyclic rotation of the R1 domain: `finRotate 4` doubles the evaluation point
(`gdom = (2^i)` and `σ : i ↦ i+1`). -/
theorem gdom_rotate : ∀ i : Fin 4, gdom (finRotate 4 i) = 2 * gdom i := by decide

/-- The R1 code is closed under the domain rotation. -/
theorem rsC_comp_rotate_mem {w : Fin 4 → F5} (hw : w ∈ rsC) :
    (w ∘ ⇑(finRotate 4)) ∈ rsC := by
  obtain ⟨a, b, h⟩ := hw
  refine ⟨a, 2 * b, fun i => ?_⟩
  have := h (finRotate 4 i)
  rw [Function.comp_apply, this, gdom_rotate i]
  ring

/-- The inverse rotation also preserves the R1 code (closure under `σ⁻¹`, needed for the
event-equivariance wrapper). -/
theorem rsC_comp_rotate_inv_mem {w : Fin 4 → F5} (hw : w ∈ rsC) :
    (w ∘ ⇑(finRotate 4)⁻¹) ∈ rsC := by
  obtain ⟨a, b, h⟩ := hw
  have hrot : ∀ i : Fin 4, gdom ((finRotate 4)⁻¹ i) = 3 * gdom i := by decide
  refine ⟨a, 3 * b, fun i => ?_⟩
  have := h ((finRotate 4)⁻¹ i)
  rw [Function.comp_apply, this, hrot i]
  ring

/-- **The A5 equivariance pin at the R1 instance:** the MCA event of `rsC` is invariant under
the smooth-domain rotation, at every radius, every stack and every scalar. -/
theorem mcaEvent_rsC_rotate (δ : ℝ≥0) (γ : F5) (u₀ u₁ : Fin 4 → F5) :
    mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) δ
        (u₀ ∘ ⇑(finRotate 4)) (u₁ ∘ ⇑(finRotate 4)) γ ↔
      mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) δ u₀ u₁ γ :=
  mcaEvent_comp_perm_iff rsC (finRotate 4)
    (fun _ hw => rsC_comp_rotate_mem hw)
    (fun _ hw => rsC_comp_rotate_inv_mem hw)

end R1Instance

/-! ## Source audit -/

#print axioms Pr_congr_iff
#print axioms prob_uniform_comp_equiv
#print axioms mcaEvent_translate
#print axioms mcaEvent_smul_both
#print axioms mcaEvent_smul_right
#print axioms mcaEvent_shift
#print axioms mcaEvent_comp_perm_iff
#print axioms prob_mcaEvent_translate
#print axioms prob_mcaEvent_smul_both
#print axioms prob_mcaEvent_smul_right
#print axioms prob_mcaEvent_shift
#print axioms prob_mcaEvent_comp_perm
#print axioms epsMCA_eq_iSup_subtype_of_reps
#print axioms comp_perm_mem_code
#print axioms mcaEvent_rs_rotate
#print axioms rsC_eq_code
#print axioms mcaEvent_rsC_rotate

end ProximityGap.MCAEquivariance
