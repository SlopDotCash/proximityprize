/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarExactPinF5

/-!
# The MCA equivariance engine and the eigenstack orbit law (#357 S3 / #334 A5)

The exact-`ε_mca` probe programme (`probe_exact_epsmca_ladder.py`,
`probe_epsmca_orbit_exact_n12.py`, `probe_s3_eigenstack_orbit_law.py`) computes worst-case
bad-scalar profiles by quotienting stacks by a symmetry group. This file is the Lean side:
it proves that `mcaEvent` (ABF26 Definition 4.3) is equivariant under the full probe group,
derives the orbit descent for `epsMCA`, and proves the **eigenstack orbit law** — the new
structural statement explaining the probes' "flat numerator" phenomenon (the worst-case
bad-scalar count of `RS[F, L, k]` at the plateau rung equals `n = |L|` at every field,
because the bad set of the maximizing stack is a *single orbit* of the affine reparametrization
induced by domain rotation).

## The invariances (any linear code, in `Submodule` form where linearity is used)

For a stack `(u₀, u₁)` and the affine line `γ ↦ u₀ + γ • u₁`:

* `mcaEvent_translate` — translating both rows by codewords preserves badness at every `γ`
  (the syndrome reduction: `mcaEvent` only sees the cosets `u₀ + C`, `u₁ + C`).
* `mcaEvent_smul_pair` — scaling both rows by `a ≠ 0` preserves badness at every `γ`.
* `mcaEvent_smul_snd` — scaling the second row by `c ≠ 0` reparametrizes `γ ↦ γ·c`.
* `mcaEvent_shear` — shearing `u₀ ↦ u₀ + b•u₁` reparametrizes `γ ↦ b + γ`.
* `mcaEvent_domainPerm` — precomposing with a code-stable domain permutation preserves
  badness at every `γ` (witness sets transport along the permutation).

Probability/counting forms: `badScalarSet_*` (`Finset.card` equalities) and
`prob_mcaEvent_*` (the `Pr_{γ ← $ᵖ F}` equalities), and the descent
`epsMCA_eq_biSup_of_cover` (the supremum may be computed over any set of orbit
representatives — the soundness statement of the probes' orbit reduction).

## The eigenstack orbit law

`mcaEvent_eigenstack_iff`: if `C` is stable under a domain permutation `σ` and the stack is
a *`σ`-eigenstack* — `u₀ ∘ σ = a • u₀ + b • u₁`, `u₁ ∘ σ = c • u₁` with `a, c ≠ 0` — then
the bad-scalar set is invariant under the affine map `T(γ) = a⁻¹b + γ·(a⁻¹c)`. Consequences
(`orderOf_le_badScalarSet_card_of_eigenstack`, `orderOf_dvd_badScalarSet_card_erase_zero…`):
off the fixed point, bad scalars come in whole orbits of size `ord(a⁻¹c)`, so the bad count
is `ε + (#orbits)·d` with `ε ∈ {0,1}`, `d = ord(a⁻¹c)` — *field-independent* orbit
arithmetic. For smooth-domain RS with `σ` = rotation, pure-frequency stacks are eigenstacks
with `d | n`, which is exactly the structure the exact probes measure (the (12,6) profile
`1, 2, 3, 12, 13` decomposes as fixed point / order-2 orbit / order-3 orbit / one full
order-12 orbit / fixed point + orbits).

## Demo (the engine replacing enumeration)

At `C = RS[F₅, F₅*, 2]` (the `DeltaStarExactPinF5` instance), the stack
`(x³, x²)` is a rotation-eigenstack with `T(γ) = 3γ` of order `4`; **one** explicit badness
certificate at `γ = 1` plus the orbit law reproduce the sharp bound `ε_mca(C, 1/4) ≥ 4/5`
that `DeltaStarExactPinF5` obtained from four hand-built certificates.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3.)
* Issue #357, hypothesis S3 of the 2026-06-11 nine-hypothesis campaign; issue #334 item A5.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAEquivariance

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## `pairJointAgreesOn` transport lemmas -/

/-- Joint explainability is a coset invariant: translating both rows by codewords does not
change it. (One half of the syndrome reduction.) -/
theorem pairJointAgreesOn_translate (C : Submodule F (ι → A)) (S : Finset ι)
    (u₀ u₁ v₀ v₁ : ι → A) (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + v₀) (u₁ + v₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ - v₀, C.sub_mem hw₀ hv₀, w₁ - v₁, C.sub_mem hw₁ hv₁, fun i hi => ?_⟩
    have h0 := (h i hi).1
    have h1 := (h i hi).2
    simp only [Pi.add_apply] at h0 h1
    constructor
    · simp only [Pi.sub_apply, h0]; abel
    · simp only [Pi.sub_apply, h1]; abel
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ + v₀, C.add_mem hw₀ hv₀, w₁ + v₁, C.add_mem hw₁ hv₁, fun i hi => ?_⟩
    simp only [Pi.add_apply, (h i hi).1, (h i hi).2, and_self]

/-- Joint explainability is invariant under scaling both rows by a nonzero scalar. -/
theorem pairJointAgreesOn_smul_pair (C : Submodule F (ι → A)) (S : Finset ι)
    {a : F} (ha : a ≠ 0) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S (a • u₀) (a • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨a⁻¹ • w₀, C.smul_mem _ hw₀, a⁻¹ • w₁, C.smul_mem _ hw₁, fun i hi => ?_⟩
    have h0 := (h i hi).1
    have h1 := (h i hi).2
    simp only [Pi.smul_apply] at h0 h1
    constructor
    · simp only [Pi.smul_apply, h0, inv_smul_smul₀ ha]
    · simp only [Pi.smul_apply, h1, inv_smul_smul₀ ha]
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨a • w₀, C.smul_mem _ hw₀, a • w₁, C.smul_mem _ hw₁, fun i hi => ?_⟩
    simp only [Pi.smul_apply, (h i hi).1, (h i hi).2, and_self]

/-- Joint explainability is invariant under scaling the second row by a nonzero scalar. -/
theorem pairJointAgreesOn_smul_snd (C : Submodule F (ι → A)) (S : Finset ι)
    {c : F} (hc : c ≠ 0) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ (c • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀, hw₀, c⁻¹ • w₁, C.smul_mem _ hw₁, fun i hi => ?_⟩
    have h1 := (h i hi).2
    simp only [Pi.smul_apply] at h1
    exact ⟨(h i hi).1, by simp only [Pi.smul_apply, h1, inv_smul_smul₀ hc]⟩
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀, hw₀, c • w₁, C.smul_mem _ hw₁, fun i hi => ?_⟩
    exact ⟨(h i hi).1, by simp only [Pi.smul_apply, (h i hi).2]⟩

/-- Joint explainability is invariant under the shear `u₀ ↦ u₀ + b • u₁` (the first-row
witness shifts by `b` times the *second-row* witness). -/
theorem pairJointAgreesOn_shear (C : Submodule F (ι → A)) (S : Finset ι)
    (b : F) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + b • u₁) u₁ ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ - b • w₁, C.sub_mem hw₀ (C.smul_mem _ hw₁), w₁, hw₁, fun i hi => ?_⟩
    have h0 := (h i hi).1
    have h1 := (h i hi).2
    simp only [Pi.add_apply, Pi.smul_apply] at h0
    refine ⟨?_, h1⟩
    simp only [Pi.sub_apply, Pi.smul_apply, h0, h1]
    abel
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ + b • w₁, C.add_mem hw₀ (C.smul_mem _ hw₁), w₁, hw₁, fun i hi => ?_⟩
    refine ⟨?_, (h i hi).2⟩
    simp only [Pi.add_apply, Pi.smul_apply, (h i hi).1, (h i hi).2]

/-- Stability of `C` under `· ∘ σ` gives stability under `· ∘ σ.symm`. -/
theorem comp_symm_mem_iff {C : Set (ι → A)} {σ : Equiv.Perm ι}
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) (w : ι → A) :
    w ∈ C ↔ w ∘ σ.symm ∈ C := by
  have h := hC (w ∘ σ.symm)
  have hw : (w ∘ σ.symm) ∘ σ = w := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hw] at h
  exact h.symm

/-- Joint explainability transports along a code-stable domain permutation, with the witness
set transported by `Finset.image`. -/
theorem pairJointAgreesOn_comp_perm {C : Set (ι → A)} {σ : Equiv.Perm ι}
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn C S (u₀ ∘ σ) (u₁ ∘ σ) ↔
      pairJointAgreesOn C (S.image σ) u₀ u₁ := by
  constructor
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ ∘ σ.symm, (comp_symm_mem_iff hC w₀).mp hw₀,
      w₁ ∘ σ.symm, (comp_symm_mem_iff hC w₁).mp hw₁, fun j hj => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have := h i hi
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this
  · rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
    refine ⟨w₀ ∘ σ, (hC w₀).mp hw₀, w₁ ∘ σ, (hC w₁).mp hw₁, fun i hi => ?_⟩
    exact h (σ i) (Finset.mem_image_of_mem σ hi)

/-! ## `mcaEvent` transport lemmas -/

/-- Generic congruence: if two stacks induce pointwise-identical lines at `γ` and `γ'` and
have equivalent joint explainability on every witness set, badness transfers. -/
theorem mcaEvent_congr_line (C : Set (ι → A)) (δ : ℝ≥0) {u₀ u₁ v₀ v₁ : ι → A} {γ γ' : F}
    (hline : ∀ i, u₀ i + γ • u₁ i = v₀ i + γ' • v₁ i)
    (hpj : ∀ S : Finset ι, pairJointAgreesOn C S u₀ u₁ ↔ pairJointAgreesOn C S v₀ v₁) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔ mcaEvent (F := F) C δ v₀ v₁ γ' := by
  unfold mcaEvent
  constructor
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    exact ⟨S, hcard, ⟨w, hwC, fun i hi => (hw i hi).trans (hline i)⟩,
      fun hpj' => hno ((hpj S).mpr hpj')⟩
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    exact ⟨S, hcard, ⟨w, hwC, fun i hi => (hw i hi).trans (hline i).symm⟩,
      fun hpj' => hno ((hpj S).mp hpj')⟩

/-- **Translation invariance (the syndrome reduction).** Shifting both rows by codewords
preserves badness at every scalar. -/
theorem mcaEvent_translate (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ v₀ v₁ : ι → A) (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + v₀) (u₁ + v₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  unfold mcaEvent
  constructor
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S, hcard,
      ⟨w - (v₀ + γ • v₁), C.sub_mem hwC (C.add_mem hv₀ (C.smul_mem _ hv₁)),
        fun i hi => ?_⟩,
      fun hpj => hno ((pairJointAgreesOn_translate C S u₀ u₁ v₀ v₁ hv₀ hv₁).mpr hpj)⟩
    have := hw i hi
    simp only [Pi.add_apply, smul_add] at this
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, this]
    abel
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S, hcard,
      ⟨w + (v₀ + γ • v₁), C.add_mem hwC (C.add_mem hv₀ (C.smul_mem _ hv₁)),
        fun i hi => ?_⟩,
      fun hpj => hno ((pairJointAgreesOn_translate C S u₀ u₁ v₀ v₁ hv₀ hv₁).mp hpj)⟩
    simp only [Pi.add_apply, Pi.smul_apply, hw i hi, smul_add]
    abel

/-- **Common-scaling invariance.** Scaling both rows by `a ≠ 0` preserves badness at every
scalar. -/
theorem mcaEvent_smul_pair (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {a : F} (ha : a ≠ 0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (a • u₀) (a • u₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  unfold mcaEvent
  constructor
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S, hcard, ⟨a⁻¹ • w, C.smul_mem _ hwC, fun i hi => ?_⟩,
      fun hpj => hno ((pairJointAgreesOn_smul_pair C S ha u₀ u₁).mpr hpj)⟩
    have := hw i hi
    simp only [Pi.smul_apply] at this
    simp only [Pi.smul_apply, this, smul_add, smul_comm a⁻¹ γ, inv_smul_smul₀ ha]
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S, hcard, ⟨a • w, C.smul_mem _ hwC, fun i hi => ?_⟩,
      fun hpj => hno ((pairJointAgreesOn_smul_pair C S ha u₀ u₁).mp hpj)⟩
    simp only [Pi.smul_apply, hw i hi, smul_add, smul_comm a γ]

/-- **Second-row scaling reparametrizes the scalar:** badness of `(u₀, c • u₁)` at `γ` is
badness of `(u₀, u₁)` at `γ·c`. -/
theorem mcaEvent_smul_snd (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {c : F} (hc : c ≠ 0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (c • u₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ * c) :=
  mcaEvent_congr_line (C : Set (ι → A)) δ
    (fun i => by simp only [Pi.smul_apply, smul_smul])
    (fun S => pairJointAgreesOn_smul_snd C S hc u₀ u₁)

/-- **Shear reparametrizes the scalar:** badness of `(u₀ + b • u₁, u₁)` at `γ` is badness
of `(u₀, u₁)` at `b + γ`. -/
theorem mcaEvent_shear (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (b : F) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁ γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (b + γ) :=
  mcaEvent_congr_line (C : Set (ι → A)) δ
    (fun i => by simp only [Pi.add_apply, Pi.smul_apply, add_smul]; abel)
    (fun S => pairJointAgreesOn_shear C S b u₀ u₁)

/-- **Domain-permutation invariance.** Precomposing the stack with a code-stable permutation
preserves badness at every scalar (witness sets transport along the permutation; their
cardinality is preserved). Works for an arbitrary code set `C`. -/
theorem mcaEvent_domainPerm (C : Set (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ) γ ↔ mcaEvent (F := F) C δ u₀ u₁ γ := by
  unfold mcaEvent
  constructor
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S.image σ, ?_, ⟨w ∘ σ.symm, (comp_symm_mem_iff hC w).mp hwC, fun j hj => ?_⟩,
      fun hpj => hno ((pairJointAgreesOn_comp_perm hC S u₀ u₁).mpr hpj)⟩
    · rwa [Finset.card_image_of_injective S σ.injective]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have := hw i hi
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this
  · rintro ⟨S, hcard, ⟨w, hwC, hw⟩, hno⟩
    refine ⟨S.image σ.symm, ?_,
      ⟨w ∘ σ, (hC w).mp hwC, fun j hj => ?_⟩, fun hpj => ?_⟩
    · rwa [Finset.card_image_of_injective S σ.symm.injective]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have := hw i hi
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
    · -- transport the joint pair back through `σ`
      have h' : pairJointAgreesOn C ((S.image σ.symm).image σ) u₀ u₁ := by
        exact (pairJointAgreesOn_comp_perm hC (S.image σ.symm) u₀ u₁).mp hpj
      have himg : (S.image σ.symm).image σ = S := by
        ext j
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨i, ⟨i', hi', rfl⟩, rfl⟩
          simpa only [Equiv.apply_symm_apply] using hi'
        · intro hj
          exact ⟨σ.symm j, ⟨j, hj, rfl⟩, σ.apply_symm_apply j⟩
      rw [himg] at h'
      exact hno h'

/-! ## The bad-scalar set and its counting transports -/

open Classical in
/-- The set of bad scalars of a stack at radius `δ` (the numerator of the stack's `epsMCA`
term). -/
noncomputable def badScalarSet (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ => mcaEvent (F := F) C δ u₀ u₁ γ)

open Classical in
theorem mem_badScalarSet {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ : ι → A} {γ : F} :
    γ ∈ badScalarSet (F := F) C δ u₀ u₁ ↔ mcaEvent (F := F) C δ u₀ u₁ γ := by
  simp [badScalarSet]

open Classical in
/-- The probability of the bad event is the bad-scalar count over `|F|`. -/
theorem prob_mcaEvent_eq_badScalarSet_card (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ u₀ u₁ γ]
      = ((badScalarSet (F := F) C δ u₀ u₁).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  rw [prob_uniform_eq_card_filter_div_card]
  rfl

open Classical in
/-- Counting transport for a scalar reparametrization: if badness of `(v₀, v₁)` at `γ` is
badness of `(u₀, u₁)` at `T γ` for an injective `T`, the bad-scalar counts agree. -/
theorem badScalarSet_card_eq_of_reparam {C : Set (ι → A)} {δ : ℝ≥0}
    {u₀ u₁ v₀ v₁ : ι → A} (T : F → F) (hT : Function.Bijective T)
    (h : ∀ γ : F, mcaEvent (F := F) C δ v₀ v₁ γ ↔ mcaEvent (F := F) C δ u₀ u₁ (T γ)) :
    (badScalarSet (F := F) C δ v₀ v₁).card
      = (badScalarSet (F := F) C δ u₀ u₁).card := by
  apply Finset.card_bij (fun γ _ => T γ)
  · intro γ hγ
    rw [mem_badScalarSet] at hγ ⊢
    exact (h γ).mp hγ
  · intro γ₁ _ γ₂ _ himg
    exact hT.injective himg
  · intro γ hγ
    obtain ⟨γ', rfl⟩ := hT.surjective γ
    rw [mem_badScalarSet] at hγ
    exact ⟨γ', mem_badScalarSet.mpr ((h γ').mpr hγ), rfl⟩

open Classical in
/-- The five probe symmetries preserve the bad-scalar **count**: translation. -/
theorem badScalarSet_card_translate (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ v₀ v₁ : ι → A) (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) :
    (badScalarSet (F := F) (C : Set (ι → A)) δ (u₀ + v₀) (u₁ + v₁)).card
      = (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card :=
  badScalarSet_card_eq_of_reparam id Function.bijective_id
    (fun γ => mcaEvent_translate C δ u₀ u₁ v₀ v₁ hv₀ hv₁ γ)

open Classical in
/-- Common scaling preserves the bad-scalar count. -/
theorem badScalarSet_card_smul_pair (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {a : F} (ha : a ≠ 0) (u₀ u₁ : ι → A) :
    (badScalarSet (F := F) (C : Set (ι → A)) δ (a • u₀) (a • u₁)).card
      = (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card :=
  badScalarSet_card_eq_of_reparam id Function.bijective_id
    (fun γ => mcaEvent_smul_pair C δ ha u₀ u₁ γ)

open Classical in
/-- Second-row scaling preserves the bad-scalar count (the bad set is scaled). -/
theorem badScalarSet_card_smul_snd (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {c : F} (hc : c ≠ 0) (u₀ u₁ : ι → A) :
    (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ (c • u₁)).card
      = (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card :=
  badScalarSet_card_eq_of_reparam (fun γ => γ * c)
    ⟨fun _ _ h => mul_right_cancel₀ hc h,
     fun γ => ⟨γ * c⁻¹, by field_simp⟩⟩
    (fun γ => mcaEvent_smul_snd C δ hc u₀ u₁ γ)

open Classical in
/-- Shear preserves the bad-scalar count (the bad set is shifted). -/
theorem badScalarSet_card_shear (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (b : F) (u₀ u₁ : ι → A) :
    (badScalarSet (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁).card
      = (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card :=
  badScalarSet_card_eq_of_reparam (fun γ => b + γ)
    ⟨fun _ _ h => add_left_cancel h, fun γ => ⟨γ - b, by ring⟩⟩
    (fun γ => mcaEvent_shear C δ b u₀ u₁ γ)

open Classical in
/-- Domain permutation preserves the bad-scalar count. -/
theorem badScalarSet_card_domainPerm (C : Set (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) (u₀ u₁ : ι → A) :
    (badScalarSet (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ)).card
      = (badScalarSet (F := F) C δ u₀ u₁).card :=
  badScalarSet_card_eq_of_reparam id Function.bijective_id
    (fun γ => mcaEvent_domainPerm C δ σ hC u₀ u₁ γ)

/-! ## Probability forms and the orbit descent for `epsMCA` -/

open Classical in
/-- The `Pr` form of the counting transports: any stack transformation that preserves the
bad-scalar count preserves the stack's probability term. -/
theorem prob_mcaEvent_eq_of_card_eq {C : Set (ι → A)} {δ : ℝ≥0}
    {u₀ u₁ v₀ v₁ : ι → A}
    (h : (badScalarSet (F := F) C δ v₀ v₁).card
      = (badScalarSet (F := F) C δ u₀ u₁).card) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ v₀ v₁ γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ u₀ u₁ γ] := by
  rw [prob_mcaEvent_eq_badScalarSet_card, prob_mcaEvent_eq_badScalarSet_card, h]

open Classical in
/-- **Orbit descent (the probes' reduction as a theorem).** If a set `R` of stacks meets
every probability fiber — every stack has a representative in `R` with the same bad-event
probability — then the `epsMCA` supremum may be computed over `R` alone. With `R` = orbit
representatives of the equivariance group and the `badScalarSet_card_*` transports supplying
the hypothesis, this is the exact statement of the orbit reduction used by
`probe_epsmca_orbit_exact_n12.py`. -/
theorem epsMCA_eq_biSup_of_cover (C : Set (ι → A)) (δ : ℝ≥0)
    (R : Set (WordStack A (Fin 2) ι))
    (hcover : ∀ u : WordStack A (Fin 2) ι, ∃ r ∈ R,
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ]
        = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (r 0) (r 1) γ]) :
    epsMCA (F := F) C δ
      = ⨆ r ∈ R, Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (r 0) (r 1) γ] := by
  apply le_antisymm
  · unfold epsMCA
    refine iSup_le fun u => ?_
    obtain ⟨r, hrR, heq⟩ := hcover u
    rw [heq]
    exact le_iSup₂ (f := fun r (_ : r ∈ R) =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (r 0) (r 1) γ]) r hrR
  · exact iSup₂_le fun r _ => mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ r

/-! ## The eigenstack orbit law -/

/-- **The eigenstack affine-reparametrization law.** If `C` is stable under the domain
permutation `σ` and `(u₀, u₁)` is a `σ`-eigenstack —
`u₀ ∘ σ = a • u₀ + b • u₁` and `u₁ ∘ σ = c • u₁` with `a, c ≠ 0` — then badness at
`T(γ) = a⁻¹·b + γ·(a⁻¹·c)` is equivalent to badness at `γ`: the bad-scalar set is invariant
under the affine map `T`. -/
theorem mcaEvent_eigenstack_iff (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ (C : Set (ι → A)) ↔ w ∘ σ ∈ (C : Set (ι → A)))
    {u₀ u₁ : ι → A} {a b c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀ + b • u₁) (h₁ : u₁ ∘ σ = c • u₁) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (a⁻¹ * b + γ * (a⁻¹ * c)) ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  have key₀ : a • (u₀ + (a⁻¹ * b) • u₁) = u₀ ∘ σ := by
    rw [h₀, smul_add, smul_smul, mul_inv_cancel_left₀ ha]
  have key₁ : a • ((a⁻¹ * c) • u₁) = u₁ ∘ σ := by
    rw [h₁, smul_smul, mul_inv_cancel_left₀ ha]
  have hac : a⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero ha) hc
  calc mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (a⁻¹ * b + γ * (a⁻¹ * c))
      ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + (a⁻¹ * b) • u₁) u₁ (γ * (a⁻¹ * c)) :=
        (mcaEvent_shear C δ (a⁻¹ * b) u₀ u₁ (γ * (a⁻¹ * c))).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + (a⁻¹ * b) • u₁) ((a⁻¹ * c) • u₁) γ :=
        (mcaEvent_smul_snd C δ hac (u₀ + (a⁻¹ * b) • u₁) u₁ γ).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ
          (a • (u₀ + (a⁻¹ * b) • u₁)) (a • ((a⁻¹ * c) • u₁)) γ :=
        (mcaEvent_smul_pair C δ ha (u₀ + (a⁻¹ * b) • u₁) ((a⁻¹ * c) • u₁) γ).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ ∘ σ) (u₁ ∘ σ) γ := by
        rw [key₀, key₁]
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ :=
        mcaEvent_domainPerm (C : Set (ι → A)) δ σ hC u₀ u₁ γ

/-! ### Orbit arithmetic over the scalar field -/

/-- **Orbit injection.** A finite scalar set invariant under multiplication by a unit `α`
and containing a nonzero element has at least `ord(α)` elements: the whole multiplicative
orbit of that element is inside. -/
theorem orderOf_le_card_of_mul_mem {α : Fˣ} {S : Finset F}
    (hinv : ∀ γ ∈ S, (α : F) * γ ∈ S) {γ₀ : F} (h₀ : γ₀ ∈ S) (hne : γ₀ ≠ 0) :
    orderOf α ≤ S.card := by
  classical
  have hmem : ∀ j : ℕ, ((α : F) ^ j) * γ₀ ∈ S := by
    intro j
    induction j with
    | zero => simpa using h₀
    | succ j ih =>
      have := hinv _ ih
      rwa [← mul_assoc, ← pow_succ'] at this
  have hinj : Set.InjOn (fun j : ℕ => ((α : F) ^ j) * γ₀)
      (Set.Iio (orderOf α)) := by
    intro i hi j hj hij
    have hcancel : ((α : F)) ^ i = ((α : F)) ^ j :=
      mul_right_cancel₀ hne hij
    have hu : (α ^ i : Fˣ) = α ^ j := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact hcancel
    exact pow_injOn_Iio_orderOf hi hj hu
  calc orderOf α
      = ((Finset.range (orderOf α)).image (fun j => ((α : F) ^ j) * γ₀)).card := by
        rw [Finset.card_image_of_injOn (by rwa [Finset.coe_range])]
        rw [Finset.card_range]
    _ ≤ S.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hmem j

/-- **Orbit divisibility.** A finite scalar set invariant under multiplication by a unit `α`
and avoiding `0` has cardinality divisible by `ord(α)`: it is a disjoint union of full
multiplicative orbits. -/
theorem orderOf_dvd_card_of_mul_mem {α : Fˣ} (S : Finset F) :
    (∀ γ ∈ S, (α : F) * γ ∈ S) → (0 : F) ∉ S → orderOf α ∣ S.card := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hinv h0
    rcases S.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
    · simp
    · have hne : γ₀ ≠ 0 := fun h => h0 (h ▸ hγ₀)
      have hd1 : 1 ≤ orderOf α := orderOf_pos α
      have hmem : ∀ j : ℕ, ((α : F) ^ j) * γ₀ ∈ S := by
        intro j
        induction j with
        | zero => simpa using hγ₀
        | succ j ihj =>
          have := hinv _ ihj
          rwa [← mul_assoc, ← pow_succ'] at this
      set d := orderOf α with hd
      set O : Finset F := (Finset.range d).image (fun j => ((α : F) ^ j) * γ₀) with hO
      have hOsub : O ⊆ S := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hmem j
      have hinj : Set.InjOn (fun j : ℕ => ((α : F) ^ j) * γ₀) (Set.Iio d) := by
        intro i hi j hj hij
        have hcancel : ((α : F)) ^ i = ((α : F)) ^ j := mul_right_cancel₀ hne hij
        have hu : (α ^ i : Fˣ) = α ^ j := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
          exact hcancel
        exact pow_injOn_Iio_orderOf hi hj hu
      have hOcard : O.card = d := by
        rw [hO, Finset.card_image_of_injOn (by rwa [Finset.coe_range]),
          Finset.card_range]
      have hONe : O.Nonempty := ⟨γ₀, by
        rw [hO]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hd1, by simp⟩⟩
      have hpow_d : ((α : F)) ^ d = 1 := by
        have := pow_orderOf_eq_one α
        calc ((α : F)) ^ d = ((α ^ d : Fˣ) : F) := by
              rw [Units.val_pow_eq_pow_val]
          _ = ((1 : Fˣ) : F) := by rw [hd, this]
          _ = 1 := Units.val_one
      have hinv' : ∀ γ ∈ S \ O, (α : F) * γ ∈ S \ O := by
        intro γ hγ
        rw [Finset.mem_sdiff] at hγ ⊢
        refine ⟨hinv _ hγ.1, fun hmemO => hγ.2 ?_⟩
        obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hmemO
        rw [Finset.mem_range] at hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · -- α γ = γ₀ ⟹ γ = α^{d-1} γ₀
          simp only [pow_zero, one_mul] at hjeq
          have : γ = ((α : F) ^ (d - 1)) * γ₀ := by
            have hαne : (α : F) ≠ 0 := Units.ne_zero α
            apply mul_left_cancel₀ hαne
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd1, hpow_d, one_mul]
            exact hjeq.symm
          rw [this, hO]
          exact Finset.mem_image.mpr ⟨d - 1, Finset.mem_range.mpr (by omega), rfl⟩
        · -- α γ = α^j γ₀ ⟹ γ = α^{j-1} γ₀
          have : γ = ((α : F) ^ (j - 1)) * γ₀ := by
            have hαne : (α : F) ≠ 0 := Units.ne_zero α
            apply mul_left_cancel₀ hαne
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hjpos]
            exact hjeq.symm
          rw [this, hO]
          exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), rfl⟩
      have h0' : (0 : F) ∉ S \ O := fun h => h0 (Finset.mem_sdiff.mp h).1
      have hss : S \ O ⊂ S := Finset.sdiff_ssubset hOsub hONe
      have hdvd' := ih (S \ O) hss hinv' h0'
      have hcards : S.card = (S \ O).card + d := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hOsub, hOcard]
        have hle := Finset.card_le_card hOsub
        rw [hOcard] at hle
        omega
      rw [hcards]
      exact Nat.dvd_add hdvd' dvd_rfl

/-- **The eigenstack orbit law, lower-propagation form.** For a `σ`-stable submodule code
and a multiplicative `σ`-eigenstack (`u₀ ∘ σ = a • u₀`, `u₁ ∘ σ = c • u₁`, `a, c ≠ 0`),
one bad nonzero scalar forces at least `ord(a⁻¹c)` bad scalars: the entire multiplicative
orbit is bad. This is the mechanism behind the probes' field-independent "flat numerator"
(at the plateau rung the maximizer is an eigenstack with `ord(a⁻¹c) = n`, so the bad count
is at least — and by the budget exactly — `n`, at every field containing the domain). -/
theorem orderOf_le_badScalarSet_card_of_eigenstack
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ (C : Set (ι → A)) ↔ w ∘ σ ∈ (C : Set (ι → A)))
    {u₀ u₁ : ι → A} {a c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀) (h₁ : u₁ ∘ σ = c • u₁)
    {γ₀ : F} (hbad : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ₀) (hne : γ₀ ≠ 0) :
    orderOf (Units.mk0 (a⁻¹ * c) (mul_ne_zero (inv_ne_zero ha) hc))
      ≤ (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card := by
  classical
  have h₀' : u₀ ∘ σ = a • u₀ + (0 : F) • u₁ := by rw [zero_smul, add_zero, h₀]
  refine orderOf_le_card_of_mul_mem (fun γ hγ => ?_) (mem_badScalarSet.mpr hbad) hne
  rw [mem_badScalarSet] at hγ ⊢
  have := (mcaEvent_eigenstack_iff C δ σ hC ha hc h₀' h₁ γ).mpr hγ
  have harith : a⁻¹ * 0 + γ * (a⁻¹ * c) = (Units.mk0 (a⁻¹ * c)
      (mul_ne_zero (inv_ne_zero ha) hc) : F) * γ := by
    rw [Units.val_mk0]
    ring
  rwa [harith] at this

/-- **The eigenstack orbit law, divisibility form.** Under the same hypotheses, if the
scalar `0` is not bad, the bad-scalar count is *exactly divisible* by `ord(a⁻¹c)`: the bad
set is a disjoint union of full multiplicative orbits. Together with the lower-propagation
form this gives the orbit arithmetic `count = ε + (#orbits)·ord(a⁻¹c)` measured by the
exact probes. -/
theorem orderOf_dvd_badScalarSet_card_of_eigenstack
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ (C : Set (ι → A)) ↔ w ∘ σ ∈ (C : Set (ι → A)))
    {u₀ u₁ : ι → A} {a c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀) (h₁ : u₁ ∘ σ = c • u₁)
    (h0bad : ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (0 : F)) :
    orderOf (Units.mk0 (a⁻¹ * c) (mul_ne_zero (inv_ne_zero ha) hc))
      ∣ (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card := by
  classical
  have h₀' : u₀ ∘ σ = a • u₀ + (0 : F) • u₁ := by rw [zero_smul, add_zero, h₀]
  refine orderOf_dvd_card_of_mul_mem _ (fun γ hγ => ?_) ?_
  · rw [mem_badScalarSet] at hγ ⊢
    have := (mcaEvent_eigenstack_iff C δ σ hC ha hc h₀' h₁ γ).mpr hγ
    have harith : a⁻¹ * 0 + γ * (a⁻¹ * c) = (Units.mk0 (a⁻¹ * c)
        (mul_ne_zero (inv_ne_zero ha) hc) : F) * γ := by
      rw [Units.val_mk0]
      ring
    rwa [harith] at this
  · exact fun h => h0bad (mem_badScalarSet.mp h)

/-! ## Demo: the engine at `RS[F₅, F₅*, 2]`

One explicit certificate + the orbit law reproduce the sharp lower bound that
`DeltaStarExactPinF5` assembled from four certificates. -/

namespace DemoF5

open ProximityGap.DeltaStarExactPin

/-- The domain rotation of `F₅* = (1, 2, 4, 3)` (multiplication by the generator `2`),
as the index cycle `i ↦ i + 1` on `Fin 4`. -/
def rot : Equiv.Perm (Fin 4) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by decide
  right_inv := by decide

theorem dom_rot : ∀ i, dom (rot i) = 2 * dom i := by decide

theorem dom_rot_symm : ∀ i, dom (rot.symm i) = 3 * dom i := by decide

/-- `C542` is stable under the domain rotation. -/
theorem C542_rot_stable :
    ∀ w : Fin 4 → F5, w ∈ (C542 : Set (Fin 4 → F5)) ↔
      w ∘ rot ∈ (C542 : Set (Fin 4 → F5)) := by
  intro w
  constructor
  · rintro ⟨A, B, rfl⟩
    refine ⟨A, 2 * B, ?_⟩
    funext i
    show lineEval A B (rot i) = lineEval A (2 * B) i
    simp only [lineEval, dom_rot i]
    ring
  · rintro ⟨A, B, hw⟩
    refine ⟨A, 3 * B, ?_⟩
    funext i
    have := congrFun hw (rot.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    rw [this]
    show lineEval A B (rot.symm i) = lineEval A (3 * B) i
    simp only [lineEval, dom_rot_symm i]
    ring

/-- First demo row: the pure frequency `x³` on the domain `(1,2,4,3)`. -/
def w₀ : Fin 4 → F5 := ![1, 3, 4, 2]

/-- Second demo row: the pure frequency `x²` on the domain `(1,2,4,3)`. -/
def w₁ : Fin 4 → F5 := ![1, 4, 1, 4]

/-- `(w₀, w₁)` is a rotation-eigenstack: `w₀ ∘ rot = 3 • w₀`. -/
theorem w₀_eigen : w₀ ∘ rot = (3 : F5) • w₀ := by decide

/-- `w₁ ∘ rot = 4 • w₁`. -/
theorem w₁_eigen : w₁ ∘ rot = (4 : F5) • w₁ := by decide

/-- The single explicit badness certificate: `γ = 1` is bad for `(w₀, w₁)` at `δ = 1/4`
(witness set `{1,2,3}`, interpolating codeword `4 + 4·X`, second row not explainable). -/
theorem mcaEvent_demo_g1 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) w₀ w₁ (1 : F5) := by
  refine ⟨{1, 2, 3}, card_cond (by decide), ⟨lineEval 4 4, lineEval_mem 4 4, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- **The orbit law in action:** the order of `3⁻¹ * 4 = 3` in `F₅ˣ` is `4`, so the single
certificate propagates to at least `4` bad scalars. -/
theorem badScalarSet_demo_ge_four :
    4 ≤ (badScalarSet (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) w₀ w₁).card := by
  have h := orderOf_le_badScalarSet_card_of_eigenstack C542 (1/4) rot C542_rot_stable
    (a := 3) (c := 4) (by decide) (by decide) w₀_eigen w₁_eigen
    mcaEvent_demo_g1 (by decide)
  have hord : orderOf (Units.mk0 ((3 : F5)⁻¹ * 4)
      (mul_ne_zero (inv_ne_zero (by decide)) (by decide))) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hm0
    rcases m with _ | _ | _ | _ | m
    · omega
    · decide
    · decide
    · decide
    · omega
  rwa [hord] at h

open Classical in
/-- **The R1 lower bound, re-derived by symmetry:** `ε_mca(C542, 1/4) ≥ 4/5` from one
certificate plus the orbit law (versus the four explicit certificates of
`DeltaStarExactPinF5.epsMCA_C542_quarter_ge`). -/
theorem epsMCA_C542_quarter_ge_via_orbit :
    (4 : ℝ≥0∞) / 5 ≤ epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) (1/4) := by
  have hle := badScalarSet_demo_ge_four
  have hbound := mcaEvent_prob_le_epsMCA (F := F5) (A := F5)
    (C542 : Set (Fin 4 → F5)) (1/4) ![w₀, w₁]
  rw [show (![w₀, w₁] : WordStack F5 (Fin 2) (Fin 4)) 0 = w₀ from rfl,
    show (![w₀, w₁] : WordStack F5 (Fin 2) (Fin 4)) 1 = w₁ from rfl,
    prob_mcaEvent_eq_badScalarSet_card] at hbound
  refine le_trans ?_ hbound
  have hF : ((Fintype.card F5 : ℝ≥0) : ℝ≥0∞) = 5 := by
    rw [show Fintype.card F5 = 5 from by simp [ZMod.card]]
    norm_num
  rw [hF]
  gcongr
  exact_mod_cast hle

end DemoF5

/-! ## Source audit -/

#print axioms mcaEvent_translate
#print axioms mcaEvent_smul_pair
#print axioms mcaEvent_smul_snd
#print axioms mcaEvent_shear
#print axioms mcaEvent_domainPerm
#print axioms epsMCA_eq_biSup_of_cover
#print axioms mcaEvent_eigenstack_iff
#print axioms orderOf_le_card_of_mul_mem
#print axioms orderOf_dvd_card_of_mul_mem
#print axioms orderOf_le_badScalarSet_card_of_eigenstack
#print axioms orderOf_dvd_badScalarSet_card_of_eigenstack
#print axioms DemoF5.epsMCA_C542_quarter_ge_via_orbit

end ProximityGap.MCAEquivariance
