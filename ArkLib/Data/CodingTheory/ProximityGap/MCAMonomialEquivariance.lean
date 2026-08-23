/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# Monomial-map equivariance of `mcaEvent`: the diagonal twist the permutation engine misses

Companion to `MCAEquivariance.lean` (#357 hypothesis S3), which proves `mcaEvent` invariance
under codeword translation, scalar scaling, the γ-shift, and **plain domain permutations**
(`mcaEvent_comp_perm_iff`). This file proves the strictly more general **monomial** invariance:
`(M u) i = d i • u (σ i)` for a permutation `σ` and a nonvanishing diagonal `d`, assuming only
that `M` stabilizes the code.

## Why the diagonal matters (probe-verified)

At the exact-pin instance `RS[F₅, (1,2,4,3), 2]` (`DeltaStarExactPinF5.lean`), the
`δ = 1/4` extremal stacks (badCount 4) number exactly 100,000 and split into **two free
orbits** of the plain symmetry group ⟨translation, scaling, γ-shift, rotation⟩
(`scripts/probes/probe_s3_extremal_orbits.py`). The merger is the **twisted inversion**
`u(x) ↦ x·u(1/x)` — coefficient reversal, a GRS-duality move: it is a monomial map (the
permutation `x ↦ x⁻¹` composed with the diagonal `d(x) = x`), it stabilizes the degree-`< 2`
code while the *untwisted* `u ↦ u(1/x)` does not (12,500 measured violations), and adding it
fuses the extremal set into **one orbit of size 100,000 with zero violations**
(`scripts/probes/probe_s3_twisted_inversion_merger.py`). The worst-case stacks of the first
machine-checked exact `δ*` instance are a *single* orbit of the full monomial normalizer —
a structure invisible to the affine/permutation symmetries used everywhere in the literature.

## References

* Issue #357, hypothesis S3 and DISPROOF_LOG entries O135/O136.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAMonomial

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- One direction of the monomial invariance. -/
private theorem mcaEvent_monomial_mp
    (C : Set (ι → A)) (δ : ℝ≥0) (τ : ι ≃ ι) (e : ι → F) (he : ∀ i, e i ≠ 0)
    (hCτ : ∀ w, w ∈ C ↔ (fun i => e i • w (τ i)) ∈ C) (v₀ v₁ : ι → A) (g : F)
    (h : mcaEvent (F := F) C δ (fun i => e i • v₀ (τ i)) (fun i => e i • v₁ (τ i)) g) :
    mcaEvent (F := F) C δ v₀ v₁ g := by
  obtain ⟨S, hS, ⟨w, hw, hagree⟩, hno⟩ := h
  refine ⟨S.map τ.toEmbedding, by rwa [Finset.card_map], ⟨fun j => (e (τ.symm j))⁻¹ • w (τ.symm j), ?_, ?_⟩, ?_⟩
  · -- The pulled-back word is in `C`: its monomial image is `w` itself.
    have himg : (fun i => e i • (fun j => (e (τ.symm j))⁻¹ • w (τ.symm j)) (τ i)) = w := by
      funext i
      simp [smul_smul, mul_inv_cancel₀ (he i)]
    have := hCτ (fun j => (e (τ.symm j))⁻¹ • w (τ.symm j))
    rw [himg] at this
    exact this.mpr hw
  · rintro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    show (e (τ.symm (τ.toEmbedding i)))⁻¹ • w (τ.symm (τ.toEmbedding i)) =
      v₀ (τ.toEmbedding i) + g • v₁ (τ.toEmbedding i)
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    -- `w i = e i • v₀ (τ i) + g • e i • v₁ (τ i)`; cancel the diagonal.
    have hwi' : w i = e i • v₀ (τ i) + g • e i • v₁ (τ i) := hagree i hi
    rw [hwi', smul_add, inv_smul_smul₀ (he i), smul_comm, inv_smul_smul₀ (he i)]
  · rintro ⟨p₀, hp₀, p₁, hp₁, hpair⟩
    refine hno ⟨fun i => e i • p₀ (τ i), (hCτ p₀).mp hp₀,
      fun i => e i • p₁ (τ i), (hCτ p₁).mp hp₁, fun i hi => ?_⟩
    obtain ⟨e₀, e₁⟩ := hpair (τ i) (Finset.mem_map_of_mem τ.toEmbedding hi)
    exact ⟨show e i • p₀ (τ i) = e i • v₀ (τ i) by rw [e₀],
      show e i • p₁ (τ i) = e i • v₁ (τ i) by rw [e₁]⟩

/-- **Monomial-map equivariance of `mcaEvent`.** A monomial transformation
`(M u) i = d i • u (σ i)` — a domain permutation composed with a nonvanishing diagonal —
that stabilizes the code leaves the event invariant. Subsumes `mcaEvent_domain_perm`
(`d = 1`) and covers the *twisted* symmetries of RS codes that plain permutations miss:
e.g. the coefficient-reversing inversion `u(x) ↦ x^{k-1}·u(1/x)` (a GRS-duality move), under
which a degree-`< k` evaluation code is stable while the untwisted `u ↦ u(1/x)` is not. -/
theorem mcaEvent_monomial
    (C : Set (ι → A)) (δ : ℝ≥0) (σ : ι ≃ ι) (d : ι → F) (hd : ∀ i, d i ≠ 0)
    (hC : ∀ w, w ∈ C ↔ (fun i => d i • w (σ i)) ∈ C) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ (fun i => d i • u₀ (σ i)) (fun i => d i • u₁ (σ i)) γ ↔
      mcaEvent (F := F) C δ u₀ u₁ γ := by
  constructor
  · exact mcaEvent_monomial_mp C δ σ d hd hC u₀ u₁ γ
  · intro h
    -- Apply the one-direction lemma to the inverse monomial map.
    have hd' : ∀ j, (d (σ.symm j))⁻¹ ≠ 0 := fun j => inv_ne_zero (hd _)
    have hMM' : ∀ v : ι → A,
        (fun i => d i • (fun j => (d (σ.symm j))⁻¹ • v (σ.symm j)) (σ i)) = v := by
      intro v
      funext i
      simp [smul_smul, mul_inv_cancel₀ (hd i)]
    have hC' : ∀ w, w ∈ C ↔ (fun j => (d (σ.symm j))⁻¹ • w (σ.symm j)) ∈ C := by
      intro w
      have h2 := hC (fun j => (d (σ.symm j))⁻¹ • w (σ.symm j))
      rw [hMM' w] at h2
      exact h2.symm
    have hM'M : ∀ v : ι → A,
        (fun j => (d (σ.symm j))⁻¹ • (fun i => d i • v (σ i)) (σ.symm j)) = v := by
      intro v
      funext j
      simp [smul_smul, inv_mul_cancel₀ (hd (σ.symm j))]
    have h' : mcaEvent (F := F) C δ
        (fun j => (d (σ.symm j))⁻¹ • (fun i => d i • u₀ (σ i)) (σ.symm j))
        (fun j => (d (σ.symm j))⁻¹ • (fun i => d i • u₁ (σ i)) (σ.symm j)) γ := by
      rw [hM'M, hM'M]
      exact h
    exact mcaEvent_monomial_mp C δ σ.symm (fun j => (d (σ.symm j))⁻¹) hd' hC'
      (fun i => d i • u₀ (σ i)) (fun i => d i • u₁ (σ i)) γ h'


/-! ## Source audit -/

#print axioms mcaEvent_monomial

end ProximityGap.MCAMonomial
