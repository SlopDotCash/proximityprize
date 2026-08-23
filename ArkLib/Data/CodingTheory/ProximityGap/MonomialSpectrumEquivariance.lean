/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# Monomial spectrum equivariance (#371): the bad set is μ_n-multiplicatively closed

The equivariance half of the **SPECTRUM = DOMAIN law**
(`probe_wb_spectrum_norm_invariant.py`: the interior bad-scalar spectrum of the
monomial adversary is exactly the domain subgroup `μ_n ∪ {0}`, with norm
invariant `γⁿ = 1` at every tested `(a, w, j)`).

For the monomial stack `(x^a, x^{a−1})` on a rotation-closed domain
(`domain (σ i) = g · domain i`), composing three in-tree equivariances —
domain rotation (`mcaEvent_rs_rotate`), whole-stack scaling
(`mcaEvent_smul_both`), and direction-row scaling (`mcaEvent_smul_right`) —
gives

  `mcaEvent (x^a, x^{a−1}) γ  ⟺  mcaEvent (x^a, x^{a−1}) (γ · g⁻¹)`

so the bad set is closed under multiplication by the rotation subgroup: it is a
union of `μ_n`-cosets of `F*` (plus possibly `0`).  The remaining (deep) half of
the law — that the only coset below the capacity cliff is the trivial one,
mechanism: `γ ∈ −μ_n` ⟺ the line `x^{a−1}(x+γ)` has a domain root — is the
named next target.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.MonomialSpectrum

open ProximityGap.MCAEquivariance

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Monomial rotation equivariance**: for the monomial stack on a
rotation-closed domain, the MCA event at `γ` is equivalent to the MCA event at
`γ · g⁻¹`.  Hence the bad set is `⟨g⟩`-multiplicatively closed. -/
theorem monomial_mcaEvent_rotate (domain : Fin n ↪ F) (k : ℕ)
    (σ : Equiv.Perm (Fin n)) {g : F} (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    {a : ℕ} (ha : 1 ≤ a) {u₀ u₁ : Fin n → F}
    (hu₀ : ∀ i, u₀ i = (domain i) ^ a)
    (hu₁ : ∀ i, u₁ i = (domain i) ^ (a - 1))
    (δ : ℝ≥0) (γ : F) :
    mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ u₀ u₁ γ ↔
      mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ u₀ u₁
        (γ * g⁻¹) := by
  have hga : g ^ a ≠ 0 := pow_ne_zero _ hg0
  -- the rotated rows are scalar multiples of the rows
  have hrot₀ : u₀ ∘ ⇑σ = (g ^ a) • u₀ := by
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hu₀ (σ i), hu₀ i, hg i, mul_pow]
  have hrot₁ : u₁ ∘ ⇑σ = (g ^ a) • (g⁻¹ • u₁) := by
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hu₁ (σ i), hu₁ i, hg i, mul_pow, ← mul_assoc]
    congr 1
    -- g^(a−1) = g⁻¹ · g^a
    rw [show g ^ a = g * g ^ (a - 1) from by
        rw [← pow_succ']
        congr 1
        omega,
      mul_comm g (g ^ (a - 1)), mul_assoc, mul_inv_cancel₀ hg0, mul_one]
  calc mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ u₀ u₁ γ
      ↔ mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ
          (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ :=
        (mcaEvent_rs_rotate domain k σ g hg0 hg δ γ u₀ u₁).symm
    _ ↔ mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ
          ((g ^ a) • u₀) ((g ^ a) • (g⁻¹ • u₁)) γ := by
        rw [hrot₀, hrot₁]
    _ ↔ mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ
          u₀ (g⁻¹ • u₁) γ :=
        mcaEvent_smul_both (ReedSolomon.code domain k) hga γ
    _ ↔ mcaEvent (F := F) (ReedSolomon.code domain k : Set (Fin n → F)) δ
          u₀ u₁ (γ * g⁻¹) :=
        mcaEvent_smul_right (ReedSolomon.code domain k) (inv_ne_zero hg0) γ

open Classical in
/-- **The spectrum closure**: the monomial bad set is invariant under
multiplication by the rotation scalar — the bad set is a union of
`⟨g⟩`-multiplicative cosets (the formal equivariance half of the
SPECTRUM = DOMAIN law). -/
theorem monomial_badSet_mul_invariant (domain : Fin n ↪ F) (k : ℕ)
    (σ : Equiv.Perm (Fin n)) {g : F} (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    {a : ℕ} (ha : 1 ≤ a) {u₀ u₁ : Fin n → F}
    (hu₀ : ∀ i, u₀ i = (domain i) ^ a)
    (hu₁ : ∀ i, u₁ i = (domain i) ^ (a - 1)) (δ : ℝ≥0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        (ReedSolomon.code domain k : Set (Fin n → F)) δ u₀ u₁ γ)).image (· * g)
      = Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          (ReedSolomon.code domain k : Set (Fin n → F)) δ u₀ u₁ γ) := by
  ext γ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨γ', hbad, rfl⟩
    have := (monomial_mcaEvent_rotate domain k σ hg0 hg ha hu₀ hu₁ δ
      (γ' * g)).mpr
    rw [mul_assoc, mul_inv_cancel₀ hg0, mul_one] at this
    exact this hbad
  · intro hbad
    refine ⟨γ * g⁻¹, ?_, by rw [mul_assoc, inv_mul_cancel₀ hg0, mul_one]⟩
    exact (monomial_mcaEvent_rotate domain k σ hg0 hg ha hu₀ hu₁ δ γ).mp hbad

end ProximityGap.MonomialSpectrum

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialSpectrum.monomial_mcaEvent_rotate
#print axioms ProximityGap.MonomialSpectrum.monomial_badSet_mul_invariant
