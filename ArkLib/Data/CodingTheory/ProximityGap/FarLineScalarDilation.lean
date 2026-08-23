/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance

/-!
# Scalar-side dilation rescaling of the far-line bad-scalar set (issue #444, R4 lane)

`FarLineIncidenceEquivariance` proved that relabelling a far line by a code automorphism `σ`
(`u₀ ↦ u₀ ∘ σ`, `u₁ ↦ u₁ ∘ σ`) leaves the bad-scalar set `explainableScalars C δ u₀ u₁`
**unchanged**. For Reed–Solomon on `μ_n`, the dilations `x ↦ g·x` (`g ∈ μ_n`) are such
automorphisms, so the set has the full `Z/n` cyclic symmetry *as a relabelling of the line*.

This file supplies the **complementary, scalar-side** structural fact that the §1.5 ground-truth
pivot's R4 GAP names but that was not in tree: how the dilation acts on the **scalar `γ` itself**.

Over a **linear** code `C` (`Submodule F (ι → A)` — every RS code is one) the bad-scalar set is
**scale-homogeneous in the line's coefficients**: rescaling the offset `u₀ ↦ c₀ • u₀` and the
direction `u₁ ↦ c₁ • u₁` by nonzero field constants rescales the bad set by the single factor
`c₁ / c₀`:

  `γ ∈ explainableScalars C δ (c₀•u₀) (c₁•u₁) ⟺ (c₀⁻¹*c₁)•γ ∈ explainableScalars C δ u₀ u₁`.

Mechanism (no moment, no count): if `w` agrees with the rescaled line on `S`,
`w i = c₀ • u₀ i + γ • (c₁ • u₁ i) = c₀ • (u₀ i + ((c₀⁻¹*c₁) • γ) • u₁ i)`, so `c₀⁻¹ • w`
(again in `C`, by `Submodule.smul_mem`) agrees with the *original* line at scalar `(c₀⁻¹*c₁)·γ`.
Linearity of `C` is **essential**: the rescaling pushes the witnessing codeword through the
`c₀⁻¹` scaling, which only stays in `C` because `C` is a subspace.

## The headline coset consequence (the structure the R4 GAP needs)

Specialize to a **monomial** RS line on `μ_n`: offset `u₀ = x^B`, direction `u₁ = x^A`. The
dilation `σ : x ↦ g·x` (`g ∈ μ_n`) is a code automorphism (`explainableScalars_rs_rotate`), and
on monomials `(x^B) ∘ σ = g^B • x^B`, `(x^A) ∘ σ = g^A • x^A`. Chaining the automorphism
invariance (the *set is unchanged under relabelling*) with this scalar-homogeneity (the relabelling
*equals* a `c₁/c₀ = g^{A−B}` rescaling) gives the **scalar dilation invariance**

  `multiplication by g^{A−B}` (every `g ∈ μ_n`) maps the bad-scalar set onto itself,

i.e. the bad set is a **union of `⟨g^{A−B} : g ∈ μ_n⟩ = μ_{n / gcd(A−B, n)}`-cosets** — exactly the
`q`-independent cyclotomic coset structure the §R4 GAP attributes to the dilation
`γ_S ↦ g^{b−a} γ_S`. The *forcing* (this invariance) is now an axiom-clean theorem; the residual
*rigidity* (why all consistent witnesses collapse to `O(1)` cosets) remains open. Honest scope: this
is the **structural lever** (the symmetry group of the bad set), NOT a magnitude/`O(n)` bound — it
does not by itself close CORE.

PROBE: `scripts/probes/probe_scalar_dilation_coset.py` — exact brute-force list-decode over THIN
PROPER `μ_n = 2^a` (`(p−1)/n ≥ 2`, never `n = q−1`), monomial directions, multiple primes incl.
Fermat-type: the bad set is multiplication-invariant under `g^{A−B}` and a union of `μ_{n'}`-cosets
in **9/9** cases (non-vacuous in 8/9).

All results are `sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Issue #444, §R4 (the symmetric-function / coset-rigidity route).
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **One direction of the scalar-rescaling homogeneity.** Over a *linear* code `C`
(`Submodule F (ι → F)`), if `γ` is bad for the rescaled line `(c₀ • u₀, c₁ • u₁)` with `c₀ ≠ 0`,
then `(c₀⁻¹ * c₁) • γ` is bad for the original line `(u₀, u₁)`: scale the witnessing codeword by
`c₀⁻¹` (still in `C` by `Submodule.smul_mem`) and factor `c₀` out of the agreement equation. -/
theorem explainableScalars_smul_line_subset
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F} (hc₀ : c₀ ≠ 0) :
    ∀ γ ∈ explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ (c₀ • u₀) (c₁ • u₁),
      (c₀⁻¹ * c₁ * γ) ∈ explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ u₀ u₁ := by
  classical
  intro γ hγ
  simp only [explainableScalars, mem_filter, mem_univ, true_and] at hγ ⊢
  obtain ⟨S, hsz, w, hwC, hw⟩ := hγ
  refine ⟨S, hsz, c₀⁻¹ • w, C.smul_mem c₀⁻¹ hwC, ?_⟩
  intro i hi
  have hwi := hw i hi
  -- hwi : w i = c₀ • u₀ i + γ • (c₁ • u₁ i)
  simp only [Pi.smul_apply, smul_eq_mul] at hwi ⊢
  -- goal : c₀⁻¹ * w i = u₀ i + (c₀⁻¹ * c₁ * γ) * u₁ i
  rw [hwi]
  field_simp

/-- **Scalar-rescaling homogeneity of the far-line bad-scalar set (the structural brick).** Over a
linear code `C`, rescaling the offset and direction of a far line by nonzero constants `c₀, c₁`
rescales the bad-scalar set by the single factor `c₁ / c₀`:

  `γ ∈ explainableScalars C δ (c₀•u₀) (c₁•u₁) ↔ (c₀⁻¹*c₁)•γ ∈ explainableScalars C δ u₀ u₁`.

The reverse direction is the forward lemma applied to the inverse rescaling `(c₀⁻¹, c₁⁻¹)` after
cancelling `c₀⁻¹ • (c₀ • u₀) = u₀`. Linearity of `C` is essential (the codeword is scaled by
`c₀⁻¹`). -/
theorem explainableScalars_smul_line
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F}
    (hc₀ : c₀ ≠ 0) (_hc₁ : c₁ ≠ 0) (γ : F) :
    γ ∈ explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ (c₀ • u₀) (c₁ • u₁)
      ↔ (c₀⁻¹ * c₁ * γ) ∈ explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ u₀ u₁ := by
  classical
  constructor
  · intro hγ
    exact explainableScalars_smul_line_subset C δ u₀ u₁ hc₀ γ hγ
  · -- reverse direction, by a direct witness construction (mirror of the forward lemma):
    -- if δ := c₀⁻¹*c₁*γ is bad for (u₀,u₁) via codeword w, then c₀ • w witnesses γ for the
    -- rescaled line, since c₀ • (u₀ i + δ • u₁ i) = c₀ • u₀ i + γ • (c₁ • u₁ i).
    intro hγ
    simp only [explainableScalars, mem_filter, mem_univ, true_and] at hγ ⊢
    obtain ⟨S, hsz, w, hwC, hw⟩ := hγ
    refine ⟨S, hsz, c₀ • w, C.smul_mem c₀ hwC, ?_⟩
    intro i hi
    have hwi := hw i hi
    simp only [Pi.smul_apply, smul_eq_mul] at hwi ⊢
    -- goal : c₀ * w i = c₀ * u₀ i + γ * (c₁ * u₁ i)
    rw [hwi]
    field_simp

/-- **Equal-scaling invariance.** When the offset and direction are rescaled by the *same* nonzero
constant `c` (e.g. a global dilation of a proportional line), the bad-scalar set is literally
**fixed** (`c₁/c₀ = 1`). The cleanest special case of `explainableScalars_smul_line`. -/
theorem explainableScalars_smul_line_eq
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c : F} (hc : c ≠ 0) :
    explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ (c • u₀) (c • u₁)
      = explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ u₀ u₁ := by
  classical
  ext γ
  have h := explainableScalars_smul_line C δ u₀ u₁ hc hc γ
  have hscal : c⁻¹ * c * γ = γ := by
    rw [inv_mul_cancel₀ hc, one_mul]
  rwa [hscal] at h

/-- **The headline coset brick: scalar-dilation invariance of the RS far-line bad-scalar set.**
Combine the *relabelling* invariance (`explainableScalars_rs_rotate`: dilating the domain by `g`
fixes the bad set) with the *scalar-homogeneity* (`explainableScalars_smul_line`: rescaling the
line's coefficients by `(c₀,c₁)` rescales the scalar by `c₁/c₀`).

Hypotheses `hu₀`/`hu₁` record that the dilation `σ` rescales the offset and direction by field
constants `c₀, c₁` — exactly what a **monomial** line does on `μ_n`: for `u₀ = x^B`, `u₁ = x^A`
and `σ : x ↦ g·x`, one has `u₀ ∘ σ = g^B • u₀` and `u₁ ∘ σ = g^A • u₁`, so `c₀ = g^B`, `c₁ = g^A`
and the rescaling factor is `c₀⁻¹·c₁ = g^{A−B}`. The conclusion is that **multiplication by
`c₀⁻¹·c₁` maps the bad-scalar set onto itself**:

  `γ ∈ explainableScalars RS δ u₀ u₁  ↔  (c₀⁻¹·c₁)·γ ∈ explainableScalars RS δ u₀ u₁`.

Iterating over all `g ∈ μ_n` gives invariance under the multiplicative group
`⟨g^{A−B} : g ∈ μ_n⟩ = μ_{n/gcd(A−B,n)}`, so the bad set is a **union of `μ_{n'}`-cosets** — the
`q`-independent cyclotomic coset structure the §R4 GAP names. (This theorem proves the *forcing*;
the `O(n)`-coset *rigidity bound* remains open.) -/
theorem explainableScalars_rs_scalar_dilation
    (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F) (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hu₀ : u₀ ∘ σ = c₀ • u₀) (hu₁ : u₁ ∘ σ = c₁ • u₁) (γ : F) :
    (γ ∈ explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁
      ↔ (c₀⁻¹ * c₁ * γ) ∈ explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁) := by
  classical
  -- relabelling by σ fixes the set, and on a monomial line equals the (c₀,c₁)-rescaling
  have hrot := explainableScalars_rs_rotate (F := F) domain k σ g hg0 hg δ u₀ u₁
  -- rewrite the relabelled line via the monomial composition hypotheses
  rw [hu₀, hu₁] at hrot
  -- hrot : explainableScalars RS δ (c₀•u₀) (c₁•u₁) = explainableScalars RS δ u₀ u₁
  -- so γ bad for original ↔ γ bad for the rescaled line ↔ (c₀⁻¹c₁γ) bad for original
  have hhom := explainableScalars_smul_line (ReedSolomon.code domain k) δ u₀ u₁ hc₀ hc₁ γ
  rw [hrot] at hhom
  exact hhom

/-- **Iterated coset closure (the explicit union-of-cosets statement).** From the single-step
scalar-dilation invariance (`explainableScalars_rs_scalar_dilation`: the bad set is fixed by
multiplication by `m := c₀⁻¹·c₁ = g^{A−B}`), the bad-scalar set is fixed by **every power** `mʲ`:

  `γ ∈ explainableScalars RS δ u₀ u₁  ↔  mʲ·γ ∈ explainableScalars RS δ u₀ u₁`   for all `j`.

Proof by induction on `j` chaining the single step. Consequently the bad set is invariant under the
whole multiplicative cyclic group `⟨m⟩` it generates, i.e. it is a genuine **union of `⟨m⟩`-cosets**
(each orbit `{mʲ·γ}` lies fully in or fully out). For a monomial RS line on `μ_n`, `m = g^{A−B}` and
`⟨m⟩` runs over `μ_{n/gcd(A−B,n)}` as `g` ranges over `μ_n`, giving the cyclotomic coset structure
explicitly. (Still the *forcing*; the `O(n)`-coset rigidity magnitude remains open.) -/
theorem explainableScalars_rs_scalar_dilation_pow
    (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F) (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hu₀ : u₀ ∘ σ = c₀ • u₀) (hu₁ : u₁ ∘ σ = c₁ • u₁) (j : ℕ) (γ : F) :
    (γ ∈ explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁
      ↔ ((c₀⁻¹ * c₁) ^ j * γ) ∈ explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁) := by
  classical
  induction j with
  | zero => simp
  | succ n ih =>
    -- step: invariance under one more multiplication by m = c₀⁻¹*c₁
    have hstep := explainableScalars_rs_scalar_dilation domain k σ g hg0 hg δ u₀ u₁ hc₀ hc₁
      hu₀ hu₁ ((c₀⁻¹ * c₁) ^ n * γ)
    rw [ih, hstep]
    -- reconcile the scalar: c₀⁻¹*c₁*((c₀⁻¹*c₁)^n*γ) = (c₀⁻¹*c₁)^(n+1)*γ
    have : c₀⁻¹ * c₁ * ((c₀⁻¹ * c₁) ^ n * γ) = (c₀⁻¹ * c₁) ^ (n + 1) * γ := by
      rw [pow_succ]; ring
    rw [this]

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_smul_line_subset
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_smul_line
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_smul_line_eq
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_rs_scalar_dilation
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_rs_scalar_dilation_pow
