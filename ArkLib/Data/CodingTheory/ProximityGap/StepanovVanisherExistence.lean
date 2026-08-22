/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The Stepanov vanisher-existence engine (Issue #232, Stepanov route to the Weil bound)

Stepanov's method bounds the number of rational points of a curve over `𝔽_q` by exhibiting a
*nonzero auxiliary polynomial* `Ψ` of controlled degree that vanishes to high order at every
rational point; the counting engine (`StepanovPointCountEngine.lean`) then turns
`|points|·M ≤ deg Ψ` into a point bound, and the Hasse-multiplicity bridge
(`HasseMultiplicityBridge.lean`) certifies the high-order vanishing from Hasse-derivative data.

The single mathematically substantive *existence* step — "such a `Ψ` exists" — is what this file
proves, in its honest abstract form. Stepanov's `Ψ` is sought inside a **special finite-dimensional
family** of generators `g₁,…,g_U` (e.g. `x^i·f(x)^j` reduced modulo the Frobenius relation
`x^q = x`), subject to `L` homogeneous **linear** vanishing conditions (each Hasse-derivative
evaluation is linear in the coefficients). Whenever the number of free coefficients exceeds the
number of conditions (`L < U`), elementary linear algebra forces a nonzero solution; linear
independence of the generators makes the resulting combination a genuine nonzero polynomial, and the
generators' degree bound controls `deg Ψ`.

## Main results (all `sorry`-free; axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `exists_nonzero_vanishing_combination` — **the existence engine** (over any `F`-module `M`): a
  linearly independent family `g : ι → M` and a linear constraint map `Φ : (ι → F) →ₗ (κ → F)` with
  `#κ < #ι` admit a coefficient vector `c ≠ 0` (hence a nonzero combination `∑ cᵢ·gᵢ`) with `Φ c = 0`.
  Pure rank–nullity (`LinearMap.ker_ne_bot_of_finrank_lt`).
* `degree_combination_le` — a combination of generators each of degree `≤ B` has degree `≤ B`.
* `exists_stepanov_vanisher` — the packaged Stepanov vanisher: from linearly independent polynomial
  generators of degree `≤ B`, a constraint map `Φ`, and `#κ < #ι`, there is a **nonzero `Ψ` of
  degree `≤ B`** that is a `Φ`-vanishing combination. This is the existence half of Stepanov's
  auxiliary; the *construction* of `g`, `B`, `Φ` so that `Φ`-vanishing forces high multiplicity at
  the rational points (with `#κ` and `B` both `√q`-scale) is the residual hard step, deliberately
  left to the caller.

## Honest scope

This is the genuinely-provable existence core of the Stepanov auxiliary — **not** the construction.
It does not by itself beat the trivial `|V|·M ≤ deg` barrier: the `√q` saving comes only when the
caller chooses `g` (the Frobenius-reduced special form) and `Φ` (the Hasse conditions) so that
`#κ < #ι` *with* `B` small — that combinatorial/degree bookkeeping is the open part. No Weil /
RH-for-curves bound is proven here, and #232 stays an open tracker (`advancesOpenCore = false`).
-/

open Polynomial Module Finset

namespace ArkLib.CodingTheory.StepanovVanisher

variable {F : Type*} [Field F]

/-- **The Stepanov existence engine.** A linearly independent family `g : ι → M` over a field `F`,
together with *any* `F`-linear constraint map `Φ : (ι → F) →ₗ[F] (κ → F)` having strictly fewer
output coordinates than generators (`#κ < #ι`), admits a nonzero coefficient vector `c` in the
kernel of `Φ`; by linear independence the combination `∑ᵢ cᵢ • gᵢ` is then a **nonzero** element of
`M` satisfying all `#κ` linear constraints. Pure rank–nullity. -/
theorem exists_nonzero_vanishing_combination
    {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommGroup M] [Module F M]
    (g : ι → M) (hg : LinearIndependent F g) (Φ : (ι → F) →ₗ[F] (κ → F))
    (hlt : Fintype.card κ < Fintype.card ι) :
    ∃ c : ι → F, (∑ i, c i • g i) ≠ 0 ∧ Φ c = 0 := by
  have hdim : Module.finrank F (κ → F) < Module.finrank F (ι → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]; exact hlt
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨c, ?_, by simpa only [LinearMap.mem_ker] using hc_mem⟩
  intro hcombo
  exact hc_ne (funext (Fintype.linearIndependent_iff.mp hg c hcombo))

/-- A linear combination of polynomial generators each of degree `≤ B` has degree `≤ B`. -/
theorem degree_combination_le {ι : Type*} [Fintype ι] (g : ι → F[X]) (c : ι → F) {B : ℕ}
    (hB : ∀ i, (g i).degree ≤ (B : WithBot ℕ)) :
    (∑ i, c i • g i).degree ≤ (B : WithBot ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i _
  exact (Polynomial.degree_smul_le _ _).trans (hB i)

/-- **The Stepanov vanisher exists, with degree control.** Given linearly independent polynomial
generators `g : ι → F[X]` each of degree `≤ B`, an `F`-linear constraint map `Φ : (ι → F) →ₗ (κ → F)`,
and `#κ < #ι`, there is a **nonzero** `Ψ : F[X]` of degree `≤ B` that is a `Φ`-vanishing combination
of the generators. This is the existence half of the Stepanov auxiliary polynomial. The caller
supplies the (hard) construction: a generator family and constraint map for which `Φ`-vanishing
entails high-multiplicity vanishing at the `𝔽_q`-rational points, with `#κ`, `B` of `√q` scale. -/
theorem exists_stepanov_vanisher {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → F[X]) (hg : LinearIndependent F g) {B : ℕ}
    (hB : ∀ i, (g i).degree ≤ (B : WithBot ℕ))
    (Φ : (ι → F) →ₗ[F] (κ → F)) (hlt : Fintype.card κ < Fintype.card ι) :
    ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ.degree ≤ (B : WithBot ℕ) ∧ ∃ c : ι → F, Ψ = ∑ i, c i • g i ∧ Φ c = 0 := by
  obtain ⟨c, hne, hΦ⟩ := exists_nonzero_vanishing_combination g hg Φ hlt
  exact ⟨∑ i, c i • g i, hne, degree_combination_le g c hB, c, rfl, hΦ⟩

end ArkLib.CodingTheory.StepanovVanisher

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.CodingTheory.StepanovVanisher
#print axioms exists_nonzero_vanishing_combination
#print axioms degree_combination_le
#print axioms exists_stepanov_vanisher
end AxiomAudit
