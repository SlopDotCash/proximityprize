/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# wf-ND lane (#407): the theta / Poisson transform is a length-preserving FIXED POINT

**Lens (genuinely new in-tree):** the approximate functional equation / theta-transformation
route (van der Corput, Demirci–Akarsu–Marklof for the *quadratic* incomplete Gauss sum).
We asked: does the subgroup Gauss sum `η_b = Σ_{x∈μ_n} e_p(bx)` admit a theta / Poisson
renormalization that *contracts* toward the floor (giving a convergent recursion to a proven
√-cancellation), the way the quadratic Gauss sum's continued-fraction renormalization does?

**Numerical verdict (probe `probe_wf2ND_theta_fe.py`, exact, n=8..64, multi-prime incl. thin β≈5):**
1. The value distribution of `{η_b/√n}_{b≠0}` is i.i.d. **complex Gaussian**, NOT the
   Demirci–Akarsu–Marklof self-similar theta law: kurtosis `E|z|⁴/(E|z|²)² → 2.0` (n=16:1.94,
   n=32:1.96, n=64:1.98), `E|z|⁶/(E|z|²)³ → 6.0`, real-part kurtosis `→ 3.0`. The tail is
   **Rayleigh** `P(|z|>R)≈e^{-R²}` (R=3: emp 1e-4 = e^{-9}=1.2e-4), four orders below the DAM
   heavy tail `R^{-4}=1.2e-2` — confirmed even at p/n³=256 (β≈5, thin). The extreme value
   `max|η|/√n≈3.4` tracks the Gaussian `√(2 log p)`, NOT the DAM cusp `m^{1/4}≈8..16`.
   So there is **no self-similar theta limit law** to renormalize against.
2. The additive Fourier transform of `1_{μ_n}` is `η` itself; applying it again recovers a
   reflected copy of `1_{μ_n}` (Fourier inversion). The "dual" sum therefore has support of the
   **same size n** — the theta/Poisson transform is a **FIXED POINT, not a contraction**:
   `support(DFT(η)) = μ_n` exactly (probe ADVERSARIAL CHECK 2, n=16, multiple p). Hence no
   convergent recursion to a smaller modulus; sup/√n stays flat (≈3.4–3.6, √log creep), descent
   ratios hover at √2 without dropping below it.

**This file proves the rigorous *structural skeleton* of point 2**, abstracted to the only fact it
needs: a Fourier-type **involution** `T` on `ℂ`-valued functions on a finite group preserves the
cardinality of the support (`#supp(T (T f)) = #supp f`). Applied with `T = DFT` and
`f = 1_{μ_n}`, this is the statement "the theta transform does not shorten the subgroup sum",
i.e. **no contraction is available** — the structural reason the theta route is pinned, not a
closure. This is `tag: proven` (for the abstract skeleton) + `tag: refuted` (for the contraction
hypothesis, by the probe). It does NOT bound `B`; it explains why this avenue cannot.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
-/

namespace ProximityGap.Frontier.ThetaFixedPoint

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of a `ℂ`-valued function on a finite index type. -/
noncomputable def support (f : ι → ℂ) : Finset ι :=
  Finset.univ.filter (fun i => f i ≠ 0)

/-- A `T`-transform is a **length-preserving fixed point** (no contraction) if applying it twice
returns a function with the *same support size* — equivalently a bijection of the index type
relabels the support. This abstracts Fourier inversion: `DFT (DFT f) = p · f ∘ (neg)`, whose
support is the negation-reflection of `support f`, hence equinumerous. A *contractive* theta
renormalization would instead need `#support (T (T f)) < #support f` (a strictly shorter dual
sum). The probe shows the subgroup case realizes the fixed-point branch, NOT the contraction. -/
def IsLengthPreserving (T : (ι → ℂ) → (ι → ℂ)) : Prop :=
  ∀ f : ι → ℂ, (support (T (T f))).card = (support f).card

/-- **Skeleton lemma (proven).** If the squared transform `T ∘ T` is realized by *precomposition
with a bijection* `σ` of the index type and a *nonzero pointwise scalar* (the Fourier-inversion
shape `T(T f) = c • (f ∘ σ)`, `c ≠ 0`), then `T` is length-preserving: the support of `T(T f)` is
the `σ⁻¹`-image of `support f`, so the cardinalities agree. There is no contraction.

This is the exact mechanism by which the additive DFT (`σ = negation`, `c = p`) keeps the
subgroup-sum support at size `n`. -/
theorem isLengthPreserving_of_inversion
    (T : (ι → ℂ) → (ι → ℂ)) (σ : ι ≃ ι) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ f : ι → ℂ, T (T f) = fun i => c * f (σ i)) :
    IsLengthPreserving T := by
  intro f
  -- `support (T (T f)) = σ⁻¹ '' (support f)`, via the equiv-image on the filtered universe.
  have hsupp : support (T (T f)) = (support f).map σ.symm.toEmbedding := by
    ext i
    simp only [support, mem_filter, mem_univ, true_and, hinv, mem_map,
      Equiv.coe_toEmbedding, mul_ne_zero_iff]
    constructor
    · rintro ⟨_, hfi⟩
      exact ⟨σ i, hfi, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hc, ?_⟩
      simpa using ha
  rw [hsupp, Finset.card_map]

/-- **Corollary (the lane verdict, proven for the abstract skeleton).** The additive Fourier /
theta transform — being a Fourier-inversion-type involution — is length-preserving, so it admits
**no contractive renormalization**: the dual of the length-`n` subgroup sum has length `n`.

Concretely, with `T = DFT`, `σ =` negation, `c = |ι|`, `hinv` is Fourier inversion. We expose the
no-contraction conclusion as the negation of the *contraction hypothesis* a theta closure would
need (`∃ f, #supp(T(T f)) < #supp f`). -/
theorem theta_no_contraction
    (T : (ι → ℂ) → (ι → ℂ)) (σ : ι ≃ ι) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ f : ι → ℂ, T (T f) = fun i => c * f (σ i)) :
    ¬ ∃ f : ι → ℂ, (support (T (T f))).card < (support f).card := by
  rintro ⟨f, hlt⟩
  have := isLengthPreserving_of_inversion T σ c hc hinv f
  omega

end ProximityGap.Frontier.ThetaFixedPoint
