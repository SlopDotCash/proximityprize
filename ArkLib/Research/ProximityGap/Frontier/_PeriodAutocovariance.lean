/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Period autocovariance — the spin-glass / Slepian self-comparison NO-GO (N1) (#407/#444)

**Negative guardrail (exotic-math sweep).** This file records the structural reason the
*spin-glass / disorder-comparison* route — Slepian's lemma, the Guerra interpolation, the
Parisi replica-symmetry-breaking comparison — is **circular** for the prize sup-norm
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} ψ(b·x)` (additive character `ψ = e_p`).

## The math (Wiener–Khinchin tautology)

Regard `b ↦ η_b` as a (deterministic) Gaussian-*like* field indexed by the frequency `b ∈ F`.
Every disorder-comparison method (Slepian, Sudakov–Fernique, Guerra, Parisi) is driven by the
**covariance structure** of the field, i.e. by `Cov(η_b, η_{b+d}) = Σ_b η_b · conj(η_{b+d})`.
The Wiener–Khinchin theorem computes that covariance exactly: the autocorrelation of `η` is
`η` itself, up to the field-size factor `q`. Concretely (the theorem in this file):

> `period_autocovariance_eq`:  `Σ_{b∈F} η_b · conj(η_{b+d}) = q · conj(η_d)`.

**Proof.** `η = FT(1_{μ_n})` is the additive-Fourier transform of the subgroup indicator, and
`1_{μ_n}² = 1_{μ_n}` is **idempotent**; the autocorrelation of a Fourier transform is the
Fourier transform of the pointwise square (the convolution theorem), so the autocorrelation of
`η` is `q · FT(1_{μ_n}²) = q · FT(1_{μ_n}) = q · η` (up to the standard conjugation/reflection).
Elementarily: expand both sides as double character sums and apply additive-character
orthogonality `Σ_b ψ(b·x)·conj(ψ((b+d)·y)) = q·[x = y]·conj(ψ(d·y))`, then collapse `x = y`
over `μ_n`. (The `d = 0` case is exactly the in-tree second moment
`SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment`: `Σ_b ‖η_b‖² = q·|G|`.)

## Why this kills the spin-glass / Slepian route (the honest boundary)

Disorder comparison works by dominating one Gaussian field by **another, simpler external
field** with a *known* covariance (an i.i.d. field, a hierarchical Parisi tree, …), then
transferring the sup bound. Here the Wiener–Khinchin identity says the covariance kernel of `η`
**is `η` again** (its own Fourier autocorrelation): there is **no second, external, dominating
field** — the comparison object you would need to import is the prize object itself. So Slepian /
Guerra / Parisi can only *re-express* `M(n)` in terms of its own autocovariance; the comparison
is a **tautology with zero analytic content**. This is the same hypothesis-circularity archetype
the exotic sweep diagnosed for QUE-amplification, autocovariance (`η = autocov`), and the
"no second endomorphism" obstruction: `λ₂ = M`, the autocovariance *is* `η`, and there is no
external field to compare against.

## Honesty (project §6)

This is a **DOCUMENTATION GUARDRAIL**, not a closure. The single theorem
`period_autocovariance_eq` is a **tautology**: it is exact, elementary, and carries **no**
analytic information about the *size* of `M(n)`. It does **NOT** prove `M(n) ≤ C√(n log q)` —
that `L^∞` `√(log)` core (the BGK / Paley-graph wall) is untouched and remains open. The brick
exists solely to record, machine-checked, *why* the disorder-comparison family is structurally
dead for this problem. All theorems are `sorry`-free and axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).

## References
- [Slepian; Sudakov–Fernique] Gaussian comparison inequalities.
- [Guerra; Talagrand; Parisi] spin-glass interpolation / replica symmetry breaking.
- [BGK] Bourgain–Glibichuk–Konyagin — best proven incomplete-character-sum bound (the wall).
- In-tree: `SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment` (the `d = 0` case).
- #407, #444, the exotic-math sweep (spin-glass / Slepian self-comparison, N1).
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ProximityGap.Frontier.PeriodAutocovariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The subgroup Gauss sum (period) at frequency `b`: `η_b = Σ_{x∈G} ψ(b·x)`. Matches the in-tree
`ProximityGap.SubgroupGaussSumSecondMoment.eta`. -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ x ∈ G, ψ (b * x)

/--
**The period autocovariance (Wiener–Khinchin) identity.**

For a primitive additive character `ψ` over a finite field `F` of size `q`, the Fourier
autocorrelation of the period field `η` at shift `d` is `η` itself up to the factor `q`:

> `Σ_{b∈F} η_b · conj(η_{b+d}) = q · conj(η_d)`.

This is the spin-glass / Slepian NO-GO (N1): the covariance kernel that every disorder-comparison
method would need *is `η` again*, so no external dominating field exists and the comparison is
circular. **Tautology, zero analytic content** — it does not bound `M(n)`.

**Proof.** Expand `η_b · conj(η_{b+d})` as a double sum over `(x, y) ∈ G × G`, factor the
character: `ψ(b·x)·conj(ψ((b+d)·y)) = ψ(b·(x−y))·conj(ψ(d·y))`. Sum over `b`: additive-character
orthogonality (`AddChar.sum_mulShift`) collapses `Σ_b ψ(b·(x−y)) = q·[x = y]`. The `x = y` slice
leaves `q·Σ_{y∈G} conj(ψ(d·y)) = q·conj(η_d)`.
-/
theorem period_autocovariance_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (d : F) :
    (∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G (b + d)))
      = (Fintype.card F : ℂ) * (starRingEnd ℂ) (eta ψ G d) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- `conj (ψ a) = ψ (-a)`.
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G (b + d))
      -- expand into a double sum over `(y, x) ∈ G × G`
      = ∑ b : F, ∑ x ∈ G, ∑ y ∈ G, ψ (b * (x - y)) * ψ (-(d * y)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : (starRingEnd ℂ) (eta ψ G (b + d)) = ∑ y ∈ G, ψ (-( (b + d) * y)) := by
          rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj ((b + d) * y))
        have hL : eta ψ G b = ∑ x ∈ G, ψ (b * x) := rfl
        rw [hconjeta, hL, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    -- pull the `b`-sum inward to the orthogonality variable
    _ = ∑ x ∈ G, ∑ y ∈ G, (∑ b : F, ψ (b * (x - y))) * ψ (-(d * y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.sum_mul]
    -- orthogonality: `Σ_b ψ(b·(x−y)) = q·[x = y]`
    _ = ∑ x ∈ G, ∑ y ∈ G, (if x = y then (Fintype.card F : ℂ) else 0) * ψ (-(d * y)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [AddChar.sum_mulShift (x - y) hψ]
        simp [sub_eq_zero]
    -- collapse the `x = y` diagonal
    _ = ∑ y ∈ G, (Fintype.card F : ℂ) * ψ (-(d * y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y hy => ?_)
        rw [← Finset.sum_mul, Finset.sum_ite_eq' G y (fun _ => (Fintype.card F : ℂ))]
        simp [hy]
    -- recognize `q · conj(η_d)`
    _ = (Fintype.card F : ℂ) * (starRingEnd ℂ) (eta ψ G d) := by
        rw [eta, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hconj (d * y)]

/--
**The `d = 0` specialization recovers the second moment.** Setting `d = 0`, the period
autocovariance becomes the exact subgroup Gauss-sum second moment
`Σ_b ‖η_b‖² = q·|G|` (cf. `SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment`).
This is the consistency check that the autocovariance identity is the right generalization:
its diagonal is the in-tree Parseval value, hence the autocovariance carries no more analytic
content than the (already-tautological) second moment. -/
theorem period_autocovariance_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) = (Fintype.card F : ℝ) * G.card := by
  have hkey := period_autocovariance_eq hψ G 0
  -- LHS at `d = 0`: `Σ_b η_b · conj(η_b) = Σ_b ‖η_b‖²` (as a complex number).
  have hlhs : (∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G (b + 0)))
      = ((∑ b : F, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [add_zero, RCLike.mul_conj]
    norm_cast
  -- RHS at `d = 0`: `q · conj(η_0) = q · |G|`.
  have hrhs : (Fintype.card F : ℂ) * (starRingEnd ℂ) (eta ψ G 0)
      = (((Fintype.card F : ℝ) * G.card : ℝ) : ℂ) := by
    have heta0 : eta ψ G 0 = (G.card : ℂ) := by
      rw [eta]
      refine (Finset.sum_congr rfl (fun x _ => by rw [zero_mul, AddChar.map_zero_eq_one])).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [heta0]
    push_cast
    simp
  rw [hlhs] at hkey
  rw [hrhs] at hkey
  exact_mod_cast hkey

end ProximityGap.Frontier.PeriodAutocovariance

/-! ## Axiom audit — kernel-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.Frontier.PeriodAutocovariance.period_autocovariance_eq
#print axioms ProximityGap.Frontier.PeriodAutocovariance.period_autocovariance_secondMoment
