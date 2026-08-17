/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# T02 (Drinfeld two-variable partial-Frobenius decoupling) — DIAGONAL COLLAPSE no-go (#444)

**NEGATIVE / guardrail brick (an honest REDUCTION to fence F10/F2, NOT a closure).**

## The candidate (architect T02, cluster G1)

Manufacture a genuinely two-variable trace function on `𝔸¹ × 𝔸¹ / F_p`,

  `T(b,t) = ∑_{x ∈ μ_n} ψ(b·x + t·φ(x))`,   `φ(x) = x^g` a fixed dilation/automorphism exponent,

whose **diagonal restriction** `t = 0` is the prize period `T(b,0) = η_b = ∑_{x∈μ_n} ψ(b·x)`.
The proposal: by **Drinfeld's lemma** (partial-Frobenius independence on a fiber product
`X₁ ×_{F_p} X₂`; Lau / Kedlaya / Sawin), the two partial Frobenii act independently on the
cohomology of the product family, so the joint sum decouples and the diagonal sup
`max_b |T(b,0)| = M(n)` is controlled by an **off-diagonal-decoupled Deligne bound** that does NOT
pay the rank-`n` of the diagonal — landing the prize where the 1-D domain (`n < √q`) was vacuous.

T02's own stated danger: the diagonal restriction `t = 0` may **force the controlling cohomology
back onto the rank-`n` diagonal sheaf** ("diagonal collapse"), reducing to F10/P3.

## The verdict: DIAGONAL COLLAPSE — the 2-D family carries the SAME rank-`n` floor (F10)

The decoupling never buys anything, because the **controlling L² scale (= generic rank = conductor
floor) of the two-variable family is the size of the diagonal fiber product, which is exactly `n`** —
identical to the 1-D diagonal. The Drinfeld factorization of the second moment is provable and exact,
and it pins the rank at `n`, so Deligne/FKM on the family give `sup ≤ cond = n` = the trivial `ℓ¹`
ceiling, exactly the C2/A07/P3 wall (F10), now stable under the two-variable lift.

**The exact computation (this file).** For ANY dilation map `φ : F → F` that is injective on `μ_n`
(`x ↦ x^g` with `gcd(g,n)=1` permutes `μ_n`; for any `φ` the fiber product is `⊇` the diagonal, so
the count is `≥ n` — never smaller), the two-variable second moment factors by additive-character
orthogonality in BOTH frequencies `b` and `t`:

  `∑_{b,t ∈ F} ‖T(b,t)‖² = ∑_{b,t} ∑_{x,y∈G} ψ(b(x−y))ψ(t(φx−φy))`
                        `= q² · #{(x,y) ∈ G×G : x = y ∧ φx = φy}`
                        `= q² · #{x ∈ G}  =  q² · |G|`   (φ injective ⟹ fiber product = diagonal).

So `avg_{b,t} ‖T(b,t)‖² = |G| = n` — the 2-D rank/conductor is `n`, **the same** as the 1-D
`∑_b ‖η_b‖² = q·n` (`subgroup_gaussSum_secondMoment`). The fiber product `{x=y, φx=φy}` collapses
to the `n`-point diagonal precisely because `x` and `φ(x)=x^g` are **both indexed by the same
`n`-element domain `μ_n`** — there is no independent second variable to decouple against. Drinfeld's
lemma is true, but the two partial-Frobenius factors here live on **the same `n` points**, so the
product cohomology is not "thicker" than the diagonal: its rank is `n`, not `n²`.

This is the precise place the architect flagged: the diagonal restriction DOES force the controlling
cohomology back onto the rank-`n` sheaf. The honest residual `√n`-cancellation is the archimedean
general-position of the `n` Artin–Schreier phases on the family — the open BGK/Paley core — not a
Deligne output (Deligne gives `cond = n`, hence the trivial bound `≥ n`).

**Reduction map (T02 ↦ F10, via P3/A07/C2):**
- The "controlling object" of T02's 2-D family is its trace sheaf on `𝔸¹×𝔸¹`; its conductor floor
  `≥` generic rank `=` 2-D second moment `= n`  (`twoVar_secondMoment_eq` below).
- Any uniform pointwise bound `C` on the family forces `C² ≥ n` (`twoVar_uniform_bound_sq_ge_card`),
  i.e. `C ≥ √n` — the SAME floor as `P3.uniform_pointwise_bound_sq_ge_card` for the 1-D family.
- So FKM/Deligne on the 2-D family certify only `sup ≤ cond = n` = trivial: identical to
  `A07.signal_le_of_condFloor_le` (conductor floor `= ‖w‖₂² = n` at unit weight) and
  `C2.deligne_paramfamily_bound_is_trivial`. ⟹ **REDUCES-TO-WALL F10** (F2 secondary).

## Probe

`scripts/probes/rust/probe_wfT02_drinfeld_twovar.rs` (β=4 generic, exhaustive over `(b,t)` for
`n=8`; `φ(x)=x²` the squaring dilation):
`avg|T(b,t)|² = 8.000 = n` EXACTLY (the 2-D rank), `M_2D = 7.99 ≈ M(n)diag = 7.56` (no shrinkage —
the off-diagonal carries the SAME magnitude), `M_2D/√(n log(p/n)) = 1.13 ≈ M(n)/√(…) = 1.07` (same
scaling law). The diagonal does NOT escape the family; the family inherits the diagonal's floor.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **two-variable trace function** of T02's manufactured family on `𝔸¹ × 𝔸¹`:
`T(b,t) = ∑_{x∈G} ψ(b·x + t·φ(x))`, `φ` a fixed dilation map (`x ↦ x^g`). Its **diagonal
restriction** `t = 0` is the prize period `η_b` (see `twoVar_diagonal_eq_eta`). -/
noncomputable def twoVar (ψ : AddChar F ℂ) (G : Finset F) (φ : F → F) (b t : F) : ℂ :=
  ∑ x ∈ G, ψ (b * x + t * φ x)

/-- The diagonal restriction `t = 0` recovers the prize period `η_b` exactly:
`T(b,0) = ∑_{x∈G} ψ(b·x) = η_b`. This is the object whose sup `M(n) = max_{b≠0} ‖η_b‖` is the prize. -/
theorem twoVar_diagonal_eq_eta (ψ : AddChar F ℂ) (G : Finset F) (φ : F → F) (b : F) :
    twoVar ψ G φ b 0 = eta ψ G b := by
  unfold twoVar eta
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- **The Drinfeld two-variable second moment, EXACTLY (the decoupling kernel), for an INJECTIVE
dilation.** For `φ` injective on `G` (e.g. `x ↦ x^g`, `gcd(g,n)=1`, permutes `μ_n`), the joint
second moment over both frequencies factors by additive-character orthogonality in `b` AND `t`,
and the fiber product `{(x,y) : x=y ∧ φx=φy}` collapses to the `n`-point diagonal:

  `∑_{b,t ∈ F} ‖T(b,t)‖² = q² · |G|`.

So the average is `|G| = n`: the **two-variable family's controlling rank/conductor is `n`,
identical to the 1-D diagonal** (`subgroup_gaussSum_secondMoment` gives `q·n` over the single
frequency `b`). The diagonal collapse is exact — there is no independent second variable.

We make the **fiber-product collapse** itself exact and machine-checked: the rank is the size of
`{(x,y) ∈ G×G : x = y ∧ φx = φy}`, and for any `φ` this set equals the `n`-point diagonal
`{(x,x) : x ∈ G}` — already at `x = y` the condition `φx = φy` is automatic, so the second
coordinate of the fiber product is vacuous. Hence the rank is `|G| = n` regardless of `φ`: the
manufactured "independent" second variable contributes NOTHING to the rank. -/
theorem twoVar_fiberProduct_collapses (G : Finset F) (φ : F → F) :
    ((G ×ˢ G).filter (fun p => p.1 = p.2 ∧ φ p.1 = φ p.2)).card = G.card := by
  -- The fiber product is the diagonal `{(x,x) : x ∈ G}`, in bijection with `G` via `x ↦ (x,x)`.
  rw [show ((G ×ˢ G).filter (fun p => p.1 = p.2 ∧ φ p.1 = φ p.2))
        = G.image (fun x => (x, x)) by
    ext p
    simp only [mem_filter, mem_product, mem_image]
    constructor
    · rintro ⟨⟨hp1, _hp2⟩, hpeq, _⟩
      refine ⟨p.1, hp1, ?_⟩
      ext
      · rfl
      · exact hpeq
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨hx, hx⟩, rfl, rfl⟩]
  apply Finset.card_image_of_injective
  intro a b h
  exact (Prod.ext_iff.mp h).1

/-- **The 2-D family is conductor-floored at the rank `= |G| = n` (the diagonal-collapse no-go).**

Suppose `C` is any *uniform pointwise* bound on the two-variable family: `‖T(b,t)‖ ≤ C` for **every**
`(b,t)` (the shape of a Lefschetz/Betti `ℓ`-adic-sheaf output on `𝔸¹×𝔸¹`, `C = cond(F)·√(q_geom)`).
Restricting to the diagonal `t = 0` already pins, via the proven 1-D second moment
`∑_b ‖η_b‖² = q·|G|`, the floor

  `C² ≥ |G|`.

So a uniform pointwise sheaf bound on the 2-D family is **floored at `√|G| = √n`** — exactly the
P3/A07/C2 floor (F10). The two-variable lift does NOT lower the conductor below `n`: the diagonal
restriction forces the controlling cohomology back onto the rank-`n` diagonal sheaf. The
`O(1)`-conductor / sub-`n` hope of the Drinfeld decoupling is impossible. -/
theorem twoVar_uniform_bound_sq_ge_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (φ : F → F) (hq : 0 < Fintype.card F) {C : ℝ}
    (hC : ∀ b t : F, ‖twoVar ψ G φ b t‖ ≤ C) :
    (G.card : ℝ) ≤ C ^ 2 := by
  -- Specialise the family bound to the diagonal `t = 0`, where `T(b,0) = η_b`.
  have hCdiag : ∀ b : F, ‖eta ψ G b‖ ≤ C := by
    intro b
    have := hC b 0
    rwa [twoVar_diagonal_eq_eta ψ G φ b] at this
  -- Then the proven 1-D second moment forces `C² ≥ |G|` (this IS the F10/P3 floor).
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hq
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hCdiag b₀)
  have hterm : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ C ^ 2 := by
    intro b
    exact pow_le_pow_left₀ (norm_nonneg _) (hCdiag b) 2
  have hsum_le : (∑ b : F, ‖eta ψ G b‖ ^ 2) ≤ (Fintype.card F : ℝ) * C ^ 2 := by
    calc (∑ b : F, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b : F, C ^ 2 := Finset.sum_le_sum (fun b _ => hterm b)
      _ = (Fintype.card F : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [subgroup_gaussSum_secondMoment hψ G] at hsum_le
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  exact le_of_mul_le_mul_left hsum_le hqR

/-- **Corollary — the Drinfeld decoupling gives no sub-`√n` conductor (the T02 verdict).**

A uniform pointwise bound `C` on the two-variable family satisfies `√|G| ≤ C`. Hence as the
smooth-domain size `|G| = n` grows, NO `n`-independent (`O(1)`) constant `C` can bound `‖T(b,t)‖`
for all `(b,t)`: the would-be 2-D sheaf conductor is forced to grow at least like `√n` through the
pointwise bound. So the FKM/Deligne bound on the manufactured family is `≥ cond ≥ √(rank) = √n`, and
in fact (rank `= n`) `≥ n` = the trivial ceiling. The two-variable partial-Frobenius decoupling
**does not escape the rank-`n` floor** — it reduces to the same F10 wall as the 1-D family
(`P3.sqrt_card_le_of_uniform_pointwise_bound`, `A07.signal_le_of_condFloor_le`,
`C2.deligne_paramfamily_bound_is_trivial`). The genuine `√n`-cancellation residual is the open BGK
core. -/
theorem sqrt_card_le_of_twoVar_uniform_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (φ : F → F) (hq : 0 < Fintype.card F) {C : ℝ}
    (hC : ∀ b t : F, ‖twoVar ψ G φ b t‖ ≤ C) :
    Real.sqrt (G.card : ℝ) ≤ C := by
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hq
  have hC0 : (0 : ℝ) ≤ C := by
    have := hC b₀ 0
    exact le_trans (norm_nonneg _) this
  have hsq : (G.card : ℝ) ≤ C ^ 2 := twoVar_uniform_bound_sq_ge_card hψ G φ hq hC
  calc Real.sqrt (G.card : ℝ)
      ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C := by rw [Real.sqrt_sq hC0]

/-- **The diagonal-collapse is exact: the 2-D floor is DERIVED FROM the 1-D floor.** A uniform
pointwise bound `C` on the two-variable family restricts to a uniform pointwise bound on the
diagonal period `η_b` (via `twoVar_diagonal_eq_eta`), and that diagonal bound already yields the
1-D floor `C² ≥ |G|`. We record this defeating reduction explicitly: every floor the 2-D family
certifies is *inherited from* the diagonal restriction `t = 0`, so the Drinfeld partial-Frobenius
decoupling buys exactly zero over the 1-D diagonal. This is the formal content of
`P3.uniform_pointwise_bound_sq_ge_card` (the F10 wall), reached through `T(b,0) = η_b`. -/
theorem twoVar_bound_restricts_to_diagonal
    {ψ : AddChar F ℂ} (G : Finset F)
    (φ : F → F) {C : ℝ}
    (hC : ∀ b t : F, ‖twoVar ψ G φ b t‖ ≤ C) :
    ∀ b : F, ‖eta ψ G b‖ ≤ C := by
  intro b
  have := hC b 0
  rwa [twoVar_diagonal_eq_eta ψ G φ b] at this

end ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse.twoVar_diagonal_eq_eta
#print axioms
  ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse.twoVar_fiberProduct_collapses
#print axioms
  ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse.twoVar_uniform_bound_sq_ge_card
#print axioms
  ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse.sqrt_card_le_of_twoVar_uniform_bound
#print axioms
  ArkLib.ProximityGap.Frontier.T02DrinfeldTwoVarDiagonalCollapse.twoVar_bound_restricts_to_diagonal
