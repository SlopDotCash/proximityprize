/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# Iterated dilation tower for subgroup Gauss sums: the `2^μ` L²-doubling vs the L^∞ gap (#407)

This file **iterates** the single-level dilation recursion of
`SubgroupGaussSumDilationRecursion.lean` over a full `2`-power tower

  `G₀ ⊆ G₁ ⊆ … ⊆ G_μ`,  `G_{i+1} = G_i ∪ ζ_i • G_i`  (disjoint dilate at each step, `ζ_i ≠ 0`),

modelling the smooth `2^μ`-subgroup tower `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}`. Two paired,
honestly-scoped statements come out, and the gap between them *is* the open prize core.

## L² side — PROVEN, exact, domain-blind (the Johnson side)

`secondMoment_tower_pow` :  `∑_b ‖η_b(G_i)‖² = 2^i · ∑_b ‖η_b(G₀)‖²`.

Pure induction on `eta_dilate_secondMoment_doubling` (Parseval / orthogonality only — no Weil,
no arithmetic of the field). Equivalently the L²-norm `‖η‖₂` scales by **exactly `√2` per level**,
so after the `μ` levels of the `2^μ`-tower `‖η‖₂ ~ √(2^μ · |G₀|) = √n` — exactly the **floor L²
scale**. This is the fully-provable, average-case cancellation direction: it makes no claim about
any individual frequency `b`.

## L^∞ side — only the trivial `2^i` bound is provable (the open BGK wall)

`maxNorm_tower_le_pow` : if every start frequency obeys `‖η_b(G₀)‖ ≤ M₀`, then iterating the
triangle inequality `‖η_b(G ⊔ ζ•G)‖ ≤ 2M` gives only

  `‖η_b(G_i)‖ ≤ 2^i · M₀`   for **every** `b`,

i.e. the sup norm provably scales by `2` per level, giving the trivial `max‖η‖ ≤ 2^μ = n`.

## The `√2`-vs-`2` gap = the open core (NOT closed here)

The prize floor `max_{b≠0} ‖η_b‖ ≲ C·√(n·log(q/n))` requires the L^∞ norm to track the **L²**
per-level scale `√2`, not the trivial `2`, along **every** path `b → ζ₀b → ζ₁(ζ₀b) → …` down the
tower. That is the statement that no frequency keeps a persistently phase-aligned trajectory — a
**cocycle large-deviation / short-character-sum cancellation** bound for thin multiplicative
subgroups (the open BGK / Paley-graph-conjecture regime; best PROVEN is `n^{1-o(1)}`, vacuous in
the prize window). It is **not** capturable by iterating any single-level lemma: this file proves
both single-level facts to the top of the tower exactly, and the gap between `√2` and `2` is
precisely the residual open content. **No closure is claimed.**

See `SubgroupGaussSumDilationRecursion.lean` (the single-level substrate) and
`docs/kb/deltastar-dilation-recursion-reformulation-2026-06-13.md`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The dilation tower** built from a start set `G₀` and a per-level dilation scalar `ζ : ℕ → F`:
`towerStep G₀ ζ 0 = G₀` and `towerStep G₀ ζ (i+1) = (towerStep …) ∪ ζ_i • (towerStep …)`. -/
noncomputable def towerStep (G₀ : Finset F) (ζ : ℕ → F) : ℕ → Finset F
  | 0     => G₀
  | i + 1 => let H := towerStep G₀ ζ i; H ∪ dilate (ζ i) H

@[simp] theorem towerStep_zero (G₀ : Finset F) (ζ : ℕ → F) : towerStep G₀ ζ 0 = G₀ := rfl

theorem towerStep_succ (G₀ : Finset F) (ζ : ℕ → F) (i : ℕ) :
    towerStep G₀ ζ (i + 1) = towerStep G₀ ζ i ∪ dilate (ζ i) (towerStep G₀ ζ i) := rfl

/-- The hypothesis package making the tower a *valid disjoint-dilate* tower: at every level `i`,
the dilation scalar is nonzero and the dilate is disjoint from the current set. -/
structure ValidTower (G₀ : Finset F) (ζ : ℕ → F) (μ : ℕ) : Prop where
  ne_zero : ∀ i < μ, ζ i ≠ 0
  disjoint : ∀ i < μ, Disjoint (towerStep G₀ ζ i) (dilate (ζ i) (towerStep G₀ ζ i))

/-- **ITERATED EXACT L²-DOUBLING (the Johnson-side floor scale, fully proven).**
For a valid disjoint-dilate tower, the second moment after `i` levels is `2^i` times the start:
`∑_b ‖η_b(G_i)‖² = 2^i · ∑_b ‖η_b(G₀)‖²`. Equivalently `‖η‖₂` scales by exactly `√2` per level.

Proof: induction on `i` using the single-level `eta_dilate_secondMoment_doubling`. No field
arithmetic, no Weil — orthogonality / Parseval only; domain-blind. -/
theorem secondMoment_tower_pow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G₀ : Finset F)
    (ζ : ℕ → F) {μ : ℕ} (hvalid : ValidTower G₀ ζ μ) (i : ℕ) (hi : i ≤ μ) :
    ∑ b : F, ‖eta ψ (towerStep G₀ ζ i) b‖ ^ 2 = 2 ^ i * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2 := by
  induction i with
  | zero => simp
  | succ j ih =>
      have hj : j < μ := hi
      have hjle : j ≤ μ := le_of_lt hj
      rw [towerStep_succ,
          eta_dilate_secondMoment_doubling hψ (towerStep G₀ ζ j) (hvalid.ne_zero j hj)
            (hvalid.disjoint j hj),
          ih hjle]
      ring

/-- **ITERATED TRIVIAL L^∞ DOUBLING (the only sup-side bound the recursion gives).**
If every start frequency obeys `‖η_b(G₀)‖ ≤ M₀`, then after `i` levels every frequency obeys
`‖η_b(G_i)‖ ≤ 2^i · M₀`. The sup norm provably scales only by `2` per level — NOT the L²-scale
`√2`. The gap is the open BGK content (see module docstring).

Proof: induction on `i` using the single-level triangle bound `eta_union_dilate_norm_le`; at each
step the inductive `2^j·M₀` bound applies to BOTH children `η_b` and `η_{ζb}`. -/
theorem maxNorm_tower_le_pow (ψ : AddChar F ℂ) (G₀ : Finset F)
    (ζ : ℕ → F) {μ : ℕ} (hvalid : ValidTower G₀ ζ μ) {M₀ : ℝ}
    (hM₀ : ∀ c : F, ‖eta ψ G₀ c‖ ≤ M₀) (i : ℕ) (hi : i ≤ μ) (b : F) :
    ‖eta ψ (towerStep G₀ ζ i) b‖ ≤ 2 ^ i * M₀ := by
  induction i generalizing b with
  | zero => simpa using hM₀ b
  | succ j ih =>
      have hj : j < μ := hi
      have hjle : j ≤ μ := le_of_lt hj
      calc ‖eta ψ (towerStep G₀ ζ (j + 1)) b‖
          = ‖eta ψ (towerStep G₀ ζ j ∪ dilate (ζ j) (towerStep G₀ ζ j)) b‖ := by
            rw [towerStep_succ]
        _ ≤ ‖eta ψ (towerStep G₀ ζ j) b‖ + ‖eta ψ (towerStep G₀ ζ j) (ζ j * b)‖ :=
            eta_union_dilate_norm_le ψ (towerStep G₀ ζ j) (hvalid.ne_zero j hj)
              (hvalid.disjoint j hj) b
        _ ≤ 2 ^ j * M₀ + 2 ^ j * M₀ := add_le_add (ih hjle b) (ih hjle (ζ j * b))
        _ = 2 ^ (j + 1) * M₀ := by ring

/-- **The `√2`-vs-`2` tower gap, side by side (the honest localization of the open core).**
For a valid tower with start bound `M₀`, after `μ` levels:
* the **L²** mass equals exactly `2^μ · (start L² mass)` (scale `√2` per level — PROVEN floor), and
* the **L^∞** norm is bounded only by `2^μ · M₀` (scale `2` per level — all the recursion gives).
The prize asks the second to actually run at the first's `√2` rate on every path; that step is the
open BGK cocycle large-deviation bound and is **not** proven here. -/
theorem tower_l2_exact_linf_trivial_gap {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G₀ : Finset F)
    (ζ : ℕ → F) {μ : ℕ} (hvalid : ValidTower G₀ ζ μ) {M₀ : ℝ}
    (hM₀ : ∀ c : F, ‖eta ψ G₀ c‖ ≤ M₀) :
    (∑ b : F, ‖eta ψ (towerStep G₀ ζ μ) b‖ ^ 2 = 2 ^ μ * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2)
      ∧ (∀ b : F, ‖eta ψ (towerStep G₀ ζ μ) b‖ ≤ 2 ^ μ * M₀) :=
  ⟨secondMoment_tower_pow hψ G₀ ζ hvalid μ le_rfl,
   fun b => maxNorm_tower_le_pow ψ G₀ ζ hvalid hM₀ μ le_rfl b⟩

/-- **Tower card doubling**: a valid disjoint-dilate tower has `|G_i| = 2^i · |G₀|`
(the structural reason the L² mass doubles: each level disjointly doubles the set). -/
theorem card_tower_pow {G₀ : Finset F} {ζ : ℕ → F} {μ : ℕ} (hvalid : ValidTower G₀ ζ μ)
    (i : ℕ) (hi : i ≤ μ) : (towerStep G₀ ζ i).card = 2 ^ i * G₀.card := by
  induction i with
  | zero => simp
  | succ j ih =>
      have hj : j < μ := hi
      have hjle : j ≤ μ := le_of_lt hj
      rw [towerStep_succ, Finset.card_union_of_disjoint (hvalid.disjoint j hj),
          card_dilate (hvalid.ne_zero j hj), ih hjle]
      ring

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.secondMoment_tower_pow
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.maxNorm_tower_le_pow
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.tower_l2_exact_linf_trivial_gap
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.card_tower_pow
