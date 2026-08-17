/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The dilation / Hadamard recursion for subgroup Gauss sums: L²-doubling vs the L^∞ gap (#407)

The prize-deciding object is `B = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈G} ψ(b·x)` for the smooth
`2^μ`-subgroup `G = μ_n`. The 2-power tower `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}` (`ζ` a primitive
`2^{i+1}`-th root) makes the incomplete sums a **non-autonomous Hadamard recursion in the dilate**:
each level-`(i+1)` frequency value is its own level-`i` value plus the value of its **dilate** `ζ·b`.

Stated generally for **any** finite set `G` and any nonzero "dilation" scalar `ζ`:

* `eta_dilate`        : `η_b(ζ•G) = η_{ζ·b}(G)`            (reindex the image set).
* `eta_union_dilate`  : if `G` and `ζ•G` are **disjoint**, `η_b(G ⊔ ζ•G) = η_b(G) + η_{ζ·b}(G)`
                        — **THE RECURSION** (`f_{i+1}(b) = f_i(b) + f_i(ζb)`).
* `eta_dilate_secondMoment_doubling` :
    `∑_b ‖η_b(G ⊔ ζ•G)‖² = 2·∑_b ‖η_b(G)‖²`  — **exact L²-doubling**.
* `eta_union_dilate_norm_le` / `eta_union_dilate_le_of_bound` :
    `‖η_b(G ⊔ ζ•G)‖ ≤ ‖η_b(G)‖ + ‖η_{ζb}(G)‖ ≤ 2·M` — **the trivial L^∞ doubling**.

## The √2-vs-2 gap *is* the open core (the honest localization)

The two recursion facts scale differently per tower level:
* **L² norm scales by exactly `√2`** (the sum of squares doubles). Iterated over the `μ` levels of
  the `2^μ`-tower this gives `‖η‖₂ ~ √n` — exactly the floor scale `√(n·…)`. This is the
  *domain-blind, Johnson-side, fully proven* direction (orthogonality / Parseval only).
* **L^∞ norm only provably scales by `2`** per level (the children `η_b(G), η_{ζb}(G)` can be
  phase-aligned, `cos = 1` empirically at the maximizer). Iterated this gives only the trivial
  `max‖η‖ ≤ 2^μ = n`.

The prize floor `max_{b≠0}‖η_b‖ ≲ C·√(n·log(q/n))` asks that the L^∞ norm track the L² scale `√2`
(not `2`) along **every** path down the tower — i.e. no frequency `b` keeps a persistently-aligned
trajectory `b → ζb → ζ²b → …`. That cocycle large-deviation statement is exactly the open BGK /
MRSS short-character-sum cancellation bound for thin multiplicative subgroups (SOTA `n^{0.989}`,
di Benedetto 2020; the prize regime `β>4` sits outside every explicit theorem). It is **not**
capturable by any single-level lemma: this file proves both single-level facts exactly and the gap
between them is precisely the residual open content. No fabrication.

See `docs/kb/deltastar-dilation-recursion-reformulation-2026-06-13.md` and
`scripts/probes/probe_dilation_recursion_tower.py`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **dilated set** `ζ•G = {ζ·x : x ∈ G}`. -/
noncomputable def dilate (ζ : F) (G : Finset F) : Finset F := G.image (fun x => ζ * x)

/-- For `ζ ≠ 0`, multiplication by `ζ` is injective on `F`. -/
private lemma mul_left_inj_of_ne_zero {ζ : F} (hζ : ζ ≠ 0) :
    Function.Injective (fun x : F => ζ * x) :=
  fun _ _ h => mul_left_cancel₀ hζ h

/-- **The dilation reindex: `η_b(ζ•G) = η_{ζ·b}(G)`.** -/
theorem eta_dilate (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) (b : F) :
    eta ψ (dilate ζ G) b = eta ψ G (ζ * b) := by
  unfold eta dilate
  rw [Finset.sum_image (fun x _ y _ h => mul_left_inj_of_ne_zero hζ h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ring

/-- **|ζ•G| = |G|** for `ζ ≠ 0` (image under an injection). -/
theorem card_dilate {ζ : F} (hζ : ζ ≠ 0) (G : Finset F) : (dilate ζ G).card = G.card :=
  Finset.card_image_of_injective G (mul_left_inj_of_ne_zero hζ)

/-- **THE DILATION RECURSION** `f_{i+1}(b) = f_i(b) + f_i(ζ·b)`. -/
theorem eta_union_dilate (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (dilate ζ G)) (b : F) :
    eta ψ (G ∪ dilate ζ G) b = eta ψ G b + eta ψ G (ζ * b) := by
  rw [← eta_dilate ψ G hζ b]
  unfold eta
  rw [Finset.sum_union hdisj]

/-- **EXACT L²-DOUBLING** `∑_b ‖η_b(G ⊔ ζ•G)‖² = 2·∑_b ‖η_b(G)‖²` (the L² norm scales by `√2`).
A corollary of the second moment `∑_b ‖η_b(H)‖² = q·|H|`: the disjoint dilate union doubles `|G|`. -/
theorem eta_dilate_secondMoment_doubling {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b : F, ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 = 2 * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  rw [subgroup_gaussSum_secondMoment hψ (G ∪ dilate ζ G),
      subgroup_gaussSum_secondMoment hψ G,
      Finset.card_union_of_disjoint hdisj, card_dilate hζ G]
  push_cast
  ring

/-- **Per-frequency triangle bound** from the recursion:
`‖η_b(G ⊔ ζ•G)‖ ≤ ‖η_b(G)‖ + ‖η_{ζb}(G)‖`. The only L^∞ control the recursion gives. -/
theorem eta_union_dilate_norm_le (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (dilate ζ G)) (b : F) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖ := by
  rw [eta_union_dilate ψ G hζ hdisj b]
  exact norm_add_le _ _

/-- **The trivial L^∞ doubling**: a uniform bound `M` on `‖η_b(G)‖` only yields `2·M` on the union
(NOT `√2·M`). The gap between this `2` and the L²-doubling's `√2` is exactly the open BGK content. -/
theorem eta_union_dilate_le_of_bound (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (dilate ζ G)) {M : ℝ} (hM : ∀ c : F, ‖eta ψ G c‖ ≤ M) (b : F) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ≤ 2 * M := by
  calc ‖eta ψ (G ∪ dilate ζ G) b‖
      ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖ := eta_union_dilate_norm_le ψ G hζ hdisj b
    _ ≤ M + M := add_le_add (hM b) (hM (ζ * b))
    _ = 2 * M := by ring

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
