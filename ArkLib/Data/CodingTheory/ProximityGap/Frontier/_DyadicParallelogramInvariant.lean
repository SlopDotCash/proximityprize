/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# HANDLE A5 — the dyadic parallelogram CONSERVED GLOBAL INVARIANT (#407)

The proximity prize reduces to `B = max_{b≠0}‖η_b‖`, `η_b = ∑_{x∈G} ψ(b·x)` over the smooth dyadic
subgroup `G = μ_n` (`n = 2^μ`).  The 2-power tower `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}` (`ζ` a
primitive `2^{i+1}`-th root) gives, per frequency `b`, the EXACT parallelogram identity (proven
in `GaussPeriodTower.gaussPeriod_parallelogram_recursion`):

> `‖η_b(μ_{2^{i+1}})‖² + ‖η^χ_b(μ_{2^{i+1}})‖² = 2·(‖η_b(μ_{2^i})‖² + ‖η_{ζb}(μ_{2^i})‖²)`,

where `η^χ_b = η_b(μ_{2^i}) − η_{ζb}(μ_{2^i})` is the quadratic-twisted period.  Handle A5 asks for a
**conserved global invariant** of the period-transition operator `T : b ↦ ζ·b` that forces the L^∞
norm to track the L² scale `√2` rather than the trivial `2`.

## What this file proves (the exact, unconditional global invariant)

Summing the per-`b` parallelogram over **all** frequencies `b ∈ F` and using that `T : b ↦ ζ·b` is a
**bijection** of `F` (so `∑_b ‖η_{ζb}‖² = ∑_b ‖η_b‖²`), the cross terms collapse and we obtain the
**conserved global L²-invariant**:

> `parallelogram_secondMoment_invariant`:
>   `∑_b ‖η_b(G ⊔ ζ•G)‖²  +  ∑_b ‖η^χ_b‖²  =  4·∑_b ‖η_b(G)‖²`,

where `η^χ_b := η_b(G) − η_{ζb}(G)` is the twisted period at frequency `b`.  Because each summed term
is a *single* number (the level moment), and `∑_b ‖η_b(G⊔ζ•G)‖² = 2·∑_b‖η_b(G)‖²` is the proven
L²-doubling (`eta_dilate_secondMoment_doubling`), the invariant pins the twisted moment EXACTLY:

> `twisted_secondMoment_eq`:  `∑_b ‖η^χ_b‖² = 2·∑_b ‖η_b(G)‖²`  (the twist carries half the level-up
> energy; untwisted and twisted moments are EQUAL, `= 2·∑_b‖η_b(G)‖²` each).

This is the precise conserved quantity A5 sought: **the untwisted and twisted second moments are
balanced and conserved up the tower** (each doubles per level).  It is exact, unconditional, needs no
Weil/BGK input, and is the global-invariant backbone of the descent.

## The HONEST obstruction (why this does NOT close the prize, with the exact gap)

The conserved invariant controls the **L² average**, not the **L^∞ maximum** — and the probes
(`probe_local_aligned_child_submaximality.py`, `probe_*invariant`) show the gap is *real and
irreducible by any L² argument*:

* **Per-level descent is REFUTED.**  `(‖A‖²+‖B‖²)/M(μ-1)² ≤ 1` (SUBMAX) fails worst-case (ratio up
  to `1.99` at low levels, `1.1–1.4` at deep levels); even the weaker literal `M(μ) ≤ √2·M(μ-1)`
  is violated (ratio up to `1.47 > √2`).  At the worst `b*`, `cos(A,B) = 1.0000` ALWAYS (the periods
  are real by negation-closure, `period_conj_eq_of_neg_closed`), so `M(μ) = ‖A‖ + ‖B‖` and one parent
  is frequently the previous maximizer itself (`‖A‖/M' = 1.000`) with a non-trivial aligned partner.

* **The worst frequency sits a `log(q/n)` factor ABOVE the L² average.**  `(‖A‖²+‖B‖²)/(2·avg) ≈
  7–11` (NOT `≈ 1`) at the worst `b*`; equivalently `M² ≈ C·n·log(q/n)`, not `2·avg = 2n`.  So *no*
  conserved L² invariant (which only knows the average) can bound the max below `√(n·log(q/n))` — the
  `√log` excess is exactly the unproven cancellation.

* **The 2nd-moment energy `E_2/n²` itself breaks at the boundary.**  It hugs the proven char-0
  Gaussian value `3` (`= (2r-1)‼` at `r=2`) only while `q > (2r)^{n/2}`; at `n ≈ q^{1/4}` it jumps
  (measured `4.99 → 11.2` as `n → 8192` at `q ≈ 8·10⁶`).  The parallelogram tower faithfully
  TRANSMITS this char-`p` additive-energy anomaly upward — it does not suppress it.  The conserved
  invariant is real but the anomaly rides inside `∑_b‖η_b(G)‖² = q·n` undetected (the L² moment is
  anomaly-blind; the anomaly lives in `E_2`, the 4th moment).

**Exact gap to `√n`.**  This invariant reaches the L² floor scale `√n` (exponent `0.5` for the
*average*).  The L^∞ max it does NOT pin; the residual is exactly the `√log(q/n)` excess of the worst
frequency over the average = the open BGK / Paley square-root-cancellation bound (SOTA proven
`n^{0.989}`, di Benedetto 2020, and only for `n > q^{1/4}`).  The dyadic structure here is genuinely
used (negation-closure ⟹ real periods ⟹ `cos = 1` worst-case; the twist is the quadratic character of
`μ_{2^i}`), but it does NOT collapse the L²→L^∞ gap: it converts the open problem into the
**non-amplification of a real-valued cocycle `b → ζb → ζ²b → …`** along the transition orbit, which is
the same open statement.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #407, Handle A5.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The twisted (quadratic-character) period at frequency `b`**: `η^χ_b = η_b(G) − η_{ζb}(G)`.
This is the second slot of the per-`b` parallelogram — the level-up period twisted by the quadratic
character of the squares-coset `G ⊆ μ_{2^{i+1}}` (which is `+1` on `G`, `−1` on `ζ•G`). -/
noncomputable def etaTwist (ψ : AddChar F ℂ) (G : Finset F) (ζ b : F) : ℂ :=
  eta ψ G b - eta ψ G (ζ * b)

/-- **The transition operator `T : b ↦ ζ·b` is a bijection of `F`** (for `ζ ≠ 0`), so summing any
function of `‖η_{ζb}‖` over all `b` equals summing over all `b` of `‖η_b‖`. -/
theorem sum_eta_sq_transition {ψ : AddChar F ℂ} {ζ : F} (hζ : ζ ≠ 0) (G : Finset F) :
    ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2 = ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  -- reindex by the bijection `b ↦ ζ·b` (left multiplication by a unit)
  refine Fintype.sum_bijective (fun b => ζ * b) ?_ _ _ (fun b => rfl)
  exact (mulLeft_bijective₀ ζ hζ)

/-- **The per-frequency parallelogram identity** (specialization of the abstract
`gaussPeriod_parallelogram_recursion` to the level-up period and its twist):
`‖η_b(G⊔ζ•G)‖² + ‖η^χ_b‖² = 2·(‖η_b(G)‖² + ‖η_{ζb}(G)‖²)`. -/
theorem eta_parallelogram_pointwise {ψ : AddChar F ℂ} {ζ : F} (hζ : ζ ≠ 0) (G : Finset F)
    (hdisj : Disjoint G (dilate ζ G)) (b : F) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 + ‖etaTwist ψ G ζ b‖ ^ 2
      = 2 * (‖eta ψ G b‖ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2) := by
  rw [eta_union_dilate ψ G hζ hdisj b]
  unfold etaTwist
  exact parallelogram_law_with_norm ℝ (eta ψ G b) (eta ψ G (ζ * b))

/-- **HANDLE A5 — the conserved global L²-invariant.**  Summing the per-frequency parallelogram over
all `b` and using that `T : b ↦ ζb` is a bijection (`sum_eta_sq_transition`) collapses the cross
terms to give the exact, unconditional invariant

> `∑_b ‖η_b(G ⊔ ζ•G)‖²  +  ∑_b ‖η^χ_b‖²  =  4·∑_b ‖η_b(G)‖²`.

This is the global invariant of the period-transition operator: the untwisted and twisted level-up
second moments together carry exactly `4×` the level moment.  No Weil/BGK input. -/
theorem parallelogram_secondMoment_invariant {ψ : AddChar F ℂ} {ζ : F} (hζ : ζ ≠ 0) (G : Finset F)
    (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2) + (∑ b : F, ‖etaTwist ψ G ζ b‖ ^ 2)
      = 4 * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  have hpt : ∀ b : F, ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 + ‖etaTwist ψ G ζ b‖ ^ 2
      = 2 * (‖eta ψ G b‖ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2) :=
    fun b => eta_parallelogram_pointwise hζ G hdisj b
  calc (∑ b : F, ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2) + (∑ b : F, ‖etaTwist ψ G ζ b‖ ^ 2)
      = ∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 + ‖etaTwist ψ G ζ b‖ ^ 2) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ b : F, 2 * (‖eta ψ G b‖ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2) :=
        Finset.sum_congr rfl (fun b _ => hpt b)
    _ = 2 * ((∑ b : F, ‖eta ψ G b‖ ^ 2) + ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]
    _ = 2 * ((∑ b : F, ‖eta ψ G b‖ ^ 2) + ∑ b : F, ‖eta ψ G b‖ ^ 2) := by
        rw [sum_eta_sq_transition hζ G]
    _ = 4 * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by ring

/-- **The twisted second moment is pinned exactly** `= 2·∑_b‖η_b(G)‖²`.  Combining the conserved
invariant with the proven L²-doubling `∑_b‖η_b(G⊔ζ•G)‖² = 2·∑_b‖η_b(G)‖²`
(`eta_dilate_secondMoment_doubling`): the untwisted and twisted level-up moments are EQUAL, each
carrying exactly half (`= 2×` the level moment) of the total `4×`.  The L²-mass is balanced between
the two characters and conserved up the tower — the exact statement of the A5 "global invariant". -/
theorem twisted_secondMoment_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ζ : F} (hζ : ζ ≠ 0)
    (G : Finset F) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b : F, ‖etaTwist ψ G ζ b‖ ^ 2 = 2 * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  have hinv := parallelogram_secondMoment_invariant (ψ := ψ) hζ G hdisj
  have hdbl := eta_dilate_secondMoment_doubling hψ G hζ hdisj
  -- 4·S = 2·S + twisted  ⟹  twisted = 2·S
  rw [hdbl] at hinv
  linarith [hinv]

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sum_eta_sq_transition
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta_parallelogram_pointwise
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.parallelogram_secondMoment_invariant
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.twisted_secondMoment_eq
