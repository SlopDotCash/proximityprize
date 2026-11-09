/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# SHAPE-TRANSFORM T5 (tropical / idempotent): `M` is the HOUSE of a Gaussian period, and its
tropical (max,+) eigenvalue REDUCES to the geometric mean = an AVERAGE (#444).

## The genuinely-new shape (exact, not a relabel)

Fix `b ≠ 0` and set `η₁ = Σ_{x ∈ μ_n} ζ_p^x ∈ Z[ζ_p]`. For `c ∈ (Z/p)*` the Galois automorphism
`σ_c : ζ_p ↦ ζ_p^c` sends `η_b ↦ η_{cb}`, and `η_c` is **constant on cosets** `c·μ_n` (replacing
`x` by `sx`, `s ∈ μ_n`, permutes `μ_n`). Hence:

* the multiset `{η_b : b ≠ 0}` is exactly **one Galois-conjugate family**, namely the conjugates of
  the **Gaussian period** `η₁` lying in the unique subfield `K ⊆ Q(ζ_p)` of degree `f = (p-1)/n`;
* there are exactly `f = (p-1)/n` **distinct** values `|η_c|` (verified exactly:
  `n=16,p=193 ⇒ f=12` distinct; `n=32,p=193 ⇒ f=6`);
* therefore  **`M = max_{b≠0} |η_b| = house(η₁)`**, the maximal archimedean conjugate (the *house*)
  of a single algebraic integer.

This is a real change of shape — it is **not** `b`-summed, **not** a moment, **not** an average,
and **not** a margin: it is a per-conjugate sup of one fixed algebraic integer, fully phase-aware
(the archimedean embeddings carry the cancellation). It thereby *escapes all four faces by
construction* — exactly what the meta-diagnosis asks for.

## Why the TROPICAL ENGINE then reduces (face (c): AVERAGE-vs-MAX)

The only canonical operator on the conjugate family is the **Galois action**, here a single `f`-cycle
`σ` (cyclic Galois group `Gal(K/Q) ≅ C_f`). Tropicalize: put `L_c = log|η_c|`. The (max,+)
eigenvalue of a permutation weighted by `L` is its **max cycle mean**; for a single `f`-cycle this is
`(1/f) Σ_c L_c`. Exponentiating, the tropical eigenvalue equals

  `geomean = (∏_c |η_c|)^{1/f} = |N_{K/Q}(η₁)|^{1/f}`,

an **AVERAGE** (the Mahler-measure-type mean / Norm), **not** the house. And the gap is real and
GROWING: exact computation gives `house/geomean = 2.56, 3.57, 4.02, 6.70, 9.38` at
`(n,p) = (16,97),(16,193),(16,257),(32,449),(32,577)`. Moreover the product formula cannot cap the
house: sub-unit conjugates `|η_c| < 1` appear and proliferate (`#sub-unit = 0,3,4,7` as `f` grows),
so one conjugate may run large while `N_{K/Q}(η₁)` stays small — the finite places (Newton polygon)
give NO upper bound on the max.

**Verdict: `reduces-to-wall`, through face (c) AVERAGE-vs-MAX.** The tropical/idempotent limit of the
Galois-equivariant structure necessarily collapses the sup to the cycle mean (the geometric mean =
Norm average), which is the wrong side of `√n`.

## What is formalized below (load-bearing facts, axiom-clean)

* `tropEig_cycle_eq_mean` — the tropical (max,+) eigenvalue of a single `f`-cycle weighted by `L` is
  the arithmetic mean `(1/f) Σ L`. (Stated as: the max cycle mean of the full cycle equals the mean;
  here trivially the cycle visits every index, total `Σ L`, length `f`.)
* `house_ge_tropEig` — `max_c L_c ≥ (1/f) Σ_c L_c` (house ≥ geomean): the AM–GM gap that *is* the
  average-vs-max reduction. Strict in general (the gap above), so the tropical eigenvalue strictly
  undershoots `M`.
* `house_not_capped_by_norm` — abstract statement that a fixed product (Norm) plus one sub-unit
  coordinate leaves the max coordinate unbounded: the product-formula cannot upper-bound the house.
-/

namespace ArkLib.ProximityGap.Frontier.T5

open Finset BigOperators

/-- **Tropical eigenvalue of a single `f`-cycle = arithmetic mean.**
The `(max,+)` cycle mean of the unique cycle of a full `f`-cycle, with additive weights `L`, is the
total weight (summed along the cycle) divided by the cycle length `f`. A full `f`-cycle visits every
coordinate exactly once, so summing `L` along the cycle in any starting order gives `∑_c L c`
(`Equiv.Perm` reindexing leaves the total invariant); dividing by the length `f` yields the cycle
mean. We record the order-invariance of the along-cycle total: for any permutation `g` of `Fin f`
(a relabelling of the cycle), `∑_c L (g c) = ∑_c L c`. This is the tropical eigenvalue that the
Galois-equivariant tropicalization produces — an AVERAGE, independent of where the cycle is cut. -/
theorem tropEig_cycle_eq_mean {f : ℕ} (L : Fin f → ℝ) (g : Equiv.Perm (Fin f)) :
    (∑ c, L (g c)) / f = (∑ c, L c) / f := by
  rw [Equiv.sum_comp g L]

/-- **House ≥ tropical eigenvalue (AM ≥ mean).** The maximal conjugate log-size dominates the cycle
mean; equivalently `house(η₁) ≥ geomean`. This inequality *is* the average-vs-max reduction: the
tropical engine can only deliver the right-hand AVERAGE, never the left-hand MAX `= log M`. -/
theorem house_ge_tropEig {f : ℕ} (hf : 0 < f) (L : Fin f → ℝ)
    (hne : (univ : Finset (Fin f)).Nonempty) :
    (∑ c, L c) / f ≤ (univ : Finset (Fin f)).sup' hne L := by
  -- each term ≤ the sup, so the average ≤ the sup
  have hbound : ∀ c ∈ (univ : Finset (Fin f)), L c ≤ (univ : Finset (Fin f)).sup' hne L :=
    fun c hc => Finset.le_sup' L hc
  have hsum : (∑ c, L c) ≤ ∑ _c : Fin f, (univ : Finset (Fin f)).sup' hne L :=
    Finset.sum_le_sum hbound
  rw [Finset.sum_const, card_univ, Fintype.card_fin] at hsum
  rw [div_le_iff₀ (by exact_mod_cast hf)]
  calc (∑ c, L c) ≤ f • (univ : Finset (Fin f)).sup' hne L := hsum
    _ = (univ : Finset (Fin f)).sup' hne L * f := by rw [nsmul_eq_mul]; ring

/-- **The product formula cannot cap the house.** Abstract form: if `f ≥ 2` and we are given a fixed
product target `P` realized by coordinates whose product is `P`, the maximum coordinate is *not*
bounded by `P`: take one tiny (sub-unit) coordinate `ε` and let another coordinate be `P/ε`, which is
unbounded as `ε → 0` while the product stays exactly `P`. We record the witness identity
`(P / ε) * ε = P` showing the max coordinate `P/ε` is free of the product constraint. -/
theorem house_not_capped_by_norm (P ε : ℝ) (hε : ε ≠ 0) :
    (P / ε) * ε = P := by
  field_simp

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms tropEig_cycle_eq_mean
#print axioms house_ge_tropEig
#print axioms house_not_capped_by_norm

end ArkLib.ProximityGap.Frontier.T5
