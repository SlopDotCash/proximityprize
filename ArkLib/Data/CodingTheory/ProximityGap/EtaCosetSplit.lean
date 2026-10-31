/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The coset-split (parity) recursion of the Gauss period (#407)

The foundational tower step. If the evaluation set splits as a disjoint union of a subset `H` and
its `ω`-translate `ωH = {ω·x : x∈H}`, the Gauss period splits as

> **`eta_coset_split`** — `η_G(b) = η_H(b) + η_H(ωb)`  when  `G = H ⊔ ωH`, `ω ≠ 0`.

For the dyadic prize tower `G = μ_{2^μ} = ⟨ω⟩`, `H = ⟨ω²⟩ = μ_{2^{μ-1}}` (index 2, the even
powers) and `ωH` (the odd powers), so `η^{(μ)}(b) = η^{(μ-1)}(b) + η^{(μ-1)}(ωb)` — the parity
split. This is the exact recursion the parallelogram tower (C1 lead) and the structural cap
(`V_k = 4^k` at the bottom ⟹ no level-by-level route reaches `√n`) are built on. Combined with
`parallelogram_law_with_norm`,
`|η_G(b)|² + |η_H(b)−η_H(ωb)|² = 2(|η_H(b)|²+|η_H(ωb)|²) ≤ 4 V_{μ-1}`.
With `V = V_{μ-1}` any common upper bound of the two sub-period squares, the exact deficit is
(`eta_split_deficit_eq`)

  `4V − |η_G(b)|² = |η_H(b)−η_H(ωb)|² + 2(V − |η_H(b)|²) + 2(V − |η_H(ωb)|²)`,

so the deficit is **at least** the **twist** `|η_H(b)−η_H(ωb)|²` (`twist_le_eta_split_deficit`),
and equals it only when both sub-periods attain `V`. The two slack terms need not vanish even at a
worst frequency: over `𝔽₅`, `H = {1,4}`, `ω = 2`, `G = 𝔽₅^×`, every nonzero frequency is worst for
`G`, yet `V = (3+√5)/2` and at `b = 1` the twist is `5 < 4V − 1 = 5 + 2√5`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.EtaCosetSplit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Coset-split recursion.** If `G` is the disjoint union of `H` and its `ω`-translate, the
Gauss period at frequency `b` splits into the period over `H` at `b` plus the period over `H` at
`ωb`. The exact dyadic tower step (parity split). -/
theorem eta_coset_split {ψ : AddChar F ℂ} {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) :
    eta ψ G b = eta ψ H b + eta ψ H (ω * b) := by
  unfold eta
  rw [hG, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hω h)]
  apply Finset.sum_congr rfl
  intro x _
  rw [show b * (ω * x) = (ω * b) * x by ring]

/-- **Deficit-twist identity.** Applying the parallelogram law to the coset split, the level-`μ`
period magnitude plus the **twist** `|η_H(b)−η_H(ωb)|²` equals `2(|η_H(b)|²+|η_H(ωb)|²)`. This is
*not* by itself "deficit = twist": with `V_{μ-1} = max|η_H|²`, the deficit `4 V_{μ-1} − |η_G(b)|²`
equals the twist **plus** the two nonnegative slack terms `2(V_{μ-1} − |η_H(b)|²)` and
`2(V_{μ-1} − |η_H(ωb)|²)` (`eta_split_deficit_eq`). Full quadrupling at `b`
(`|η_G(b)|² = 4 V_{μ-1}`) holds iff the twist vanishes **and** both sub-periods attain `V_{μ-1}`.
The twist's uniform-in-`μ` positivity is one candidate form of the one-level BGK input of the C1
tower lead. -/
theorem eta_split_parallelogram {ψ : AddChar F ℂ} {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) :
    ‖eta ψ G b‖ ^ 2 + ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2
      = 2 * (‖eta ψ H b‖ ^ 2 + ‖eta ψ H (ω * b)‖ ^ 2) := by
  have hsplit := eta_coset_split (ψ := ψ) hω hG hdisj b
  rw [hsplit]
  have := parallelogram_law_with_norm ℂ (eta ψ H b) (eta ψ H (ω * b))
  linarith [this]

/-- **Exact deficit with slack terms.** For any real `V`, the deficit `4V − |η_G(b)|²` equals the
twist plus the two sub-period slacks `2(V − |η_H(b)|²) + 2(V − |η_H(ωb)|²)`. -/
theorem eta_split_deficit_eq {ψ : AddChar F ℂ} {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) (V : ℝ) :
    4 * V - ‖eta ψ G b‖ ^ 2
      = ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2
        + 2 * (V - ‖eta ψ H b‖ ^ 2) + 2 * (V - ‖eta ψ H (ω * b)‖ ^ 2) := by
  have := eta_split_parallelogram (ψ := ψ) hω hG hdisj b
  linarith

/-- **Deficit ≥ twist.** If `V` bounds both sub-period squares, the deficit `4V − |η_G(b)|²` is at
least the twist `|η_H(b) − η_H(ωb)|²` (equality needs both sub-periods to attain `V`). -/
theorem twist_le_eta_split_deficit {ψ : AddChar F ℂ} {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) {V : ℝ}
    (hb : ‖eta ψ H b‖ ^ 2 ≤ V) (hωb : ‖eta ψ H (ω * b)‖ ^ 2 ≤ V) :
    ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2 ≤ 4 * V - ‖eta ψ G b‖ ^ 2 := by
  rw [eta_split_deficit_eq hω hG hdisj b V]
  linarith

end ArkLib.ProximityGap.EtaCosetSplit
#print axioms ArkLib.ProximityGap.EtaCosetSplit.eta_coset_split
#print axioms ArkLib.ProximityGap.EtaCosetSplit.eta_split_parallelogram
