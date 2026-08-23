/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaCosetSplit

/-!
# The unconditional tower ceiling — the structural cap (#407)

Dropping the non-negative twist term from the deficit-twist identity (`eta_split_parallelogram`)
gives the **unconditional** one-level bound

> **`eta_sq_le_four_max`** — `‖η_G(b)‖² ≤ 4·V`  whenever  `‖η_H(b)‖² ≤ V` and `‖η_H(ωb)‖² ≤ V`.

i.e. each dyadic tower level **at most quadruples** the squared period. Iterating from the bottom
(`V_0 = 1`, the trivial subgroup) gives only `V_μ ≤ 4^μ = n²`, the trivial `M ≤ n` — *no*
cancellation. This is the **structural cap**: the period's `√n`-cancellation (BGK) is **global**,
not the product of per-level gains, because the bottom levels (`n = 2,4`) genuinely have no
deficit (`V_1 ≈ 4`). The **only** source of improvement is the twist `‖η_H(b)−η_H(ωb)‖²` at the
worst frequency — and a uniform-in-`μ` lower bound on it is itself one-level BGK. This is *why*
no level-by-level recursion (C1/C7/C9) reaches `√n`.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.EtaCosetSplit

namespace ArkLib.ProximityGap.TowerCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Structural cap (one level).** Each dyadic tower level at most quadruples the squared period:
if both sub-periods are bounded by `V`, then `‖η_G(b)‖² ≤ 4V`. Unconditional — the twist is dropped.
Iterated from `V_0 = 1` this gives only `M ≤ n`; improvement requires the per-level twist (BGK). -/
theorem eta_sq_le_four {ψ : AddChar F ℂ} {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) {V : ℝ}
    (hb : ‖eta ψ H b‖ ^ 2 ≤ V) (hωb : ‖eta ψ H (ω * b)‖ ^ 2 ≤ V) :
    ‖eta ψ G b‖ ^ 2 ≤ 4 * V := by
  have hpar := eta_split_parallelogram (ψ := ψ) hω hG hdisj b
  have htwist : (0 : ℝ) ≤ ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2 := sq_nonneg _
  -- ‖η_G‖² = 2(‖η_H(b)‖²+‖η_H(ωb)‖²) − twist ≤ 2(V+V) = 4V
  nlinarith [hpar, htwist, hb, hωb]

end ArkLib.ProximityGap.TowerCeiling
#print axioms ArkLib.ProximityGap.TowerCeiling.eta_sq_le_four
