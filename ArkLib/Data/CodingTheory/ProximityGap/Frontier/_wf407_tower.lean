/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Gauss-period FOLDING / dyadic-tower recursion for the proximity-prize floor (Issue #407)

## Route: Hasse–Weil / Fermat-curve moments + 2-power tower self-similarity

This file is the analytic counterpart, *on the Gauss-sum side*, of the census `full_tower`
(`LamLeungTwoPow.lean`) and the polynomial tower factorization (`TwoPowerTowerFactorization.lean`).
It proves — axiom-clean, machine-verified to `1e-14` by `scripts/probes/_wf407_tower_recursion.py`
and `_wf407_tower_2ndmoment.py` — the **exact folding identity** that drives any 2-power tower
self-similarity argument for the prize floor `B = max_{b≠0} ‖η_b‖`,
`η_b(G) = ∑_{x∈G} ψ(b·x)`.

## The object and the regime

For `p − 1 = m·n`, `μ_n ⊆ F_p^×` the order-`n` (index-`m`) subgroup, `η_b(μ_n)` is the Gaussian
period / incomplete subgroup sum. The PRIZE FLOOR is `B(μ_n) = max_{b≠0} ‖η_b(μ_n)‖`, conjectured
`≤ C·√(n·log m)`. In the fixed-index regime of the newest #407 spec (`m ≈ 2^128` held constant,
`n → ∞`), the empirical `B/√(n log m) ∈ [1.0, 1.5]` is flat (`_wf407_hasseweil_dict.py`).

## What this file proves (the tower recursion)

If `μ_n ⊆ μ_{2n}` with `μ_{2n} = μ_n ⊔ ζ·μ_n` where `ζ ∈ μ_{2n}` has `ζ^n = −1` (a primitive
`2n`-th root, the dyadic generator), then for *every* frequency `b`:

> **`eta_fold`** :  `η_b(μ_{2n}) = η_b(μ_n) + η_{ζ·b}(μ_n)`.

This is the duplication formula `T⁴ − x⁴`-analog on the *analytic* side (cf. `QuartetTowerLaw`'s
`quartet_prod` on the census side): going one level up the dyadic tower splits the period into two
periods of the level below, the second shifted by the dyadic generator `ζ`. It is a pure splitting
of the index set, no Weil input.

Consequences (this file, axiom-clean):
* **`eta_fold_norm_le`** : `‖η_b(μ_{2n})‖ ≤ ‖η_b(μ_n)‖ + ‖η_{ζb}(μ_n)‖ ≤ 2·B(μ_n)` — the *trivial*
  triangle bound, giving only `B(μ_{2n}) ≤ 2·B(μ_n)` (i.e. `B ≤ n`, useless).
* **`eta_fold_normSq`** : `‖η_b(μ_{2n})‖² = ‖η_b(μ_n)‖² + ‖η_{ζb}(μ_n)‖² + 2·Re(η_b·conj η_{ζb})`
  — the second-moment fold, isolating the **cross term** `Re(η_b(μ_n)·conj η_{ζb}(μ_n))` whose sum
  over cosets the probe `_wf407_tower_2ndmoment.py` measures to be EXACTLY `−n/2` (negligible vs
  `V₂ ≈ p`): the second moments add cleanly up the tower. This is why the *typical* scale is
  `√n` at every level (`√2` per level on `Σ‖·‖²`); the **worst-case** `√(log m)` over-`√n` factor
  is NOT recovered at second-moment level and lives entirely in the higher moments.

## The obstruction this localizes (precise, honest)

The folding identity reduces `B(μ_{2n})` to controlling the SUM of two level-`n` periods. The √2
(not 2) growth — empirically `B(μ_{2n})/B(μ_n) ↓ √2` (`_wf407_tower_4thmoment.py`: 1.99→1.81→
1.59→1.50→…→1.4142) — requires the two summands `η_b(μ_n)`, `η_{ζb}(μ_n)` to be effectively
INDEPENDENT (no phase alignment) at the worst-case frequency. The second moment proves they are
*L²-orthogonal on average* (cross sum `= −n/2`), but the per-frequency worst-case independence is
the SAME open core as the per-frequency `√n` bound: the tower recursion does not by itself cross
the wall, it *re-expresses* it one level at a time. The deep-moment file `CharSumMomentDeepWall.lean`
records that the 2-power tower does not lower the deep moments (`E_r(μ_{2^a}) ≥ r!·n^r`, ratio grows
in `r`), consistent with this: the folding splits the worst case but cannot prove the two halves
don't align. **Residual: per-frequency worst-case independence of `η_b(μ_n)` and `η_{ζb}(μ_n)`** —
equivalently a square-root-cancellation bound on the `m` Gauss-sum phases, the prize core.

## References
- [Garcia–Lorenz–Todd] *Moments of Gaussian Periods and Modified Fermat Curves*, arXiv:2112.13886.
  Fixed-`k` Thm 1: `V₄ = 3p(k−1) − k³` (`2|k`); the `kurtosis-3` heavier-than-Gaussian tail.
- [LamLeung2000] vanishing sums of roots of unity (the census tower, `LamLeungTwoPow.lean`).
- [ABF26] 2026/680; [BGK06]; [HBK00].
-/

open Finset AddChar

namespace ArkLib.ProximityGap.Wf407Tower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Gaussian period / incomplete subgroup Gauss sum at frequency `b`:
`η_b(G) = ∑_{x∈G} ψ(b·x)`. (Re-declared standalone to keep imports minimal for `pg-iterate`.) -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ x ∈ G, ψ (b * x)

/-- **Scaling/shift law for the Gaussian period**: `η_b(ζ • G) = η_{ζb}(G)`, where `ζ • G` is the
image of `G` under multiplication by `ζ`. Pure reindexing of the sum (multiplication by `ζ ≠ 0`
is a bijection of `F`). This is the engine of the fold: the second coset `ζ·μ_n` of `μ_{2n}`
contributes the period of `μ_n` at the *shifted* frequency `ζb`. -/
theorem eta_smul (ψ : AddChar F ℂ) (G : Finset F) (b ζ : F) (hζ : ζ ≠ 0) :
    eta ψ (G.image (fun x => ζ * x)) b = eta ψ G (ζ * b) := by
  unfold eta
  rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel₀ hζ h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ring

/-- **THE GAUSS-PERIOD FOLDING IDENTITY** (the dyadic-tower recursion).  If the larger subgroup
splits as a disjoint union `H₂ = H ⊔ (ζ • H)` (the level-up coset decomposition, with `ζ` the
dyadic generator, `ζ^n = −1` for `H = μ_n`), then the period at level up is the sum of two
level-down periods, the second shifted by `ζ`:

`η_b(H₂) = η_b(H) + η_{ζb}(H)`.

Machine-verified exact (`_wf407_tower_recursion.py`, error `1e-14`). The analytic analog of the
census duplication `quartet_prod` (`QuartetTowerLaw.lean`); the recursion the whole 2-power
self-similarity route runs on. Stated with the disjoint-union hypothesis so it is a pure
index-splitting fact (no roots-of-unity arithmetic needed here — that only fixes *which* `ζ`). -/
theorem eta_fold (ψ : AddChar F ℂ) (H : Finset F) (b ζ : F) (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun x => ζ * x))) :
    eta ψ (H ∪ H.image (fun x => ζ * x)) b = eta ψ H b + eta ψ H (ζ * b) := by
  unfold eta
  rw [Finset.sum_union hdisj]
  congr 1
  -- second sum: ∑_{x ∈ ζ•H} ψ(b·x) = ∑_{y∈H} ψ(b·ζ·y) = ∑_{y∈H} ψ((ζb)·y)
  rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel₀ hζ h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ring

/-- **The trivial triangle bound up the tower**: `‖η_b(H₂)‖ ≤ ‖η_b(H)‖ + ‖η_{ζb}(H)‖`.  Hence
`B(H₂) ≤ 2·B(H)` — the recursion gives only the *useless* `B ≤ n` by itself; the √2-per-level
saving needs the cross-term cancellation (next), which is the open content. -/
theorem eta_fold_norm_le (ψ : AddChar F ℂ) (H : Finset F) (b ζ : F) (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun x => ζ * x))) :
    ‖eta ψ (H ∪ H.image (fun x => ζ * x)) b‖ ≤ ‖eta ψ H b‖ + ‖eta ψ H (ζ * b)‖ := by
  rw [eta_fold ψ H b ζ hζ hdisj]
  exact norm_add_le _ _

/-- **The second-moment fold**, isolating the cross term.  `‖η_b(H₂)‖² = ‖η_b(H)‖² + ‖η_{ζb}(H)‖²
+ 2·Re(η_b(H)·conj η_{ζb}(H))`.  The probe `_wf407_tower_2ndmoment.py` measures the *coset sum* of
the cross term to be EXACTLY `−n/2` (negligible), so the second moments add cleanly (`√2` per
level) — the typical scale is `√n` at every tower level.  The worst-case `√(log m)` factor is NOT
visible here; it is entirely in the higher moments (the deep-moment wall). -/
theorem eta_fold_normSq (ψ : AddChar F ℂ) (H : Finset F) (b ζ : F) (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun x => ζ * x))) :
    ‖eta ψ (H ∪ H.image (fun x => ζ * x)) b‖ ^ 2
      = ‖eta ψ H b‖ ^ 2 + ‖eta ψ H (ζ * b)‖ ^ 2
        + 2 * (eta ψ H b * (starRingEnd ℂ) (eta ψ H (ζ * b))).re := by
  rw [eta_fold ψ H b ζ hζ hdisj]
  -- ‖z + w‖² = ‖z‖² + ‖w‖² + 2 Re(z · conj w)
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]

end ArkLib.ProximityGap.Wf407Tower

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound`) -/
#print axioms ArkLib.ProximityGap.Wf407Tower.eta_smul
#print axioms ArkLib.ProximityGap.Wf407Tower.eta_fold
#print axioms ArkLib.ProximityGap.Wf407Tower.eta_fold_norm_le
#print axioms ArkLib.ProximityGap.Wf407Tower.eta_fold_normSq
