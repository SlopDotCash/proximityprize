/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Sweep A12 — Tower-recursive phase alignment as a NAMED STRUCTURAL lemma (#407, merged 389-T03)

**Actionable A12.** Re-land, as an axiom-clean Lean brick, the *exact* 2-adic tower recursion
behind the empirically-observed "phase alignment" of the two half-coset Gauss sums at the worst
frequency `b*`. The earlier `GaussPeriodTower.lean` (the parallelogram backbone) and
`_DyadicPhaseChaining*.lean` (the refuted descent) lived only on parallel worktrees and are
**absent from this checkout**; this file is the in-tree representative of the *structural* fact.

## The setup (substrate `SubgroupGaussSumSecondMoment.eta`)

`η_b(G) = Σ_{y∈G} ψ(b·y)` is the incomplete (Gauss-period) character sum over a `Finset G ⊆ F`.
For `n = 2^μ` and `μ_n` the order-`n` multiplicative subgroup of `Fˣ`, write `z` for a generator
of `μ_n` and split `μ_n = μ_{n/2} ⊔ z·μ_{n/2}` (`μ_{n/2} = ⟨z²⟩`; the two halves are disjoint).
Put

  `A := η_b(μ_{n/2})`,   `B := η_{b·z}(μ_{n/2})`   ( `= Σ_{x∈z·μ_{n/2}} ψ(b·x)` ).

## What is PROVEN here (axiom-clean, elementary; the structural fact)

1. **The untwisted half-coset split** (`eta_split_coset`):
   `η_b(G_half ⊔ z·G_half) = η_b(G_half) + η_{b·z}(G_half) = A + B`.
   Pure `Finset.sum_union` + reindex of the `z`-coset (`Finset.sum_image`).

2. **The TWISTED companion** (`etaTwist`, `eta_twist_split`):
   `η^χ_b := η_b(G_half) − η_{b·z}(G_half) = A − B`
   — the sum over `μ_n` with the order-2 multiplicative character `χ` (trivial on `μ_{n/2}`,
   `−1` on the `z`-coset) folded in.

3. **The exact PARALLELOGRAM tower identity** (`gaussPeriod_tower_parallelogram`):
   `‖η_b(μ_n)‖² + ‖η^χ_b(μ_n)‖² = 2·(‖A‖² + ‖B‖²)`.
   This is the exact 2-adic recursion: the level-`n` untwisted+twisted energy equals **twice**
   the sum of the two level-`n/2` half-energies. No approximation.

4. **The alignment characterization** (`untwisted_ge_twisted_iff_align`):
   `‖A+B‖ ≥ ‖A−B‖ ⟺ 0 ≤ re⟨A,B⟩` (the cross term `2·Re(A·conj B)` is `≥0`).
   At the maximizing frequency `b*` the maximum is realized by the **untwisted** branch
   `A+B = η_{b*}(μ_n)` (the cross term is `≥0`), which is exactly the measured
   "phase alignment". Since `μ_n` is negation-closed (`−1 = z^{n/2} ∈ μ_n`), `A` and `B` are
   real (probe: `max|Im| ~ 1e-15`), so the cross term `= 2·A·B` and "cos = 1.0000" is just
   "`A,B` have the same sign at `b*`".

## What this is NOT (honesty contract — the descent is REFUTED, do not reread it in)

- This is **NOT** a descent claim. The naive `M(n)² ≤ 2·M(n/2)²` (taking `‖η^χ‖² ≥ 0` and
  `‖A‖,‖B‖ ≤ M(n/2)`) is **FALSE at finite `n`** (worst-case ratios spike to `2.68 > 2`; the
  single-level `LocalAlignedChildSubmaximality` was refuted axiom-clean). The parallelogram
  identity is an EXACT equality with NO inequality direction that closes the floor.
- The value of this brick is precisely as the actionable states: **a precise statement of the
  one mechanism the moment hierarchy (L², L⁴, …, `E_r`) cannot see.** The moment hierarchy sees
  only `Σ_b ‖η_b‖^{2r}` (symmetric in `b`, blind to *which* frequency aligns); the
  parallelogram split tracks the per-`b*` *coherent addition* of the two children — the
  worst-vs-average gap. It is a structural lemma, not a closure.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Cross-checked by `scripts/probes/sweep_A12_phase_align.py`
  (split residual ~1e-15, parallelogram residual ~1e-14, alignment cos>0.999 in/out of regime,
  persistence one level down, proxy faithfulness tabulated).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.Sweep_A12

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Reindexing the `z`-coset.** `η_b` summed over `z·G_half` equals `η_{b·z}` over `G_half`:
`Σ_{x∈ z·G_half} ψ(b·x) = Σ_{y∈G_half} ψ((b·z)·y)`. Pure `Finset.sum_image` (`z·` injective for
`z ≠ 0`) + `b·(z·y) = (b·z)·y`. -/
theorem eta_over_smul_coset (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) (hz : z ≠ 0) :
    eta ψ (Ghalf.image (fun y => z * y)) b = eta ψ Ghalf (b * z) := by
  unfold eta
  rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel₀ hz h)]
  exact Finset.sum_congr rfl (fun y _ => by rw [mul_assoc])

/-- **The untwisted half-coset split.** For the disjoint union `G = G_half ⊔ (z·G_half)`,
`η_b(G) = η_b(G_half) + η_{b·z}(G_half) = A + B`. (`Finset.sum_union` over the disjoint halves
plus the reindex above.) -/
theorem eta_split_coset (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) (hz : z ≠ 0)
    (hdisj : Disjoint Ghalf (Ghalf.image (fun y => z * y))) :
    eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b
      = eta ψ Ghalf b + eta ψ Ghalf (b * z) := by
  have hsplit : eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b
      = eta ψ Ghalf b + eta ψ (Ghalf.image (fun y => z * y)) b := by
    unfold eta
    exact Finset.sum_union hdisj
  rw [hsplit, eta_over_smul_coset ψ Ghalf b z hz]

/-- The **twisted** companion period `η^χ_b := A − B`, the order-2 multiplicative character `χ`
(trivial on `G_half`, `−1` on `z·G_half`) folded into the Gauss period over `μ_n`. -/
noncomputable def etaTwist (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) : ℂ :=
  eta ψ Ghalf b - eta ψ Ghalf (b * z)

/-- The twisted period is `A − B` with `A = η_b(G_half)`, `B = η_{b·z}(G_half)` — definitional,
recorded for symmetry with `eta_split_coset`. -/
theorem eta_twist_split (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) :
    etaTwist ψ Ghalf b z = eta ψ Ghalf b - eta ψ Ghalf (b * z) := rfl

/-- **The exact parallelogram tower identity (the structural backbone).** For ANY two complex
half-period values `A, B`, the untwisted+twisted energy at level `n` equals twice the sum of the
two level-`n/2` half-energies:
`‖A + B‖² + ‖A − B‖² = 2·(‖A‖² + ‖B‖²)`. -/
theorem norm_parallelogram (A B : ℂ) :
    ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) :=
  parallelogram_law_with_norm ℝ A B

/-- **The Gauss-period tower recursion, instantiated.** With `A = η_b(G_half)`,
`B = η_{b·z}(G_half)`, the untwisted period (`= η_b(μ_n)` by `eta_split_coset`) and the twisted
period `η^χ_b` satisfy
`‖η_b(μ_n)‖² + ‖η^χ_b‖² = 2·(‖A‖² + ‖B‖²)`.
This is the exact 2-adic energy recursion; NOTE it is an EQUALITY — it does NOT yield the
(refuted) descent `M(n)² ≤ 2·M(n/2)²`. -/
theorem gaussPeriod_tower_parallelogram (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F)
    (hz : z ≠ 0) (hdisj : Disjoint Ghalf (Ghalf.image (fun y => z * y))) :
    ‖eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b‖ ^ 2 + ‖etaTwist ψ Ghalf b z‖ ^ 2
      = 2 * (‖eta ψ Ghalf b‖ ^ 2 + ‖eta ψ Ghalf (b * z)‖ ^ 2) := by
  rw [eta_split_coset ψ Ghalf b z hz hdisj, eta_twist_split]
  exact norm_parallelogram _ _

/-- **The squared-norm cross-term identity.** `‖A+B‖² − ‖A−B‖² = 4·Re(A·conj B)`. The exact
difference between the untwisted and twisted branches is `4×` the cross term. -/
theorem norm_add_sub_norm_sub_eq_cross (A B : ℂ) :
    ‖A + B‖ ^ 2 - ‖A - B‖ ^ 2 = 4 * (A * (starRingEnd ℂ) B).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  ring

/-- **The phase-alignment characterization.** The untwisted branch `A+B` dominates the twisted
branch `A−B` (in squared norm) **iff** the cross term `Re(A·conj B) ≥ 0` — i.e. the two children
add coherently. This is the *exact* content of the measured `cos = 1.0000`: at the maximizing
frequency `b*`, the maximum `η_{b*}(μ_n) = A+B` is the untwisted branch because the cross term is
nonnegative (probe: `untwist_bigger = True` in all cases). Since `A, B` are real (negation
symmetry), `Re(A·conj B) = A·B`, so this is exactly "`A, B` have the same sign". -/
theorem untwisted_ge_twisted_iff_align (A B : ℂ) :
    ‖A - B‖ ^ 2 ≤ ‖A + B‖ ^ 2 ↔ 0 ≤ (A * (starRingEnd ℂ) B).re := by
  rw [← sub_nonneg, norm_add_sub_norm_sub_eq_cross]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Corollary: alignment ⟹ the untwisted period is the worst-case branch.** When the cross
term is nonnegative (`0 ≤ Re(A·conj B)`), the *untwisted* Gauss period `η_b(μ_n) = A+B`
(`= eta ψ (Ghalf ∪ z·Ghalf) b`) has norm at least that of its twisted companion `η^χ_b = A−B`.
At the maximizing frequency `b*` this is forced (the maximum is realized by the untwisted
branch), which is the measured phase alignment. -/
theorem eta_untwisted_norm_ge_twist_of_align (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F)
    (hz : z ≠ 0) (hdisj : Disjoint Ghalf (Ghalf.image (fun y => z * y)))
    (halign : 0 ≤ (eta ψ Ghalf b * (starRingEnd ℂ) (eta ψ Ghalf (b * z))).re) :
    ‖etaTwist ψ Ghalf b z‖ ≤ ‖eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b‖ := by
  rw [eta_split_coset ψ Ghalf b z hz hdisj, eta_twist_split]
  have hsq : ‖eta ψ Ghalf b - eta ψ Ghalf (b * z)‖ ^ 2
      ≤ ‖eta ψ Ghalf b + eta ψ Ghalf (b * z)‖ ^ 2 :=
    (untwisted_ge_twisted_iff_align _ _).mpr halign
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq

/-
**VERDICT (A12 — phase-alignment tower, structural).**
Probe `scripts/probes/sweep_A12_phase_align.py` (n=8,16,32,64; p~n² and prize-shaped p~n⁴):
- `cos(align A,B) = +1.00000` EXACTLY at the worst frequency `b*`, ALL 8 cases (the untwisted
  `|A+B|` realizes the max; `untwist_bigger = True` everywhere).
- SPLIT residual ≤ 7e-15, PARALLELOGRAM residual ≤ 5e-13 (= float noise): both identities exact.
- A, B real to ≤ 5e-15 (negation symmetry `−1 = z^{n/2} ∈ μ_n` — so "cos=1" = "same sign").
- PERSISTENCE one 2-adic level down: cos = +1 in 7/8 cases but **flips to −1** at n=8,p=73 — the
  top-level alignment is forced (it IS the max), but it does NOT robustly persist deeper. This is a
  fresh, independent confirmation of why the descent fails.
- PROXY faithfulness `|S_b*(μ_{n/2})| / B(μ_{n/2})` rises toward 1 with `p` (0.92–0.999 at p~n⁴)
  but dips to 0.47/0.63 at the smallest primes — the worst `μ_n` frequency only *approximately*
  maximizes `μ_{n/2}`.

This file lands the EXACT structural backbone (split + twist + parallelogram + alignment iff),
axiom-clean. It is **NOT** a descent: the parallelogram is an EQUALITY; the naive
`M(n)² ≤ 2·M(n/2)²` is refuted (worst-case ratios spike to 2.68). The value is a precise
statement of the worst-vs-average coherent-addition mechanism that the symmetric moment hierarchy
`Σ_b ‖η_b‖^{2r}` cannot see. No fabricated closure.
-/

end ArkLib.ProximityGap.Sweep_A12

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.Sweep_A12.eta_over_smul_coset
#print axioms ArkLib.ProximityGap.Sweep_A12.eta_split_coset
#print axioms ArkLib.ProximityGap.Sweep_A12.norm_parallelogram
#print axioms ArkLib.ProximityGap.Sweep_A12.gaussPeriod_tower_parallelogram
#print axioms ArkLib.ProximityGap.Sweep_A12.norm_add_sub_norm_sub_eq_cross
#print axioms ArkLib.ProximityGap.Sweep_A12.untwisted_ge_twisted_iff_align
#print axioms ArkLib.ProximityGap.Sweep_A12.eta_untwisted_norm_ge_twist_of_align
