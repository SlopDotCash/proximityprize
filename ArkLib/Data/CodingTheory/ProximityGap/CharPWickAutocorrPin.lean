/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPWickConditionalPin

/-!
# Sharpening the Wick pin: `c_r ≤ 1` from the WORST single off-diagonal autocorrelation (#444)

`CharPWickConditionalPin` reduced the prize to the single inequality `c_r ≤ 1`
(`cross_r ≤ 2r·n·Wick_r`), where `cross_r = ∑_{s∈G} ∑_{t∈G,t≠s} C_r(s−t)` is the off-diagonal
autocorrelation mass.  The only in-tree handle on each term was the diagonal bound
`autocorr_le_energy : C_r(δ) ≤ E_r`, giving `cross_r ≤ |G|(|G|−1)·E_r` — the trivial ceiling.

This file sharpens that:  `cross_r ≤ |G|(|G|−1)·M`, where `M` is **any** upper bound on the WORST
single off-diagonal autocorrelation `max_{s≠t} C_r(s−t)`.  The probe
`scripts/probes/probe_cross_structure.py` (exact, PROPER thin `μ_n`, `p ≈ n^4`, never `n = q−1`)
shows the off-diagonal autocorrelations are NEARLY UNIFORM (`cross_r ≈ |G|(|G|−1)·max C`, shell
concentration ≈ 1.03) AND the worst one is `2–16×` below `E_r` (`maxC/E_r` ranges `0.06–0.48` on the
clean rungs), so this is a genuinely tighter handle: the single inequality `c_r ≤ 1` follows from a
sup-bound on ONE localized autocorrelation, not the full energy.

## What is proven (axiom-clean, char-`p`, any finite `G`)

* `cross_le_card_mul_of_autocorrBound` : `(∀ s∈G, ∀ t∈G.erase s, C_r(s−t) ≤ M) ⟹
    cross_r ≤ |G|·(|G|−1)·M`.  The sharper cross ceiling (worst autocorrelation `M` replaces `E_r`).
* `crossBoundedByWick_of_autocorrBound` : if for every `r ≥ 1` the worst off-diagonal autocorrelation
    is `≤ M_r` with `|G|·(|G|−1)·M_r ≤ 2r·|G|·Wick_r`, then the single open `Prop`
    `CrossBoundedByWick` holds — i.e. the prize pin's hypothesis reduces to the per-`r` autocorrelation
    sup-bound `M_r ≤ 2r·Wick_r/(|G|−1)`.
* `eta_pow2r_le_wick_of_autocorrBound` : the end-to-end consumer — the per-`r` autocorrelation
    sup-bound ⟹ `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for every `b`.

## Honest scope

Still a CONDITIONAL pin.  The per-`r` autocorrelation sup-bound `max_{δ≠0} C_r(δ) ≤ 2r·Wick_r/(n−1)`
at depth `r ≍ log m` IS the same recognized-open char-`p` BGK/Lam–Leung wall, just localized to the
single worst off-diagonal autocorrelation instead of the full energy.  It is FALSE in the thick
window and only conjectured at `β ≥ 4`; STATED, not proved.  The sharpening is real (the probe shows
`|G|(|G|−1)·M ≪ |G|(|G|−1)·E_r`), but it does NOT close `CrossBoundedByWick`.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

## References
- Shaw, `docs/kb/direct-charp-supnorm-assault-2026-06-15.md` (#444).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open scoped Nat
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPMomentRecursion (autocorr)
open ArkLib.ProximityGap.CharPWickConditionalPin
  (cross wick CrossBoundedByWick eta_pow2r_le_wick_of_crossBound)

namespace ArkLib.ProximityGap.CharPWickAutocorrPin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The sharper cross ceiling: worst single autocorrelation `M` replaces `E_r` -/

/-- **The sharper cross ceiling `cross_r ≤ |G|·(|G|−1)·M`** from any uniform upper bound `M` on the
off-diagonal autocorrelations `C_r(s−t)` (`s ≠ t`).  Each of the `|G|·(|G|−1)` off-diagonal terms is
`≤ M`; the erase-set has `|G|−1` elements.  Strictly sharpens the trivial `cross_r ≤ |G|(|G|−1)·E_r`
(take `M = E_r`), since the probe shows `max_{δ≠0} C_r(δ) ≪ E_r`. -/
theorem cross_le_card_mul_of_autocorrBound (G : Finset F) (r : ℕ) (M : ℕ)
    (hM : ∀ s ∈ G, ∀ t ∈ G.erase s, autocorr G r (s - t) ≤ M) :
    cross G r ≤ G.card * (G.card - 1) * M := by
  unfold cross
  calc ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t)
      ≤ ∑ s ∈ G, ∑ _t ∈ G.erase s, M := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        exact Finset.sum_le_sum (fun t ht => hM s hs t ht)
    _ = ∑ _s ∈ G, (G.card - 1) * M := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [Finset.sum_const, Finset.card_erase_of_mem hs, smul_eq_mul]
    _ = G.card * (G.card - 1) * M := by
        rw [Finset.sum_const, smul_eq_mul]; ring

/-! ### The autocorrelation sup-bound ⟹ the single open `Prop` -/

/-- **The per-`r` autocorrelation sup-bound implies `CrossBoundedByWick`.**  If for every `r ≥ 1` the
worst off-diagonal autocorrelation is `≤ M r` and the localized budget
`|G|·(|G|−1)·(M r) ≤ 2r·|G|·Wick_r` holds, then the single open hypothesis `CrossBoundedByWick` of the
Wick pin holds.  So the prize reduces to the per-`r` autocorrelation sup-bound
`max_{δ≠0} C_r(δ) ≤ 2r·Wick_r/(|G|−1)`. -/
theorem crossBoundedByWick_of_autocorrBound (G : Finset F) (M : ℕ → ℕ)
    (hM : ∀ r, 1 ≤ r → ∀ s ∈ G, ∀ t ∈ G.erase s, autocorr G r (s - t) ≤ M r)
    (hbudget : ∀ r, 1 ≤ r → G.card * (G.card - 1) * (M r) ≤ 2 * r * (G.card * wick G.card r)) :
    CrossBoundedByWick G := by
  intro r hr
  calc cross G r ≤ G.card * (G.card - 1) * (M r) :=
        cross_le_card_mul_of_autocorrBound G r (M r) (hM r hr)
    _ ≤ 2 * r * (G.card * wick G.card r) := hbudget r hr

/-! ### The end-to-end consumer -/

/-- **End-to-end: the per-`r` autocorrelation sup-bound ⟹ the prize-floor moment bound.**
Compose `crossBoundedByWick_of_autocorrBound` with the Wick-pin consumer: a per-`r` bound on the
worst off-diagonal autocorrelation gives `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for every `b`. -/
theorem eta_pow2r_le_wick_of_autocorrBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (M : ℕ → ℕ)
    (hM : ∀ r, 1 ≤ r → ∀ s ∈ G, ∀ t ∈ G.erase s, autocorr G r (s - t) ≤ M r)
    (hbudget : ∀ r, 1 ≤ r → G.card * (G.card - 1) * (M r) ≤ 2 * r * (G.card * wick G.card r))
    (r : ℕ) (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r) :=
  eta_pow2r_le_wick_of_crossBound hψ G
    (crossBoundedByWick_of_autocorrBound G M hM hbudget) r hr b

end ArkLib.ProximityGap.CharPWickAutocorrPin

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CharPWickAutocorrPin.cross_le_card_mul_of_autocorrBound
#print axioms ArkLib.ProximityGap.CharPWickAutocorrPin.crossBoundedByWick_of_autocorrBound
#print axioms ArkLib.ProximityGap.CharPWickAutocorrPin.eta_pow2r_le_wick_of_autocorrBound
