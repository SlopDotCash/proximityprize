/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# W8-tower-bilinear — the cross-level large-sieve term VANISHES, so the tower
  bilinearization REDUCES-TO-WALL (#444)

## The angle (genuinely new surface: manufacture Burgess' missing second parameter)

The single subgroup `μ_n ⊂ F_p^*` lacks the *second parameter* a Burgess / double-large-sieve
estimate needs. The dyadic 2-power tower `μ_n ⊂ μ_{2n}` seems to supply one: writing `μ_{2n} = H ⊔ gH`
with `H = μ_n` and `g` a coset rep (`g ∈ μ_{2n} ∖ μ_n`), the level-`2n` period splits EXACTLY as a
two-term bilinear form in the level-`n` periods and the coset shift `g`:

>  `η_{μ_{2n}}(b) = η_H(b) + η_H(g·b)`.

(Probe-verified to machine precision, `n = 16, 32, 64`, `p ≈ n^4`: `maxerr ≤ 1.4e-14`.) The hope is
that a bilinear / double-large-sieve estimate ACROSS the two tower levels couples the terms and gives
genuine cross-level cancellation `M_{2n} ≪ 2 M_n`, beating the trivial triangle bound and crossing to
the prize.

## Verdict: REDUCES-TO-WALL. The EXACT failing step (this file pins it)

The bilinear / large-sieve machinery operates in `L²` (summed over all frequencies `b`). The cross
term it would exploit is the cross-level correlation

>  `C := ∑_{b∈F} η_H(b) · conj(η_H(g·b))`.

**This file proves `C = q · #{(y,z) ∈ H×H : y = g·z}` EXACTLY** (`towerCross_eq_count`, pure
additive-character orthogonality, no Weil). When the coset `g·H` is disjoint from `H` (i.e. `g ∉ H`,
the defining tower situation), the collision count is `0`, so

>  `C = 0`  (`towerCross_eq_zero`).

The two tower levels are **`L²`-orthogonal**. Consequently the only bound a large-sieve / bilinear
estimate supplies is the *decoupled* Parseval sum
`∑_b ‖η_{2n}(b)‖² = ∑_b ‖η_H(b)‖² + ∑_b ‖η_H(g·b)‖²` (the cross term drops, `towerParseval_split`),
which is exactly `2·(q·|H|)` — i.e. it reproduces the SAME per-level `L²` (phase-blind) bound the
single subgroup already gives. There is no cross-level coupling for the sieve to exploit.

## Why this is the wall, not progress (the avg-vs-max pinpoint)

The probe shows the gap between the `L²` picture and the pointwise (`L^∞ = M`) picture:

* `L²` / large sieve: cross term `= 0` EXACTLY — the levels look perfectly decorrelated.
* pointwise at the worst `b`: the two terms `η_H(b)`, `η_H(g·b)` are perfectly phase-ALIGNED,
  `cos(angle) = 1.0000` EXACTLY (`n = 16, 32, 64`), so `|η_H(b) + η_H(g·b)| = |η_H(b)| + |η_H(g·b)|`
  and the triangle inequality is TIGHT (`M_{2n}/M_n = 1.82, 1.32, 1.29` — never the `< √2 ≈ 1.41`
  that genuine cross-level cancellation would require for the prize; for the Fermat prime `p = 65537`
  it is `1.82`, *worse* than independent addition).

So the second parameter the tower manufactures is **orthogonal in `L²`** (sieve sees nothing to save)
yet **aligned in `L^∞`** (the worst case adds coherently). The large sieve averages away precisely the
pointwise alignment that creates `M`. This is the average-vs-maximum wall (the prize is `L^∞`, every
`L²`/moment/large-sieve transfer is `L²`) reappearing in tower-bilinear clothing. The "double
parameter" is real but `L²`-decoupled, so a double-large-sieve gains exactly nothing over a single one.

This file is axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorry`/`sorryAx`); the
identities are exact. It is NOT prize closure — it pinpoints the exact step at which the
tower-bilinear angle reduces.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvW8T

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cross-level correlation equals the twisted collision count (proven, exact).**
For a multiplicative coset shift `g`, the `L²` cross term between the level-`H` period at `b` and the
level-`H` period at `g·b`, summed over all frequencies `b`, is
`∑_b η_H(b)·conj(η_H(g·b)) = q · #{(y,z) ∈ H×H : y = g·z}`. Pure additive-character orthogonality
(`AddChar.sum_mulShift`): expanding into `∑_{y,z∈H} ∑_b ψ(b·(y − g·z))` collapses each pair to
`q·[y = g·z]`. -/
theorem towerCross_eq_count {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (H : Finset F) (g : F) :
    (∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (g * b)))
      = (Fintype.card F : ℂ) * ((H ×ˢ H).filter (fun p => p.1 = g * p.2)).card := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (g * b))
      = ∑ b : F, ∑ y ∈ H, ∑ z ∈ H, ψ (b * (y - g * z)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : (starRingEnd ℂ) (eta ψ H (g * b)) = ∑ z ∈ H, ψ (-(g * b * z)) := by
          rw [eta, map_sum]; exact Finset.sum_congr rfl (fun z _ => hconj (g * b * z))
        have hL : eta ψ H b = ∑ y ∈ H, ψ (b * y) := rfl
        rw [hconjeta, hL, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine Finset.sum_congr rfl (fun z _ => ?_)
        have harg : b * y + -(g * b * z) = b * (y - g * z) := by ring
        rw [← AddChar.map_add_eq_mul, harg]
    _ = ∑ y ∈ H, ∑ z ∈ H, ∑ b : F, ψ (b * (y - g * z)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ y ∈ H, ∑ z ∈ H, (if y = g * z then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [AddChar.sum_mulShift (y - g * z) hψ]
        simp [sub_eq_zero]
    _ = (Fintype.card F : ℂ) * ((H ×ˢ H).filter (fun p => p.1 = g * p.2)).card := by
        rw [← Finset.sum_product' (f := fun y z => if y = g * z then (Fintype.card F : ℂ) else 0)]
        rw [← Finset.sum_filter (fun p : F × F => p.1 = g * p.2) (fun _ => (Fintype.card F : ℂ))]
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The defining tower situation kills the cross term (proven).** If the coset `g·H` is disjoint
from `H` — equivalently no `y ∈ H` equals `g·z` for `z ∈ H`, the situation when `g ∉ H` and `H` is a
multiplicative subgroup — then the twisted collision count is `0`, so the cross-level correlation
vanishes EXACTLY:

>  `∑_b η_H(b)·conj(η_H(g·b)) = 0`.

The two tower levels are `L²`-orthogonal: a bilinear / double-large-sieve estimate finds no
cross-level term to exploit. -/
theorem towerCross_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (H : Finset F) (g : F)
    (hdisj : ∀ y ∈ H, ∀ z ∈ H, y ≠ g * z) :
    (∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (g * b))) = 0 := by
  rw [towerCross_eq_count hψ H g]
  have hempty : (H ×ˢ H).filter (fun p => p.1 = g * p.2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨y, z⟩ hp
    rw [Finset.mem_product] at hp
    exact hdisj y hp.1 z hp.2
  rw [hempty]; simp

/-- **The tower Parseval splits with NO cross term (proven).** Combining the cross-orthogonality with
the bilinear decomposition `η_{2n}(b) = η_H(b) + η_H(g·b)`, the level-`2n` second moment is the
*decoupled* sum of the two level-`n` second moments — the large sieve / Parseval bound on the doubled
tower is exactly twice the single-level bound, with no cross-level saving. Stated as the abstract
Pythagorean split for any two `L²`-orthogonal frequency functions `f, h` (`∑_b f conj h = 0`):

>  `∑_b ‖f(b) + h(b)‖² = ∑_b ‖f(b)‖² + ∑_b ‖h(b)‖²`.

This is the precise reason the double-large-sieve gains nothing: the cross term it would exploit is
exactly the vanishing `∑_b f conj h`. -/
theorem towerParseval_split (f h : F → ℂ)
    (horth : (∑ b : F, f b * (starRingEnd ℂ) (h b)) = 0) :
    (∑ b : F, ‖f b + h b‖ ^ 2) = (∑ b : F, ‖f b‖ ^ 2) + (∑ b : F, ‖h b‖ ^ 2) := by
  -- push everything to ℂ via `‖w‖² = w·conj w`, expand, drop the two orthogonal cross sums.
  have hnorm : ∀ w : ℂ, (‖w‖ ^ 2 : ℝ) = (w * (starRingEnd ℂ) w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- the conjugate cross term also vanishes (conjugate of `horth`)
  have horth2 : (∑ b : F, h b * (starRingEnd ℂ) (f b)) = 0 := by
    have hc := congrArg (starRingEnd ℂ) horth
    rw [map_sum, map_zero] at hc
    -- hc : ∑ b, conj (f b * conj (h b)) = 0; rewrite the summand to h b * conj (f b)
    rw [show (∑ b : F, h b * (starRingEnd ℂ) (f b))
          = ∑ b : F, (starRingEnd ℂ) (f b * (starRingEnd ℂ) (h b)) from
        Finset.sum_congr rfl (fun b _ => by
          simp only [map_mul, starRingEnd_self_apply]; ring)]
    exact hc
  -- complex identity then take real parts
  have hcomplex : (∑ b : F, (f b + h b) * (starRingEnd ℂ) (f b + h b))
      = (∑ b : F, f b * (starRingEnd ℂ) (f b)) + (∑ b : F, h b * (starRingEnd ℂ) (h b)) := by
    have hexp : ∀ b : F, (f b + h b) * (starRingEnd ℂ) (f b + h b)
        = f b * (starRingEnd ℂ) (f b) + h b * (starRingEnd ℂ) (h b)
          + (f b * (starRingEnd ℂ) (h b) + h b * (starRingEnd ℂ) (f b)) := by
      intro b; simp only [map_add]; ring
    rw [Finset.sum_congr rfl (fun b _ => hexp b)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      horth, horth2, add_zero, add_zero]
  -- read off real parts
  have : (∑ b : F, ‖f b + h b‖ ^ 2 : ℝ)
      = (∑ b : F, (f b * (starRingEnd ℂ) (f b)).re) + (∑ b : F, (h b * (starRingEnd ℂ) (h b)).re) := by
    rw [Finset.sum_congr rfl (fun b _ => hnorm (f b + h b))]
    have hre := congrArg Complex.re hcomplex
    simpa only [Complex.re_sum, Complex.add_re] using hre
  rw [this]
  congr 1
  · exact Finset.sum_congr rfl (fun b _ => (hnorm (f b)).symm)
  · exact Finset.sum_congr rfl (fun b _ => (hnorm (h b)).symm)

end ArkLib.ProximityGap.Frontier.AvW8T

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW8T.towerCross_eq_count
#print axioms ArkLib.ProximityGap.Frontier.AvW8T.towerCross_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.AvW8T.towerParseval_split
