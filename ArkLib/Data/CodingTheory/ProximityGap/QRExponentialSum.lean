/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The quadratic-residue exponential sum equals a Gauss sum (#389)

For the quadratic-residue subgroup `QR = {a ∈ F_p : χ a = 1}` (`χ` the quadratic character to `ℂ`),
the incomplete exponential sum `η_b = ∑_{a∈QR} ψ(b·a)` is expressed via the Gauss sum
`τ = gaussSum χ ψ`:

> **`eta_QR_eq`** — for `b ≠ 0`, `∑_{a∈QR} ψ(b·a) = (χ(b)·τ − 1)/2`.

This is the foundational step toward the exact additive energy of the quadratic residues
(`E(QR) = (p−1)(p²−2p+9)/16` for `p≡1 mod 4`, `(p−1)(p²−2p+5)/16` for `p≡3 mod 4`): combined with
the in-tree 4th-moment bridge `∑_b ‖η_b‖⁴ = p·E(QR)` (`SubgroupGaussSumFourthMoment`, since `QR` is
a multiplicative subgroup) and the quadratic Gauss-sum value `τ² = χ(−1)·p` (`gaussSum_sq`), it
evaluates the QR additive energy in closed form — the exact "bad-side" extreme of the δ\* dichotomy.
Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic character of `ZMod p` valued in `ℂ`. -/
noncomputable def chiC : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The quadratic-residue subgroup `{a : χ a = 1}` as a `Finset`. -/
noncomputable def QR (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter (fun a => chiC (p := p) a = 1)

theorem chiC_apply (a : ZMod p) :
    chiC a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := rfl

theorem chiC_zero : chiC (0 : ZMod p) = 0 := by
  simp [chiC_apply, quadraticChar_zero]

theorem ringChar_zmod_ne_two_of_two_lt (hp2 : 2 < p) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ringChar.eq (ZMod p) p]
  omega

/-- The pushed quadratic character is nontrivial for odd prime fields. -/
theorem chiC_ne_one (hp2 : 2 < p) : chiC (p := p) ≠ 1 := by
  rw [chiC, Ne, MulChar.ringHomComp_eq_one_iff (f := Int.castRingHom ℂ)
      (by exact_mod_cast Int.cast_injective)]
  exact quadraticChar_ne_one (F := ZMod p) (ringChar_zmod_ne_two_of_two_lt hp2)

/-- The pushed quadratic character is quadratic. -/
theorem chiC_isQuadratic : (chiC (p := p)).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

/-- The value of `χ` at `-1`, exposed in the `chiC` API. -/
theorem chiC_neg_one (hp2 : 2 < p) :
    chiC (p := p) (-1) = ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℂ) := by
  rw [chiC_apply,
    quadraticChar_neg_one (F := ZMod p) (ringChar_zmod_ne_two_of_two_lt hp2), ZMod.card]

/-- The quadratic Gauss-sum square specialized to `chiC`. This is the exact algebraic input
needed to evaluate the QR fourth-moment expression. -/
theorem gaussSum_chiC_sq (hp2 : 2 < p) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC (p := p)) ψ ^ 2 = chiC (p := p) (-1) * (p : ℂ) := by
  simpa [ZMod.card] using
    (gaussSum_sq (chiC_ne_one (p := p) hp2) chiC_isQuadratic hψ)

theorem zero_not_mem_QR : (0 : ZMod p) ∉ QR p := by
  simp [QR, chiC_zero]

/-- For `a ≠ 0`, the indicator `[a ∈ QR] = (1 + χ a)/2` over `ℂ`. -/
theorem qr_indicator {a : ZMod p} (ha : a ≠ 0) :
    (if chiC (p := p) a = 1 then (1 : ℂ) else 0) = (1 + chiC a) / 2 := by
  have hsq : chiC (p := p) a = 1 ∨ chiC (p := p) a = -1 := by
    have := quadraticChar_dichotomy (F := ZMod p) ha
    rcases this with h | h <;> [left; right] <;>
      simp [chiC_apply, h]
  rcases hsq with h | h <;> rw [h] <;> norm_num

/-- **QR exponential sum = Gauss sum.** For `b ≠ 0`,
`∑_{a∈QR} ψ(b·a) = (χ(b)·gaussSum χ ψ − 1)/2`. -/
theorem eta_QR_eq {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) {b : ZMod p} (hb : b ≠ 0) :
    eta ψ (QR p) b = (chiC b * gaussSum chiC ψ - 1) / 2 := by
  classical
  have hbu : IsUnit b := Ne.isUnit hb
  -- rewrite the sum over QR as an indicator sum over univ
  have hfilt : eta ψ (QR p) b
      = ∑ a : ZMod p, (if chiC (p := p) a = 1 then ψ (b * a) else 0) := by
    rw [eta, QR, Finset.sum_filter]
  rw [hfilt]
  -- split each term: indicator·ψ = ((1+χa)/2)·ψ for a≠0; the a=0 term is 0 both ways
  have hterm : ∀ a : ZMod p, (if chiC (p := p) a = 1 then ψ (b * a) else 0)
      = (1 + chiC a) / 2 * ψ (b * a) - (if a = 0 then (1 : ℂ) / 2 else 0) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · rw [chiC_zero]
      simp [AddChar.map_zero_eq_one]
    · rw [if_neg ha, ← qr_indicator ha]
      by_cases h : chiC (p := p) a = 1 <;> simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib]
  -- the correction sum is just the a=0 term = 1/2
  have hcorr : ∑ a : ZMod p, (if a = 0 then (1 : ℂ) / 2 else 0) = 1 / 2 := by
    simp
  rw [hcorr]
  -- main sum splits into the trivial part and the gauss part
  have hmain : ∑ a : ZMod p, (1 + chiC a) / 2 * ψ (b * a)
      = (1 / 2) * ((∑ a : ZMod p, ψ (b * a)) + ∑ a : ZMod p, chiC a * ψ (b * a)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [hmain]
  -- ∑ ψ(b·a) = 0  (b ≠ 0, primitive ψ)
  have hψ0 : ∑ a : ZMod p, ψ (b * a) = 0 := by
    have h := AddChar.sum_mulShift (R := ZMod p) b hψ
    simp_rw [mul_comm b] at *
    simpa [hb] using h
  -- ∑ χa·ψ(b·a) = gaussSum χ (mulShift ψ b) = χ(b)·τ
  have hgs : ∑ a : ZMod p, chiC a * ψ (b * a) = chiC b * gaussSum chiC ψ := by
    have hmul : ∑ a : ZMod p, chiC a * ψ (b * a)
        = gaussSum chiC (AddChar.mulShift ψ b) := by
      rw [gaussSum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [AddChar.mulShift_apply]
    have hb1 : chiC (p := p) b * gaussSum chiC (AddChar.mulShift ψ (hbu.unit : (ZMod p)ˣ))
        = gaussSum chiC ψ := gaussSum_mulShift chiC ψ hbu.unit
    have hbeq : ((hbu.unit : (ZMod p)ˣ) : ZMod p) = b := IsUnit.unit_spec hbu
    rw [hbeq] at hb1
    have hbsq : chiC (p := p) b * chiC b = 1 := by
      rcases quadraticChar_dichotomy (F := ZMod p) hb with h | h <;>
        rw [chiC_apply, h] <;> norm_num
    rw [hmul]
    calc gaussSum chiC (AddChar.mulShift ψ b)
        = chiC b * chiC b * gaussSum chiC (AddChar.mulShift ψ b) := by rw [hbsq, one_mul]
      _ = chiC b * (chiC b * gaussSum chiC (AddChar.mulShift ψ b)) := by ring
      _ = chiC b * gaussSum chiC ψ := by rw [hb1]
  rw [hψ0, hgs]; ring

end ArkLib.ProximityGap.QRExpSum

#print axioms ArkLib.ProximityGap.QRExpSum.eta_QR_eq
