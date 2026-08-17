/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Round 9 (Issue #232, ABF26) — the twisted Gauss pieces: elementary quadratic/Salié magnitudes,
# and the EXACT reduction of the χ-twisted Salié sum to a quartic Weil sum.

`Round9SubgroupCharExpansion.lean` decomposed the subgroup-restricted mixed Gauss sum
`∑_{x∈G} ψ(b₁x + b₂x²)` into `[Fˣ:G]` twisted character Gauss sums
`T_χ = ∑_{x∈Fˣ} χ(x)·ψ(b₁x + b₂x²)`. This file analyses those pieces, separating what is **elementary**
(provable from Mathlib's `gaussSum` API) from the genuine **Weil/RH-for-curves** residual.

## Elementary pieces (no Weil)

* `norm_gaussSum_quadratic` — for the quadratic character `χ` and a primitive `ψ`,
  `‖gaussSum χ ψ‖ = √q` (square via Mathlib's `gaussSum_sq`, then take norms).
* `norm_gaussSum_mulShift` — shift-invariance: `‖∑_x χ(x)ψ(ax)‖ = √q` for `a ≠ 0`.
* `norm_sum_quadratic` / `norm_sum_quadratic_linear` — the **untwisted** quadratic additive Gauss
  sum `∑_x ψ(b₂x² + b₁x)` (`b₂ ≠ 0`) has magnitude `√q`, via the square-root count
  `#{x : x² = t} = χ(t) + 1` (`quadraticChar_card_sqrts`) reducing it to `gaussSum χ (mulShift ψ b₂)`,
  plus completing the square for the linear term. This is the `χ = 1` twisted piece — fully elementary.

## The Weil residual, isolated exactly

* `salieSum_eq_quartic_sub_quadratic` — the **exact** reduction of the quadratic-character-twisted
  Salié sum:
  ```
  ∑_x χ(x)·ψ(b₂x² + b₁x) = (∑_y ψ(b₂y⁴ + b₁y²)) − (∑_x ψ(b₂x² + b₁x)).
  ```
  The second term is the elementary quadratic sum (magnitude `√q` above). The first term
  `∑_y ψ(b₂y⁴ + b₁y²)` is a **degree-4 additive (Weil) sum**, whose `√q` bound for general `b₁ ≠ 0`
  is exactly the Riemann-hypothesis-for-curves input Mathlib **lacks**. So the χ-twisted Salié piece
  is *not* elementary in general — it reduces precisely to a quartic Weil sum.

**Net:** combined with `Round9SubgroupCharExpansion.lean` and the additive Plancherel layer
(`MomentCollisionSpectral.lean`), this pins the open #232 core to a single, named, machine-checked
object — the `√q`-magnitude of the quartic additive sum (general `χ` ⇒ general Weil curve count) —
and proves everything around it elementarily. No closure is claimed; the residual is exactly Weil.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.style.longLine false


open scoped BigOperators
open AddChar MulChar Finset

namespace ArkLib.ProximityGap.Round9SalieQuartic

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

/-- The norm of a quadratic character value at `-1` (a unit) is `1`. -/
lemma norm_quadraticChar_neg_one {χ : MulChar F ℂ} (hχ₂ : χ.IsQuadratic) :
    ‖χ (-1)‖ = 1 := by
  rcases hχ₂ (-1) with h | h | h
  · exact (not_isUnit_zero <| h ▸ IsUnit.map χ (isUnit_one.neg)).elim
  · rw [h]; simp
  · rw [h]; simp

/-- The norm of a quadratic character at any unit `a` is `1`. -/
lemma norm_quadraticChar_unit {χ : MulChar F ℂ} (hχ₂ : χ.IsQuadratic) {a : F}
    (ha : IsUnit a) : ‖χ a‖ = 1 := by
  rcases hχ₂ a with h | h | h
  · exact (not_isUnit_zero <| h ▸ IsUnit.map χ ha).elim
  · rw [h]; simp
  · rw [h]; simp

/-- **Quadratic Gauss sum magnitude.** For a nontrivial quadratic `χ : MulChar F ℂ` and a primitive
`ψ`, `‖gaussSum χ ψ‖ = √q`. Elementary: square via `gaussSum_sq`, then take norms. -/
theorem norm_gaussSum_quadratic {χ : MulChar F ℂ} (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have hsq : gaussSum χ ψ ^ 2 = χ (-1) * (Fintype.card F : ℂ) := gaussSum_sq hχ₁ hχ₂ hψ
  have hnorm : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have : ‖gaussSum χ ψ ^ 2‖ = ‖χ (-1) * (Fintype.card F : ℂ)‖ := by rw [hsq]
    rw [norm_pow, norm_mul, norm_quadraticChar_neg_one hχ₂, one_mul,
        Complex.norm_natCast] at this
    exact this
  have hpos : (0:ℝ) ≤ ‖gaussSum χ ψ‖ := norm_nonneg _
  rw [← hnorm, Real.sqrt_sq hpos]

/-- **Shift-invariance.** For `a ≠ 0`, `‖∑_x χ(x)ψ(ax)‖ = √q` (the magnitude form of
`gaussSum_mulShift`). -/
theorem norm_gaussSum_mulShift {χ : MulChar F ℂ} (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    ‖∑ x : F, χ x * ψ (a * x)‖ = Real.sqrt (Fintype.card F) := by
  have haU : IsUnit a := ha.isUnit
  have hsum : (∑ x : F, χ x * ψ (a * x)) = gaussSum χ (mulShift ψ haU.unit) := by
    unfold gaussSum
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mulShift_apply, IsUnit.unit_spec]
  rw [hsum]
  have key := gaussSum_mulShift χ ψ haU.unit
  have hnorm : ‖χ ((haU.unit : F))‖ * ‖gaussSum χ (mulShift ψ haU.unit)‖ =
      ‖gaussSum χ ψ‖ := by
    rw [← norm_mul, key]
  have hcoe : ((haU.unit : F)) = a := IsUnit.unit_spec haU
  rw [hcoe, norm_quadraticChar_unit hχ₂ haU, one_mul] at hnorm
  rw [hcoe, hnorm, norm_gaussSum_quadratic hχ₁ hχ₂ hψ]

variable [DecidableEq F]

/-- `chiC F` is the quadratic character pushed into `ℂ`. -/
noncomputable def chiC (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] lemma chiC_apply (t : F) : chiC F t = (quadraticChar F t : ℂ) := by
  simp [chiC, MulChar.ringHomComp_apply]

lemma chiC_isQuadratic : (chiC F).IsQuadratic := (quadraticChar_isQuadratic F).comp _

lemma chiC_ne_one (hF : ringChar F ≠ 2) : chiC F ≠ 1 := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := by intro a b h; simpa using h
  rw [chiC, MulChar.ringHomComp_ne_one_iff hinj]
  exact quadraticChar_ne_one hF

/-- The cast of the square-root count to `ℂ` is `χ(t) + 1`. -/
lemma cast_card_sqrts_eq (hF : ringChar F ≠ 2) (t : F) :
    ((#({x ∈ Finset.univ | x ^ 2 = t} : Finset F)) : ℂ) = (chiC F t) + 1 := by
  have h := quadraticChar_card_sqrts hF t
  have heq : ({x ∈ Finset.univ | x ^ 2 = t} : Finset F) = {x : F | x ^ 2 = t}.toFinset := by
    ext x; simp
  rw [heq, chiC_apply]
  calc ((#({x : F | x ^ 2 = t}.toFinset)) : ℂ)
      = (((#({x : F | x ^ 2 = t}.toFinset)) : ℤ) : ℂ) := by push_cast; ring
    _ = (((quadraticChar F t) + 1 : ℤ) : ℂ) := by rw [h]
    _ = (quadraticChar F t : ℂ) + 1 := by push_cast; ring

/-- **Key identity.** For `b₂ ≠ 0`, the additive quadratic sum `∑_x ψ(b₂x²)` equals the
linearly-twisted quadratic-character Gauss sum `gaussSum χℂ (mulShift ψ b₂)`. -/
theorem sum_quadratic_eq_gaussSum (hF : ringChar F ≠ 2)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b2 : F} (hb2 : b2 ≠ 0) :
    (∑ x : F, ψ (b2 * x ^ 2)) = gaussSum (chiC F) (mulShift ψ b2) := by
  have hfib : ∑ t : F, (∑ x ∈ Finset.univ with x ^ 2 = t, ψ (b2 * x ^ 2))
      = ∑ x : F, ψ (b2 * x ^ 2) :=
    Finset.sum_fiberwise Finset.univ (fun x => x ^ 2) (fun x => ψ (b2 * x ^ 2))
  rw [← hfib]
  have hinner : ∀ t : F, (∑ x ∈ Finset.univ with x ^ 2 = t, ψ (b2 * x ^ 2))
      = (#({x ∈ Finset.univ | x ^ 2 = t} : Finset F)) • ψ (b2 * t) := by
    intro t
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
    rw [Finset.sum_const]
  simp_rw [hinner]
  have hsmul : ∀ t : F, (#({x ∈ Finset.univ | x ^ 2 = t} : Finset F)) • ψ (b2 * t)
      = (chiC F t + 1) * ψ (b2 * t) := by
    intro t
    rw [nsmul_eq_mul, cast_card_sqrts_eq hF t]
  simp_rw [hsmul, add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ t : F, ψ (b2 * t)) = 0 := by
    have := AddChar.sum_mulShift b2 hψ
    rw [if_neg hb2] at this
    simpa [mul_comm] using this
  rw [hzero, add_zero]
  unfold gaussSum
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [mulShift_apply]

/-- **Untwisted quadratic additive Gauss sum magnitude.** `‖∑_x ψ(b₂x²)‖ = √q` for `b₂ ≠ 0`.
Elementary: equals the linearly-twisted quadratic-character Gauss sum, magnitude `√q`. -/
theorem norm_sum_quadratic (hF : ringChar F ≠ 2)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b2 : F} (hb2 : b2 ≠ 0) :
    ‖∑ x : F, ψ (b2 * x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  rw [sum_quadratic_eq_gaussSum hF hψ hb2]
  exact norm_gaussSum_quadratic (chiC_ne_one hF) (chiC_isQuadratic)
    (IsPrimitive.of_ne_one (hψ hb2))

/-- **Untwisted quadratic additive Gauss sum with a linear term.** For `b₂ ≠ 0` and any `b₁`,
`‖∑_x ψ(b₂x² + b₁x)‖ = √q`. Complete the square `b₂x² + b₁x = b₂(x + b₁/(2b₂))² − b₁²/(4b₂)`, shift,
factor the magnitude-1 constant, reduce to `norm_sum_quadratic`. The multiplicative twist is trivial
here — the elementary `χ = 1` piece. -/
theorem norm_sum_quadratic_linear (hF : ringChar F ≠ 2)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b2 : F} (hb2 : b2 ≠ 0) (b1 : F) :
    ‖∑ x : F, ψ (b2 * x ^ 2 + b1 * x)‖ = Real.sqrt (Fintype.card F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h2b2 : (2 * b2 : F) ≠ 0 := mul_ne_zero h2 hb2
  set c : F := b1 / (2 * b2) with hc
  have hcb : 2 * b2 * c = b1 := by rw [hc]; field_simp
  set k : F := -(b2 * c ^ 2) with hk
  have hpt : ∀ x : F, b2 * x ^ 2 + b1 * x = b2 * (x + c) ^ 2 + k := by
    intro x
    rw [hk, ← hcb]; ring
  have hsum : (∑ x : F, ψ (b2 * x ^ 2 + b1 * x)) = ψ k * ∑ x : F, ψ (b2 * x ^ 2) := by
    have hshift : (∑ x : F, ψ (b2 * x ^ 2 + b1 * x))
        = ∑ x : F, ψ (b2 * (x + c) ^ 2 + k) := by
      refine Finset.sum_congr rfl (fun x _ => ?_); rw [hpt x]
    rw [hshift]
    have hre : (∑ x : F, ψ (b2 * (x + c) ^ 2 + k))
        = ∑ y : F, ψ (b2 * y ^ 2 + k) :=
      Equiv.sum_comp (Equiv.addRight c) (fun y => ψ (b2 * y ^ 2 + k))
    rw [hre]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [add_comm (b2 * y ^ 2) k, ψ.map_add_eq_mul]
  rw [hsum, norm_mul, AddChar.norm_apply, one_mul, norm_sum_quadratic hF hψ hb2]

/-- **Salié reduction (exact, the Weil-residual isolation).** The quadratic-character-twisted Salié
sum equals a quartic additive sum minus the elementary quadratic additive sum:
```
∑_x χ(x)·ψ(b₂x² + b₁x) = (∑_y ψ(b₂y⁴ + b₁y²)) − (∑_x ψ(b₂x² + b₁x)).
```
The subtrahend has magnitude `√q` (`norm_sum_quadratic_linear`, elementary); the minuend is a
degree-4 additive Weil sum whose `√q` bound for general `b₁ ≠ 0` is exactly the
Riemann-hypothesis-for-curves input Mathlib lacks. This pins the obstruction to the quartic term. -/
theorem salieSum_eq_quartic_sub_quadratic (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (b2 b1 : F) :
    (∑ x : F, (chiC F x) * ψ (b2 * x ^ 2 + b1 * x))
      = (∑ y : F, ψ (b2 * (y ^ 2) ^ 2 + b1 * y ^ 2))
        - (∑ x : F, ψ (b2 * x ^ 2 + b1 * x)) := by
  have hpt : ∀ x : F, (chiC F x) * ψ (b2 * x ^ 2 + b1 * x)
      = (#({y ∈ Finset.univ | y ^ 2 = x} : Finset F)) • ψ (b2 * x ^ 2 + b1 * x)
        - ψ (b2 * x ^ 2 + b1 * x) := by
    intro x
    rw [nsmul_eq_mul, cast_card_sqrts_eq hF x]
    ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib]
  congr 1
  have hinner : ∀ x : F,
      (#({y ∈ Finset.univ | y ^ 2 = x} : Finset F)) • ψ (b2 * x ^ 2 + b1 * x)
      = ∑ y ∈ Finset.univ with y ^ 2 = x, ψ (b2 * (y ^ 2) ^ 2 + b1 * y ^ 2) := by
    intro x
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2]), Finset.sum_const]
  simp_rw [hinner]
  exact Finset.sum_fiberwise Finset.univ (fun y => y ^ 2)
    (fun y => ψ (b2 * (y ^ 2) ^ 2 + b1 * y ^ 2))

end

end ArkLib.ProximityGap.Round9SalieQuartic

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round9SalieQuartic.norm_gaussSum_quadratic
#print axioms ArkLib.ProximityGap.Round9SalieQuartic.norm_sum_quadratic
#print axioms ArkLib.ProximityGap.Round9SalieQuartic.norm_sum_quadratic_linear
#print axioms ArkLib.ProximityGap.Round9SalieQuartic.salieSum_eq_quartic_sub_quadratic
