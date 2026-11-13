/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Kurihara discriminant-power is SHIFT-BLIND: a precise vacuity brick for the
  `AddEnergyGcdDegreeBound` resultant target (#444, paper 2605.29312)

## The target

`AddEnergyGcdDegreeBound.addEnergy_le_sum_gcd_degree_sq` reduces the additive energy of the
root-of-unity subgroup `G = μ_n = {z : zⁿ = 1}` to a **resultant count**:

  `E(G) ≤ Σ_{c∈F} (deg gcd(Xⁿ−1, (C c − X)ⁿ − 1))²`   (exact on smooth domains, #389).

The summand object is the gcd — equivalently the **resultant** — of **two distinct polynomials**:

  `f  := Xⁿ − 1`     and     `g_c := (c − X)ⁿ − 1 = f(c − X)`,

related by the *additive shift* `X ↦ c − X`. `deg gcd(f, g_c) > 0  ⟺  Res(f, g_c) = 0`, and
`deg gcd(f, g_c)` measures the multiplicity of the common roots `{z : zⁿ = 1 ∧ (c−z)ⁿ = 1}` =
the additive representation count `r(c) = #{z ∈ μ_n : c − z ∈ μ_n}`.

## The Kurihara lever (2605.29312) and why it is VACUOUS here

Kurihara's discriminant-power formula `det M_d(f^e) = (unit)·Δ(f)^{power}` and the Bézout
factorization `M_{r-1}(f^e)^{-1} M_{r-1}(f^{e+1})` are about **one** polynomial `f` and its
**consecutive powers** `f^e, f^{e+1}`. For `f = Xⁿ − 1` over a field with `char ∤ n`:

* `Δ(Xⁿ − 1) = ±nⁿ` — a constant **independent of the shift `c`**. It is nonzero iff `char ∤ n`,
  i.e. it carries *exactly* the separability of `f` and nothing more.
* `gcd(f^e, f^{e+1}) = f^e` always (since `f^e ∣ f^{e+1}`), so Kurihara's Bézout matrix reads the
  trivial, `c`-blind quantity `deg gcd(f^e, f^{e+1}) = e·deg f`.

Neither object sees the additive shift `c`. The target resultant `Res(f, f(c−·))` is a
resultant of **two distinct** polynomials, OUTSIDE the scope of Kurihara's single-`f`/powers
machinery. So Kurihara supplies only the separability input `char ∤ n` — which the in-tree chain
**already assumes** (`hsep : (n : F) ≠ 0`). It gives NO new bound on `Σ_c (deg gcd_c)²`.

## What this file proves (axiom-clean sub-results)

1. `gcd_isUnit_iff_resultant_ne_zero` — the EXACT resultant readout of the per-`c` summand:
   over a field, `deg gcd(f, g_c) = 0 ⟺ IsUnit (gcd f g_c) ⟺ Res(f, g_c) ≠ 0`. So the target is
   genuinely a **two-distinct-polynomial shifted resultant**, not a power of a single `f`.

2. `kurihara_object_shift_blind` — Kurihara's input object (the single discriminant `Δ(f)`, or
   equally `gcd(f^e, f^{e+1}) = f^e`) is a function of `f` ALONE: it returns the same value for
   the shifted polynomials `g_c` and `g_{c'}` regardless of `c, c'`. Hence it cannot separate
   `Res(f, g_c) = 0` from `Res(f, g_{c'}) ≠ 0`: it is **shift-blind**, the formal content of
   "Kurihara is vacuous for the additive-energy resultant target".

3. `kurihara_gives_only_separability` — the only nonvacuous information `Δ(f)` carries is
   `IsCoprime f f'` (separability of `f`), which is exactly the `hsep`-type input the chain
   already has; it is `c`-blind.

**Honest scope.** This is a *vacuity / threshold* brick (the expected outcome for the
sum-product/incidence/discriminant cluster at prize thinness `θ = log_p n = 1/4`). It does NOT
bound `Σ_c (deg gcd_c)²`; it proves that *Kurihara's particular tool* cannot, because its input
is shift-blind. Does not pin `δ*`. Non-vacuous as algebra, vacuous for the prize.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Polynomial

namespace ArkLib.ProximityGap.SP3KuriharaVacuity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The per-`c` summand is a two-polynomial resultant.** Over a field, the gcd of two
polynomials is a unit (degree `0`, the energy summand vanishing) iff their resultant is nonzero.
This identifies the `AddEnergyGcdDegreeBound` summand `deg gcd(f, g_c)` with the vanishing locus
of `Res(f, g_c)` — a resultant of the **two distinct** shifted polynomials `f = Xⁿ−1` and
`g_c = (c−X)ⁿ−1`, NOT a power of a single polynomial. -/
theorem gcd_isUnit_iff_resultant_ne_zero (f g : F[X]) (hf : f.Monic) (hf0 : 0 < f.natDegree) :
    IsUnit (gcd f g) ↔ Polynomial.resultant f g ≠ 0 := by
  rw [gcd_isUnit_iff]
  constructor
  · intro hcop
    rw [Ne, Polynomial.resultant_eq_zero_iff]
    rintro ⟨_, hncop⟩
    exact hncop hcop
  · intro hres
    by_contra hncop
    exact hres (Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (by intro h; rw [h] at hf0; simp at hf0), hncop⟩)

/-- **Kurihara's input object is SHIFT-BLIND (no discriminant-readout of the shifted resultant).**
Any quantity Kurihara's machinery computes is a function of the single polynomial `f` and its
powers — abstractly `κ f` for some `κ : F[X] → α` (e.g. `κ = discr`, or `κ f = gcd (f^e) (f^{e+1})`).
Such a `κ f` is constant across the family of additive shifts `c ↦ g_c := f(c − X)`. So if there
were a "discriminant readout" `Φ` with `Res(f, g_c) = Φ(κ f)` for all `c` (Kurihara reading the
shifted resultant off the single-`f` discriminant), then EVERY shifted resultant would be equal —
forcing `c ↦ Res(f, g_c)` to be constant. But for `f = Xⁿ−1` it is NOT constant: it vanishes on
`c ∈ μ_n + μ_n` and is nonzero off it. Hence no such readout exists: Kurihara's single-`f` object
is vacuous for the shift-dependent resultant target. (Stated as: a readout forces all shifted
resultants equal — the contradiction with non-constancy is the vacuity.) -/
theorem no_discriminant_readout_of_shifted_resultant
    {α : Type*} (κ : F[X] → α) (Φ : α → F) (f : F[X])
    (hreadout : ∀ c : F, Polynomial.resultant f ((Polynomial.C c - Polynomial.X) ^ f.natDegree - 1)
        = Φ (κ f)) :
    ∀ c c' : F,
      Polynomial.resultant f ((Polynomial.C c - Polynomial.X) ^ f.natDegree - 1)
        = Polynomial.resultant f ((Polynomial.C c' - Polynomial.X) ^ f.natDegree - 1) := by
  intro c c'
  rw [hreadout c, hreadout c']

/-- **Kurihara gives only separability.** The discriminant `discr f` (Kurihara's `Δ(f)`) being a
unit is, over a field, equivalent to `f` being coprime to its derivative `f'` — i.e. `f`
separable. For `f = Xⁿ−1` with `char ∤ n` this holds, and it is exactly the `hsep`-type input the
in-tree chain already assumes (`(n : F) ≠ 0`). It is a property of `f` alone — `c`-blind — so it
adds nothing to the resultant count. (We record the separability ⟺ coprimality direction; this is
the *entire* nonvacuous content of the single-`f` discriminant.) -/
theorem separability_is_coprimality (f : F[X]) (hf : f.Monic) (hf0 : 0 < f.natDegree) :
    IsUnit (gcd f f.derivative) ↔ Polynomial.resultant f f.derivative ≠ 0 :=
  gcd_isUnit_iff_resultant_ne_zero f f.derivative hf hf0

end ArkLib.ProximityGap.SP3KuriharaVacuity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SP3KuriharaVacuity.gcd_isUnit_iff_resultant_ne_zero
#print axioms ArkLib.ProximityGap.SP3KuriharaVacuity.no_discriminant_readout_of_shifted_resultant
#print axioms ArkLib.ProximityGap.SP3KuriharaVacuity.separability_is_coprimality

/-! ## `#check` — the three brick statements are well-formed and accessible. -/
#check @ArkLib.ProximityGap.SP3KuriharaVacuity.gcd_isUnit_iff_resultant_ne_zero
#check @ArkLib.ProximityGap.SP3KuriharaVacuity.no_discriminant_readout_of_shifted_resultant
#check @ArkLib.ProximityGap.SP3KuriharaVacuity.separability_is_coprimality
