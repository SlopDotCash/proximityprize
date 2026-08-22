/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Tannakian non-torsion rank-pump: the multiplicative `θ`-twist CANNOT break cyclotomic vanishing
(#444, frontier tool #5)

## The tool (and its claimed evasion)

The "Tannakian non-torsion rank-pump" proposes to escape the Paley/BGK sup-norm wall by **twisting
the period family by a non-`n`-torsion multiplicative character** `χ_θ`:
`η_b^{(θ)} = Σ_{x ∈ μ_n} χ_θ(x) · e_p(b x)`, hoping the twist breaks the `n`-torsion resonance that
degenerates the middle-convolution input to a Kummer sheaf at `μ_n` (which is what makes the
"gapped Vandermonde / convolution minor" **vanish** at `μ_n` via the antipodal relation
`1 + ζ^{n/2} = 0`).

## The two load-bearing facts this file pins (both PROVEN here)

**Fact 1 (the twist is diagonal ⇒ it cannot un-vanish a minor).**
A multiplicative character acts on the rows of any convolution/Vandermonde minor by *scaling row
`i` by the scalar `χ_θ(μ_i)`*. Row-scaling multiplies the determinant by `∏_i χ_θ(μ_i)`, a **unit**.
Hence the twisted minor det is `(unit) · (untwisted minor det)`: if the untwisted minor **vanishes**
(the cyclotomic wall), the twisted minor **vanishes too**. The twist is structurally incapable of
changing a `0` det to a nonzero one. This is `twist_det_eq` / `twist_det_eq_zero_iff` below.

**Fact 2 (a non-torsion / coprime-order twist is IDENTICALLY trivial on `μ_n`).**
If `χ_θ` has order `d` with `gcd(d, n) = 1`, then `χ_θ` restricted to the cyclic group `μ_n`
(order `n`) is a character whose order divides `gcd(d, n) = 1`, hence is **trivial**. So
`η_b^{(θ)} = η_b` *identically* — the "non-torsion twist" does literally nothing. To get a
nontrivial twist on `μ_n` one needs `n ∣ d` (an `n`-torsion direction — exactly the resonance the
tool claimed to *break*). This is `coprime_order_trivial_on_mu` below (the group-order form).

## Verdict (computed in `_AvTannakianNonTorsionPump` notes; this file proves the structure)

- **Does it bound `M`?** No. When the twist is nontrivial (`n ∣ d`) the twisted sum is a *different*
  object — a Gauss period with a multiplicative weight — and exact `F_p` computation (`n = 8`,
  `p = 4129`) shows it has the **identical sub-Gaussian moment profile** (`E|η^{(θ)}|^{2r}/(E|·|²)^r
  = 2.62, 9.99, 46.4` vs untwisted `2.62, 9.93, 45.7`) and the **identical Cramér regime**
  (`M_θ/√n = 2.700` vs `M/√n = 2.672`). Bounding it is the *same* Burgess problem for the twisted
  family; there is no transfer to `M`.
- **Does it evade the wall?** No (Fact 1): the diagonal twist preserves every vanishing minor.

So tool #5 **reduces to the wall** (and a coprime twist is even vacuous). This file lands the exact
structural reason.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.Tannakian

open Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

/-- **Fact 1 (diagonal twist identity).** Twisting a minor `A` by a multiplicative weight
`χ : n → R` — i.e. scaling row `i` by `χ i` — multiplies the determinant by `∏ i, χ i`.

This is the exact mechanism by which the Tannakian `θ`-twist acts on a convolution/Vandermonde
minor over `μ_n`: it is *diagonal*. -/
theorem twist_det_eq (χ : n → R) (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = (∏ i, χ i) * A.det :=
  Matrix.det_mul_column χ A

/-- **Fact 1, contrapositive form (the wall is preserved).** If the twist weight is a *unit*
(any genuine multiplicative character is unit-valued — `χ_θ(μ_i) ≠ 0`), then the twisted minor
vanishes **iff** the untwisted minor vanishes. A diagonal twist can never turn a vanishing
cyclotomic minor into a nonvanishing one. -/
theorem twist_det_eq_zero_iff [IsDomain R] {χ : n → R} (hχ : ∀ i, χ i ≠ 0)
    (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = 0 ↔ A.det = 0 := by
  rw [twist_det_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hp | hd
    · exact absurd (Finset.prod_eq_zero_iff.mp hp) (by
        rintro ⟨i, -, hi⟩; exact hχ i hi)
    · exact hd
  · intro h; rw [h, mul_zero]

/-- A unit-valued twist (`χ_θ(μ_i)` are units) keeps the determinant a unit-multiple, so it is
zero exactly when the original is. Packaged with `IsUnit` for the product. -/
theorem twist_det_isUnit_mul {χ : n → R} (A : Matrix n n R)
    (hχ : IsUnit (∏ i, χ i)) :
    IsUnit (Matrix.of fun i j => χ i * A i j).det ↔ IsUnit A.det := by
  rw [twist_det_eq]
  exact ⟨fun h => (IsUnit.mul_iff.mp h).2, fun h => hχ.mul h⟩

/-- **Fact 2 (coprime-order twist is trivial on `μ_n`).** Group-theoretic core: a homomorphism
`χ` from a group `G` of order `n` into a group `H`, whose image has order dividing `d` with
`gcd(d, n) = 1`, is **trivial**. (Apply with `G = μ_n`, `H = μ_d ⊂ F_p^×`: a character of order `d`
coprime to `n` restricts trivially to `μ_n`, so `η_b^{(θ)} = η_b` identically.)

Concretely: the order of `χ g` divides both `n` (Lagrange in `G`) and `d`; coprimality forces it
to be `1`. -/
theorem coprime_order_trivial_on_mu {G H : Type*} [Group G] [Group H] [Fintype G]
    (χ : G →* H) {d : ℕ} (hdiv : ∀ g : G, orderOf (χ g) ∣ d)
    (hcop : Nat.Coprime d (Fintype.card G)) :
    ∀ g : G, χ g = 1 := by
  intro g
  have h1 : orderOf (χ g) ∣ Fintype.card G := by
    exact (orderOf_map_dvd χ g).trans (orderOf_dvd_card)
  have h2 : orderOf (χ g) ∣ d := hdiv g
  have : orderOf (χ g) ∣ Nat.gcd d (Fintype.card G) := Nat.dvd_gcd h2 h1
  rw [hcop] at this
  rw [Nat.dvd_one] at this
  exact orderOf_eq_one_iff.mp this

/-- **Concrete period consequence: a trivial twist does nothing to the period.** If the
row-weight/character is `1` on every `x ∈ G`, the twisted period `Σ χ(x) f(x)` is exactly the
untwisted period `Σ f(x)`. This is the period-level form of the coprime non-torsion no-go: once
the character restricts trivially to `μ_n`, there is no new object and no new cancellation. -/
theorem twist_period_eq_original_of_trivial {ι A : Type*} [Semiring A]
    (G : Finset ι) (χ f : ι → A) (hχ : ∀ x ∈ G, χ x = 1) :
    (∑ x ∈ G, χ x * f x) = ∑ x ∈ G, f x := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [hχ x hx, one_mul]

/-- **Coprime-order twist period identity.** If a multiplicative twist has image orders dividing
`d` with `gcd(d, |G|)=1`, then it is trivial on `G`; consequently the twisted period over all of
`G` equals the original untwisted period. This packages Fact 2 at the actual finite-sum level. -/
theorem coprime_order_twisted_period_eq_original {G H A : Type*} [Group G] [Group H]
    [Fintype G] [Semiring A] (χ : G →* H) {d : ℕ}
    (hdiv : ∀ g : G, orderOf (χ g) ∣ d) (hcop : Nat.Coprime d (Fintype.card G))
    (embed : H → A) (hembed_one : embed 1 = 1) (f : G → A) :
    (∑ x : G, embed (χ x) * f x) = ∑ x : G, f x := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hχx : χ x = 1 := coprime_order_trivial_on_mu χ hdiv hcop x
  rw [hχx, hembed_one, one_mul]

end ArkLib.ProximityGap.Frontier.Tannakian

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.twist_det_isUnit_mul
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_trivial_on_mu
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.twist_period_eq_original_of_trivial
#print axioms ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_twisted_period_eq_original
