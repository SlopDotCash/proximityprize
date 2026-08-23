/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# N10 — the TQFT / quantum-modularity NO-GO: reciprocity touches only quadratic phases (#407/#444)

**This is a NEGATIVE (guardrail) brick, not a closure.** It records, axiom-clean, why the
quadratic-reciprocity / Landsberg–Schaar / quantum-modularity (TQFT / WRT-invariant) lens is
structurally incapable of producing the proximity prize `M(n) ≤ C·√(n log(p/n))` for the thin
2-power subgroup `μ_n` in the prize regime (`n ~ p^{1/4}`, index `m = (p-1)/n ~ 2^128`).

## The mechanism

`M(n) = max_{b≠0} |∑_{x∈μ_n} e_p(b x)|` is the sup-norm of an incomplete additive character sum
over the order-`n` multiplicative subgroup. Orthogonality expands each Gauss phase
`τ(χ^j)/√q` (`j = 0,…,m-1`) of the *non-principal* characters trivial on `μ_n`. Quadratic
reciprocity / Landsberg–Schaar / quantum modularity (the modular transformation law of the
classical theta / Jacobi function, equivalently the `S`-matrix of an abelian TQFT) evaluates
**only order-2 Gauss sums** `g(χ)` with `χ² = 1` — these are the quadratic / Legendre-symbol
phases. Higher-order Gauss phases `τ(χ^j)` with `χ^{2j} ≠ 1` lie outside its reach.

So among the `m` Gauss phases of the prize problem, reciprocity controls **at most the quadratic
ones**, and there are at most `2` multiplicative characters `ψ` with `ψ² = 1` (exactly
`1 + [2 ∣ p-1] = gcd(2, p-1)`). The fraction of the `m`-phase family that the
reciprocity / TQFT lens *touches* is therefore `≤ 2/m`, which `→ 0` in the prize regime
`m ~ 2^128`. The lens supplies square-root cancellation for `O(1)` of `2^128` phases: it
**consumes, not produces** the prize. (Cf. #407/#444; this is N10 of the exotic-sweep census
— the TQFT / quantum-modularity / WRT-invariant entry, which "dies" by spectral flatness +
wrong-coordinate decoupling: reciprocity is a statement about the *quadratic* coordinate of the
character group, while `M(n)` needs *all* `m` phases.)

## What is proven here (character-count + the ratio bound, exactly as scoped)

* `card_orderTwo_le_two_of_cyclic` / `card_orderTwo_eq_gcd_two` — in *any* finite cyclic group
  (the character group `MulChar F ℂ` is cyclic of order `p-1`), the number of elements `x` with
  `x² = 1` is `gcd(card, 2) ≤ 2`.
* `card_quadratic_mulChar_le_two` / `card_quadratic_mulChar_eq_gcd_two` — specialized to the
  multiplicative characters `ψ : MulChar F ℂ` of a finite field `F`: `#{ψ // ψ² = 1} ≤ 2`,
  exactly `gcd(card Fˣ, 2)`.
* `quadratic_fraction_le` / `quadratic_fraction_vanishes` — the touched fraction is `≤ 2/m`
  and tends to `0` as the index `m → ∞`.

No `sorry`, no `native_decide`, no custom axiom: the `#print axioms` block shows only
`[propext, Classical.choice, Quot.sound]`.
-/

namespace ProximityGap.Frontier.QuadraticGaussFraction

open scoped Classical

/-! ## 1. The abstract character-count: order-≤2 elements of a finite cyclic group -/

/-- In a finite cyclic commutative group `G`, the number of elements `x` with `x² = 1`
(`= x ∈ ker (·)²`) is exactly `gcd(card G, 2)`. This is the load-bearing count: the group of
multiplicative characters is cyclic, and the "quadratic" characters are precisely the elements
of order dividing 2. -/
theorem card_orderTwo_eq_gcd_two (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] :
    Nat.card {x : G // x ^ 2 = 1} = (Nat.card G).gcd 2 := by
  have hcong : Nat.card {x : G // x ^ 2 = 1}
      = Nat.card (powMonoidHom 2 : G →* G).ker := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquivRight ?_)
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
  rw [hcong, IsCyclic.card_powMonoidHom_ker]

/-- In a finite cyclic commutative group, at most `2` elements satisfy `x² = 1`. -/
theorem card_orderTwo_le_two_of_cyclic (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] :
    Nat.card {x : G // x ^ 2 = 1} ≤ 2 := by
  rw [card_orderTwo_eq_gcd_two]
  exact Nat.gcd_le_right _ (by norm_num)

/-! ## 2. Specialization to multiplicative characters of a finite field -/

variable (F : Type*) [Field F] [Fintype F]

/-- The group of `ℂ`-valued multiplicative characters of a finite field is cyclic: it is
(noncanonically) isomorphic to the cyclic unit group `Fˣ`. -/
instance moduleInstance_QuadraticGaussFraction_1 : IsCyclic (MulChar F ℂ) :=
  isCyclic_of_surjective _ (MulChar.mulEquiv_units F ℂ).some.symm.surjective

/-- The number of multiplicative characters `ψ : MulChar F ℂ` with `ψ² = 1` equals
`gcd(card Fˣ, 2)`. These `ψ` are exactly the *quadratic* (order-dividing-2) characters —
the only Gauss phases that quadratic reciprocity / Landsberg–Schaar / quantum modularity
controls. -/
theorem card_quadratic_mulChar_eq_gcd_two :
    Nat.card {ψ : MulChar F ℂ // ψ ^ 2 = 1} = (Nat.card Fˣ).gcd 2 := by
  rw [card_orderTwo_eq_gcd_two (MulChar F ℂ), MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]

/-- **N10 character count.** At most two multiplicative characters of a finite field are
quadratic (`ψ² = 1`). Reciprocity / TQFT modularity touches only these. -/
theorem card_quadratic_mulChar_le_two :
    Nat.card {ψ : MulChar F ℂ // ψ ^ 2 = 1} ≤ 2 :=
  card_orderTwo_le_two_of_cyclic (MulChar F ℂ)

/-! ## 3. The vanishing fraction in the prize regime -/

/-- The fraction of the `m` non-principal Gauss phases that reciprocity / TQFT modularity can
touch is at most `2/m`. (`m = (p-1)/n` is the subgroup index; the quadratic phases number at
most `2`.) -/
theorem quadratic_fraction_le (m : ℝ) (hm : 0 < m)
    (k : ℕ) (hk : (k : ℝ) ≤ 2) :
    (k : ℝ) / m ≤ 2 / m := by
  gcongr

/-- **N10 vanishing fraction.** As the subgroup index `m → ∞` (prize regime `m ~ 2^128`), the
touched fraction `2/m → 0`. The quadratic-reciprocity / Landsberg–Schaar / quantum-modularity
(TQFT) lens controls a vanishing fraction of the Gauss phases that `M(n)` depends on; it cannot
produce the prize bound, only consume `O(1)` of the `m` phases. -/
theorem quadratic_fraction_vanishes :
    Filter.Tendsto (fun m : ℝ => (2 : ℝ) / m) Filter.atTop (nhds 0) := by
  simpa using (tendsto_const_nhds.div_atTop Filter.tendsto_id)

#print axioms card_orderTwo_eq_gcd_two
#print axioms card_orderTwo_le_two_of_cyclic
#print axioms card_quadratic_mulChar_eq_gcd_two
#print axioms card_quadratic_mulChar_le_two
#print axioms quadratic_fraction_le
#print axioms quadratic_fraction_vanishes

end ProximityGap.Frontier.QuadraticGaussFraction
