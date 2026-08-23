/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KambireSumsetR2
import Mathlib.Tactic

/-!
# `e₂ = 0` is the energy constraint `e₁² = p₂` — the bridge from the bad-scalar locus to the
antipodal / SidonModNeg count (#407, thread T1)

The δ* unified object is `K = #{dilation-orbits of e₁(S) : S a (k+m)-subset of μ_n with e_{≥2}
elementary-symmetric vanishing}`. For the two-monomial affine pencil `h_α(z)=z^{k+1}+α z^{k+2}`, a
bad scalar at agreement `k+2` corresponds to a `(k+2)`-subset `S` with `e₂(S)=0`, `e₁(S)≠0`, and
`α=−1/e₁(S)`. This file pins the **algebraic core** that makes the `e₂=0` locus accessible to the
negation-pair (Lam–Leung / `SidonModNeg`) energy machinery:

> `e2_zero_iff` :  in char `≠ 2`,  `e₂(S) = 0  ⟺  e₁(S)² = p₂(S)`,  i.e.  `(∑ s)² = ∑ s²`.

The vanishing of the second elementary symmetric is **exactly** an additive-energy / quadratic
constraint — `e₁²` (a square) equals the second power sum `p₂ = ∑ s²` (a sum of squares, landing in
the dilated subgroup `μ_{n/2}` over a dyadic domain). This is the constraint that
`AdditiveEnergySidonModNeg` / `KambireSumsetR2` control: the `fiber_zero` collapse of antipodal
pairs `{ζ,−ζ}` (which contribute `ζ·(−ζ)=−ζ²` to the off-diagonal sum, `offDiag_antipodal_contribution`)
is precisely the energy structure underneath `e₂`.

Also landed:
* `e1_sq_eq_offDiag_add_p2` — the order-free Newton split `(∑ s)² = (∑_{offDiag} a·b) + ∑ s²`.
* `e2_eq` — `e₂(S) = (e₁(S)² − p₂(S))/2`, the Newton identity `e₂ = (p₁² − p₂)/2` over a Finset.
* `badScalar_of_energy` — the energy locus `{S : e₁(S)² = p₂(S), e₁(S)≠0}` produces the bad scalar
  `α = −1/e₁(S)` of the pencil.
* `e2_pair` / `e2_pair_ne_zero` — `e₂({a,b}) = a·b`; the **`w=2` floor**: no 2-subset of a zero-free
  set (`S ⊆ μ_n`) has `e₂=0`, matching the BCH/rigidity floor (numerically `e₂=0` first appears at
  `w ≥ 4`).

This reduces the K=O(1)-above-δ* claim to **counting the energy locus `e₁² = p₂`** over `(k+2)`-
subsets of `μ_n` — a q-dependent, character-sum-free combinatorial object, NOT the BGK character-sum
wall. (The extremal `r ≈ |G|/2` count remains the open core; this file pins the algebra, not the
count.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- The second elementary symmetric function of a finset, as the sum over the off-diagonal
(each unordered pair counted twice, hence the `(·)/2`); equivalently `∑_{a<b} a·b`. We use the
offDiag form to keep it order-free. -/
noncomputable def e2 (S : Finset F) : F := (∑ p ∈ S.offDiag, p.1 * p.2) / 2

/-- `e₁(S) = ∑_{s∈S} s` (the power sum `p₁` and the first elementary symmetric coincide). -/
def e1 (S : Finset F) : F := ∑ s ∈ S, s

/-- `p₂(S) = ∑_{s∈S} s²` (the second power sum). -/
def p2 (S : Finset F) : F := ∑ s ∈ S, s ^ 2

/-- **Newton bridge (key identity).** For any finset `S` over a field, the full square of the
first power sum splits into off-diagonal + diagonal:
`(∑ s)² = (∑_{offDiag} a·b) + (∑ s²)`. This is `sum_mul_sum` over `S×S` decomposed via
`diag ∪ offDiag = S ×ˢ S`. -/
theorem e1_sq_eq_offDiag_add_p2 (S : Finset F) :
    e1 S ^ 2 = (∑ p ∈ S.offDiag, p.1 * p.2) + p2 S := by
  classical
  unfold e1 p2
  have hsq : (∑ s ∈ S, s) ^ 2 = ∑ p ∈ S ×ˢ S, p.1 * p.2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [hsq, ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag S)]
  have hdiag : (∑ p ∈ S.diag, p.1 * p.2) = ∑ s ∈ S, s ^ 2 := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl (fun s _ => (pow_two (s : F)).symm)
  rw [hdiag, add_comm]

/-- **`e₂` as `(e₁² − p₂)/2`.** The off-diagonal sum `∑_{offDiag} a·b = e₁² − p₂`, so
`e₂(S) = (e₁(S)² − p₂(S))/2`. This is the order-free Newton identity `e₂ = (p₁² − p₂)/2`. -/
theorem e2_eq (S : Finset F) : e2 S = (e1 S ^ 2 - p2 S) / 2 := by
  unfold e2
  rw [e1_sq_eq_offDiag_add_p2]
  ring

/-- **The energy characterization of `e₂ = 0`.** Over a field of characteristic `≠ 2`,
`e₂(S) = 0 ⟺ e₁(S)² = p₂(S)`, i.e. `(∑ s)² = ∑ s²`. The vanishing of the second elementary
symmetric is *exactly* the additive-energy / quadratic constraint that the negation-pair
(Lam–Leung / SidonModNeg) machinery addresses. -/
theorem e2_zero_iff (h2 : (2 : F) ≠ 0) (S : Finset F) :
    e2 S = 0 ↔ e1 S ^ 2 = p2 S := by
  rw [e2_eq, div_eq_zero_iff]
  simp only [h2, or_false, sub_eq_zero]

/-- **The two-monomial-pencil bad-scalar criterion (Chai–Fan / #400 bridge).** A `(k+2)`-subset `S`
gives a bad scalar of the affine pencil `z^{k+1}+α z^{k+2}` at agreement `k+2` exactly when
`e₂(S)=0` and `e₁(S)≠0`, with `α = −1/e₁(S)`. Reformulated via the energy characterization:
the bad-`α` value is `−1/e₁(S)` over the subsets `S` with `e₁(S)² = p₂(S)` (the energy locus)
and `e₁(S) ≠ 0`. This packages the bad-scalar locus as an *energy-constraint locus*, the object
the SidonModNeg / antipodal count bounds. -/
theorem badScalar_of_energy (h2 : (2 : F) ≠ 0) (S : Finset F)
    (hen : e1 S ^ 2 = p2 S) (hne : e1 S ≠ 0) :
    e2 S = 0 ∧ ∃ α : F, α = -(e1 S)⁻¹ ∧ α * e1 S = -1 := by
  refine ⟨(e2_zero_iff h2 S).mpr hen, -(e1 S)⁻¹, rfl, ?_⟩
  field_simp

/-- **`e₂` of a 2-element subset is the product.** For distinct `a ≠ b` in char `≠ 2`,
`e₂({a,b}) = a·b`. -/
theorem e2_pair (h2 : (2 : F) ≠ 0) {a b : F} (hab : a ≠ b) :
    e2 ({a, b} : Finset F) = a * b := by
  classical
  unfold e2
  have hoff : ({a, b} : Finset F).offDiag = {(a, b), (b, a)} := by
    ext ⟨c, d⟩
    simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hc, hd, hcd⟩
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hcd
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hcd
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl rfl, Or.inr rfl, hab⟩
      · exact ⟨Or.inr rfl, Or.inl rfl, hab.symm⟩
  have hnotmem : (a, b) ∉ ({(b, a)} : Finset (F × F)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
    intro h _
    exact hab h
  rw [hoff, Finset.sum_insert hnotmem, Finset.sum_singleton]
  rw [div_eq_iff h2]; ring

/-- **The `w=2` floor: no 2-subset of a zero-free set has `e₂ = 0`.** If every element of `S` is
nonzero (e.g. `S ⊆ μ_n`, a multiplicative subgroup) then a 2-subset `{a,b}` has `e₂ = a·b ≠ 0`.
Hence the elementary-symmetric-vanishing locus is **empty at width 2** — matching the BCH/rigidity
floor (one needs `w ≥ 4` for `e₂ = 0`, verified numerically). -/
theorem e2_pair_ne_zero (h2 : (2 : F) ≠ 0) {a b : F} (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    e2 ({a, b} : Finset F) ≠ 0 := by
  rw [e2_pair h2 hab]
  exact mul_ne_zero ha hb

/-- **Antipodal pairs and the off-diagonal sum.** An antipodal pair `{ζ, −ζ}` contributes
`ζ·(−ζ) = −ζ²` to the off-diagonal product sum, so it pulls `e₂` toward `0` precisely by the
square of the element. This is the algebraic content behind the `fiber_zero` collapse in
`KambireSumsetR2`: antipodal pairs are exactly the ones whose product is `−ζ²`, the negative of a
square in `μ_{n/2}`. -/
theorem offDiag_antipodal_contribution (ζ : F) :
    ζ * (-ζ) = -(ζ ^ 2) := by ring

/-- **First power sum vanishes for a negation-closed set in char ≠ 2.** If `S` is closed under
negation (`∀ x ∈ S, -x ∈ S`) and char `F ≠ 2`, then `e₁(S) = ∑_{s∈S} s = 0`. Pair `S` under the
fixed-point-free involution `x ↦ -x` (`add_neg_cancel`); the fixed-point-free obligation `-a ≠ a`
when `a ≠ 0` follows from char `≠ 2` (`-a = a ⟹ 2a = 0 ⟹ a = 0`). The zero-free hypothesis is not
needed: an `a = 0` summand is harmless (it contributes `0`), so the `f a ≠ 0` premise the involution
lemma supplies is exactly enough. This is the algebraic seed of the Lam–Leung / SidonModNeg negation
pairing underlying the `e₂ = 0` energy locus. -/
theorem e1_eq_zero_of_neg_closed (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hcl : ∀ x ∈ S, -x ∈ S) : e1 S = 0 := by
  unfold e1
  refine Finset.sum_involution (fun a _ => -a) ?_ ?_ ?_ ?_
  · -- pairing: a + (-a) = 0
    intro a _
    exact add_neg_cancel a
  · -- fixed-point-free: a ≠ 0 → -a ≠ a
    intro a _ ha hfix
    -- hfix : -a = a, so 2*a = 0, and char ≠ 2 forces a = 0, contradicting ha
    apply ha
    have h2a : (2 : F) * a = 0 := by
      have : (-a : F) = a := hfix
      linear_combination -this
    rcases mul_eq_zero.mp h2a with h | h
    · exact absurd h h2
    · exact h
  · -- membership: -a ∈ S
    intro a ha
    exact hcl a ha
  · -- involution: -(-a) = a
    intro a _
    exact neg_neg a


/-- **`2·e₂` is the off-diagonal sum (integral/division-free form).** In characteristic `≠ 2`,
clearing the `/2` in the definition of `e₂` gives `2 · e₂(S) = ∑_{offDiag} a·b`, the
order-free off-diagonal product sum with no division. This is the division-free companion to
`e2_eq`, convenient when transporting the energy identity into rings/contexts where dividing by
`2` is undesirable. -/
theorem two_mul_e2_eq_offDiag (h2 : (2 : F) ≠ 0) (S : Finset F) :
    2 * e2 S = ∑ p ∈ S.offDiag, p.1 * p.2 := by
  unfold e2
  rw [mul_div_cancel₀ _ h2]


/-- **Cross-thread connector: a negation-closed set is never a two-monomial bad-`α` witness.**
The two-monomial-pencil bad-scalar criterion (`badScalar_of_energy`) fires on exactly the
*energy locus* `{S : e₁(S)² = p₂(S) ∧ e₁(S) ≠ 0}` (the `(hen, hne)` pair that produces the bad
scalar `α = −1/e₁(S)`). This connector ties that locus to the *antipodal-free reduction*: in
characteristic `≠ 2`, a set `S` closed under negation (`∀ x ∈ S, -x ∈ S`) can **never** sit on the
bad-scalar locus, because the negation pairing forces `e₁(S) = 0`
(`e1_eq_zero_of_neg_closed`), directly contradicting the `e₁(S) ≠ 0` component. Hence the energy
locus `e₁² = p₂` that the SidonModNeg / antipodal count bounds is automatically **disjoint** from
the negation-closed sets — a structural witness-suppression on the antipodal-free side. -/
theorem no_badScalar_of_neg_closed (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hcl : ∀ x ∈ S, -x ∈ S) : ¬ (e1 S ^ 2 = p2 S ∧ e1 S ≠ 0) :=
  fun ⟨_, hne⟩ => hne (e1_eq_zero_of_neg_closed h2 hcl)


end ArkLib.ProximityGap.E2VanishEnergy

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e1_sq_eq_offDiag_add_p2
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e2_eq
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e2_zero_iff
#print axioms ArkLib.ProximityGap.E2VanishEnergy.badScalar_of_energy
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e2_pair
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e2_pair_ne_zero
#print axioms ArkLib.ProximityGap.E2VanishEnergy.offDiag_antipodal_contribution
#print axioms ArkLib.ProximityGap.E2VanishEnergy.e1_eq_zero_of_neg_closed
#print axioms ArkLib.ProximityGap.E2VanishEnergy.two_mul_e2_eq_offDiag
#print axioms ArkLib.ProximityGap.E2VanishEnergy.no_badScalar_of_neg_closed
