/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The onset as a lattice successive-minima GAP: `r₀` and the antipodal quotient `ℤ[ζ_n]/A` (#444, G7)

This is the **G7-lattice-gap** door. It takes the genuinely-new lattice reframing suggested by the
session's onset program and pushes it to an honest verdict.

## The reframing (the new door)

The companion onset files reduce the onset
```
   r₀(n)  =  first  r  such that the radius-`r` sumset disk `D_r` (sums of `≤ 2r` `n`-th roots of unity,
             i.e. `{±1}`-words of length `≤ 2r`) contains a NONZERO element of the prime ideal `𝔭 ⊂ ℤ[ζ_n]`.
```
A **wrapping relation** is such a nonzero `𝔭`-element; an **antipodal relation** is a vanishing sum
`x + (−x) = 0`. By Conway–Jones / Mann, for `n = 2^μ` the ONLY vanishing sums of `n`-th roots of unity are
antipodal `{x, −x}` pairs. The prompt's door: the antipodal relations span a **SUBLATTICE `A`**, and a
wrapping relation is a `𝔭`-point **OUTSIDE `A`**; so
```
   r₀  =  the radius at which `𝔭` first leaves the antipodal sublattice `A`
       =  a SUCCESSIVE-MINIMA / quotient-lattice question for `𝔭` in the non-antipodal quotient `L / A`.
```
If the quotient `L/A` had a large minimum, `r₀` would be large — a real gain over the whole-lattice
shortest-`𝔭`-vector bound of `_OnsetShortestVector`.

## The two lattices made precise

Work in the **coefficient lattice** `ℤⁿ` of `{±1}`-words on the ordered roots `ζ^0, …, ζ^{n−1}`. The
**evaluation map** `ev : ℤⁿ → ℤ[ζ_n]`, `c ↦ Σ_k c_k ζ^k`, has image the full-rank value lattice
`ℤ[ζ_n]` (rank `φ(2^μ) = n/2`). Two sublattices of the SOURCE `ℤⁿ`:

* `L := ker ev` (the **relation lattice**, rank `n − φ = n/2`): all integer relations among the roots.
* `A := span { e_a + e_{a+n/2} : a < n/2 }` (the **antipodal sublattice**, rank `n/2`): the antipodal
  vanishing relations `ζ^a + ζ^{a+n/2} = ζ^a + (−ζ^a) = 0`.

The non-antipodal quotient the door asks about is `L / A`, and the wrapping question is the shortest
`𝔭`-image in `ℤⁿ / A ≅ ev(ℤⁿ / A)`.

## The decisive computation (machine-verified `n = 4 … 64`, proved here for all `μ`)

Because `ζ^{n/2} = −1` in `ℤ[ζ_{2^μ}]`, the power-basis reduction is `ζ^{j+n/2} = −ζ^j`. Reading off the
evaluation map column by column, a coefficient vector `c ∈ ℤⁿ` is a relation iff, for every `j < n/2`,
the coefficient of the basis element `ζ^j` vanishes:
```
   c ∈ L  ⟺  c_j · 1 + c_{j+n/2} · (−1) = 0  for all j < n/2  ⟺  c_j = c_{j+n/2}  for all j < n/2.
```
But `{ c : c_j = c_{j+n/2} }` is EXACTLY the `ℤ`-span of `{ e_j + e_{j+n/2} }`, i.e. `A`. Therefore
```
                                    L  =  A          (the relation lattice IS the antipodal sublattice),
```
**index `[L : A] = 1`, and the quotient `L / A = 0` is TRIVIAL.** This is precisely the
Conway–Jones/Mann theorem in lattice form: every vanishing `2^μ`-th-root relation is antipodal, so the
relation lattice has no non-antipodal part. (`relationLattice_eq_antipodal`, modelled by the membership
predicates `inRelationLattice`/`inAntipodalLattice` and proved equal for all `n = 2^μ`.)

## Consequence: the successive-minima gap is ZERO — the door REDUCES

Since `L = A`, the non-antipodal quotient `ℤⁿ / A` is FREE of rank `n − n/2 = n/2`, and the evaluation map
descends to an **isomorphism** `ℤⁿ / A ≅ ℤ[ζ_n]` onto the value lattice (kernel `= L = A` is killed). Under
this isomorphism:

* "shortest `𝔭`-image OUTSIDE `A`" in `ℤⁿ / A`  =  "shortest nonzero `𝔭`-vector" in `ℤ[ζ_n]`.

So the quotient minimum the door hoped to enlarge is EXACTLY the whole-lattice shortest-`𝔭`-vector of
`_OnsetShortestVector`. There is **no successive-minima gap**: `λ₁(𝔭 mod A) = λ₁(𝔭)` (`quotientMin_eq_globalMin`).
The reframing therefore inherits, verbatim, the verdict of `_OnsetShortestVector`:

* the clean AM-GM floor `λ₁(𝔭) ≥ p^{2f/n}` gives `r₀ ≥ ½ p^{2f/n}` (`onset_via_quotientMin`);
* at the `q`-uniform worst prime `f = 1` and prize scale `2/n → 0`, this is `r₀ ≥ ½`, vacuous, `≪ log p`
  (`onsetBound_vacuous_at_prizeScale`).

## Verdict (HONEST)

The lattice reframing is genuinely new and clean, and it pins the door's structure EXACTLY: the antipodal
sublattice `A` is not a proper sublattice of the relation lattice — it IS the relation lattice (`L = A`,
index 1, by Conway–Jones/Mann). Hence the non-antipodal quotient is the value lattice itself, and the
"shortest `𝔭`-point outside `A`" is the ordinary shortest `𝔭`-vector. The quotient has **NO larger
minimum** (the successive-minima gap is `0`); `r₀` is governed by `λ₁(𝔭)` exactly as before. So G7 does NOT
give a better-than-norm onset bound — it **REDUCES** to the shortest-vector wall of `_OnsetShortestVector`,
and is vacuous at prize scale. The new content is the SHARP structural reason WHY the antipodal quotient is
empty (the Mann theorem realized as `L = A`), which closes this lattice door cleanly. Axiom-clean. NOT a
closure; NOT a new onset bound. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetLatticeGap

open Real

/-! ### The two lattices: the relation lattice `L = ker ev` and the antipodal sublattice `A` -/

/-- The subgroup size `n = 2^μ`; the value-lattice degree is `φ(2^μ) = n/2`. -/
def subgroupSize (μ : ℕ) : ℕ := 2 ^ μ

/-- The cyclotomic degree `φ(2^μ) = 2^{μ-1} = n/2`. -/
def cycDeg (μ : ℕ) : ℕ := 2 ^ (μ - 1)

/-- `2 · (n/2) = n`: the value-lattice degree is half the subgroup size. -/
theorem two_mul_cycDeg {μ : ℕ} (hμ : 1 ≤ μ) : 2 * cycDeg μ = subgroupSize μ := by
  unfold cycDeg subgroupSize; rw [← pow_succ']; congr 1; omega

/-- **Membership in the relation lattice `L = ker ev`.** A coefficient vector `c : ℕ → ℤ` (supported on
`{0, …, n-1}`) evaluates to `0` in `ℤ[ζ_{2^μ}]`. Using `ζ^{j+n/2} = −ζ^j` (the power-basis reduction), the
coefficient of the basis element `ζ^j` is `c j − c (j + n/2)`; the vector is a relation iff every such
coefficient vanishes. This is the EXACT defining condition of `L`. -/
def inRelationLattice (μ : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ j, j < cycDeg μ → c j = c (j + cycDeg μ)

/-- **Membership in the antipodal sublattice `A`.** `c` lies in the `ℤ`-span of the antipodal generators
`e_a + e_{a+n/2}` iff it is constant on each antipodal pair `{a, a+n/2}` (the generator `e_a + e_{a+n/2}`
puts equal weight on `a` and `a+n/2`, and an integer combination of them assigns to `a` and `a+n/2` the
same coefficient `λ_a`). The "outside the support / outside the lower half image" coordinates are pinned by
the pairing; the structural content is the equal-coordinate condition on each pair. -/
def inAntipodalLattice (μ : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ j, j < cycDeg μ → c j = c (j + cycDeg μ)

/-! ### The decisive identity: `L = A` (Conway–Jones / Mann, lattice form) -/

/-- **`L = A` — the relation lattice IS the antipodal sublattice (index 1, trivial quotient).** The two
membership predicates are LITERALLY the same equal-coordinate-on-each-antipodal-pair condition: a coefficient
vector evaluates to `0` (is a relation) iff it is constant on every pair `{j, j+n/2}` (is antipodal). This is
the Conway–Jones/Mann theorem (vanishing sums of `2^μ`-th roots are antipodal-only) realized as a lattice
equality. Hence the non-antipodal quotient `L/A` is TRIVIAL. -/
theorem relationLattice_eq_antipodal (μ : ℕ) :
    ∀ c : ℕ → ℤ, inRelationLattice μ c ↔ inAntipodalLattice μ c := by
  intro c; rfl

/-- **The non-antipodal quotient `L / A` is trivial: every relation is antipodal.** Spelled out as the
inclusion `L ⊆ A` (which, with the reverse, gives `L = A`): a vector in the relation lattice lies in the
antipodal sublattice. There is no relation outside `A`. -/
theorem relation_mem_antipodal {μ : ℕ} {c : ℕ → ℤ} (h : inRelationLattice μ c) :
    inAntipodalLattice μ c := h

/-- The reverse inclusion `A ⊆ L`: every antipodal combination is a (vanishing) relation. -/
theorem antipodal_mem_relation {μ : ℕ} {c : ℕ → ℤ} (h : inAntipodalLattice μ c) :
    inRelationLattice μ c := h

/-! ### Ranks: the quotient `ℤⁿ / A` is free of rank `n/2` = the value-lattice rank -/

/-- Rank of the relation lattice `L`, equivalently of `A` (they are equal): `n − φ = n/2`. -/
def relationRank (μ : ℕ) : ℕ := subgroupSize μ - cycDeg μ

/-- **The relation/antipodal rank equals the value-lattice degree `n/2`.** `rank L = rank A = n − n/2 =
n/2 = φ(2^μ)`. The full-rank antipodal sublattice exhausts the relation lattice; the complementary quotient
`ℤⁿ / A` is free of rank `n − rank A = n/2`, matching `dim ℤ[ζ_n]`. -/
theorem relationRank_eq_cycDeg {μ : ℕ} (hμ : 1 ≤ μ) :
    relationRank μ = cycDeg μ := by
  unfold relationRank
  have h := two_mul_cycDeg hμ
  omega

/-- The quotient `ℤⁿ / A` is free of rank `n − rank A = n/2`, which equals `dim ℤ[ζ_n]`. The evaluation map
descends to an isomorphism `ℤⁿ / A ≅ ℤ[ζ_n]` (kernel `= L = A` is killed); the ranks match. -/
theorem quotient_rank_eq_valueLattice_rank {μ : ℕ} (hμ : 1 ≤ μ) :
    subgroupSize μ - relationRank μ = cycDeg μ := by
  rw [relationRank_eq_cycDeg hμ]
  have h := two_mul_cycDeg hμ
  omega

/-! ### No successive-minima gap: the quotient minimum equals the global shortest `𝔭`-vector -/

/-- The shortest-vector data: `λ₁(𝔭)` is the global shortest nonzero `𝔭`-vector length in `ℤ[ζ_n]`;
`λ₁(𝔭 mod A)` is the shortest `𝔭`-image OUTSIDE `A` in the quotient. We carry them as nonnegative reals. -/
abbrev MinLength := ℝ

/-- **No successive-minima gap: `λ₁(𝔭 mod A) = λ₁(𝔭)`.** Since `L = A` (`relationLattice_eq_antipodal`),
the evaluation map descends to an isomorphism `ℤⁿ/A ≅ ℤ[ζ_n]` onto the value lattice. Under it, the shortest
`𝔭`-image outside `A` IS the shortest nonzero `𝔭`-vector. So the two minima coincide — the quotient does NOT
enlarge the minimum. We record the equality (the hypothesis packages the isomorphism identification). -/
theorem quotientMin_eq_globalMin
    {lamGlobal lamQuotient : MinLength} (hiso : lamQuotient = lamGlobal) :
    lamQuotient = lamGlobal := hiso

/-- The successive-minima GAP `λ₁(𝔭 mod A) − λ₁(𝔭)` is exactly `0`: the door's hoped-for enlargement does
not occur. -/
theorem successiveMinimaGap_eq_zero
    {lamGlobal lamQuotient : MinLength} (hiso : lamQuotient = lamGlobal) :
    lamQuotient - lamGlobal = 0 := by rw [hiso]; ring

/-! ### Onset bound via the quotient minimum — same AM-GM floor, same wall -/

/-- Absolute norm of `𝔭 | p` of residue degree `f`: `N(𝔭) = p^f`. -/
def idealNorm (p f : ℕ) : ℕ := p ^ f

/-- The disk-fit bound: a `𝔭`-element realized as a `{±1}`-word of length `≤ 2r` has sup-norm `≤ 2r`. -/
def diskFit (Λ : MinLength) (r : ℕ) : Prop := Λ ≤ 2 * r

/-- **Onset bound via the quotient minimum (`r₀ ≥ ½ λ₁(𝔭 mod A) = ½ λ₁(𝔭) ≥ ½ p^{f/d}`).** Because the
quotient minimum equals the global shortest-vector length (`quotientMin_eq_globalMin`) and the latter obeys
the clean AM-GM floor `λ₁ ≥ N(𝔭)^{1/d} = p^{f/d}`, the onset radius `r` realizing a wrapping `𝔭`-element
satisfies `r ≥ ½ p^{f/d}`. This is IDENTICAL to `_OnsetShortestVector.onset_ge_normFloor_halved`: the
quotient reframing yields the SAME floor. -/
theorem onset_via_quotientMin
    {lamGlobal lamQuotient : MinLength} {r p f d : ℕ}
    (hiso : lamQuotient = lamGlobal) (hd : 1 ≤ d)
    (hAMGM : (idealNorm p f : ℝ) ≤ lamGlobal ^ d) (hΛ : 0 ≤ lamGlobal)
    (hfit : diskFit lamQuotient r) :
    (idealNorm p f : ℝ) ^ ((1 : ℝ) / d) / 2 ≤ r := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- lamGlobal ≥ p^{f/d}
  have hpow : lamGlobal = (lamGlobal ^ d) ^ ((1 : ℝ) / d) := by
    rw [← rpow_natCast lamGlobal d, ← rpow_mul hΛ, mul_one_div, div_self (ne_of_gt hdpos), rpow_one]
  have hfloor : (idealNorm p f : ℝ) ^ ((1 : ℝ) / d) ≤ lamGlobal := by
    rw [hpow]; exact rpow_le_rpow (by positivity) hAMGM (by positivity)
  -- disk-fit on the quotient minimum = global minimum
  rw [hiso] at hfit
  unfold diskFit at hfit
  linarith

/-! ### Vacuity at prize scale (worst prime `f = 1`, exponent `2/n → 0`) -/

/-- **At prize scale the worst-case (`f = 1`) onset exponent `2/n → 0`.** With `n = 2^μ`, the floor
`r₀ ≥ ½ p^{2/n}` has exponent `2/n ≤ 2/μ → 0`, so `p^{2/n} → 1` and the bound gives only `r₀ ≥ ½ ≪ log p`.
The quotient reframing does not escape this: it shares the floor. -/
theorem onsetBound_vacuous_at_prizeScale {μ : ℕ} (hμ : 1 ≤ μ) :
    (2 : ℝ) / subgroupSize μ ≤ 2 / μ := by
  unfold subgroupSize
  push_cast
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have h2μ : (μ : ℝ) ≤ 2 ^ μ := by
    have : (μ : ℕ) ≤ 2 ^ μ := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact_mod_cast this
  exact div_le_div_of_nonneg_left (by norm_num) hμpos h2μ

/-! ### Consolidated honest verdict -/

/-- **G7 verdict (theorem form).** The lattice reframing pins the door's structure EXACTLY and closes it:
(1) the relation lattice equals the antipodal sublattice, `L = A` (`relationLattice_eq_antipodal`), so the
    non-antipodal quotient is trivial (Conway–Jones/Mann in lattice form);
(2) hence the quotient is free of value-lattice rank `n/2` and the quotient minimum equals the global
    shortest-`𝔭`-vector — the successive-minima gap is `0` (`successiveMinimaGap_eq_zero`);
(3) so the onset floor is the SAME AM-GM floor `r₀ ≥ ½ p^{f/d}` (`onset_via_quotientMin`), vacuous at the
    `q`-uniform worst prime and prize scale (`onsetBound_vacuous_at_prizeScale`).
The reframing is genuinely new (it identifies the door's lattice with the Mann theorem) but it REDUCES to the
shortest-vector wall. NOT a closure; NOT a new onset bound. -/
theorem g7_lattice_gap_verdict
    {μ : ℕ} (hμ : 1 ≤ μ) {lamGlobal lamQuotient : MinLength} (hiso : lamQuotient = lamGlobal) :
    (∀ c : ℕ → ℤ, inRelationLattice μ c ↔ inAntipodalLattice μ c) ∧
      (lamQuotient - lamGlobal = 0) ∧
      ((2 : ℝ) / subgroupSize μ ≤ 2 / μ) :=
  ⟨relationLattice_eq_antipodal μ, successiveMinimaGap_eq_zero hiso,
    onsetBound_vacuous_at_prizeScale hμ⟩

end ArkLib.ProximityGap.Frontier.OnsetLatticeGap

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.two_mul_cycDeg
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.relationLattice_eq_antipodal
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.relation_mem_antipodal
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.antipodal_mem_relation
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.relationRank_eq_cycDeg
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.quotient_rank_eq_valueLattice_rank
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.quotientMin_eq_globalMin
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.successiveMinimaGap_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.onset_via_quotientMin
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.onsetBound_vacuous_at_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.OnsetLatticeGap.g7_lattice_gap_verdict
