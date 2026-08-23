/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GenuineQuadrupleSidonModNeg

/-!
# The multiplicative-closure converse: `SidonModNeg ↔ ¬GenuineQuadrupleNZ` for a subgroup (#444 k=2)

`GenuineQuadrupleSidonModNeg` formalized one direction of the `k = 2` shadow of the BGK wall:

> `not_genuineQuadrupleNZ_of_sidonModNeg` : `1 ∈ G → SidonModNeg G → ¬ GenuineQuadrupleNZ G`

and explicitly flagged the converse as **not formalized**, only probe-validated:

> "The reverse implication `¬ GenuineQuadrupleNZ G → SidonModNeg G` is NOT free for a GENERAL
>  finite set: `SidonModNeg` is a `∀`-statement over EVERY distinguished left element `a ∈ G`,
>  whereas `GenuineQuadrupleNZ` normalizes only to the single element `1`.  For a
>  MULTIPLICATIVELY-CLOSED `μ_n` the two coincide (any coincidence `a + b = c + d` divides through
>  by `a ∈ μ_n` ...). We do NOT formalize that multiplicative normalization here (it would require
>  the subgroup-closure hypotheses)."

This file supplies exactly that missing brick.  The multiplicative-closure hypotheses are the
defining properties of `μ_n = {z : zⁿ = 1}` (closed under `·`, inverses, contains `1`, all elements
nonzero), packaged as `MulClosed1`.  Under them the `1`-normalized obstruction `GenuineQuadrupleNZ`
is the EXACT complement of `SidonModNeg`, giving the full `iff`:

> **`sidonModNeg_iff_not_genuineQuadrupleNZ`** :
> `MulClosed1 G → (SidonModNeg G ↔ ¬ GenuineQuadrupleNZ G)`.

The new content is the converse `sidonModNeg_of_not_genuineQuadrupleNZ`: a coincidence
`a + b = c + d` with `a + b ≠ 0` is divided through by `a⁻¹ ∈ G` to the `1`-normalized form
`1 + a⁻¹b = a⁻¹c + a⁻¹d`, whose sum `a⁻¹(a+b) ≠ 0`.  If its unordered pairs differed we would have a
`GenuineQuadrupleNZ`, contradicting the hypothesis; so `{1, a⁻¹b} = {a⁻¹c, a⁻¹d}`, and multiplying
back by the unit `a` (an injection) gives `{a, b} = {c, d}`, hence the ordered SidonModNeg branch.

This closes the `k = 2` energy characterization into a single biconditional for any multiplicative
subgroup, completing the hook left by `GenuineQuadrupleSidonModNeg`.

## Scope (honesty contract)

Pure char-free / field-universal additive-multiplicative combinatorics: it relates two Props about a
finite multiplicative subgroup; thickness/regime never enters and no field-arithmetic input is
consumed.  It does **not** decide whether `μ_n` actually IS Sidon-mod-negation at the prize prime
`p ~ n⁴` (the `energyExcess = 0` / non-existence-of-genuine-quadruple question).  Exact computation
shows that property holds for a density-`→1` set of primes in the prize window but has a thin,
structured exceptional set (e.g. `p = 65537`; `12/46823` primes for `n = 64`), so the matching
field-arithmetic statement remains the `k = 2` shadow of the BGK wall.  This brick only WIRES the
two obstruction Props into one biconditional; CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.GenuineQuadrupleMulClosed

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Multiplicative-closure-with-`1`.**  The defining algebraic properties of `μ_n` as a subset of
a field: it contains `1`, is closed under multiplication and inverses, and all elements are nonzero
(so the inverse used in the converse is a genuine unit). -/
structure MulClosed1 (G : Finset F) : Prop where
  one_mem : (1 : F) ∈ G
  mul_mem : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G
  inv_mem : ∀ x ∈ G, x⁻¹ ∈ G
  ne_zero : ∀ x ∈ G, x ≠ 0

/-- **Unordered pair equality is the ordered-trivial disjunction** (general two-element form).
`{a,b} = {c,d}` over any type with `DecidableEq` iff `(a=c ∧ b=d) ∨ (a=d ∧ b=c)`. -/
theorem pair_eq_iff_ordered_gen {α : Type*} [DecidableEq α] (a b c d : α) :
    (({a, b} : Finset α) = {c, d}) ↔ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  rw [Finset.ext_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hc : c = a ∨ c = b := by have := (h c).mpr (Or.inl rfl); tauto
    have hd : d = a ∨ d = b := by have := (h d).mpr (Or.inr rfl); tauto
    have hamem : a = c ∨ a = d := (h a).mp (Or.inl rfl)
    have hbmem : b = c ∨ b = d := (h b).mp (Or.inr rfl)
    rcases hamem with hac | had
    · rcases hbmem with hbc | hbd
      · rcases hd with hda | hdb
        · left; exact ⟨hac, by rw [hbc, ← hac, ← hda]⟩
        · left; exact ⟨hac, hdb.symm⟩
      · exact Or.inl ⟨hac, hbd⟩
    · rcases hbmem with hbc | hbd
      · exact Or.inr ⟨had, hbc⟩
      · rcases hc with hca | hcb
        · right; exact ⟨had, by rw [hbd, ← had, ← hca]⟩
        · right; exact ⟨had, hcb.symm⟩
  · rintro (⟨hac, hbd⟩ | ⟨had, hbc⟩) x
    · rw [hac, hbd]
    · rw [had, hbc]; tauto

/-- Dividing an unordered pair equality by a nonzero `a`: `{a,b} = {c,d} ↔ {1,a⁻¹b} = {a⁻¹c,a⁻¹d}`.
Multiplication by the unit `a⁻¹` (equivalently by `a`) is injective, so the Finset image equality is
equivalent on both sides. -/
theorem pair_div_eq_iff {a b c d : F} (ha : a ≠ 0) :
    (({a, b} : Finset F) = {c, d})
      ↔ (({(1 : F), a⁻¹ * b} : Finset F) = {a⁻¹ * c, a⁻¹ * d}) := by
  constructor
  · intro h
    have := congrArg (Finset.image (fun x : F => a⁻¹ * x)) h
    simp only [Finset.image_insert, Finset.image_singleton] at this
    rwa [inv_mul_cancel₀ ha] at this
  · intro h
    have := congrArg (Finset.image (fun x : F => a * x)) h
    simp only [Finset.image_insert, Finset.image_singleton] at this
    rw [mul_one] at this
    rwa [mul_inv_cancel_left₀ ha, mul_inv_cancel_left₀ ha, mul_inv_cancel_left₀ ha] at this

/-- **The converse, for a multiplicative subgroup.**  If `G` is closed under `·`, inverses, and
contains `1` (with all elements nonzero), then the absence of a `1`-normalized nonzero-sum genuine
quadruple forces the full `SidonModNeg` property.  The proof divides an arbitrary coincidence
`a + b = c + d` by the unit `a⁻¹ ∈ G`. -/
theorem sidonModNeg_of_not_genuineQuadrupleNZ {G : Finset F}
    (hMC : MulClosed1 G) (hng : ¬ GenuineQuadrupleNZ G) :
    SidonModNeg G := by
  intro a ha b hb c hc d hd habcd
  by_cases hab0 : a + b = 0
  · exact Or.inr (Or.inr hab0)
  · -- divide by the unit a⁻¹
    have ha0 : a ≠ 0 := hMC.ne_zero a ha
    have hai : a⁻¹ ∈ G := hMC.inv_mem a ha
    have hBmem : a⁻¹ * b ∈ G := hMC.mul_mem _ hai _ hb
    have hCmem : a⁻¹ * c ∈ G := hMC.mul_mem _ hai _ hc
    have hDmem : a⁻¹ * d ∈ G := hMC.mul_mem _ hai _ hd
    have hia : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
    have hrel : (1 : F) + a⁻¹ * b = a⁻¹ * c + a⁻¹ * d := by
      have : a⁻¹ * (a + b) = a⁻¹ * (c + d) := by rw [habcd]
      rw [mul_add, mul_add, hia] at this
      exact this
    have hnz : (1 : F) + a⁻¹ * b ≠ 0 := by
      have hne : a⁻¹ * (a + b) ≠ 0 := mul_ne_zero (inv_ne_zero ha0) hab0
      rwa [mul_add, inv_mul_cancel₀ ha0] at hne
    -- the divided pair MUST match, else GenuineQuadrupleNZ
    have hpair : ({(1 : F), a⁻¹ * b} : Finset F) = {a⁻¹ * c, a⁻¹ * d} := by
      by_contra hne
      exact hng ⟨a⁻¹ * b, a⁻¹ * c, a⁻¹ * d, hBmem, hCmem, hDmem, hrel, hnz, hne⟩
    -- multiply back: {a,b} = {c,d}, then read off the ordered branch
    have hpair' : ({a, b} : Finset F) = {c, d} := (pair_div_eq_iff ha0).mpr hpair
    rcases (pair_eq_iff_ordered_gen a b c d).mp hpair' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- **The `k = 2` biconditional for a multiplicative subgroup.**  For a multiplicatively-closed
`G ∋ 1` (e.g. `μ_n`), `SidonModNeg G` holds iff there is no `1`-normalized nonzero-sum genuine
quadruple.  Forward direction is `not_genuineQuadrupleNZ_of_sidonModNeg`; converse is this file's
`sidonModNeg_of_not_genuineQuadrupleNZ`. -/
theorem sidonModNeg_iff_not_genuineQuadrupleNZ {G : Finset F} (hMC : MulClosed1 G) :
    SidonModNeg G ↔ ¬ GenuineQuadrupleNZ G :=
  ⟨not_genuineQuadrupleNZ_of_sidonModNeg hMC.one_mem,
   sidonModNeg_of_not_genuineQuadrupleNZ hMC⟩

/-! ## Specialization to `μ_n = {z : zⁿ = 1}` -/

/-- **`μ_n` satisfies `MulClosed1`.**  The subgroup `μ_n = {z : zⁿ = 1}` of a field's unit group
(with `n ≥ 1`) contains `1`, is closed under `·` and inverses, and has no zero element.  This is the
concrete instance that makes `sidonModNeg_iff_not_genuineQuadrupleNZ` apply directly to the prize
object: for `μ_n`, the `∀`-over-every-element `SidonModNeg` and the `1`-normalized
`GenuineQuadrupleNZ` are EQUIVALENT obstructions. -/
theorem mulClosed1_mu_n {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) : MulClosed1 G where
  one_mem := by rw [hGmem]; exact one_pow n
  mul_mem := by
    intro x hx y hy
    rw [hGmem] at hx hy ⊢
    rw [mul_pow, hx, hy, mul_one]
  inv_mem := by
    intro x hx
    rw [hGmem] at hx ⊢
    rw [inv_pow, hx, inv_one]
  ne_zero := by
    intro x hx hx0
    rw [hGmem, hx0, zero_pow (by omega)] at hx
    exact zero_ne_one hx

/-- **The `k = 2` biconditional, specialized to `μ_n`.**  For `μ_n = {z : zⁿ = 1}` (`n ≥ 1`),
`SidonModNeg μ_n` (the `r = 2` additive-energy floor `E₂ = 3n²−3n`, by
`AdditiveEnergyCharacterization.additiveEnergy_eq_iff_sidonModNeg`) holds iff there is no
`1`-normalized nonzero-sum genuine quadruple `1 + B = C + D` in `μ_n`.  This reduces the
quartic-quantifier Sidon condition to a single-element-normalized one, which is the `k = 2` shadow
of the BGK wall: the field-arithmetic question of whether that quadruple exists at the prize prime
`p ~ n⁴` remains open (it does NOT for a density-`→1` set of primes, but has a thin structured
exceptional set). -/
theorem sidonModNeg_mu_n_iff_not_genuineQuadrupleNZ {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    SidonModNeg G ↔ ¬ GenuineQuadrupleNZ G :=
  sidonModNeg_iff_not_genuineQuadrupleNZ (mulClosed1_mu_n hn hGmem)

end ArkLib.ProximityGap.GenuineQuadrupleMulClosed

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms pair_eq_iff_ordered_gen
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms pair_div_eq_iff
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms sidonModNeg_of_not_genuineQuadrupleNZ
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms sidonModNeg_iff_not_genuineQuadrupleNZ
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms mulClosed1_mu_n
open ArkLib.ProximityGap.GenuineQuadrupleMulClosed in
#print axioms sidonModNeg_mu_n_iff_not_genuineQuadrupleNZ
