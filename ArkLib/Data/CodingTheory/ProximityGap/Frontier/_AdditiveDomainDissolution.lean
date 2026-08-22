/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Additive/Binius domain dissolution (#466, lane L5, dossier §6 Tier-3)

**The multiplicative wall is a domain artifact — formal statement.**

For the multiplicative smooth domains `μ_n ⊆ F_p^×` of the Proximity Prize regime, the whole
Johnson→capacity gap is governed by the far-direction character-sum maximum
`M = max_b |∑_{x∈μ_n} e_p(bx)|`, a genuinely transcendental quantity (Gauss-period house,
`√p`-Weil ceiling, the entire #444/#464/#466 no-go landscape).  This file proves that for
**F₂-linear (additive-NTT / Binius) evaluation domains** — `S` an `F₂`-subspace, or in fact ANY
additive subgroup of ANY additive group — the corresponding object is **degenerate by
orthogonality**:

* `addChar_sum_addSubgroup_dichotomy` (and the `SetLike` master form
  `addChar_sum_subgroupClass_dichotomy`): for any additive character `ψ` into an integral
  domain, `∑_{x∈S} ψ x` is either `|S|` (iff `ψ` is trivial on `S`) or `0`.  The additive
  analogue of `M(μ_n)` collapses to the trivial two-point spectrum `{0, |S|}` — there is **no**
  intermediate eigenvalue, hence no analogue of the `M`-wall on additive domains.
* `subgroupClass_energy` / `addSubgroup_energy` / `submodule_energy`: the additive energy is
  exactly extremal, `E(S) := #{(a,b,c,d) ∈ S⁴ : a+b = c+d} = |S|³` — the quantity whose
  multiplicative counterpart (`E(μ_n)` beyond `n³`) consumed entire #444 campaigns is an exact
  one-bijection identity here.
* `addChar_sum_submodule_dichotomy`: the dichotomy phrased for a linear subspace
  `V : Submodule K F` (Binius instantiation: `K = ZMod 2`, `F = F_{2^k}`, `R = ℂ`).

## The honest caveat: where the hardness relocates (do NOT over-claim)

**This file does NOT solve any Binius/additive-RS proximity question.**  What it proves is that
the *specific* obstruction blocking δ* on multiplicative smooth domains — a nondegenerate
far-direction character spectrum — does not exist on additive domains.  The hardness relocates,
and the relocation is itself made precise here:

* `addChar_coset_sum` / `addChar_coset_sum_eq_zero_of_nontrivial`: for every character `ψ`
  nontrivial on `S`, **every** coset sum `∑_{x∈S} ψ(y+x) = ψ(y)·∑_{x∈S} ψ(x) = 0` vanishes
  identically in `y`.  So ambient Fourier/character analysis is *blind* on additive domains: it
  cannot distinguish cosets of `S`, and in particular carries zero information about agreement
  on proper subsets of `S` — which is the actual proximity object.  The discriminating data for
  additive RS lives in the **dual filtration**: the characters trivial on `S` form the
  annihilator `S^⊥` (a subgroup of the dual of index `[Ĝ : S^⊥] = [G : S]` under the
  finite-field trace pairing), and the far-direction analysis for an additive-RS proximity
  statement moves to the **coset geometry of `S^⊥`** — which characters are trivial on which
  members of the `F₂`-flag `S = S_k ⊃ S_{k-1} ⊃ ⋯ ⊃ S_0` used by the additive NTT.  That is a
  different (combinatorial, subspace-lattice) problem with its own open questions; nothing here
  bounds it.
* In particular the prize-shaped question "beyond-Johnson mutual correlated agreement for
  additive-NTT RS codes" remains **open**; this brick only certifies that its analytic core is
  not the multiplicative `M`-wall.

Companion kb note: `docs/kb/deltastar-466-additive-domain-dissolution.md`.
-/

namespace ArkLib.ProximityGap.AdditiveDomainDissolution

open Finset

/-! ## Part 1: the character-sum dichotomy on an additive subgroup

Stated once for any `SetLike` additive-subgroup class, so it instantiates verbatim for
`AddSubgroup G` and for `Submodule K F` (the Binius `F₂`-subspace shape). -/

section Dichotomy

variable {G : Type*} [AddGroup G] {R : Type*} [CommRing R]
variable {S : Type*} [SetLike S G] [AddSubgroupClass S G]

/-- Restriction of an additive character of `G` to a subgroup `s`, as an additive character
of `↥s`. -/
def restrict (ψ : AddChar G R) (s : S) : AddChar s R :=
  ψ.compAddMonoidHom (AddSubgroupClass.subtype s)

@[simp] lemma restrict_apply (ψ : AddChar G R) (s : S) (x : s) :
    restrict ψ s x = ψ (x : G) := rfl

/-- The restricted character is trivial iff `ψ` takes the value `1` on all of `s`. -/
lemma restrict_eq_one_iff (ψ : AddChar G R) (s : S) :
    restrict ψ s = 1 ↔ ∀ x ∈ s, ψ x = 1 := by
  constructor
  · intro h x hx
    have := DFunLike.congr_fun h (⟨x, hx⟩ : s)
    simpa using this
  · intro h
    ext x
    simpa using h x x.2

/-- **Trivial branch.** If `ψ` is trivial on the subgroup `s`, the character sum over `s`
is `|s|`. -/
theorem addChar_sum_subgroupClass_of_trivial [IsDomain R] (ψ : AddChar G R) (s : S) [Fintype s]
    (h : ∀ x ∈ s, ψ x = 1) :
    ∑ x : s, ψ (x : G) = (Fintype.card s : R) := by
  have h1 : restrict ψ s = 1 := (restrict_eq_one_iff ψ s).2 h
  calc ∑ x : s, ψ (x : G) = ∑ x : s, restrict ψ s x := by simp
    _ = (Fintype.card s : R) := AddChar.sum_eq_card_of_eq_one h1

/-- **Vanishing branch (the dissolution).** If `ψ` is nontrivial somewhere on the subgroup
`s`, the character sum over `s` vanishes exactly.  This is character orthogonality on the
subgroup: the additive-domain analogue of the far-direction eigenvalue `η_b(μ_n)` has NO
intermediate values. -/
theorem addChar_sum_subgroupClass_of_nontrivial [IsDomain R] (ψ : AddChar G R) (s : S)
    [Fintype s] (h : ∃ x ∈ s, ψ x ≠ 1) :
    ∑ x : s, ψ (x : G) = 0 := by
  obtain ⟨x, hxS, hx⟩ := h
  have hne : restrict ψ s ≠ 1 :=
    AddChar.ne_one_iff.2 ⟨⟨x, hxS⟩, by simpa using hx⟩
  calc ∑ x : s, ψ (x : G) = ∑ x : s, restrict ψ s x := by simp
    _ = 0 := AddChar.sum_eq_zero_of_ne_one hne

/-- **The dichotomy (SetLike master form).**  For any additive subgroup `s` of any additive
group `G` and any additive character `ψ` into an integral domain,
`∑_{x∈s} ψ x ∈ {|s|, 0}`.  The additive analogue of `M(μ_n) = max_b |η_b|` collapses to the
trivial two-point spectrum — the Johnson→capacity character-sum wall is specific to
multiplicative domains. -/
theorem addChar_sum_subgroupClass_dichotomy [IsDomain R] (ψ : AddChar G R) (s : S) [Fintype s] :
    ∑ x : s, ψ (x : G) = (Fintype.card s : R) ∨ ∑ x : s, ψ (x : G) = 0 := by
  by_cases h : ∀ x ∈ s, ψ x = 1
  · exact Or.inl (addChar_sum_subgroupClass_of_trivial ψ s h)
  · refine Or.inr (addChar_sum_subgroupClass_of_nontrivial ψ s ?_)
    simpa [not_forall] using h

/-- The dichotomy for an `AddSubgroup`. -/
theorem addChar_sum_addSubgroup_dichotomy [IsDomain R] (ψ : AddChar G R) (s : AddSubgroup G)
    [Fintype s] :
    ∑ x : s, ψ (x : G) = (Fintype.card s : R) ∨ ∑ x : s, ψ (x : G) = 0 :=
  addChar_sum_subgroupClass_dichotomy ψ s

/-- The Binius instantiation shape: the dichotomy for a **linear subspace** `V` of a module
(take `K = ZMod 2`, `F = F_{2^k}`, `R = ℂ` for the additive-NTT evaluation domain). -/
theorem addChar_sum_submodule_dichotomy [IsDomain R] {K F : Type*} [Ring K] [AddCommGroup F]
    [Module K F] (ψ : AddChar F R) (V : Submodule K F) [Fintype V] :
    ∑ x : V, ψ (x : F) = (Fintype.card V : R) ∨ ∑ x : V, ψ (x : F) = 0 :=
  addChar_sum_subgroupClass_dichotomy ψ V

end Dichotomy

/-! ## Part 2: the honest caveat — coset blindness, i.e. where the hardness relocates

For `ψ` nontrivial on `s`, not only does the sum over `s` vanish: the sum over EVERY coset
`y + s` vanishes, identically in `y`.  So ambient character sums carry **zero** information
distinguishing cosets of `s` — the discriminating structure for additive-RS far-direction
analysis is not any `η`-spectrum but the annihilator/coset geometry of `s^⊥` in the dual
(which characters are trivial on which members of the NTT subspace flag).  This file proves
the blindness; it does NOT touch the relocated (subspace-lattice) problem. -/

section Coset

variable {G : Type*} [AddGroup G] {R : Type*} [CommRing R]
variable {S : Type*} [SetLike S G]

/-- Coset factorization: `∑_{x∈s} ψ(y+x) = ψ(y) · ∑_{x∈s} ψ(x)`. -/
theorem addChar_coset_sum (ψ : AddChar G R) (s : S) [Fintype s] (y : G) :
    ∑ x : s, ψ (y + (x : G)) = ψ y * ∑ x : s, ψ (x : G) := by
  simp_rw [AddChar.map_add_eq_mul, Finset.mul_sum]

/-- **Coset blindness.**  If `ψ` is nontrivial on `s`, then every coset sum vanishes:
the character spectrum cannot see WHICH coset of `s` it is looking at.  This is the precise
sense in which the additive-domain hardness relocates to the `s^⊥`-coset structure rather
than being resolved. -/
theorem addChar_coset_sum_eq_zero_of_nontrivial [IsDomain R] [AddSubgroupClass S G]
    (ψ : AddChar G R) (s : S) [Fintype s] (h : ∃ x ∈ s, ψ x ≠ 1) (y : G) :
    ∑ x : s, ψ (y + (x : G)) = 0 := by
  rw [addChar_coset_sum, addChar_sum_subgroupClass_of_nontrivial ψ s h, mul_zero]

end Coset

/-! ## Part 3: additive energy of a subgroup is exactly extremal, `E(S) = |S|³` -/

section Energy

/-- For a whole additive commutative group `H` (in particular any subgroup, as a group in its
own right), the solution set of `a + b = c + d` in `H⁴` is in bijection with `H³`: the triple
`(a, b, c)` determines `d = a + b - c`. -/
def energyEquiv (H : Type*) [AddCommGroup H] :
    {x : H × H × H × H // x.1 + x.2.1 = x.2.2.1 + x.2.2.2} ≃ H × H × H where
  toFun x := (x.1.1, x.1.2.1, x.1.2.2.1)
  invFun y := ⟨(y.1, y.2.1, y.2.2, y.1 + y.2.1 - y.2.2), sub_eq_iff_eq_add'.mp rfl⟩
  left_inv := by
    rintro ⟨⟨a, b, c, d⟩, h⟩
    have hd : a + b - c = d := sub_eq_iff_eq_add'.mpr h
    subst hd
    rfl
  right_inv := fun y => rfl

/-- Additive energy of a full finite group, `Nat.card` form: `E(H) = |H|³`. -/
theorem energy_nat_card (H : Type*) [AddCommGroup H] :
    Nat.card {x : H × H × H × H // x.1 + x.2.1 = x.2.2.1 + x.2.2.2} = Nat.card H ^ 3 := by
  rw [Nat.card_congr (energyEquiv H), Nat.card_prod, Nat.card_prod]
  ring

/-- **`E(s) = |s|³` for an additive subgroup**, with the quadruple condition stated in the
AMBIENT group (the form relevant to an evaluation domain `s ⊆ F`): the number of quadruples
`(a,b,c,d) ∈ s⁴` with `a + b = c + d` in `G` is exactly `|s|³`.  Compare the multiplicative
smooth domains, where pinning `E(μ_n)` beyond `n³` was a campaign-scale effort — on additive
domains the energy is extremal by closure, in one bijection. -/
theorem subgroupClass_energy {G : Type*} [AddCommGroup G] {S : Type*} [SetLike S G]
    [AddSubgroupClass S G] (s : S) :
    Nat.card {x : s × s × s × s //
      (x.1 : G) + (x.2.1 : G) = (x.2.2.1 : G) + (x.2.2.2 : G)} = Nat.card s ^ 3 := by
  have e : {x : s × s × s × s //
        (x.1 : G) + (x.2.1 : G) = (x.2.2.1 : G) + (x.2.2.2 : G)} ≃
      {x : s × s × s × s // x.1 + x.2.1 = x.2.2.1 + x.2.2.2} :=
    Equiv.subtypeEquivRight fun x =>
      ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  rw [Nat.card_congr e, energy_nat_card]

/-- `E(s) = |s|³` for an `AddSubgroup`. -/
theorem addSubgroup_energy {G : Type*} [AddCommGroup G] (s : AddSubgroup G) :
    Nat.card {x : s × s × s × s //
      (x.1 : G) + (x.2.1 : G) = (x.2.2.1 : G) + (x.2.2.2 : G)} = Nat.card s ^ 3 :=
  subgroupClass_energy s

/-- `E(V) = |V|³` for a linear subspace (Binius shape: `K = ZMod 2`, `F = F_{2^k}`). -/
theorem submodule_energy {K F : Type*} [Ring K] [AddCommGroup F] [Module K F]
    (V : Submodule K F) :
    Nat.card {x : V × V × V × V //
      (x.1 : F) + (x.2.1 : F) = (x.2.2.1 : F) + (x.2.2.2 : F)} = Nat.card V ^ 3 :=
  subgroupClass_energy V

/-- `Fintype.card` form of `subgroupClass_energy`. -/
theorem subgroupClass_energy_fintype {G : Type*} [AddCommGroup G] {S : Type*} [SetLike S G]
    [AddSubgroupClass S G] (s : S) [Fintype s] :
    Nat.card {x : s × s × s × s //
      (x.1 : G) + (x.2.1 : G) = (x.2.2.1 : G) + (x.2.2.2 : G)} = Fintype.card s ^ 3 := by
  rw [subgroupClass_energy, Nat.card_eq_fintype_card]

/-- Tie-in to Mathlib's canonical `Finset.addEnergy`: the energy of a full finite group is
`|H|³` in the `E[univ, univ]` normalization as well. -/
theorem addEnergy_univ_cube (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H] :
    Finset.addEnergy (Finset.univ : Finset H) Finset.univ = Fintype.card H ^ 3 := by
  rw [Finset.addEnergy_univ_left, Finset.card_univ]
  ring

end Energy

end ArkLib.ProximityGap.AdditiveDomainDissolution

-- Honesty contract: every claim above must be axiom-clean
-- (expected: subset of [propext, Classical.choice, Quot.sound], 0 sorryAx).
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_sum_subgroupClass_of_trivial
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_sum_subgroupClass_of_nontrivial
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_sum_subgroupClass_dichotomy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_sum_addSubgroup_dichotomy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_sum_submodule_dichotomy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addChar_coset_sum_eq_zero_of_nontrivial
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.energy_nat_card
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.subgroupClass_energy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addSubgroup_energy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.submodule_energy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.subgroupClass_energy_fintype
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addEnergy_univ_cube
