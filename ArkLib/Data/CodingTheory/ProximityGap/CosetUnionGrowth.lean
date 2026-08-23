/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity

/-!
# The coset-union growth law: a unified deep-band supply lower bound (#389)

`EvenTowerSupplyGrowth` (additive antipodal pairs, `d = 2`) and `CubicCosetSupplyGrowth`
(multiplicative cube cosets, `d = 3`) are both instances of one combinatorial fact, abstracted
here away from any rotation/root-of-unity machinery:

> Given a family of **disjoint zero-sum `d`-subsets** of the domain (the "cosets"), choosing any
> `j` of them and taking their union yields a zero-sum `(d·j)`-subset; distinct `j`-subfamilies
> give distinct unions.  Hence there are at least `C(#cosets, j)` zero-sum `(d·j)`-subsets.

* **`coset_union_growth`** — `C(|orbits|, j) ≤ #{ zero-sum (d·j)-subsets }` for any family
  `orbits` of pairwise-disjoint zero-sum `d`-subsets.
* **`cosetSupply_ge`** — via the orchard identity: the deep-band supply of the tower word
  `x^{d·j}` is `≥ C(|orbits|, j)`.

Specializations recover the landed bounds:
* antipodal pairs (`d = 2`, `|orbits| = n/2`) ⟹ `x^{2j}` supply `≥ C(n/2, j) = Θ(n^j)`;
* cube cosets (`d = 3`, `j = 1`, `|orbits| = n/3`) ⟹ `x³` supply `≥ n/3 = Θ(n)`;
and extend to every `(d, j)` and every domain carrying a disjoint sum-zero coset family
(`μ_d`-cosets when `μ_d ⊂ F` and `d ∣ n`).  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- **The coset-union growth law.**  From a family `orbits` of pairwise-disjoint zero-sum
`d`-subsets, the union of any `j` of them is a zero-sum `(d·j)`-subset, and the union map is
injective — so there are at least `C(|orbits|, j)` zero-sum `(d·j)`-subsets. -/
theorem coset_union_growth (dom : Fin n ↪ F) (orbits : Finset (Finset (Fin n)))
    (d j : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ O ∈ orbits, O.card = d)
    (hsum : ∀ O ∈ orbits, ∑ i ∈ O, dom i = 0)
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O') :
    (orbits.card).choose j ≤ (((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  rw [show (orbits.card).choose j = (orbits.powersetCard j).card from
    (Finset.card_powersetCard j orbits).symm]
  refine Finset.card_le_card_of_injOn (fun P => P.biUnion id) ?_ ?_
  · -- the union of a j-subfamily is a zero-sum (d·j)-subset
    intro P hP
    obtain ⟨hPsub, hPcard⟩ := Finset.mem_powersetCard.mp hP
    have hPdisj : ∀ O ∈ P, ∀ O' ∈ P, O ≠ O' → Disjoint (id O) (id O') :=
      fun O hO O' hO' hne => hdisj O (hPsub hO) O' (hPsub hO') hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_biUnion hPdisj]
      have hsz : ∑ O ∈ P, (id O).card = P.card * d :=
        by rw [Finset.sum_congr rfl (fun O hO => by simpa using hcard O (hPsub hO)),
          Finset.sum_const, smul_eq_mul]
      rw [hsz, hPcard]; ring
    · rw [Finset.sum_biUnion hPdisj]
      exact Finset.sum_eq_zero (fun O hO => hsum O (hPsub hO))
  · -- distinct j-subfamilies give distinct unions
    intro P hP Q hQ hPQ
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP hQ
    have hbi : P.biUnion id = Q.biUnion id := hPQ
    -- membership transfer: O ∈ P → O ∈ Q (and symmetrically), using disjointness + nonempty
    have key : ∀ (A B : Finset (Finset (Fin n))), A ⊆ orbits → B ⊆ orbits →
        A.biUnion id = B.biUnion id → A ⊆ B := by
      intro A B hA hB hAB O hO
      have hOne : O.Nonempty := Finset.card_pos.mp (by rw [hcard O (hA hO)]; omega)
      obtain ⟨x, hx⟩ := hOne
      have hxU : x ∈ B.biUnion id := by
        rw [← hAB]; exact Finset.mem_biUnion.mpr ⟨O, hO, hx⟩
      obtain ⟨O', hO', hxO'⟩ := Finset.mem_biUnion.mp hxU
      have : O = O' := by
        by_contra hne
        exact (Finset.disjoint_left.mp (hdisj O (hA hO) O' (hB hO') hne) hx) hxO'
      rwa [this]
    exact Finset.Subset.antisymm (key P Q hP.1 hQ.1 hbi) (key Q P hQ.1 hP.1 hbi.symm)

open Classical in
/-- **Unified coset supply growth.**  The deep-band supply of the tower word `x^{d·j}` is at
least `C(|orbits|, j)` whenever the domain carries `|orbits|` pairwise-disjoint zero-sum
`d`-subsets.  Recovers the antipodal `Θ(n^j)` (`d = 2`) and cube-coset `Θ(n)` (`d = 3, j = 1`)
bounds, for every `(d, j)`. -/
theorem cosetSupply_ge (dom : Fin n ↪ F) (orbits : Finset (Finset (Fin n)))
    (d j : ℕ) (hd : 1 ≤ d) (hdj : 2 ≤ d * j)
    (hcard : ∀ O ∈ orbits, O.card = d)
    (hsum : ∀ O ∈ orbits, ∑ i ∈ O, dom i = 0)
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O') :
    (orbits.card).choose j ≤ ((Finset.univ.filter (fun c =>
        c ∈ (rsCode dom (d * j - 1) : Submodule F (Fin n → F))
          ∧ d * j - 1 + 1 ≤ (agreeSet c (fun i => (dom i) ^ (d * j - 1 + 1))).card))).card := by
  rw [general_orchard_card dom (by omega : 1 ≤ d * j - 1),
    show d * j - 1 + 1 = d * j from by omega]
  exact coset_union_growth dom orbits d j hd hcard hsum hdisj

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.coset_union_growth
#print axioms ProximityGap.PairRank.cosetSupply_ge
