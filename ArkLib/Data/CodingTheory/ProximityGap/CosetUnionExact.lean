/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetUnionGrowth
import ArkLib.Data.CodingTheory.ProximityGap.CosetUnionSuperAdditive

/-!
# Exact tower supply, conditional on the antipodal/coset-closure law (#389)

`coset_union_growth` gives the *unconditional* lower bound `C(|orbits|, j) ≤ #{zero-sum (d·j)-
subsets}` (the antipodal/coset relation `⟸`).  The fleet's `PROOFS.md` distills the whole
even-moment / supply program to a **single** hypothesis — the **antipodal/coset-closure law (ACL)**:
*every* zero-sum subset decomposes into cosets (the relation `⟹`).  ACL is Lam–Leung in
characteristic `0`; its mod-`p` survival above the Sidon threshold is exactly the open kernel.

This file isolates that dependency cleanly (the project's modularity convention): **under ACL the
lower bound is tight**, so the tower supply is pinned *exactly*.

* **`coset_union_growth_exact`** — if every zero-sum `(d·j)`-subset is a union of `j` cosets
  (ACL at this size), then `#{zero-sum (d·j)-subsets} = C(|orbits|, j)` exactly.
* **`cosetSupply_exact_under_acl`** — hence the deep-band supply of `x^{d·j}` equals
  `C(|orbits|, j)` exactly.

So the entire tower-supply question reduces, formally, to ACL: the unconditional lower bound
plus the one named hypothesis gives the exact answer.  (`Mu8AntipodalProfile` is the
unconditional witness that ACL — and hence this exact count — holds at the FRI domain `μ_8`.)
Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- **Exact coset count under ACL.**  With a disjoint zero-sum `d`-coset family `orbits`, if every
zero-sum `(d·j)`-subset is a `j`-coset union (ACL), the zero-sum `(d·j)`-subset count is *exactly*
`C(|orbits|, j)` — the unconditional lower bound `coset_union_growth` is tight. -/
theorem coset_union_growth_exact (dom : Fin n ↪ F) (orbits : Finset (Finset (Fin n)))
    (d j : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ O ∈ orbits, O.card = d)
    (hsum : ∀ O ∈ orbits, ∑ i ∈ O, dom i = 0)
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O')
    (hacl : ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
        (fun T => ∑ i ∈ T, dom i = 0),
        T ∈ (orbits.powersetCard j).image (fun P => P.biUnion id)) :
    (((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card = (orbits.card).choose j := by
  classical
  obtain ⟨-, hinj⟩ := coset_family_facts dom orbits d j hd hcard hsum hdisj
  have himgcard : ((orbits.powersetCard j).image (fun P => P.biUnion id)).card
      = (orbits.card).choose j := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard]
  refine le_antisymm ?_ ?_
  · calc (((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
          (fun T => ∑ i ∈ T, dom i = 0)).card
        ≤ ((orbits.powersetCard j).image (fun P => P.biUnion id)).card :=
          Finset.card_le_card (fun T hT => hacl T hT)
      _ = (orbits.card).choose j := himgcard
  · exact coset_union_growth dom orbits d j hd hcard hsum hdisj

open Classical in
/-- **Exact tower supply under ACL.**  If every zero-sum `(d·j)`-subset is a `j`-coset union, the
deep-band supply of `x^{d·j}` is *exactly* `C(|orbits|, j)`. -/
theorem cosetSupply_exact_under_acl (dom : Fin n ↪ F) (orbits : Finset (Finset (Fin n)))
    (d j : ℕ) (hd : 1 ≤ d) (hdj : 2 ≤ d * j)
    (hcard : ∀ O ∈ orbits, O.card = d)
    (hsum : ∀ O ∈ orbits, ∑ i ∈ O, dom i = 0)
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O')
    (hacl : ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
        (fun T => ∑ i ∈ T, dom i = 0),
        T ∈ (orbits.powersetCard j).image (fun P => P.biUnion id)) :
    ((Finset.univ.filter (fun c =>
        c ∈ (rsCode dom (d * j - 1) : Submodule F (Fin n → F))
          ∧ d * j - 1 + 1 ≤ (agreeSet c (fun i => (dom i) ^ (d * j - 1 + 1))).card))).card
      = (orbits.card).choose j := by
  rw [general_orchard_card dom (by omega : 1 ≤ d * j - 1),
    show d * j - 1 + 1 = d * j from by omega]
  exact coset_union_growth_exact dom orbits d j hd hcard hsum hdisj hacl

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.coset_union_growth_exact
#print axioms ProximityGap.PairRank.cosetSupply_exact_under_acl
