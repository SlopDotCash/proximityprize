/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoGenPackingCapacity

/-!
# Issue #232 — PACKING IS EXACTLY CLASS-CONSTRAINT SATISFACTION: the CSP
# characterization of coset packing, at every modulus (O121's foundation)

O119 proved the intersection trichotomy; O121 used it to exhibit the
chromatic triangle obstruction.  This file closes the identification: for an
ARBITRARY finite family of canonical cosets (any mix of divisors and bases),

* `packing_iff_csp` — **the iff**: the family is pairwise disjoint **iff**
  every cross-type pair of members has bases in DISTINCT residue classes
  modulo the pairwise step-gcd.  (Same-type members with distinct bases are
  disjoint for free; equal members are excluded by the family being a set.)

So `k`-generator packability is — exactly, not just morally — a constraint
satisfaction / graph-coloring problem: vertices are the family members, the
constraint between a type-`d` and a type-`d'` member is "classes differ in
`ℤ/gcd(n/d, n/d')`", and the geometry of `[0, n)` drops out entirely.  Every
landed law is a statement about this CSP: O119 = the 2-type instance is
interval-capacity-solvable; O121 = a triangle of `gcd ∣ 2` constraints is
infeasible; the open exact `k`-type law = feasibility of heterogeneous
"differ-mod-g" CSPs (BFF disjoint-covering-systems theory).

The structure constants were verified exhaustively before formalization
(`probe_two_gen_capacity.py` check (A): same-type disjointness and the
cross-type class criterion over n ∈ {12, 18, 20, 24, 30, 36}, all divisor
pairs, all base pairs; exit 0).
-/

namespace PackingClassCSP

open Finset DeBruijnWindowedLaw TwoGenPackingCapacity

/-- A valid family member at modulus `n`: a divisor paired with a canonical
base. -/
def ValidMember (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∣ n ∧ p.2 < n / p.1

/-- **The CSP characterization of coset packing**: a finite family
`F ⊆ {(d, r) : d ∣ n, r < n/d}` of canonical cosets is pairwise disjoint
(as distinct pairs) iff every CROSS-TYPE pair occupies distinct base-classes
modulo the pairwise step-gcd.  The geometry of `[0, n)` reduces to pure
residue arithmetic on the index set. -/
theorem packing_iff_csp {n : ℕ} (hn : 0 < n) {F : Finset (ℕ × ℕ)}
    (hF : ∀ p ∈ F, ValidMember n p) :
    (∀ p ∈ F, ∀ q ∈ F, p ≠ q →
        Disjoint (cosetOf n p.1 p.2) (cosetOf n q.1 q.2))
      ↔ ∀ p ∈ F, ∀ q ∈ F, p ≠ q → p.1 ≠ q.1 →
          p.2 % Nat.gcd (n / p.1) (n / q.1)
            ≠ q.2 % Nat.gcd (n / p.1) (n / q.1) := by
  constructor
  · -- disjointness forces the class constraints (the CRT direction)
    intro hdisj p hp q hq hne hdne heq
    obtain ⟨hpd, hpr⟩ := hF p hp
    obtain ⟨hqd, hqr⟩ := hF q hq
    exact cosetOf_not_disjoint_cross hn hpd hqd hpr hqr heq
      (hdisj p hp q hq hne)
  · -- the class constraints rebuild disjointness (the trichotomy)
    intro hcsp p hp q hq hne
    obtain ⟨hpd, hpr⟩ := hF p hp
    obtain ⟨hqd, hqr⟩ := hF q hq
    by_cases hd : p.1 = q.1
    · -- same type: distinct pairs with equal divisor have distinct bases
      have hrne : p.2 ≠ q.2 := by
        intro hcon
        exact hne (Prod.ext hd hcon)
      exact hd ▸ cosetOf_disjoint_same hpr (hd ▸ hqr) hrne
    · -- cross type: the class constraint is exactly the disjointness criterion
      exact cosetOf_disjoint_cross hpr hqr (hcsp p hp q hq hne hd)

/-- The union of a CSP-satisfying family realizes the full mass
`Σ_{(d,r) ∈ F} d` — packing feasibility transfers to exact mass realization
(`card_biUnion` over the disjointness the CSP rebuilds). -/
theorem csp_family_card {n : ℕ} (hn : 0 < n) {F : Finset (ℕ × ℕ)}
    (hF : ∀ p ∈ F, ValidMember n p)
    (hcsp : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → p.1 ≠ q.1 →
        p.2 % Nat.gcd (n / p.1) (n / q.1)
          ≠ q.2 % Nat.gcd (n / p.1) (n / q.1)) :
    (F.biUnion (fun p => cosetOf n p.1 p.2)).card = ∑ p ∈ F, p.1 := by
  classical
  have hdisj := (packing_iff_csp hn hF).mpr hcsp
  rw [Finset.card_biUnion (fun p hp q hq hne => hdisj p hp q hq hne)]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpd, hpr⟩ := hF p hp
  exact DeBruijnTwoPrimeAssembly.IsPacket.card_eq
    (Nat.div_pos (Nat.le_of_dvd hn hpd) (Nat.pos_of_dvd_of_pos hpd hn))
    ⟨p.2, hpr, rfl⟩

/-- A CSP-satisfying family of cosets is a window-coset union as soon as every
chosen divisor lies past the window threshold.  This is the direct bridge from
packing feasibility to the `IsWindowCosetUnion` surface used by the window laws. -/
theorem csp_family_isWindowCosetUnion {n t : ℕ} (hn : 0 < n)
    {F : Finset (ℕ × ℕ)} (hF : ∀ p ∈ F, ValidMember n p)
    (hgt : ∀ p ∈ F, t < p.1)
    (hcsp : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → p.1 ≠ q.1 →
        p.2 % Nat.gcd (n / p.1) (n / q.1)
          ≠ q.2 % Nat.gcd (n / p.1) (n / q.1)) :
    IsWindowCosetUnion n t (F.biUnion fun p => cosetOf n p.1 p.2) := by
  classical
  have hdisj := (packing_iff_csp hn hF).mpr hcsp
  refine ⟨F.image (fun p => cosetOf n p.1 p.2), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hpd, hpr⟩ := hF p hp
    exact ⟨p.1, hpd, hgt p hp, ⟨p.2, hpr, rfl⟩⟩
  · intro P hP Q hQ hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hQ)
    have hpq : p ≠ q := by
      intro h
      exact hne (by rw [h])
    exact hdisj p hp q hq hpq
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · rintro ⟨p, hp, hx⟩
      exact ⟨cosetOf n p.1 p.2, ⟨p, hp, rfl⟩, hx⟩
    · rintro ⟨P, ⟨p, hp, rfl⟩, hx⟩
      exact ⟨p, hp, hx⟩

end PackingClassCSP

#print axioms PackingClassCSP.packing_iff_csp
#print axioms PackingClassCSP.csp_family_card
#print axioms PackingClassCSP.csp_family_isWindowCosetUnion
