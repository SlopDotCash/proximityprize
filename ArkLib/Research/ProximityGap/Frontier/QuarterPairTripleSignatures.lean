/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SingleCosetTripleSignatures

/-!
# Equal triple sums with a pair in one coset of the fourth roots

The remaining entry of each triple is unrestricted in the ambient subgroup.
After deletion of opposite pairs, the two lists of normalized triples are
(1,1,x) and (1,i,x), with i a square root of minus one. The first list omits
minus one; the second omits all four fourth roots.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.QuarterPairTripleSignatures

open SingleCosetTripleSignatures
open SixthMomentAntipodalShape (pair Pairable)

variable {F : Type*} [Field F] {n : ℕ}

def triple (a b c : F) : Multiset F := {a} + {b} + {c}

/-- The two families compared by the finite-field verifier. -/
def reps (n : ℕ) (i : F) : Set (Multiset F) :=
  {T | (∃ x : F, x^n=1 ∧ x ≠ -1 ∧ T = triple 1 1 x) ∨
    (∃ x : F, x^n=1 ∧ x ≠ 1 ∧ x ≠ -1 ∧ x ≠ i ∧ x ≠ -i ∧ T = triple 1 i x)}

/-- The rows visited by the two integer exponent loops, including their exact exclusions. -/
def scannedRows (n : ℕ) (g : F) : Set (Multiset F) :=
  {T | (∃ j < n, j ≠ n/2 ∧ T = triple 1 1 (g^j)) ∨
    (∃ j < n, j ≠ 0 ∧ j ≠ n/4 ∧ j ≠ n/2 ∧ j ≠ 3*n/4 ∧
      T = triple 1 (g^(n/4)) (g^j))}

/-- The numerical loop predicates suffice for the field-level signature hypotheses. -/
theorem checks_of_scanned_rows {g : F} (hn : 0 < n) (hg : IsPrimitiveRoot g n)
    (hh : g^(n/2) = -1) (ht : g^(3*n/4) = -g^(n/4))
    (hc : TagChecks n (scannedRows n g)) : TagChecks n (reps n (g^(n/4))) := by
  let : NeZero n := ⟨hn.ne'⟩
  have incl : reps n (g^(n/4)) ⊆ scannedRows n g := by
    rintro T (⟨x,hx,hx',rfl⟩ | ⟨x,hx,h1,h2,h3,h4,rfl⟩)
    · obtain ⟨j,hj,rfl⟩ := hg.eq_pow_of_pow_eq_one hx
      exact Or.inl ⟨j,hj,fun e => hx' (e ▸ hh),rfl⟩
    · obtain ⟨j,hj,rfl⟩ := hg.eq_pow_of_pow_eq_one hx
      exact Or.inr ⟨j,hj,fun e => h1 (e ▸ pow_zero g),fun e => h3 (congrArg (g^·) e),
        fun e => h2 (e ▸ hh),fun e => h4 (e ▸ ht),rfl⟩
  exact ⟨fun T h => hc.nonzero T (incl h), fun T h => hc.ne_one T (incl h),
    hc.injective.mono incl⟩

/-- The chosen pair can be repeated or lie anywhere inside one fourth-root coset. -/
def hasQuarterPair (n : ℕ) (T : Multiset F) : Prop :=
  ∃ a u z : F, a^n = 1 ∧ u^4 = 1 ∧ z^n = 1 ∧ T = triple a (a*u) z

private theorem root_nz (hn : 0 < n) {a : F} (ha : a^n=1) : a ≠ 0 := by
  rintro rfl
  simp [zero_pow hn.ne'] at ha

private theorem scaled (hn : 0 < n) {a : F} (ha : a^n=1) (u z : F) :
    triple a (a*u) z = scale a (triple 1 u (z/a)) := by
  have h : a * (z/a) = z := by field_simp [root_nz hn ha]
  simp [triple, scale, h]

private theorem double_covered (hn : 0 < n) (i : F) {a z : F} (ha : a^n=1) (hz : z^n=1) :
    Covered n (reps n i) (triple a a z) := by
  have ha0 := root_nz hn ha
  by_cases h : z/a = -1
  · have he : z = -a := by simpa using (div_eq_iff ha0).mp h
    subst z
    exact Or.inl ⟨a,a,ha,by dsimp only [triple,pair]; ac_rfl⟩
  · refine Or.inr ⟨triple 1 1 (z/a), Or.inl ⟨z/a,by rw [div_pow,hz,ha,div_one],h,rfl⟩,a,ha,?_⟩
    simpa using scaled hn ha 1 z

private theorem quarter_covered (hn : 0 < n) {i a z : F} (hi : i^n=1) (ha : a^n=1) (hz : z^n=1) :
    Covered n (reps n i) (triple a (a*i) z) := by
  have ha0 := root_nz hn ha
  have hai : (a*i)^n=1 := by rw [mul_pow,ha,hi,one_mul]
  by_cases h1 : z/a = 1
  · have he := (div_eq_one_iff_eq ha0).mp h1
    subst z
    have heq : triple a (a*i) a = triple a a (a*i) := by dsimp only [triple]; ac_rfl
    rw [heq]
    exact double_covered hn i ha hai
  by_cases h2 : z/a = -1
  · have he : z = -a := by simpa using (div_eq_iff ha0).mp h2
    subst z
    exact Or.inl ⟨a,a*i,hai,by dsimp only [triple,pair]; ac_rfl⟩
  by_cases h3 : z/a = i
  · have he : z = a*i := by simpa [mul_comm] using (div_eq_iff ha0).mp h3
    subst z
    have heq : triple a (a*i) (a*i) = triple (a*i) (a*i) a := by dsimp only [triple]; ac_rfl
    rw [heq]
    exact double_covered hn i hai ha
  by_cases h4 : z/a = -i
  · have he : z = -(a*i) := by simpa [mul_comm] using (div_eq_iff ha0).mp h4
    subst z
    exact Or.inl ⟨a*i,a,ha,by dsimp only [triple,pair]; ac_rfl⟩
  refine Or.inr ⟨triple 1 i (z/a), Or.inr ⟨z/a,by rw [div_pow,hz,ha,div_one],h1,h2,h3,h4,rfl⟩,
    a,ha,scaled hn ha i z⟩

/-- The declared lists cover every triple with a same-coset pair. -/
theorem covered_of_quarter_pair {i : F} (hn : 0 < n) (hi : i^2 = -1) (hin : i^n=1)
    (heven : Even n) {T : Multiset F} (hT : hasQuarterPair n T) : Covered n (reps n i) T := by
  obtain ⟨a,u,z,ha,hu,hz,rfl⟩ := hT
  have hfac : (u-1)*(u+1)*(u-i)*(u+i) = 0 := by
    calc
      _ = (u^2-1)*(u^2-i^2) := by ring
      _ = 0 := by rw [hi]; linear_combination hu
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have he := sub_eq_zero.mp h
        subst u
        simpa using double_covered hn i ha hz
      · have he : u = -1 := eq_neg_of_add_eq_zero_left h
        subst u
        exact Or.inl ⟨a,z,hz,by simp [triple,pair]⟩
    · obtain rfl := sub_eq_zero.mp h
      exact quarter_covered hn hin ha hz
  · have he : u = -i := eq_neg_of_add_eq_zero_left h
    subst u
    have hprod : (a*(-i))*i=a := by linear_combination -a*hi
    have hai : (a*(-i))^n=1 := by rw [mul_pow,heven.neg_pow,hin,ha,one_mul]
    have swap : triple a (a*(-i)) z = triple (a*(-i)) ((a*(-i))*i) z := by
      rw [hprod]; dsimp only [triple]; ac_rfl
    rw [swap]
    exact quarter_covered hn hin hai hz

/-- Two disjoint pairs in fourth-root cosets force a pairable six-term relation
whenever the checked triple signatures are distinct and avoid zero and one. -/
theorem collision {i : F} (hn : 0 < n) (hi : i^2 = -1) (hin : i^n=1) (heven : Even n)
    (checks : TagChecks n (reps n i)) {S T : Multiset F}
    (hS : hasQuarterPair n S) (hT : hasQuarterPair n T) (hsum : S.sum = T.sum) :
    Pairable (S + T.map (- ·)) := by
  have hc : S.card=3 := by obtain ⟨a,u,z,_,_,_,rfl⟩ := hS; simp [triple]
  exact pairable_of_equal_sum hn checks hc
    (covered_of_quarter_pair hn hi hin heven hS) (covered_of_quarter_pair hn hi hin heven hT) hsum

/-- Direct zero-sum version. The remaining entries z,w can be arbitrary ambient roots. -/
theorem two_disjoint_pairs {i a b u v z w : F} (hn : 0 < n) (hi : i^2 = -1)
    (hin : i^n=1) (heven : Even n) (checks : TagChecks n (reps n i))
    (ha : a^n=1) (hb : b^n=1) (hu : u^4=1) (hv : v^4=1) (hz : z^n=1) (hw : w^n=1)
    (hs : a+a*u+z+(b+b*v+w)=0) :
    Pairable (triple a (a*u) z + triple b (b*v) w) := by
  have hnb : (-b)^n=1 := (heven.neg_pow b).trans hb
  have hnw : (-w)^n=1 := (heven.neg_pow w).trans hw
  have hS : hasQuarterPair n (triple a (a*u) z) := ⟨a,u,z,ha,hu,hz,rfl⟩
  have hT : hasQuarterPair n (triple (-b) ((-b)*v) (-w)) := ⟨-b,v,-w,hnb,hv,hnw,rfl⟩
  have hsum : (triple a (a*u) z).sum = (triple (-b) ((-b)*v) (-w)).sum := by
    simp only [triple, Multiset.sum_add, Multiset.sum_singleton, neg_mul]
    linear_combination hs
  simpa only [triple, Multiset.map_add, Multiset.map_singleton, neg_neg, neg_mul] using
    collision hn hi hin heven checks hS hT hsum

#print axioms two_disjoint_pairs
#print axioms covered_of_quarter_pair
#print axioms collision
#print axioms checks_of_scanned_rows

end ArkLib.ProximityGap.Frontier.QuarterPairTripleSignatures
