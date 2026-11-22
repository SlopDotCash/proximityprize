/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Four polynomial cores on the sixty-fourth-root quotient -/

namespace ArkLib.ProximityGap.Frontier.EighthQuotientCoreCap

/-- At least one adjacent pair of cyclic gaps of seven occupied sites on μ64 spans
at most eighteen exponent steps. Reflection exchanges the two gaps. -/
theorem short_span (a b c d e f g : ℕ) (total : a+b+c+d+e+f+g=64) :
    a+b≤18 ∨ b+c≤18 ∨ c+d≤18 ∨ d+e≤18 ∨ e+f≤18 ∨ f+g≤18 ∨ g+a≤18 := by omega

/-- The weighted pair-root benefit can exceed six only for three disjoint
seven-site fibers of a degree-seven pencil. -/
theorem root_benefit {d a b c : ℕ} (hd : d≤7) (ha : a≤d) (hb : b≤d) (hc : c≤d)
    (hseven : ¬(d=7 ∧ a=7 ∧ b=7 ∧ c=7)) : a+b+c≤2*d+6 := by omega

/-- The multiplicity at one received coordinate is bounded by one base agreement,
two common-root credits or one pair-only credit, and one transverse overlap. -/
theorem local_cover {V : Type*} [DecidableEq V] (a b c t r : V) :
    (if a=r then 1 else 0) + (if b=r then 1 else 0) +
      (if c=r then 1 else 0) + (if t=r then 1 else 0) ≤
    1 + (if a=b ∧ a=c then 2 else 0) + (if a=b ∧ a≠c then 1 else 0) +
      (if a=c ∧ a≠b then 1 else 0) + (if b=c ∧ a≠b then 1 else 0) +
      (if t=r ∧ (a=r ∨ b=r ∨ c=r) then 1 else 0 : ℕ) := by
  by_cases hab : a=b <;> by_cases hac : a=c <;> by_cases hbc : b=c <;>
    by_cases har : a=r <;> by_cases hbr : b=r <;> by_cases hcr : c=r <;>
    by_cases htr : t=r <;> simp_all

/-- After the common quotient zeros have been removed, the scalar quotient degree
is d, the common locator has G roots, and the primitive direction has degree ell.
The fourth head meets the triple's line in at most k-1+ell coordinates. -/
theorem balanced_core_cap {d a b c G ell c₀ c₁ c₂ c₃ : ℕ}
    (hd : d≤7) (ha : a≤d) (hb : b≤d) (hc : c≤d)
    (hseven : ¬(d=7 ∧ a=7 ∧ b=7 ∧ c=7))
    (degree : G+ell+16777216*d+1≤134217728)
    (coverage : c₀+c₁+c₂+c₃ ≤ 1073741824 + 2*G + 16777216*(a+b+c) + 134217727+ell) :
    min (min c₀ c₁) (min c₂ c₃) ≤ 394264575 := by
  have h := root_benefit hd ha hb hc hseven
  omega

/-- If a fourth one-fresh core is unavailable through this count, the other
three heads cannot exhaust the second-prime bad-label budget. -/
theorem three_labels {e : ℕ} (he : e≤679477247) : 3*(e+1)≤2147483648 := by omega

/-- At a private coordinate of the remaining collinear head, two selected foreign
heads cannot both use that coordinate for distinct labels. Count the unused slots. -/
theorem missed_pair {I : Type*} [DecidableEq I] (A B L R privateSites : Finset I)
    (hl : L⊆A) (hr : R⊆B) (hA : privateSites⊆A) (hB : privateSites⊆B)
    (unique : ∀ x ∈ privateSites, x∉L ∨ x∉R) :
    L.card+R.card+privateSites.card ≤ A.card+B.card := by
  have sub : privateSites⊆(A \ L) ∪ (B \ R) := by
    intro x hx
    rcases unique x hx with h|h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hA hx,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hB hx,h⟩)
  have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hl, Finset.card_sdiff_of_subset hr] at h
  have h₁ := Finset.card_le_card hl
  have h₂ := Finset.card_le_card hr
  omega

/-- A head representing its necessary share of labels at the predecessor has a
core missing at most six of the required agreements. -/
theorem core_floor {c L : ℕ} (many : 109051905≤L)
    (fresh : L*(394264577-c)≤1073741824-c) : 394264571≤c := by
  have h := (Nat.mul_le_mul_right (394264577-c) many).trans fresh
  omega

/-- Four or more fresh agreements per label bound the deficient head's share. -/
theorem deficient_share {c L : ℕ} (small : c≤394264573)
    (fresh : L*(394264577-c)≤1073741824-c) : L≤169869312 := by
  by_contra! large
  have hh : 169869313≤L := by omega
  have h := (Nat.mul_le_mul_right (394264577-c) hh).trans fresh
  omega

/-- Three rich cores leave a deficit of four on the fourth. The remaining triple
head has enough private sites to rule out even arbitrarily many fresh witnesses. -/
theorem predecessor {c₀ c₁ c₂ c₃ cPrivate Lrich L₃ : ℕ}
    (rich₀ : 394264576≤c₀) (rich₁ : 394264576≤c₁) (rich₂ : 394264576≤c₂)
    (sumcap : c₀+c₁+c₂+c₃≤1577058301)
    (large : 394264571≤cPrivate)
    (duplicate : Lrich+(cPrivate-2*134217727)≤3*679477248)
    (fresh : L₃*(394264577-c₃)≤1073741824-c₃) : Lrich+L₃≤2082471939 := by
  have h := deficient_share (show c₃≤394264573 by omega) fresh
  omega

/-- If all four heads lie on one line, the three large jointly covered cores give
only one foreign direction per covered coordinate. -/
theorem collinear_predecessor {covered labels : ℕ}
    (union : 3*394264571 ≤ covered+3*134217727)
    (incidences : labels+3*covered≤4*1073741824) : labels≤1954545700 := by omega

/-- Without a quotient assumption, a strict improvement requires a larger
root-count benefit on the full evaluation domain. -/
theorem full_domain_benefit {I roots d ell : ℕ}
    (balanced : 4*394264577-5≤I)
    (degree : I+2*d+ell≤1073741824+3*134217728-3+roots) :
    2*d+100663298+ell≤roots := by omega

/-- Six test sites are covered by allowing adjacent gap sums through twenty-one. -/
theorem short_span_six (a b c d e f : ℕ) (total : a+b+c+d+e+f=64) :
    a+b≤21 ∨ b+c≤21 ∨ c+d≤21 ∨ d+e≤21 ∨ e+f≤21 ∨ f+a≤21 := by omega

/-- Three degree-seven members with pair root benefit six would require
at least two full seven-site fibers and a third with at least six sites. -/
theorem almost_septic {a b c : ℕ} (ha : a≤7) (hb : b≤7) (hc : c≤7)
    (total : 20≤a+b+c) : (a=7 ∧ b=7 ∧ 6≤c) ∨ (a=7 ∧ c=7 ∧ 6≤b) ∨ (b=7 ∧ c=7 ∧ 6≤a) := by omega

/-- At a successful endpoint the integer degree and core slack force the common
locator to use its entire degree allowance, and force the primitive direction
degree to be one or two. -/
theorem equality_degree {G ell d a b c : ℕ} (nonconstant : 1≤ell) (degree : d≤7)
    (ha : a≤d) (hb : b≤d) (hc : c≤d)
    (septic : d=7 → a+b+c≤19)
    (locator : G+ell+16777216*d+1≤134217728)
    (cover : 1577058299≤1073741824+2*G+16777216*(a+b+c)+134217727+ell) :
    d=6 ∧ a=6 ∧ b=6 ∧ c=6 ∧ ell≤2 ∧ G+ell=33554431 := by omega

#print axioms local_cover
#print axioms balanced_core_cap
#print axioms missed_pair
#print axioms predecessor
#print axioms equality_degree
end ArkLib.ProximityGap.Frontier.EighthQuotientCoreCap
