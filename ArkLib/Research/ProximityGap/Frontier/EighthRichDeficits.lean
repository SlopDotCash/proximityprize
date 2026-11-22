/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthQuotientCoreCap

/-! # Rich-head accounting for the eighth-rate interpolation window -/

namespace ArkLib.ProximityGap.Frontier.EighthRichDeficits

abbrev n : ℕ := 1073741824
abbrev e : ℕ := 671088639
abbrev t : ℕ := 402653185
abbrev deg : ℕ := 134217727
abbrev coreFloor : ℕ := 402644994

/-- Fresh positions required by one bad scalar represented by a head of core size c. -/
def deficit (required c : ℕ) : ℕ := max 1 (required-c)

/-- Number of distinct labels possible at a given positive deficit. -/
def price (errors D : ℕ) : ℕ := 1+errors/D

private theorem positive (required c : ℕ) : 0<deficit required c := by
  unfold deficit
  omega

private theorem mono {a b : ℕ} (errors : ℕ) (ha : 0<a) (hab : a≤b) :
    price errors b≤price errors a :=
  Nat.add_le_add_left (Nat.div_le_div_left hab ha) 1

/-- The supports for scalar labels assigned to a single head are disjoint outside
its joint core. Convert their total incidence bound into the reciprocal price. -/
theorem head_share {length errors required c L : ℕ} (len : required+errors=length)
    (fresh : L*deficit required c+c≤length) : L≤price errors (deficit required c) := by
  cases L with
  | zero => omega
  | succ L =>
    rw [Nat.succ_mul] at fresh
    have bound : required≤c+deficit required c := by unfold deficit; omega
    have h : L*deficit required c≤errors := by omega
    have hh := (Nat.le_div_iff_mul_le (positive required c)).mpr h
    unfold price
    omega

/-- The cutoff is strict. A label population greater than 81,920 forces the
joint core used in the determinant and union estimates. -/
theorem rich_core {c L : ℕ} (many : 81920<L) (fresh : L*deficit t c + c≤n) :
    coreFloor≤c := by
  have lo := Nat.mul_le_mul_right (deficit t c) many
  simp only [deficit, t, n, deg, coreFloor] at *
  omega

/-- Four noncollinear heads obey the determinant bound on their total core size. -/
theorem four_sum {A B C D : ℕ} (cores : A+B+C+D≤n+4*deg) :
    8≤deficit t A+deficit t B+deficit t C+deficit t D := by
  simp only [deficit, t, n, deg] at *
  omega

/-- The only four deficits that can exceed this allowance, sorted in increasing order. -/
theorem four_except {a b c d : ℕ} (ha : 0<a) (hab : a≤b) (hbc : b≤c) (hcd : c≤d)
    (total : 8≤a+b+c+d) (other : ¬(a=1 ∧ b=1 ∧ c=1 ∧ d=5)) :
    price e a+price e b+price e c+price e d≤2125114027 := by
  have a1 := mono e (by decide : 0<1) ha
  have b1 := mono e (by decide : 0<1) (show 1≤b by omega)
  by_cases hc : 2≤c
  · have c2 := mono e (by decide : 0<2) hc
    have d2 := mono e (by decide : 0<2) (hc.trans hcd)
    norm_num [price] at a1 b1 c2 d2 ⊢
    omega
  · have c1 := mono e (by decide : 0<1) (show 1≤c by omega)
    have d6 := mono e (by decide : 0<6) (show 6≤d by omega)
    norm_num [price] at a1 b1 c1 d6 ⊢
    omega

/-- Equality in the exceptional tuple forces exact cardinalities of all four
joint cores. The fourth has five missing sites at the present error count. -/
theorem exceptional_cores {A B C D : ℕ} (cores : A+B+C+D≤n+4*deg)
    (ha : deficit t A=1) (hb : deficit t B=1) (hc : deficit t C=1) (hd : deficit t D=5) :
    A=402653184 ∧ B=402653184 ∧ C=402653184 ∧ D=402653180 := by
  simp only [deficit, t, n, deg, coreFloor] at *
  omega

/-- At one fewer error the first three exceptional heads each need two fresh
sites and the fourth needs six. Their combined price is below the base allowance. -/
theorem prior_exceptional {A B C D : ℕ}
    (a : A*deficit (t+1) 402653184 + 402653184≤n)
    (b : B*deficit (t+1) 402653184 + 402653184≤n)
    (c : C*deficit (t+1) 402653184 + 402653184≤n)
    (d : D*deficit (t+1) 402653180 + 402653180≤n) : A+B+C+D≤1118481067 := by
  have ha := head_share (errors:=e-1) (by decide : t+1+(e-1)=n) a
  have hb := head_share (errors:=e-1) (by decide : t+1+(e-1)=n) b
  have hc := head_share (errors:=e-1) (by decide : t+1+(e-1)=n) c
  have hd := head_share (errors:=e-1) (by decide : t+1+(e-1)=n) d
  norm_num [price, deficit] at ha hb hc hd
  omega

/-- Three collinear heads plus a transverse head lose two primitive-direction
degrees per unit of direction degree. -/
theorem line_triple_sum {A B C Z r : ℕ} (hr : 1≤r) (cores : A+B+C+Z+2*r≤n+4*deg) :
    10≤deficit t A+deficit t B+deficit t C+deficit t Z := by
  simp only [deficit, t, n, deg] at *
  omega

/-- Bonferroni for four rich line cores gives the full-cluster label allowance.
The constant-direction case has only one label shared over all covered sites. -/
theorem line_union {U H : ℕ} (cover : 4*coreFloor≤U+6*deg) :
    805273614≤U ∧ (H+3*U≤4*n → H≤1879146454) ∧ (H≤1+4*(n-U) → H≤1073872841) := by
  simp only [n, deg, coreFloor] at *
  omega

/-- One core of a third line member loses at most two pair-intersection sets. -/
theorem private_count {privateSites : ℕ} (cover : coreFloor≤privateSites+2*deg) :
    134209540≤privateSites := by
  simp only [deg, coreFloor] at cover
  omega

/-- The two deficit-one heads each have at most e+1 available fresh coordinates.
At a private site of the third collinear head, two distinct assigned labels
cannot use both slots. -/
theorem line_pair {I : Type*} [DecidableEq I]
    (availA availB chosenA chosenB priv : Finset I)
    (ha : chosenA⊆availA) (hb : chosenB⊆availB) (hpa : priv⊆availA) (hpb : priv⊆availB)
    (separate : ∀ x ∈ priv, x∉chosenA ∨ x∉chosenB)
    (sites : coreFloor≤priv.card+2*deg)
    (largeA : availA.card≤e+1) (largeB : availB.card≤e+1) :
    chosenA.card+chosenB.card+134209540≤2*(e+1) := by
  have missed := EighthQuotientCoreCap.missed_pair availA availB chosenA chosenB priv
    ha hb hpa hpb separate
  have count := private_count sites
  omega

/-- A constant-direction cluster and one transverse head jointly fit this cap. -/
theorem five_constant {line extra : ℕ} (hl : line≤1073872841) (he : extra≤e+1) :
    line+extra≤1744961481 := by
  simp only [e] at he
  omega

/-- When a transverse head needs at least three fresh sites, the union of the
four collinear cores already bounds the combined assigned labels. -/
theorem five_high {line Z z : ℕ} (hl : line≤1879146454) (hz : 3≤z) (he : Z≤price e z) :
    line+Z≤2102842668 := by
  have h := he.trans (mono e (by decide : 0<3) hz)
  norm_num [price] at h
  omega

/-- Four collinear heads of positive primitive-direction degree and one transverse
head. The four line deficits are sorted. A and B count disjointly assigned labels,
so their selected fresh sites lose one slot per private site of a third head. -/
theorem five_positive {a b c d z A B C D Z : ℕ}
    (ha : 0<a) (hab : a≤b) (hbc : b≤c) (hcd : c≤d) (hz : 0<z)
    (total : 10≤z+a+b+c) (pa : A≤price e a) (pb : B≤price e b)
    (pc : C≤price e c) (pd : D≤price e d) (pz : Z≤price e z)
    (line : A+B+C+D≤1879146454)
    (unused : a=1 → b=1 → A+B+134209540≤2*(e+1)) :
    A+B+C+D+Z≤2125114028 := by
  by_cases high : 3≤z
  · have h := five_high line high pz
    omega
  have z1 := pz.trans (mono e (by decide : 0<1) hz)
  by_cases hb : 2≤b
  · have hc : 3≤c := by omega
    have a1 := pa.trans (mono e (by decide : 0<1) ha)
    have b2 := pb.trans (mono e (by decide : 0<2) hb)
    have c3 := pc.trans (mono e (by decide : 0<3) hc)
    have d3 := pd.trans (mono e (by decide : 0<3) (hc.trans hcd))
    norm_num [price] at a1 b2 c3 d3 z1
    omega
  · have hc : 6≤c := by omega
    have loss := unused (by omega) (by omega)
    norm_num [e] at loss
    have c6 := pc.trans (mono e (by decide : 0<6) hc)
    have d6 := pd.trans (mono e (by decide : 0<6) (hc.trans hcd))
    norm_num [price] at c6 d6 z1
    omega

/-- At exactly five eighths, with the existing four-head residual allowance, the
only sorted deficit profiles that can overrun have the form `(1,1,1,q)`, `q≤5`. -/
theorem next_four_profile {a b c d : ℕ} (ha : 0<a) (hab : a≤b) (hbc : b≤c) (hcd : c≤d)
    (tooMany : 2*n < price (e+1) a+price (e+1) b+price (e+1) c+price (e+1) d+20607410) :
    a=1 ∧ b=1 ∧ c=1 ∧ d≤5 := by
  have a1 := mono (e+1) (by decide : 0<1) ha
  have b1 := mono (e+1) (by decide : 0<1) (show 1≤b by omega)
  have c1 := mono (e+1) (by decide : 0<1) (show 1≤c by omega)
  by_cases hc : 2≤c
  · have c2 := mono (e+1) (by decide : 0<2) hc
    have d2 := mono (e+1) (by decide : 0<2) (hc.trans hcd)
    norm_num [n,e,price] at tooMany a1 b1 c2 d2
    omega
  · by_contra! h
    have d6 := mono (e+1) (by decide : 0<6) (show 6≤d by omega)
    norm_num [n,e,price] at tooMany a1 b1 c1 d6
    omega

/-- The excess incidence is within `q-1` of saturation. The same
calculation bounds twice the primitive direction degree in the collinear-triple case. -/
theorem next_four_incidence {A B C D q r : ℕ} (hA : deficit (t-1) A=1)
    (hB : deficit (t-1) B=1) (hC : deficit (t-1) C=1) (hD : deficit (t-1) D=q)
    (bound : A+B+C+D+2*r≤n+4*deg) :
    n+4*deg≤A+B+C+D+(q-1) ∧ 2*r≤q-1 := by
  simp only [deficit,t,n,deg] at *
  omega

/-- If the primitive direction is constant, the line union supplies at most
one scalar across all three line heads. Each head has at least `coreFloor-1` sites. -/
theorem next_three_constant {U line extra : ℕ} (cover : 3*(coreFloor-1)≤U+3*deg)
    (hl : line≤1+3*(n-U)) (he : extra≤e+2) : line+extra≤1476468720 := by
  simp only [n,deg,coreFloor,e] at *
  omega

/-- For a positive-degree line triple, the incidence lemma forces `q≥3`.
Two deficit-one heads lose a common slot on each private site of the third. -/
theorem next_three_positive {a b c d q lost : ℕ} (high : 3≤q)
    (priv : coreFloor-1≤lost+2*deg) (ab : a+b+lost≤2*(e+2))
    (hc : c≤e+2) (hd : d≤price (e+1) q) : a+b+c+d≤2102752598 := by
  have small := hd.trans (mono (e+1) (by decide : 0<3) high)
  norm_num [e,price,coreFloor,deg] at priv ab hc small
  omega

/-- For every multiplicity and scalar-degree cap, the value-degree-three
mixed-Hasse monomial count falls strictly below the cost of the first two
jet orders alone at five eighths. The omitted higher orders only add conditions. -/
theorem next_cubic_no_surplus (r l : ℕ) (hr : 0<r) :
    (l+1)*(r*(t-1)) + l*(r*(t-1)-deg) +
      (l-1)*(r*(t-1)-2*deg) + (l-2)*(r*(t-1)-3*deg)
      < n*((l+1)*r + l*(r-1)) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  have h1 : (r+1)*(t-1)-deg = r*(t-1)+268435457 := by
    norm_num [t,deg,Nat.add_mul]
  have h2 : (r+1)*(t-1)-2*deg = r*(t-1)+134217730 := by
    norm_num [t,deg,Nat.add_mul]
  have h3 : (r+1)*(t-1)-3*deg = r*(t-1)+3 := by
    norm_num [t,deg,Nat.add_mul]
  simp only [Nat.succ_eq_add_one, h1, h2, h3, Nat.add_sub_cancel]
  rcases l with _ | l
  · norm_num [n,t] <;> omega
  rcases l with _ | l
  · norm_num [n,t] <;> omega
  · simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have hl : l+1+1-2=l := by omega
    rw [hl]
    norm_num [n,t]
    nlinarith [Nat.zero_le (l*r)]

#print axioms next_cubic_no_surplus
#print axioms next_four_profile
#print axioms next_four_incidence
#print axioms next_three_constant
#print axioms next_three_positive
#print axioms four_except
#print axioms exceptional_cores
#print axioms prior_exceptional
#print axioms five_positive
end ArkLib.ProximityGap.Frontier.EighthRichDeficits
