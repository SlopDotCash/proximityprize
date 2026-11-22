/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListThreshold
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound

/-! # From multiplicative subgroup intersection estimates to list thresholds -/

namespace ProximityGap.ReflectionListSampling

open Finset Code

/-- A cardinality estimate for non-dihedral fractional-linear graphs between
families of roots. This is the interface of the production Stepanov bound. -/
def GraphCap (F : Type) [Field F] (n C : ℕ) : Prop :=
  ∀ {J : Type} [Fintype J] (x y : J → F), Function.Injective x →
    (∀ i,(x i)^n=1) → (∀ i,(y i)^n=1) → ∀ {a b c d : F}, a*d-b*c≠0 →
    (b≠0 ∨ c≠0) → (a≠0 ∨ d≠0) → (∀ i,a*x i+b=y i*(c*x i+d)) → Fintype.card J≤C

private theorem root_orbit {I F : Type} [Field F]
    {n C T : ℕ} (cap : GraphCap F n C) (enough : C<2*(T+1))
    (D : I ↪ F) (roots : ∀ i,(D i)^n=1)
    (points : Fin (T+1) × Fin 2 ↪ I) (a b c : F) (det : a^2+b*c≠0)
    (law : ∀ i,c*D (points (i,0))*D (points (i,1))-a*(D (points (i,0))+D (points (i,1)))=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  classical
  by_contra! non
  obtain ⟨ha,non⟩ := non
  let src (i : Fin (T+1) × Fin 2) := D (points i)
  let dst (i : Fin (T+1) × Fin 2) := D (points (i.1,if i.2=0 then 1 else 0))
  have inj : Function.Injective src := D.injective.comp points.injective
  have rs (i) : (src i)^n=1 := roots _
  have rt (i) : (dst i)^n=1 := roots _
  have line (i) : (c*src i-a)*dst i=a*src i+b := by
    obtain ⟨j,k⟩ := i
    fin_cases k <;> simp [src,dst] <;> linear_combination law j
  have lim : Fintype.card (Fin (T+1) × Fin 2) ≤ C := by
    refine cap src dst inj rs rt (a:=a) (b:=b) (c:=c) (d := -a) ?_ ?_ (Or.inl ha) ?_
    · intro he
      exact det (by linear_combination -he)
    · by_cases h : c=0
      · exact Or.inl (non h)
      · exact Or.inr h
    · intro i
      simpa only [sub_eq_add_neg,mul_comm (dst i)] using (line i).symm
  simp only [Fintype.card_prod,Fintype.card_fin] at lim
  omega

/-- Scaling an arbitrary smooth coset to the root subgroup and applying the
intersection estimate gives at most floor(C/2) non-dihedral transpositions. -/
theorem pairCap_of_intersections {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F]
    [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] {n C T : ℕ} (hn : Fintype.card I=n)
    (cap : GraphCap F n C) (enough : C<2*(T+1)) (hT : 1≤T) : PairCap D T := by
  classical
  obtain ⟨e,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I e
  have ch : Fintype.card H=n := (Fintype.card_congr e).symm.trans hn
  let G : I ↪ F := ⟨fun i => ((e i : Fˣ) : F),fun _ _ h => e.injective (Subtype.ext (Units.ext h))⟩
  let s := ReedSolomon.Smooth.a D
  have gn (i) : G i≠0 := (e i).val.ne_zero
  have roots (i) : (G i)^n=1 := by
    have h : (e i)^n=1 := ch ▸ pow_card_eq_one
    exact congrArg (fun g : H => ((g:Fˣ):F)) h
  apply pairCap_of_involutions D hT (fun i => he i ▸ mul_ne_zero s.ne_zero (gn i))
  intro q a b c det law
  have ds (i) : D i=(s:F)*G i := he i
  have law' (i) : (c*(s:F)^2)*G (q (i,0))*G (q (i,1)) -
      (a*(s:F))*(G (q (i,0))+G (q (i,1)))=b := by
    have h := law i
    simp only [ds] at h
    linear_combination h
  have det' : (a*(s:F))^2+b*(c*(s:F)^2)≠0 := by
    rw [show (a*(s:F))^2+b*(c*(s:F)^2)=(a^2+b*c)*(s:F)^2 by ring]
    exact mul_ne_zero det (pow_ne_zero _ s.ne_zero)
  rcases root_orbit cap enough G roots q _ b _ det' law' with hh|⟨hh,hb⟩
  · exact .inl ((mul_eq_zero.mp hh).resolve_right s.ne_zero)
  · exact .inr ⟨(mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ s.ne_zero),hb⟩

/-- Every smooth prime-field coset of length at least `u³` has the displayed
two-thirds bound on its nonreflection pair fibers when the exponents fit below
the characteristic. Choosing the largest admissible `u` gives `T ~ 3n/(2u)`. -/
theorem cubic_cap {I : Type} [Fintype I] [DecidableEq I] {p n u T : ℕ} [Fact p.Prime]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=n)
    (hu : 0<u) (size : u^3≤n) (char : u^2-1+n*(u-1)<p) (hT : 1≤T)
    (enough : u^2-1+n*(u-1)+n*(2*u-1)<2*(T+1)*u^2) : PairCap D T := by
  have pos : 0<u^2 := by positivity
  apply pairCap_of_intersections D hn (C := (u^2-1+n*(u-1)+n*(2*u-1))/u^2) _
    ((Nat.div_lt_iff_lt_mul pos).mpr enough) hT
  intro J _ x y ix hx hy a b c d det diag anti law
  apply (Nat.le_div_iff_mul_le pos).mpr
  simpa only [Nat.mul_comm (Fintype.card J)] using
    MobiusSubgroupBound.cubic_graph_graded (Fact.out : p.Prime) hu size char x y ix hx hy det diag anti law

/-- The production intersection bound supplies at most 1,980,058
non-dihedral transpositions on any smooth coset of length 2^30. -/
theorem production_cap {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (hp : 2^40<p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^30) :
    PairCap D 1980058 := by
  apply pairCap_of_intersections D hn (C:=3960117) _ (by decide) (by decide)
  intro J _ x y ix hx hy a b c d det diag anti law
  exact MobiusSubgroupBound.production_graph (Fact.out : p.Prime) hp x y ix hx hy det diag anti law

/-- Exact list threshold at any of the four production dimensions, whenever
the displayed sampling upper bound and common-product lower bound straddle
the chosen budget. -/
theorem production_threshold {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (hp : 2^40<p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^30)
    {k r B : ℕ} [NeZero k] (split : k+3+r=2^30) (hr : 2≤r)
    (large : 6144≤k) (rate : r+1≤16*k) (upper : bound k r 1980058≤B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → ZMod p))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) :=
  threshold_of_payment D (hn.trans split.symm) hr (sponsor_payment large rate)
    (production_cap hp D hn) (by decide) upper lower m hm δ

/-- The graded Stepanov intersection bound supplies at most 1,571,839
non-dihedral transpositions on any smooth coset of length 2^30. -/
theorem production_cap_graded {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (hp : 2^40<p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^30) :
    PairCap D 1571839 := by
  apply pairCap_of_intersections D hn (C:=3143679) _ (by decide) (by decide)
  intro J _ x y ix hx hy a b c d det diag anti law
  exact MobiusSubgroupBound.production_graph_graded (Fact.out : p.Prime) hp x y ix hx hy det diag anti law

/-- The improved budget interval at any of the four production dimensions, whenever
the displayed sampling upper bound and common-product lower bound straddle
the chosen budget. -/
theorem production_threshold_graded {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (hp : 2^40<p) (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^30)
    {k r B : ℕ} [NeZero k] (split : k+3+r=2^30) (hr : 2≤r)
    (large : 6144≤k) (rate : r+1≤16*k) (upper : bound k r 1571839≤B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → ZMod p))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) :=
  threshold_of_payment D (hn.trans split.symm) hr (sponsor_payment large rate)
    (production_cap_graded hp D hn) (by decide) upper lower m hm δ

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.pairCap_of_intersections
#print axioms ProximityGap.ReflectionListSampling.cubic_cap
#print axioms ProximityGap.ReflectionListSampling.production_cap
#print axioms ProximityGap.ReflectionListSampling.production_threshold
#print axioms ProximityGap.ReflectionListSampling.production_threshold_graded
