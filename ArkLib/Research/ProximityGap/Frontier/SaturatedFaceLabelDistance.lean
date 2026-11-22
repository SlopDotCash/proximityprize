/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.FiniteDomainQuotient
import Mathlib.Tactic

/-! # Distance from a lower-degree labelled face configuration

Subtract the fourth head from every head. The first three coordinates of a face vector
determine its fourth coordinate since the four sum to zero. At a marked double site
this vector is supported on the two equal heads with opposite coefficients.
-/

namespace ProximityGap.SaturatedFaceLabelDistance
open Polynomial Finset
variable {K : Type*} [Field K]

/-- Values of the four scalar heads after subtracting the last head. -/
def heads (a : Fin 3 → K[X]) (x : K) : Fin 4 → K :=
  ![(a 0).eval x, (a 1).eval x, (a 2).eval x, 0]

/-- Values of the four signed face coordinates, which sum to zero. -/
def faces (l : Fin 3 → K[X]) (x : K) : Fin 4 → K :=
  ![(l 0).eval x, (l 1).eval x, (l 2).eval x, -((l 0).eval x + (l 1).eval x + (l 2).eval x)]

/-- Both rows of the proposed quartet agree on the pair encoded by the face vector. -/
def PreservesPair (l a b : Fin 3 → K[X]) (x : K) : Prop :=
  ∃ (i j : Fin 4) (u : K), i ≠ j ∧ u ≠ 0 ∧
    (∀ k, faces l x k = (if k = i then u else 0) - (if k = j then u else 0)) ∧
    heads a x i = heads a x j ∧ heads b x i = heads b x j

/-- Pair a scalar head row with the three independent signed faces. -/
noncomputable def pairing (l a : Fin 3 → K[X]) := l 0*a 0 + l 1*a 1 + l 2*a 2

private theorem eval_pairing_eq_zero (l a : Fin 3 → K[X]) (x : K) (i j : Fin 4) (u : K)
    (h : ∀ k, faces l x k = (if k = i then u else 0) - (if k = j then u else 0))
    (he : heads a x i = heads a x j) : (pairing l a).eval x = 0 := by
  have hs : ∑ k, faces l x k * heads a x k = 0 := by
    simp_rw [h, sub_mul, ite_mul, zero_mul, sum_sub_distrib]
    simp [he]
  simpa [faces, heads, pairing, Fin.sum_univ_four] using hs

private theorem degree_pairing (l a : Fin 3 → K[X]) {E D : ℕ}
    (hl : ∀ i, (l i).natDegree ≤ E) (ha : ∀ i, (a i).natDegree ≤ D) :
    (pairing l a).natDegree ≤ E+D := by
  have term (i : Fin 3) : (l i * a i).natDegree ≤ E+D :=
    natDegree_mul_le.trans (Nat.add_le_add (hl i) (ha i))
  exact (natDegree_add_le ..).trans (max_le ((natDegree_add_le ..).trans (max_le (term 0) (term 1))) (term 2))

/-- After cancelling the locator of the preserved sites, both rows have residuals
of degree at most the slack in the agreement bound. At equality they are constants. -/
theorem residual_rows (l a b : Fin 3 → K[X]) {E D : ℕ}
    (hl : ∀ i, (l i).natDegree ≤ E)
    (ha : ∀ i, (a i).natDegree ≤ D) (hb : ∀ i, (b i).natDegree ≤ D)
    (S : Finset K) (hmatch : ∀ x ∈ S, PreservesPair l a b x) :
    ∃ u v : K[X], pairing l a = u * Lagrange.nodal S id ∧
      pairing l b = v * Lagrange.nodal S id ∧
      u.natDegree ≤ E+D-S.card ∧ v.natDegree ≤ E+D-S.card := by
  have hr (x : K) (hx : x ∈ S) : (pairing l a).eval x = 0 ∧ (pairing l b).eval x = 0 := by
    obtain ⟨i,j,c,_,_,hf,he₁,he₂⟩ := hmatch x hx
    exact ⟨eval_pairing_eq_zero l a x i j c hf he₁, eval_pairing_eq_zero l b x i j c hf he₂⟩
  have h₁ : ZeroOn S (pairing l a) := fun x hx => (hr x hx).1
  have h₂ : ZeroOn S (pairing l b) := fun x hx => (hr x hx).2
  obtain ⟨u, ⟨hu,du⟩, _⟩ := h₁.existsUnique_quotient
  obtain ⟨v, ⟨hv,dv⟩, _⟩ := h₂.existsUnique_quotient
  exact ⟨u,v,hu,hv,du.le.trans (Nat.sub_le_sub_right (degree_pairing l a hl ha) _),
    dv.le.trans (Nat.sub_le_sub_right (degree_pairing l b hl hb) _)⟩

/-- If a set of marked agreements exceeds the degree bound, both target rows preserve
every labelled pair encoded by the comparison faces, including those outside the set. -/
theorem recover_all_pairs (l a b : Fin 3 → K[X]) {E D : ℕ}
    (hl : ∀ i, (l i).natDegree ≤ E)
    (ha : ∀ i, (a i).natDegree ≤ D) (hb : ∀ i, (b i).natDegree ≤ D)
    (S : Finset K) (hs : E+D < S.card) (hmatch : ∀ x ∈ S, PreservesPair l a b x)
    (x : K) (i j : Fin 4) (u : K) (hu : u ≠ 0)
    (hf : ∀ k, faces l x k = (if k = i then u else 0) - (if k = j then u else 0)) :
    heads a x i = heads a x j ∧ heads b x i = heads b x j := by
  classical
  have hr (y : K) (hy : y ∈ S) : (pairing l a).eval y = 0 ∧ (pairing l b).eval y = 0 := by
    obtain ⟨i',j',v,_,_,h,ha',hb'⟩ := hmatch y hy
    exact ⟨eval_pairing_eq_zero l a y i' j' v h ha', eval_pairing_eq_zero l b y i' j' v h hb'⟩
  have recover (w : Fin 3 → K[X]) (hw : ∀ i, (w i).natDegree ≤ D)
      (hz : ∀ y ∈ S, (pairing l w).eval y = 0) : heads w x i = heads w x j := by
    have hzero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (pairing l w) S hz
      ((degree_pairing l w hl hw).trans_lt hs)
    have he := congrArg (Polynomial.eval x) hzero
    have hh : ∑ t, faces l x t * heads w x t = 0 := by
      simpa [faces, heads, pairing, Fin.sum_univ_four] using he
    simp_rw [hf, sub_mul, ite_mul, zero_mul, sum_sub_distrib] at hh
    apply sub_eq_zero.mp
    simpa [hu, ← mul_sub] using hh
  exact ⟨recover a ha (fun y hy => (hr y hy).1), recover b hb (fun y hy => (hr y hy).2)⟩

/-- A target face vanishes simply on its marked sites in the saturated application.
Only set-theoretic vanishing and the rank of its two rows at those sites are needed here. -/
def OtherMinorNonzero (a b : Fin 3 → K[X]) (x : K) : Prop :=
  (a 1).eval x * (b 2).eval x - (a 2).eval x * (b 1).eval x = 0 ∧
  ((a 2).eval x * (b 0).eval x - (a 0).eval x * (b 2).eval x ≠ 0 ∨
   (a 0).eval x * (b 1).eval x - (a 1).eval x * (b 0).eval x ≠ 0)

/-- If a target triple has more roots than the degree of a nonzero comparison face,
the number of preserved marked pairs is at most the sum of the face and head degrees. -/
theorem label_agreement_bound (l a b : Fin 3 → K[X]) {E D : ℕ}
    (hl0 : l 0 ≠ 0) (hl : ∀ i, (l i).natDegree ≤ E)
    (ha : ∀ i, (a i).natDegree ≤ D) (hb : ∀ i, (b i).natDegree ≤ D)
    (S T : Finset K) (hmatch : ∀ x ∈ S, PreservesPair l a b x)
    (ht : E < T.card) (hrank : ∀ x ∈ T, OtherMinorNonzero a b x) :
    S.card ≤ E+D := by
  classical
  by_contra! hm
  have hrows (x : K) (hx : x ∈ S) : (pairing l a).eval x = 0 ∧ (pairing l b).eval x = 0 := by
    obtain ⟨i,j,u,_,_,hf,h₁,h₂⟩ := hmatch x hx
    exact ⟨eval_pairing_eq_zero l a x i j u hf h₁, eval_pairing_eq_zero l b x i j u hf h₂⟩
  have hA := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (pairing l a) S
    (fun x hx => (hrows x hx).1) ((degree_pairing l a hl ha).trans_lt hm)
  have hB := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (pairing l b) S
    (fun x hx => (hrows x hx).2) ((degree_pairing l b hl hb).trans_lt hm)
  apply hl0
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (l 0) T _ ((hl 0).trans_lt ht)
  intro x hx
  have h₁ := congrArg (Polynomial.eval x) hA
  have h₂ := congrArg (Polynomial.eval x) hB
  simp [pairing] at h₁ h₂
  obtain ⟨g0, g1 | g2⟩ := hrank x hx
  · apply (mul_eq_zero.mp _).resolve_left g1
    linear_combination (a 2).eval x * h₂ - (b 2).eval x * h₁ + (l 1).eval x * g0
  · apply (mul_eq_zero.mp _).resolve_left g2
    linear_combination (b 1).eval x * h₁ - (a 1).eval x * h₂ + (l 2).eval x * g0

/-- Compose all comparison faces with a power quotient. -/
noncomputable def powerPullback (l : Fin 3 → K[X]) (r : ℕ) (i : Fin 3) :=
  (l i).comp (X^r)

/-- With new head degree determined by the quarter-rate scaling, a power lift
from a base head degree `d` loses at least `r*(d-1)+1` of its prescribed pairs. -/
theorem pullback_distance (l a b : Fin 3 → K[X]) {d r D : ℕ}
    (hd : 0 < d) (hr : 2 ≤ r) (hD : D+1 = r*(d+1))
    (hl0 : 0 < (l 0).natDegree) (hl : ∀ i, (l i).natDegree ≤ 2*d)
    (ha : ∀ i, (a i).natDegree ≤ D) (hb : ∀ i, (b i).natDegree ≤ D)
    (S T : Finset K) (hmatch : ∀ x ∈ S, PreservesPair (powerPullback l r) a b x)
    (ht : T.card = 2*D) (hrank : ∀ x ∈ T, OtherMinorNonzero a b x) :
    r*(d-1) + 1 + S.card ≤ 4*r*d := by
  have deg (i : Fin 3) : (powerPullback l r i).natDegree = (l i).natDegree*r := by
    simp [powerPullback, natDegree_comp]
  have hne : powerPullback l r 0 ≠ 0 := by
    intro hz
    have hp : 0 < (powerPullback l r 0).natDegree := by
      rw [deg]
      exact Nat.mul_pos hl0 (by omega)
    simp [hz] at hp
  have he : 2*d*r < T.card := by rw [ht]; nlinarith
  have bound := label_agreement_bound (powerPullback l r) a b hne
    (fun i => (deg i).le.trans (Nat.mul_le_mul_right r (hl i))) ha hb S T hmatch he hrank
  have hpred : d-1+1=d := by omega
  have hscaled := congrArg (r * ·) hpred
  nlinarith

/-- Numerical distance from any degree-six face template pulled back along the
order-16 quotient of the production domain, among its 805306368 marked sites. -/
theorem production_distance (l a b : Fin 3 → K[X])
    (hl0 : l 0 ≠ 0) (hl : ∀ i, (l i).natDegree ≤ 402653184)
    (ha : ∀ i, (a i).natDegree ≤ 268435455) (hb : ∀ i, (b i).natDegree ≤ 268435455)
    (S T : Finset K) (hmatch : ∀ x ∈ S, PreservesPair l a b x)
    (ht : T.card = 536870910) (hrank : ∀ x ∈ T, OtherMinorNonzero a b x) :
    134217729 + S.card ≤ 805306368 := by
  have h := label_agreement_bound l a b hl0 hl ha hb S T hmatch (by omega) hrank
  omega

#print axioms recover_all_pairs
#print axioms residual_rows
#print axioms label_agreement_bound
#print axioms pullback_distance
#print axioms production_distance

end ProximityGap.SaturatedFaceLabelDistance
