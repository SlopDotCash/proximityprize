/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.TangentVeronesePacking

/-! # Half-rate residual interpolation at 310,285,000 errors -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.HalfCoreWeightedJets
open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 536870911
abbrev e : ℕ := 310285000
abbrev t : ℕ := n - e
abbrev coreFloor : ℕ := t - 255
abbrev bound : ℕ := 2101754336

/-- Order, ordinate degree, scalar/ordinate degree and order drop per owning head. -/
structure Shape where
  r : ℕ
  v : ℕ
  s : ℕ
  drop : ℕ

/-- Number of selected cores, truncated at six. -/
def group (j : ℕ) : Fin 7 := ⟨min 6 j, by omega⟩

/-- Both surfaces for each of the seven possible conditioning cases. -/
def shape (p : Fin 7) (companion : Bool) : Shape := if companion then
  ![⟨51,72,1355,0⟩, ⟨51,70,1284,2⟩, ⟨51,68,1229,2⟩, ⟨53,69,1190,2⟩,
    ⟨49,65,1164,1⟩, ⟨49,64,1128,1⟩, ⟨46,59,1097,1⟩] p else
  ![⟨26,36,227608,0⟩, ⟨26,35,209858,1⟩, ⟨26,34,195264,1⟩, ⟨26,33,183748,1⟩,
    ⟨26,32,175231,1⟩, ⟨26,31,169633,1⟩, ⟨26,30,166876,1⟩] p

def weight (p : Fin 7) (s : Shape) := s.r * t - p.val * s.drop * d
private def rows (s r : ℕ) := ∑ j ∈ range r, (r - j) * (s + 1 - j)
private def cols (s v w : ℕ) := ∑ j ∈ range (v + 1), (s + 1 - j) * (w - j * d)
private def saving (h : Shape) := rows h.s h.r - rows h.s (h.r - h.drop)
private def pairCost (h : Shape) := h.drop ^ 2 * (h.s + 1)

private theorem local_jet : ∀ p : Fin 7, ∀ b : Bool, ∀ m : Fin (p.val + 1),
    let h := shape p b
    rows h.s (h.r - h.drop * m.val) + m.val * saving h ≤
      rows h.s h.r + m.val.choose 2 * pairCost h := by decide +kernel

private theorem shape_room : ∀ p : Fin 7, ∀ b : Bool,
    let h := shape p b
    h.drop * p.val ≤ h.r ∧ h.r ≤ h.s + 1 ∧ 0 < weight p h ∧
      n * rows h.s h.r + p.val.choose 2 * d * pairCost h <
      cols h.s h.v (weight p h) + p.val * coreFloor * saving h := by decide +kernel

private theorem card_rows (s r : ℕ) : Fintype.card (JetRows s r) = rows s r := by
  simp only [JetRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, rows]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (r - j) * (s + 1 - j)) r

private theorem card_cols (s v w : ℕ) : Fintype.card (Monomials s v d w) = cols s v w := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, cols]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (s + 1 - j) * (w - j * d)) (v + 1)

/-- The physical site orders fit the mixed-jet monomial space from the two
double counts of single ownership and unordered pairs of owners. -/
theorem room {I : Type*} [Fintype I] (hn : Fintype.card I = n) (p : Fin 7) (b : Bool)
    (own : I → Fin (p.val + 1)) (coverage : p.val * coreFloor ≤ ∑ x, (own x).val)
    (pairs : (∑ x, (own x).val.choose 2) ≤ p.val.choose 2 * d) :
    let h := shape p b
    Fintype.card ((x : I) × JetRows h.s (h.r - h.drop * (own x).val)) <
      Fintype.card (Monomials h.s h.v d (weight p h)) := by
  classical
  dsimp only
  rw [Fintype.card_sigma, card_cols]
  simp_rw [card_rows]
  have total := sum_le_sum (s := univ) (fun x _ => local_jet p b (own x))
  simp only [sum_add_distrib, ← sum_mul, sum_const, card_univ, smul_eq_mul, hn] at total
  have left := Nat.mul_le_mul_right (saving (shape p b)) coverage
  have right := Nat.mul_le_mul_right (pairCost (shape p b)) pairs
  have strict := (shape_room p b).2.2.2
  omega

/-- Actual mixed Hasse surfaces contain every outside polynomial section whose
agreement set meets the chosen cores at most pd times, counting ownership. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (p : Fin 7) (b : Bool) (own : I → Fin (p.val + 1))
    (coverage : p.val * coreFloor ≤ ∑ x, (own x).val)
    (pairs : (∑ x, (own x).val.choose 2) ≤ p.val.choose 2 * d) :
    let h := shape p b
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i x, ((Q.coeff j).coeff i).coeff x ≠ 0 →
        j ≤ h.v ∧ i + j ≤ h.s ∧ x + j * d < weight p h) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (∑ x ∈ S, (own x).val) ≤ p.val * d →
        (∀ x ∈ S, q.eval (dom x) = u x + z * v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  classical
  dsimp only
  let h := shape p b
  have hm (x : I) : h.drop * (own x).val ≤ h.r :=
    (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (own x).isLt)).trans (shape_room p b).1
  obtain ⟨a, ha, _, hf⟩ := exists_order_surface dom u v (fun x => h.r - h.drop * (own x).val)
    (shape_room p b).2.2.1 (fun x => (Nat.sub_le _ _).trans (shape_room p b).2.1)
    (room hn p b own coverage pairs)
  refine ⟨surface a, surface_ne_zero ha, fun _ _ _ hq => surface_support a hq, ?_⟩
  intro z q hq S hs hov ag
  rw [surface_eval]
  apply hf z q hq S _ ag
  have add := sum_congr (s₁ := S) rfl (fun x _ => Nat.sub_add_cancel (hm x))
  rw [sum_add_distrib, ← mul_sum] at add
  simp only [sum_const, smul_eq_mul] at add
  have low := Nat.mul_le_mul_left h.r hs
  have high := Nat.mul_le_mul_left h.drop hov
  rw [Nat.mul_comm S.card h.r] at add
  change h.r * t - p.val * h.drop * d ≤ _
  have rearrange : h.drop * (p.val * d) = p.val * h.drop * d := by ring
  omega

open TangentVeronesePacking in
/-- A genuine triangle determinant of rational tangent coordinates vanishes
when the three denominator heights and regular-agreement losses are too small.
A polynomial anchor contributes zero height and at most 255 lost agreements. -/
theorem zero_triangle {I K : Type*} [Fintype I] [Field K] (dom : I ↪ K) (u v : I → K)
    (hn : Fintype.card I = n)
    (H X Y : ↥(monomials 1) → K[X]) (c loss : ↥(monomials 1) → ℕ)
    (degrees : ∀ i, (H i).natDegree ≤ c i ∧ (X i).natDegree ≤ d + c i ∧
      (Y i).natDegree ≤ d + c i)
    (S : I → Finset ↥(monomials 1))
    (agreement : ∀ x, ∀ i ∈ S x, (X i).eval (dom x) = u x * (H i).eval (dom x) ∧
      (Y i).eval (dom x) = v x * (H i).eval (dom x))
    (regular : 3 * t ≤ (∑ x, (S x).card) + ∑ i, loss i)
    (cheap : n + 2 * d + (∑ i, loss i) + ∑ i, c i < 3 * t) :
    Matrix.det (fun i j : ↥(monomials 1) => monomial 1 j.val (H i) (X i) (Y i)) = 0 := by
  by_contra independent
  have h := tangent_incidence 1 d 1 dom u v H X Y c degrees independent S agreement
  have short : (∑ j : ↥(monomials 1), (1 - (j.val.1 + j.val.2))) = 1 := by decide
  have deg : (∑ j : ↥(monomials 1), (j.val.1 + j.val.2)) = 2 := by decide
  simp only [short, deg, hn, one_mul, mul_one] at h
  omega

private def headMass (j : ℕ) : ℕ :=
  let den := coreFloor + (j - 1) * d
  let union := (j * coreFloor ^ 2 + den - 1) / den
  if j < 3 then j * (e + 1) else min (j * (e + 1)) (j * n - (j - 1) * union)

private def headCap (p : Fin 7) : ℕ :=
  ![0, 310285001, 620570002, 930855003, 1241140004, 1364051584, 1372573534] p

def cutoff (p : Fin 7) : ℕ :=
  let h := shape p false
  let k := shape p true
  max (e / 256 + 1) (h.s * k.v + h.v * k.s + 1)

/-- Each case of the greedy rich-head partition satisfies the resultant
cutoff, polynomial head test, collinearity test, and denominator tests. -/
theorem hypotheses : 3 * coreFloor > n + 2 * d ∧ 227608 < e / 256 + 1 ∧
    (∀ j : Fin 37, headMass j.val ≤ headCap (group j.val)) ∧
    (∀ p : Fin 7, let a := (shape p true).s
      d + a * n / cutoff p + 3 * (a * n / (cutoff p - a)) < t) ∧
    n + 2 * d + 2 * 255 < 3 * t ∧ 560 * n + 1632 * d < 14 * 153 * t := by decide +kernel

private def polar (b m W s a fixed : ℕ) : ℕ :=
  let A := (2 * b - 2) * W - b * (b - 1) * d
  let G := (2 * b - 2) * m - b * (b - 1)
  let height := 2 * A * G + 2 * W * m
  let loss := (G + m) * n
  let h := (s + 2).choose 2
  let gap := a * h * t - ((a + 2).choose 3 * n + (s * (s + 1) * (s + 2) / 3) * d +
    a * fixed * 255)
  G + 2 * b * m + s * m * (m - 1) + (h - fixed) * (a * loss + s * height) / gap

/-- Price of a single residual irreducible factor after greedy removal
of the polynomial heads. -/
def price (p : Fin 7) (f b : ℕ) : ℕ :=
  let primary := shape p false
  let W := weight p primary - 1 - (f - b) * d
  let m := (shape p true).s
  if b ≤ 1 then cutoff p else
    max (cutoff p) (if p.val = 0 then max (polar b 240 W 1 1 0) (polar b m W 16 14 0)
      else polar b m W 1 1 (min 2 p.val))

private def base (p : Fin 7) := headCap p + (shape p false).s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 18000000 in
-- Reduce all value-degree allocations for the seven residual shape pairs.
private theorem finite_prices : ∀ p : Fin 7, ∀ f : Fin ((shape p false).v + 1),
    ∀ b : Fin (f.val + 1), base p ≤ bound ∧ (0 < b.val →
      f.val * price p f.val b.val < b.val * (bound - base p + 1)) := by decide +kernel

/-- Every partition into positive residual value-degrees obeys the asserted
production label budget, including all extracted heads and scalar-only factors. -/
theorem allocations {J : Type*} (S : Finset J) (value cost : J → ℕ) (j : Fin 37)
    (f : Fin ((shape (group j.val) false).v + 1))
    (positive : ∀ i ∈ S, 0 < value i) (total : ∑ i ∈ S, value i = f.val)
    (prices : ∀ i ∈ S, cost i ≤ price (group j.val) f.val (value i)) :
    headMass j.val + (shape (group j.val) false).s + ∑ i ∈ S, cost i ≤ bound := by
  classical
  let p := group j.val
  have hhead := hypotheses.2.2.1 j
  have enough := (finite_prices p f 0).1
  change headMass j.val ≤ headCap p at hhead
  apply (Nat.add_le_add_right (Nat.add_le_add_right hhead _) _).trans
  change base p + ∑ i ∈ S, cost i ≤ bound
  by_cases empty : S = ∅
  · simpa [empty] using enough
  have one (i : J) (hi : i ∈ S) :
      f.val * cost i < value i * (bound - base p + 1) := by
    have hv := (single_le_sum (fun k _ => Nat.zero_le (value k)) hi).trans_eq total
    exact (Nat.mul_le_mul_left f.val (prices i hi)).trans_lt
      ((finite_prices p f ⟨value i, by omega⟩).2 (positive i hi))
  have h := sum_lt_sum_of_nonempty (nonempty_iff_ne_empty.mpr empty) one
  rw [← mul_sum, ← sum_mul, total] at h
  have hc := Nat.lt_of_mul_lt_mul_left h
  omega

#print axioms zero_triangle
#print axioms hypotheses
#print axioms allocations

#print axioms surfaces
end ArkLib.ProximityGap.Frontier.HalfCoreWeightedJets
