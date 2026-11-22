/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseCollisions
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseCore

/-! # Fresh folded agreements at each regular physical coordinate -/

namespace ArkLib.ProximityGap.Frontier.EighthTransverseIncidences
open EighthMobiusSites EighthTransverseRows EighthTransverseMobius EighthTransverseCollisions
open EighthTransverseCore SecondPrimeSmoothSeed PrizeShapePrimeP30Second
open _root_.ProximityGap.MobiusSeamCoordinateSupply (Mobius)
local instance : Fact P.Prime := ⟨prime_P⟩
set_option autoImplicit false
set_option maxRecDepth 10000

private def partner (l : Fin 15) (t : Tag) : Fin 4 :=
  if t = .solo3 then foreignTag l.succ t else ownerTag t

private theorem chart_at (l : Fin 15) :
    chart l.succ = (⟨pole l - u - v, u * v, 1, -pole l⟩ : Mobius F) := by
  fin_cases l <;> rfl

private theorem partner_shape (l : Fin 15) (j : Fin 32) (t : Tag)
    (h : scheduled l.succ j t) :
    (foreignTag l.succ t = 3 ∧ ownerTag t = partner l t ∨
      foreignTag l.succ t = partner l t ∧ ownerTag t = 3) ∧
    (partner l t : ℕ) < 3 ∧ t ≠ .p01 ∧
    (l = 0 → partner l t = 0) ∧ (l = 1 → partner l t = 1) ∧
    (2 ≤ l.val → partner l t = 2) := by
  revert l j t
  decide

private theorem triple (x p q : F) (a : Fin 4) (ha : a.val < 3) :
    aVal x p q a = x * bVal 0 p q a ∧ bVal x p q a = bVal 0 p q a := by
  fin_cases a <;> simp_all [aVal, bVal]

private theorem regular_fraction {l : Fin 15} {i : Site} (hi : i ∈ loci l.succ)
    (hr : (chart l.succ).den (dom i) ≠ 0) :
    let x := dom i
    let j := fiber i
    let b := bVal x (pv j) (qv j)
    let a := aVal x (pv j) (qv j)
    let γ := (chart l.succ).value x
    b (foreign l.succ i) ≠ b (owner i) ∧
      a (foreign l.succ i) + γ * b (foreign l.succ i) = a (owner i) + γ * b (owner i) := by
  dsimp only
  let j := fiber i
  let t := tag i
  obtain ⟨side, ht, hn, h0, h1, h2⟩ := partner_shape l j t (mem_loci.mp hi)
  have zero : pv j ≠ 0 := by
    intro eq
    apply hn
    exact (pair_tags i).1.mpr ((by decide : ∀ j : Fin 32, pv j = 0 →
      j ∈ ({0, 2, 16} : Finset (Fin 32))) j eq)
  let p := pv j
  let q := qv j
  have ratio : bVal 0 p q (partner l t) = p * (intercept + slope * pole l) := by
    by_cases h : l = 0
    · rw [h0 h, h, poles.1]
      simp [bVal]
    by_cases h' : l = 1
    · rw [h1 h', h', poles.2.1]
      simp [bVal]
    have hl : 2 ≤ l.val := by
      have : l.val ≠ 0 := fun hh => h (Fin.ext hh)
      have : l.val ≠ 1 := fun hh => h' (Fin.ext hh)
      omega
    let a : Fin 13 := ⟨l.val - 2, by omega⟩
    have hvar : j = variableFiber a := by
      exact variable_fiber (l := l.succ) (by change 3 ≤ l.val + 1; omega) hi
    have idx : (⟨a.val + 2, by dsimp [a]; omega⟩ : Fin 15) = l := Fin.ext (by dsimp [a]; omega)
    rw [h2 hl]
    change qv j = pv j * (intercept + slope * pole l)
    rw [hvar, mul_comm, ← idx]
    exact (poles.2.2 a).2.symm
  let x := dom i
  have hx : x ≠ pole l := by
    rw [chart_at] at hr
    change (1 : F) * x + -pole l ≠ 0 at hr
    simpa only [one_mul, ← sub_eq_add_neg, sub_ne_zero] using hr
  have val : (chart l.succ).value x = ((pole l - u - v) * x + u * v) / (x - pole l) := by
    rw [chart_at]
    change ((pole l - u - v) * x + u * v) / ((1 : F) * x + -pole l) = _
    rw [one_mul, sub_eq_add_neg x]
  obtain ⟨ha, hb⟩ := triple x p q (partner l t) ht
  obtain ⟨ne, eq⟩ := cross (x := x) (h := pole l) (p := p) zero hx
  have b : bVal x p q 3 ≠ bVal x p q (partner l t) := by
    rw [hb, ratio]
    exact ne
  have f : aVal x p q 3 + (chart l.succ).value x * bVal x p q 3 =
      aVal x p q (partner l t) + (chart l.succ).value x * bVal x p q (partner l t) := by
    rw [ha, hb, ratio, val]
    exact eq
  change bVal x p q (foreignTag l.succ t) ≠ bVal x p q (ownerTag t) ∧ _
  change _ ∧ aVal x p q (foreignTag l.succ t) + _ * bVal x p q (foreignTag l.succ t) =
    aVal x p q (ownerTag t) + _ * bVal x p q (ownerTag t)
  rcases side with ⟨hf, ho⟩ | ⟨hf, ho⟩ <;> rw [hf, ho]
  · exact ⟨b, f⟩
  · exact ⟨Ne.symm b, f.symm⟩

/-- Every non-pole in every scheduled chart gives a genuine extra folded
agreement, with unequal second-row entries on the same physical site. -/
theorem fresh {l : Fin 16} {i : Site} (hi : i ∈ loci l)
    (hr : (chart l).den (dom i) ≠ 0) :
    (rowB locator (foreign l i)).eval (dom i) ≠ recvB i ∧
    (rowA locator (foreign l i)).eval (dom i) +
      (chart l).value (dom i) * (rowB locator (foreign l i)).eval (dom i) =
      recvA i + (chart l).value (dom i) * recvB i := by
  cases l using Fin.cases with
  | zero =>
    have val : (chart 0).value (dom i) = -(dom i) := by
      change ((-1 : F) * dom i + 0) / (0 * dom i + 1) = _
      simp
    rw [val]
    exact minus_incidence hi
  | succ l =>
    obtain ⟨ne, eq⟩ := regular_fraction hi hr
    have hf := evals locator (foreign l.succ i) i (fiber i) (fiber_mod i)
    have ho := evals locator (owner i) i (fiber i) (fiber_mod i)
    have hj := mt locator_eval.mp (locus_nonroot hi)
    unfold recvA recvB
    rw [hf.1, hf.2, ho.1, ho.2]
    refine ⟨fun h => ne (mul_left_cancel₀ hj h), ?_⟩
    linear_combination locator.eval (dom i) * eq

#print axioms fresh
end ArkLib.ProximityGap.Frontier.EighthTransverseIncidences
