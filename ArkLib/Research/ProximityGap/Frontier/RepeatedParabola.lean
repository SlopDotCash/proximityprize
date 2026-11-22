/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Repeated points and distinct secants of a parabola at dimension one -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.RepeatedParabola
open _root_.ProximityGap HalfPredecessorCoreFreshDecode

variable {I F E : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [Fintype E]

/-- A parabola secant based at a repeated value supplies a bad scalar if it
reaches the agreement threshold with one further coordinate. Distinct endpoint
sums count distinct bad scalars for the same received pair. -/
theorem mass_of_cores (dom : I ↪ F) (δ : ℝ≥0) (v : I → F) (a : E → F) (core : E → Finset I)
    (tip : E → I) (nonempty : ∀ e, 1 ≤ (core e).card)
    (size : ∀ e, (1-δ)*(Fintype.card I : ℝ≥0) ≤ (((core e).card+1 : ℕ) : ℝ≥0))
    (hit : ∀ e x, x ∈ core e → v x = a e) (apart : ∀ e, a e ≠ v (tip e))
    (distinct : Function.Injective (fun e => a e + v (tip e))) (width : ℕ) [NeZero width] :
    (Fintype.card E : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (I → F)) ^⋈ (Fin width)) δ := by
  classical
  let rows : WordStack F (Fin 2) I := ![fun i => v i ^ 2, v]
  let label : E ↪ F := ⟨fun e => -(a e + v (tip e)), fun e f h => distinct (neg_injective h)⟩
  have degreeC (b : F) : (C b).degree < (1 : ℕ) :=
    degree_le_natDegree.trans_lt (by simp)
  have event (e : E) : mcaEvent (ReedSolomon.code dom 1 : Set (I → F)) δ
      (rows 0) (rows 1) (label e) := by
    apply mcaEvent_of_affine_core_fresh dom 1 δ rows (label e) (core e) (tip e) (C (a e ^ 2)) (C (a e))
    · exact fun h => apart e (hit e _ h).symm
    · exact degreeC _
    · exact degreeC _
    · rw [← C_mul, ← C_add]
      exact degreeC _
    · exact nonempty e
    · exact size e
    · intro x hx
      change (C (a e ^ 2)).eval _ = v x ^ 2 ∧ (C (a e)).eval _ = v x
      simp [hit e x hx]
    · change (C (a e ^ 2) + C (label e) * C (a e)).eval _ =
        v (tip e) ^ 2 + label e * v (tip e)
      simp only [eval_add, eval_mul, eval_C]
      change _ + -(a e + v (tip e)) * _ = _ + -(a e + v (tip e)) * _
      ring
    · intro he
      have h : a e = v (tip e) := by simpa [rows] using congrArg Prod.snd he
      exact apart e h
  rw [epsMCA_interleaved_eq]
  have hm := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom 1 : Set (I → F)) δ rows (univ.map label) (by
      intro z hz
      obtain ⟨e, _, rfl⟩ := mem_map.mp hz
      exact event e)
  simpa only [card_map, card_univ] using hm

private abbrev Sites (m u s : ℕ) := (Fin m × Fin u) ⊕ Fin s
private abbrev Edges (m s : ℕ) := (Fin m × Fin s) ⊕ Unit

private def index (m u s : ℕ) : Sites m u s ≃ Fin (m*u+s) :=
  (finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv

private def val {m u s : ℕ} : Sites m u s → ℕ
  | .inl (i, _) => i.val
  | .inr j => m*(j.val+1)

private def src {m s : ℕ} (hm : 2 ≤ m) : Edges m s → Fin m
  | .inl (i, _) => i
  | .inr _ => ⟨0, by omega⟩

private def tip {m u s : ℕ} [NeZero u] (hm : 2 ≤ m) : Edges m s → Sites m u s
  | .inl (_, j) => .inr j
  | .inr _ => .inl (⟨1, by omega⟩, 0)

private def pairSum {m u s : ℕ} [NeZero u] (hm : 2 ≤ m) (e : Edges m s) : ℕ :=
  (src hm e).val + val (tip (u := u) hm e)

private theorem sums {m u s : ℕ} [NeZero u] (hm : 2 ≤ m) :
    Function.Injective (pairSum (u := u) (s := s) hm) := by
  intro e f eq
  rcases e with ⟨i,j⟩|⟨⟩ <;> rcases f with ⟨i',j'⟩|⟨⟩
  · change i.val + m*(j.val+1) = i'.val + m*(j'.val+1) at eq
    have same : i = i' := Fin.ext (by
      simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt]
        using congrArg (fun x => x % m) eq)
    subst i'
    have same' : j = j' := Fin.ext (by
      have q := Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (Nat.add_left_cancel eq)
      omega)
    rw [same']
  · change i.val + m*(j.val+1) = 1 at eq
    rw [Nat.mul_add, Nat.mul_one] at eq
    omega
  · change 1 = i'.val + m*(j'.val+1) at eq
    rw [Nat.mul_add, Nat.mul_one] at eq
    omega
  · rfl

/-- Repeat each of `m` integer parabola parameters `u` times and add `s`
singletons. The center–singleton secants and one center–center secant have
distinct slopes, giving at least `m*s+1` bad scalars at `u+1` agreements. -/
theorem prime_mass {p m u s : ℕ} [Fact p.Prime] [NeZero u] (hm : 2 ≤ m)
    (dom : Fin (m*u+s) ↪ ZMod p) (room : m*(s+1) < p) (width : ℕ) [NeZero width] :
    ((m*s+1 : ℕ) : ℝ≥0∞) / p ≤
      epsMCA (F := ZMod p) ((ReedSolomon.code dom 1 : Set (Fin (m*u+s) → ZMod p)) ^⋈ (Fin width))
        (((m*u+s-(u+1) : ℕ) : ℝ≥0)/(m*u+s : ℕ)) := by
  classical
  have hu := Nat.pos_of_ne_zero (NeZero.ne u)
  have un : u ≤ m*u := by
    calc
      u = 1*u := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have npos : 0 < m*u+s := by omega
  have : Nonempty (Fin (m*u+s)) := ⟨⟨0, npos⟩⟩
  let ep := index m u s
  let v (x : Fin (m*u+s)) : ZMod p := val (ep.symm x)
  let a (e : Edges m s) : ZMod p := (src hm e).val
  let coord (e : Edges m s) := ep (tip (u := u) hm e)
  let copies (i : Fin m) : Fin u ↪ Fin (m*u+s) :=
    ⟨fun j => ep (.inl (i,j)), fun _ _ eq => (Prod.mk.inj (Sum.inl.inj (ep.injective eq))).2⟩
  let core (e : Edges m s) := univ.map (copies (src hm e))
  have card (e) : (core e).card = u := by simp [core]
  have value (e) : v (coord e) = ((val (tip (u := u) hm e) : ℕ) : ZMod p) := by
    simp [v, coord]
  have bound (e : Edges m s) : pairSum (u := u) hm e < p := by
    rcases e with ⟨i,j⟩|⟨⟩
    · change i.val + m*(j.val+1) < p
      have h := Nat.mul_le_mul_left m (show j.val+1 ≤ s from j.isLt)
      rw [Nat.mul_add, Nat.mul_one] at room
      omega
    · change 1 < p
      rw [Nat.mul_add, Nat.mul_one] at room
      omega
  have cast {b c : ℕ} (hb : b < p) (hc : c < p) (eq : (b : ZMod p) = c) : b = c := by
    simpa only [ZMod.val_natCast_of_lt hb, ZMod.val_natCast_of_lt hc] using congrArg (@ZMod.val p) eq
  have add (e) : a e + v (coord e) = ((pairSum (u := u) hm e : ℕ) : ZMod p) := by
    rw [value, pairSum, Nat.cast_add]
  have distinct : Function.Injective (fun e => a e + v (coord e)) := by
    intro e f eq
    change a e + v (coord e) = a f + v (coord f) at eq
    rw [add, add] at eq
    exact sums hm (cast (bound e) (bound f) eq)
  have apart (e) : a e ≠ v (coord e) := by
    rw [value]
    have small := bound e
    unfold pairSum at small
    intro eq
    have he := cast (show (src hm e).val < p by omega)
      (show val (tip (u := u) hm e) < p by omega) eq
    rcases e with ⟨i,j⟩|⟨⟩
    · change i.val = m*(j.val+1) at he
      rw [Nat.mul_add, Nat.mul_one] at he
      omega
    · exact (by decide : (0 : ℕ) ≠ 1) he
  have h := mass_of_cores dom (((m*u+s-(u+1) : ℕ) : ℝ≥0)/(m*u+s : ℕ)) v a core coord
    (fun e => (card e).symm ▸ hu) (fun e => by
      rw [card, Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast npos.ne'),
        ← Nat.cast_tsub]
      exact_mod_cast (show m*u+s-(m*u+s-(u+1)) ≤ u+1 by omega))
    (by
      intro e x hx
      obtain ⟨j, _, rfl⟩ := mem_map.mp hx
      change ((val (ep.symm (ep (.inl (src hm e, j)))) : ℕ) : ZMod p) = _
      rw [ep.symm_apply_apply]
      rfl)
    apart distinct width
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit,
    ZMod.card, Edges] using h

end ArkLib.ProximityGap.Frontier.RepeatedParabola
