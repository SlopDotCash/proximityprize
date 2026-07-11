/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry
import Mathlib.LinearAlgebra.Lagrange

/-!
# P1: a half-billion `K`-cores need not consolidate

The Hall-safe forced-secant matching has at least `2^29-6` edges, each carrying a core of size
`K=2^28` in an `N=4K` coordinate domain.  Cardinality alone still cannot force two cores to agree
on `K` coordinates.

This file gives an explicit packing of `2K` distinct `K`-subsets in a `4K`-point domain.  Start
from one `K`-point base block; for each base coordinate and either of two spare blocks, replace
that base point by the corresponding spare point.  Every resulting core has size `K`, the family
has size `2K`, and distinct cores intersect in at most `K-1` points.

At the P1 constants this is `2^29` cores—six more than the forced matching lower bound.  Hence
matching cardinality plus core weights cannot perform pencil consolidation.  Any successful next
step must use correlations between secant parameters and their cores, not only the core set system.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1HalfBillionCorePackingNoGo

abbrev CoreIndex (k : Nat) := Fin 2 × Fin k
abbrev Coord (k : Nat) := Fin 4 × Fin k

def basePoint {k : Nat} (i : Fin k) : Coord k := (0, i)

def addedPoint {k : Nat} (p : CoreIndex k) : Coord k :=
  (⟨p.1.val + 1, by omega⟩, p.2)

theorem basePoint_injective {k : Nat} : Function.Injective (@basePoint k) := by
  intro i j h
  exact congrArg Prod.snd h

def base (k : Nat) : Finset (Coord k) :=
  Finset.univ.map ⟨basePoint, basePoint_injective⟩

@[simp]
theorem mem_base_iff {k : Nat} (x : Coord k) :
    x ∈ base k ↔ x.1 = 0 := by
  constructor
  · intro hx
    simp only [base, Finset.mem_map, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rfl
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨x.2, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact hx.symm
    · rfl

@[simp]
theorem basePoint_mem_base {k : Nat} (i : Fin k) : basePoint i ∈ base k := by
  simp [mem_base_iff, basePoint]

@[simp]
theorem addedPoint_not_mem_base {k : Nat} (p : CoreIndex k) :
    addedPoint p ∉ base k := by
  simp only [mem_base_iff, addedPoint]
  apply Fin.ne_of_val_ne
  simp

def core {k : Nat} (p : CoreIndex k) : Finset (Coord k) :=
  insert (addedPoint p) ((base k).erase (basePoint p.2))

@[simp]
theorem addedPoint_mem_core {k : Nat} (p : CoreIndex k) :
    addedPoint p ∈ core p := by simp [core]

theorem base_card (k : Nat) : (base k).card = k := by
  simp [base]

theorem core_card {k : Nat} (p : CoreIndex k) : (core p).card = k := by
  rw [core, Finset.card_insert_of_notMem]
  · rw [Finset.card_erase_of_mem (basePoint_mem_base p.2), base_card]
    have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
    omega
  · exact fun h => addedPoint_not_mem_base p (Finset.mem_of_mem_erase h)

theorem addedPoint_mem_core_iff {k : Nat} (p q : CoreIndex k) :
    addedPoint p ∈ core q ↔ p = q := by
  constructor
  · intro h
    simp only [core, Finset.mem_insert, Finset.mem_erase] at h
    rcases h with h | h
    · have hfst := congrArg (fun x : Coord k => x.1.val) h
      have hsnd : p.2 = q.2 := congrArg (fun x : Coord k => x.2) h
      have hp1 : p.1 = q.1 := by
        apply Fin.ext
        simp only [addedPoint] at hfst
        omega
      exact Prod.ext hp1 hsnd
    · exact absurd h.2 (addedPoint_not_mem_base p)
  · rintro rfl
    exact addedPoint_mem_core p

theorem core_injective {k : Nat} : Function.Injective (@core k) := by
  intro p q h
  have hp : addedPoint p ∈ core q := by rw [← h]; exact addedPoint_mem_core p
  exact (addedPoint_mem_core_iff p q).mp hp

/-- Distinct packed cores have intersection strictly smaller than `k`. -/
theorem inter_card_lt {k : Nat} {p q : CoreIndex k} (hpq : p ≠ q) :
    (core p ∩ core q).card < k := by
  calc
    (core p ∩ core q).card < (core p).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have hp : addedPoint p ∈ core p ∩ core q := by
        rw [heq]
        exact addedPoint_mem_core p
      exact hpq ((addedPoint_mem_core_iff p q).mp (Finset.mem_inter.mp hp).2)
    _ = k := core_card p

/-- There are exactly `2*k` cores in the packing. -/
theorem coreIndex_card (k : Nat) : Fintype.card (CoreIndex k) = 2 * k := by
  simp [CoreIndex]

/-- The ambient coordinate domain has exactly `4*k` points. -/
theorem coord_card (k : Nat) : Fintype.card (Coord k) = 4 * k := by
  simp [Coord]

/-! ## Literal P1 calibration -/

abbrev K : Nat := 2 ^ 28
abbrev N : Nat := 2 ^ 30

theorem production_core_count : Fintype.card (CoreIndex K) = 2 ^ 29 := by
  rw [coreIndex_card]
  norm_num [K]

theorem production_coord_count : Fintype.card (Coord K) = N := by
  rw [coord_card]
  norm_num [K, N]

theorem production_matching_lower_fits : 2 ^ 29 - 6 ≤ Fintype.card (CoreIndex K) := by
  rw [production_core_count]
  omega

/-! ## Every packed core has a degree-`<k` line realization -/

open Polynomial
open HalfPredecessorLineCoreGeometry

noncomputable def interpolant
    {F X : Type} [Field F] [DecidableEq X]
    (domain : X → F) (u : X → F) (S : Finset X) : F[X] :=
  Lagrange.interpolate S domain u

theorem interpolant_mem_degreeLT
    {F X : Type} [Field F] [DecidableEq X]
    (domain : X → F) (u : X → F) (S : Finset X)
    (hdomain : Function.Injective domain) {k : Nat} (hcard : S.card = k) :
    interpolant domain u S ∈ Polynomial.degreeLT F k := by
  rw [Polynomial.mem_degreeLT, interpolant, ← hcard]
  exact Lagrange.degree_interpolate_lt u hdomain.injOn

theorem interpolant_eval_of_mem
    {F X : Type} [Field F] [DecidableEq X]
    (domain : X → F) (u : X → F) (S : Finset X)
    (hdomain : Function.Injective domain) {x : X} (hx : x ∈ S) :
    (interpolant domain u S).eval (domain x) = u x := by
  exact Lagrange.eval_interpolate_at_node u hdomain.injOn hx

/-- The degree-`<k` polynomial line obtained by interpolating the two received-word coordinates
on one packed core. -/
noncomputable def packedLine
    {F : Type} [Field F] {k : Nat}
    (domain : Coord k → F) (u₀ u₁ : Coord k → F) (p : CoreIndex k) : F[X] × F[X] :=
  (interpolant domain u₀ (core p), interpolant domain u₁ (core p))

theorem packedLine_degreeLT
    {F : Type} [Field F] {k : Nat}
    (domain : Coord k → F) (hdomain : Function.Injective domain)
    (u₀ u₁ : Coord k → F) (p : CoreIndex k) :
    (packedLine domain u₀ u₁ p).1 ∈ Polynomial.degreeLT F k ∧
      (packedLine domain u₀ u₁ p).2 ∈ Polynomial.degreeLT F k := by
  exact ⟨interpolant_mem_degreeLT domain u₀ (core p) hdomain (core_card p),
    interpolant_mem_degreeLT domain u₁ (core p) hdomain (core_card p)⟩

/-- **Polynomial realization of the packing.**  Against any shared received stack and any
injective field embedding of the `4k` coordinates, every packed set is contained in the literal
joint core of its degree-`<k` Lagrange-interpolated line. -/
theorem core_subset_jointCore_packedLine
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : Nat}
    (domain : Coord k ↪ F) (u₀ u₁ : Coord k → F) (p : CoreIndex k) :
    core p ⊆ jointCore domain u₀ u₁
      (packedLine (fun x => domain x) u₀ u₁ p).1
      (packedLine (fun x => domain x) u₀ u₁ p).2 := by
  intro x hx
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨interpolant_eval_of_mem (fun x => domain x) u₀ (core p)
      domain.injective hx,
    interpolant_eval_of_mem (fun x => domain x) u₁ (core p)
      domain.injective hx⟩

/-! ## Explicitly distinct nodal line parameters -/

/-- The root polynomial of the base block with the coordinate `i` deleted. -/
noncomputable def erasedBaseNodal
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F) (i : Fin k) : F[X] :=
  Lagrange.nodal (Finset.univ.erase i) (fun j => domain (basePoint j))

theorem erasedBaseNodal_eval_self_ne_zero
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (hdomain : Function.Injective domain) (i : Fin k) :
    (erasedBaseNodal domain i).eval (domain (basePoint i)) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro j hj h
  have hij : i = j := basePoint_injective (hdomain h)
  exact (Finset.mem_erase.mp hj).1 hij.symm

theorem erasedBaseNodal_eval_other_eq_zero
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    {i j : Fin k} (hij : i ≠ j) :
    (erasedBaseNodal domain j).eval (domain (basePoint i)) = 0 := by
  unfold erasedBaseNodal
  change Polynomial.eval ((fun t : Fin k => domain (basePoint t)) i)
    (Lagrange.nodal (Finset.univ.erase j)
      (fun t : Fin k => domain (basePoint t))) = 0
  exact Lagrange.eval_nodal_at_node
    (R := F) (s := Finset.univ.erase j)
    (v := fun t : Fin k => domain (basePoint t))
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

/-- Two weighted copies of every erased-base nodal polynomial. -/
noncomputable def nodalParameter
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (p : CoreIndex k) : F[X] :=
  C (weight p.1) * erasedBaseNodal domain p.2

theorem nodalParameter_mem_degreeLT
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0) (p : CoreIndex k) :
    nodalParameter domain weight p ∈ Polynomial.degreeLT F k := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  have hnodal : erasedBaseNodal domain p.2 ∈ Polynomial.degreeLT F k := by
    rw [Polynomial.mem_degreeLT, erasedBaseNodal, Lagrange.degree_nodal,
      Finset.card_erase_of_mem (Finset.mem_univ p.2), Finset.card_univ]
    rw [Fintype.card_fin]
    exact_mod_cast (Nat.sub_lt (by omega : 0 < k) one_pos)
  rw [nodalParameter, ← Polynomial.smul_eq_C_mul]
  exact (Polynomial.degreeLT F k).smul_mem (weight p.1) hnodal

/-- **The `2k` nodal polynomial parameters are genuinely distinct.** -/
theorem nodalParameter_injective
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (hdomain : Function.Injective domain)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (hweightInj : Function.Injective weight) :
    Function.Injective (nodalParameter domain weight : CoreIndex k → F[X]) := by
  intro p q hpq
  by_cases hi : p.2 = q.2
  · have heval := congrArg
      (fun f : F[X] => f.eval (domain (basePoint p.2))) hpq
    simp only [nodalParameter, eval_mul, eval_C] at heval
    rw [hi] at heval
    have hn := erasedBaseNodal_eval_self_ne_zero domain hdomain q.2
    have hw : weight p.1 = weight q.1 := by
      exact mul_right_cancel₀ hn heval
    exact Prod.ext (hweightInj hw) hi
  · have heval := congrArg
      (fun f : F[X] => f.eval (domain (basePoint p.2))) hpq
    simp only [nodalParameter, eval_mul, eval_C] at heval
    rw [erasedBaseNodal_eval_other_eq_zero domain hi] at heval
    have hleft : weight p.1 *
        (erasedBaseNodal domain p.2).eval (domain (basePoint p.2)) ≠ 0 :=
      mul_ne_zero (hweight p.1)
        (erasedBaseNodal_eval_self_ne_zero domain hdomain p.2)
    rw [mul_zero] at heval
    exact (hleft heval).elim

end ArkLib.ProximityGap.Frontier.P1HalfBillionCorePackingNoGo

open ArkLib.ProximityGap.Frontier.P1HalfBillionCorePackingNoGo

#print axioms core_card
#print axioms core_injective
#print axioms inter_card_lt
#print axioms production_core_count
#print axioms production_coord_count
#print axioms production_matching_lower_fits
#print axioms interpolant_mem_degreeLT
#print axioms packedLine_degreeLT
#print axioms core_subset_jointCore_packedLine
#print axioms nodalParameter_mem_degreeLT
#print axioms nodalParameter_injective
