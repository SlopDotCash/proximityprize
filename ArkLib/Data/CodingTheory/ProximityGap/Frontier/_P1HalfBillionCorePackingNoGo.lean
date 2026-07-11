/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph
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
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

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

theorem addedPoint_injective {k : Nat} : Function.Injective (@addedPoint k) := by
  intro p q h
  have hp : addedPoint p ∈ core q := by
    rw [h]
    exact addedPoint_mem_core q
  exact (addedPoint_mem_core_iff p q).mp hp

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

theorem nodalParameter_natDegree_lt
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0) (p : CoreIndex k) :
    (nodalParameter domain weight p).natDegree < k := by
  rw [nodalParameter, Polynomial.natDegree_C_mul (hweight p.1),
    erasedBaseNodal, Lagrange.natDegree_nodal,
    Finset.card_erase_of_mem (Finset.mem_univ p.2), Finset.card_univ]
  simp only [Fintype.card_fin]
  exact Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) p.2.isLt) one_pos

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

/-! ## Simultaneous shared-stack realization -/

/-- A shared received word: zero on the base block, and at each indexed spare point the value of
its own nodal parameter.  The sum form avoids choosing a partial inverse to `addedPoint`. -/
noncomputable def nodalReceived
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (x : Coord k) : F :=
  ∑ p : CoreIndex k,
    if addedPoint p = x then (nodalParameter domain weight p).eval (domain x) else 0

@[simp]
theorem nodalReceived_basePoint
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (i : Fin k) :
    nodalReceived domain weight (basePoint i) = 0 := by
  apply Finset.sum_eq_zero
  intro p _hp
  rw [if_neg]
  intro h
  have hfirst := congrArg (fun x : Coord k => x.1.val) h
  simp [addedPoint, basePoint] at hfirst

@[simp]
theorem nodalReceived_addedPoint
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (p : CoreIndex k) :
    nodalReceived domain weight (addedPoint p) =
      (nodalParameter domain weight p).eval (domain (addedPoint p)) := by
  rw [nodalReceived, Fintype.sum_eq_single p]
  · simp
  · intro q hpq
    rw [if_neg]
    exact fun h => hpq (addedPoint_injective h)

/-- Every explicit nodal parameter agrees with the one shared received word on its packed core. -/
theorem nodalParameter_agrees_on_core
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (p : CoreIndex k) :
    ∀ x ∈ core p,
      (nodalParameter domain weight p).eval (domain x) =
        nodalReceived domain weight x := by
  intro x hx
  simp only [core, Finset.mem_insert, Finset.mem_erase] at hx
  rcases hx with rfl | hx
  · exact (nodalReceived_addedPoint domain weight p).symm
  · obtain ⟨hxp, hxbase⟩ := hx
    simp only [base, Finset.mem_map, Finset.mem_univ, true_and] at hxbase
    obtain ⟨i, rfl⟩ := hxbase
    change (nodalParameter domain weight p).eval (domain (basePoint i)) =
      nodalReceived domain weight (basePoint i)
    rw [nodalReceived_basePoint]
    simp only [nodalParameter, eval_mul, eval_C, mul_eq_zero]
    have hip : i ≠ p.2 := by
      intro h
      subst i
      exact hxp rfl
    exact Or.inr (erasedBaseNodal_eval_other_eq_zero domain hip)

/-- The explicit polynomial line with nodal intercept and zero slope. -/
noncomputable def nodalLine
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (p : CoreIndex k) : F[X] × F[X] :=
  (nodalParameter domain weight p, 0)

theorem nodalLine_injective
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (hdomain : Function.Injective domain)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (hweightInj : Function.Injective weight) :
    Function.Injective (nodalLine domain weight : CoreIndex k → F[X] × F[X]) := by
  intro p q h
  apply nodalParameter_injective domain hdomain weight hweight hweightInj
  exact congrArg Prod.fst h

/-- **Simultaneous polynomial-line realization.**  All `2k` distinct nodal lines use the same
received stack `(nodalReceived,0)`, and the prescribed packed core is contained in the literal
joint core of its line. -/
theorem core_subset_jointCore_nodalLine
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : Nat}
    (domain : Coord k ↪ F) (weight : Fin 2 → F) (p : CoreIndex k) :
    core p ⊆ jointCore domain (nodalReceived (fun x => domain x) weight) (fun _ => 0)
      (nodalLine (fun x => domain x) weight p).1
      (nodalLine (fun x => domain x) weight p).2 := by
  intro x hx
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and,
    nodalLine, eval_zero]
  exact ⟨nodalParameter_agrees_on_core (fun x => domain x) weight p x hx, trivial⟩

/-! ## A half-billion large-core lines through one fixed lifted centre -/

/-- Couple the first received coordinate to the nodal received slope so that every line passes
through the same lifted centre `(delta,qDelta)`. -/
noncomputable def pencilReceived₀
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (delta : F) (qDelta : F[X]) (x : Coord k) : F :=
  qDelta.eval (domain x) - delta * nodalReceived domain weight x

/-- The line of nodal slope `r_p` through the common lifted centre `(delta,qDelta)`. -/
noncomputable def nodalPencilLine
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (delta : F) (qDelta : F[X])
    (p : CoreIndex k) : F[X] × F[X] :=
  (qDelta - C delta * nodalParameter domain weight p,
    nodalParameter domain weight p)

/-- Every nodal pencil line passes through the same lifted centre. -/
@[simp]
theorem nodalPencilLine_at_centre
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (delta : F) (qDelta : F[X]) (p : CoreIndex k) :
    (nodalPencilLine domain weight delta qDelta p).1 +
      C delta * (nodalPencilLine domain weight delta qDelta p).2 = qDelta := by
  simp [nodalPencilLine]

/-- **Simultaneous common-centre realization.**  The same received stack supports the prescribed
`k`-point packed core for every nodal pencil line. -/
theorem core_subset_jointCore_nodalPencilLine
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : Nat}
    (domain : Coord k ↪ F) (weight : Fin 2 → F) (delta : F) (qDelta : F[X])
    (p : CoreIndex k) :
    core p ⊆ jointCore domain
      (pencilReceived₀ (fun x => domain x) weight delta qDelta)
      (nodalReceived (fun x => domain x) weight)
      (nodalPencilLine (fun x => domain x) weight delta qDelta p).1
      (nodalPencilLine (fun x => domain x) weight delta qDelta p).2 := by
  intro x hx
  have hagree := nodalParameter_agrees_on_core
    (fun x => domain x) weight p x hx
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and,
    nodalPencilLine, pencilReceived₀, eval_sub, eval_mul, eval_C]
  constructor
  · rw [hagree]
  · exact hagree

/-- Distinct nodal slopes remain distinct lines after forcing the common centre. -/
theorem nodalPencilLine_injective
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (hdomain : Function.Injective domain)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (hweightInj : Function.Injective weight) (delta : F) (qDelta : F[X]) :
    Function.Injective
      (nodalPencilLine domain weight delta qDelta : CoreIndex k → F[X] × F[X]) := by
  intro p q h
  apply nodalParameter_injective domain hdomain weight hweight hweightInj
  exact congrArg Prod.snd h

/-- If the common centre polynomial has degree `<k`, then both coordinates of every pencil line
also have degree `<k`. -/
theorem nodalPencilLine_degreeLT
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (delta : F) (qDelta : F[X]) (hqDelta : qDelta ∈ Polynomial.degreeLT F k)
    (p : CoreIndex k) :
    (nodalPencilLine domain weight delta qDelta p).1 ∈ Polynomial.degreeLT F k ∧
      (nodalPencilLine domain weight delta qDelta p).2 ∈ Polynomial.degreeLT F k := by
  have hr := nodalParameter_mem_degreeLT domain weight hweight p
  constructor
  · simp only [nodalPencilLine]
    apply (Polynomial.degreeLT F k).sub_mem hqDelta
    rw [← Polynomial.smul_eq_C_mul]
    exact (Polynomial.degreeLT F k).smul_mem delta hr
  · exact hr

/-- Each common-centre line has a joint core of size at least `k`. -/
theorem nodalPencilLine_core_card_ge
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : Nat}
    (domain : Coord k ↪ F) (weight : Fin 2 → F) (delta : F) (qDelta : F[X])
    (p : CoreIndex k) :
    k ≤ (jointCore domain
      (pencilReceived₀ (fun x => domain x) weight delta qDelta)
      (nodalReceived (fun x => domain x) weight)
      (nodalPencilLine (fun x => domain x) weight delta qDelta p).1
      (nodalPencilLine (fun x => domain x) weight delta qDelta p).2).card := by
  calc
    k = (core p).card := (core_card p).symm
    _ ≤ _ := Finset.card_le_card
      (core_subset_jointCore_nodalPencilLine domain weight delta qDelta p)

/-! ## Canonical secant realization and the exact threshold deficit -/

/-- Family-free form of the canonical polynomial secant used by `secantParameter`. -/
noncomputable def rawSecantParameter
    {F : Type} [Field F] (gamma beta : F) (qGamma qBeta : F[X]) : F[X] × F[X] :=
  let r := slopePolynomial gamma beta qGamma qBeta
  (qGamma - C gamma * r, r)

/-- Two distinct scalar witnesses decoded by the same polynomial have that polynomial as their
canonical secant intercept and zero canonical slope. -/
theorem rawSecantParameter_same_polynomial
    {F : Type} [Field F] (gamma beta : F) (q : F[X]) :
    rawSecantParameter gamma beta q q = (q, 0) := by
  simp [rawSecantParameter, slopePolynomial]

/-- Every explicit nodal line is therefore a literal canonical secant of any two scalar labels
that are decoded by its common nodal polynomial. -/
theorem rawSecantParameter_nodal
    {F : Type} [Field F] {k : Nat} (domain : Coord k → F)
    (weight : Fin 2 → F) (p : CoreIndex k) (gamma beta : F) :
    rawSecantParameter gamma beta
      (nodalParameter domain weight p) (nodalParameter domain weight p) =
        nodalLine domain weight p := by
  exact rawSecantParameter_same_polynomial gamma beta (nodalParameter domain weight p)

/-- A line is recovered exactly as the canonical secant of its values at any two distinct
scalars. -/
theorem rawSecantParameter_lineValues
    {F : Type} [Field F] {gamma beta : F} (hne : gamma ≠ beta)
    (line : F[X] × F[X]) :
    rawSecantParameter gamma beta
      (line.1 + C gamma * line.2) (line.1 + C beta * line.2) = line := by
  have hslope : slopePolynomial gamma beta
      (line.1 + C gamma * line.2) (line.1 + C beta * line.2) = line.2 := by
    simp only [slopePolynomial]
    rw [show line.1 + C gamma * line.2 - (line.1 + C beta * line.2) =
        C (gamma - beta) * line.2 by rw [C_sub]; ring]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]
  simp only [rawSecantParameter, hslope]
  apply Prod.ext
  · simp only
    ring
  · rfl

/-- **Coupled two-route compatibility no-go.**  Put both outside lifted endpoints on one nodal
pencil line and route each back to the common centre.  Both cross-secants and the outside pair's
original secant are literally the same line, which still carries its prescribed `k`-core in the
shared received stack.  Thus even exact compatibility of two routed `k`-core secants does not
cluster the family. -/
theorem nodalPencilLine_two_routes_and_original
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : Nat}
    (domain : Coord k ↪ F) (weight : Fin 2 → F)
    {gamma beta delta : F} (hgd : gamma ≠ delta) (hbd : beta ≠ delta)
    (hgb : gamma ≠ beta) (qDelta : F[X]) (p : CoreIndex k) :
    let line := nodalPencilLine (fun x => domain x) weight delta qDelta p
    rawSecantParameter gamma delta
        (line.1 + C gamma * line.2) qDelta = line ∧
      rawSecantParameter beta delta
        (line.1 + C beta * line.2) qDelta = line ∧
      rawSecantParameter gamma beta
        (line.1 + C gamma * line.2) (line.1 + C beta * line.2) = line ∧
      k ≤ (jointCore domain
        (pencilReceived₀ (fun x => domain x) weight delta qDelta)
        (nodalReceived (fun x => domain x) weight) line.1 line.2).card := by
  let line := nodalPencilLine (fun x => domain x) weight delta qDelta p
  change rawSecantParameter gamma delta
      (line.1 + C gamma * line.2) qDelta = line ∧
    rawSecantParameter beta delta
      (line.1 + C beta * line.2) qDelta = line ∧
    rawSecantParameter gamma beta
      (line.1 + C gamma * line.2) (line.1 + C beta * line.2) = line ∧
    k ≤ (jointCore domain
      (pencilReceived₀ (fun x => domain x) weight delta qDelta)
      (nodalReceived (fun x => domain x) weight) line.1 line.2).card
  have hcentre : line.1 + C delta * line.2 = qDelta := by
    exact nodalPencilLine_at_centre (fun x => domain x) weight delta qDelta p
  have hgamma : rawSecantParameter gamma delta
      (line.1 + C gamma * line.2) qDelta = line := by
    rw [← hcentre]
    exact rawSecantParameter_lineValues hgd line
  have hbeta : rawSecantParameter beta delta
      (line.1 + C beta * line.2) qDelta = line := by
    rw [← hcentre]
    exact rawSecantParameter_lineValues hbd line
  have horiginal : rawSecantParameter gamma beta
      (line.1 + C gamma * line.2) (line.1 + C beta * line.2) = line :=
    rawSecantParameter_lineValues hgb line
  have hcore : k ≤ (jointCore domain
      (pencilReceived₀ (fun x => domain x) weight delta qDelta)
      (nodalReceived (fun x => domain x) weight) line.1 line.2).card := by
    exact nodalPencilLine_core_card_ge domain weight delta qDelta p
  exact ⟨hgamma, hbeta, horiginal, hcore⟩

/-- Literal P1 predecessor agreement threshold. -/
abbrev T : Nat := 592794966

/-- The construction's guaranteed `K`-core falls short of a threshold witness by exactly
`324359510` coordinates.  This is the sole remaining quantitative gap in the abstract
canonical-secant construction. -/
theorem production_threshold_deficit : T - K = 324359510 := by
  norm_num [T, K]

theorem production_core_strictly_below_threshold : K < T := by
  norm_num [T, K]

/-! ## Threshold amplification of the repeated-polynomial pairs is impossible -/

open P1RateQuarterAgreementOverlapGraph

/-- Symbolic five-line obstruction.  The displayed arithmetic inequality is exactly the sharp
five-set integral Johnson contradiction for a `4k`-point domain, weight `t`, and pair cap `k-1`. -/
theorem not_five_nodalLines_all_of_integralJohnson
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k t : Nat} (harith : 6 * (4 * k) + 20 * (k - 1) < 20 * t)
    (domain : Coord k ↪ F)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (hweightInj : Function.Injective weight)
    (index : Fin 5 → CoreIndex k) (hindex : Function.Injective index) :
    ¬ ∀ i : Fin 5, t ≤
      (jointCore domain (nodalReceived (fun x => domain x) weight) (fun _ => 0)
        (nodalLine (fun x => domain x) weight (index i)).1
        (nodalLine (fun x => domain x) weight (index i)).2).card := by
  intro hcore
  let line : Fin 5 → F[X] × F[X] := fun i =>
    nodalLine (fun x => domain x) weight (index i)
  have hline : Function.Injective line :=
    (nodalLine_injective (fun x => domain x) domain.injective weight hweight
      hweightInj).comp hindex
  have hdeg : ∀ i, (line i).1.natDegree < k ∧ (line i).2.natDegree < k := by
    intro i
    constructor
    · change (nodalParameter (fun x => domain x) weight (index i)).natDegree < k
      exact nodalParameter_natDegree_lt (fun x => domain x) weight hweight (index i)
    · simp only [line, nodalLine, natDegree_zero]
      exact lt_of_le_of_lt (Nat.zero_le _) (index i).2.isLt
  let D : Fin 5 → Finset (Coord k) := fun i =>
    jointCore domain (nodalReceived (fun x => domain x) weight) (fun _ => 0)
      (line i).1 (line i).2
  have hpair : ∀ i j : Fin 5, i ≠ j → (D i ∩ D j).card ≤ k - 1 := by
    intro i j hij
    have hne : (line i).1 ≠ (line j).1 ∨ (line i).2 ≠ (line j).2 := by
      by_contra hnot
      push Not at hnot
      exact hline.ne hij (Prod.ext hnot.1 hnot.2)
    exact jointCore_inter_card_le_of_line_ne domain
      (nodalReceived (fun x => domain x) weight) (fun _ => 0)
      (k := k) (lt_of_le_of_lt (by omega : 0 ≤ (index i).2.val) (index i).2.isLt)
      (hdeg i).1 (hdeg i).2 (hdeg j).1 (hdeg j).2 hne
  have hJ := fiveSet_integral_johnson D hcore hpair
  simp only [Fintype.card_prod, Fintype.card_fin] at hJ
  omega

/-- **Five-line threshold-amplification no-go at literal P1.**  Choose any five distinct packed
indices and the corresponding distinct nodal lines.  They cannot all have threshold-size joint
cores against the shared received stack. -/
theorem not_five_nodalLines_all_threshold
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Coord K ↪ F)
    (weight : Fin 2 → F) (hweight : ∀ b, weight b ≠ 0)
    (hweightInj : Function.Injective weight)
    (index : Fin 5 → CoreIndex K) (hindex : Function.Injective index) :
    ¬ ∀ i : Fin 5, T ≤
      (jointCore domain (nodalReceived (fun x => domain x) weight) (fun _ => 0)
        (nodalLine (fun x => domain x) weight (index i)).1
        (nodalLine (fun x => domain x) weight (index i)).2).card := by
  apply not_five_nodalLines_all_of_integralJohnson
    (k := K) (t := T) (by norm_num [K, T]) domain weight hweight hweightInj index hindex

/-! ## Pair-local threshold amplification is combinatorially feasible -/

/-- Two disjoint extensions of prescribed size exist outside `C` whenever the complement has
twice that many points. -/
theorem exists_two_disjoint_extensions
    {X : Type} [Fintype X] [DecidableEq X]
    (C : Finset X) (d : Nat) (hroom : 2 * d ≤ Fintype.card X - C.card) :
    ∃ E₀ E₁ : Finset X,
      E₀ ⊆ Finset.univ \ C ∧ E₁ ⊆ Finset.univ \ C ∧
      Disjoint E₀ E₁ ∧ E₀.card = d ∧ E₁.card = d := by
  let U := Finset.univ \ C
  have hUcard : U.card = Fintype.card X - C.card := by
    simp [U, Finset.card_sdiff]
  have hdU : d ≤ U.card := by omega
  obtain ⟨E₀, hE₀U, hE₀card⟩ := Finset.exists_subset_card_eq hdU
  have hremain : d ≤ (U \ E₀).card := by
    rw [Finset.card_sdiff_of_subset hE₀U, hE₀card, hUcard]
    omega
  obtain ⟨E₁, hE₁remain, hE₁card⟩ := Finset.exists_subset_card_eq hremain
  refine ⟨E₀, E₁, hE₀U, hE₁remain.trans Finset.sdiff_subset, ?_, hE₀card, hE₁card⟩
  exact Finset.disjoint_left.mpr fun x hx₀ hx₁ =>
    (Finset.mem_sdiff.mp (hE₁remain hx₁)).2 hx₀

/-- Adding disjoint outside extensions to a common core preserves exactly that intersection. -/
theorem core_union_extensions_inter
    {X : Type} [Fintype X] [DecidableEq X] (C E₀ E₁ : Finset X)
    (hE₀ : E₀ ⊆ Finset.univ \ C) (hE₁ : E₁ ⊆ Finset.univ \ C)
    (hdisj : Disjoint E₀ E₁) :
    (C ∪ E₀) ∩ (C ∪ E₁) = C := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hxC | hx₀, hxC' | hx₁⟩
    · exact hxC
    · exact hxC
    · exact hxC'
    · exact (Finset.disjoint_left.mp hdisj hx₀ hx₁).elim
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

/-- The exact number of coordinates used by two threshold witnesses meeting in a `K`-core. -/
theorem production_two_threshold_union_size : 2 * T - K = 917154476 := by
  norm_num [T, K]

/-- Exact remaining ambient slack for one threshold pair. -/
theorem production_two_threshold_union_slack : N - (2 * T - K) = 156587348 := by
  norm_num [N, T, K]

/-- **Pair-local amplification exists.**  Every packed `K`-core extends to two subsets of the
`N=4K` domain, each of cardinality exactly `T`, whose intersection is exactly the original core.
Thus the threshold obstruction is not local to one differing-polynomial secant; it is the
simultaneous compatibility of many such pairs. -/
theorem exists_threshold_pair_with_intersection_core (p : CoreIndex K) :
    ∃ A B : Finset (Coord K), A.card = T ∧ B.card = T ∧ A ∩ B = core p := by
  have hroom : 2 * (T - K) ≤ Fintype.card (Coord K) - (core p).card := by
    rw [coord_card, core_card]
    norm_num [T, K]
  obtain ⟨E₀, E₁, hE₀, hE₁, hdisj, hE₀card, hE₁card⟩ :=
    exists_two_disjoint_extensions (core p) (T - K) hroom
  refine ⟨core p ∪ E₀, core p ∪ E₁, ?_, ?_,
    core_union_extensions_inter (core p) E₀ E₁ hE₀ hE₁ hdisj⟩
  · rw [Finset.card_union_of_disjoint]
    · rw [core_card, hE₀card]
      norm_num [T, K]
    · exact Finset.disjoint_left.mpr fun x hxC hxE =>
        (Finset.mem_sdiff.mp (hE₀ hxE)).2 hxC
  · rw [Finset.card_union_of_disjoint]
    · rw [core_card, hE₁card]
      norm_num [T, K]
    · exact Finset.disjoint_left.mpr fun x hxC hxE =>
        (Finset.mem_sdiff.mp (hE₁ hxE)).2 hxC

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
#print axioms nodalReceived_addedPoint
#print axioms nodalParameter_agrees_on_core
#print axioms nodalLine_injective
#print axioms core_subset_jointCore_nodalLine
#print axioms nodalPencilLine_at_centre
#print axioms core_subset_jointCore_nodalPencilLine
#print axioms nodalPencilLine_injective
#print axioms nodalPencilLine_degreeLT
#print axioms nodalPencilLine_core_card_ge
#print axioms rawSecantParameter_same_polynomial
#print axioms rawSecantParameter_nodal
#print axioms rawSecantParameter_lineValues
#print axioms nodalPencilLine_two_routes_and_original
#print axioms production_threshold_deficit
#print axioms not_five_nodalLines_all_of_integralJohnson
#print axioms not_five_nodalLines_all_threshold
#print axioms exists_two_disjoint_extensions
#print axioms exists_threshold_pair_with_intersection_core
