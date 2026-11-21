/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientSignatureTables

/-! # Simultaneous original and rotated dyadic signatures on a common mask space -/

namespace ProximityGap.QuotientMaskSelections
open Finset QuotientSignatureCensus

/-- A complete binary tree of leaf labels. -/
def Leaves (α : Type*) : ℕ → Type _
  | 0 => α
  | d+1 => Leaves α d × Leaves α d

/-- One two-bit choice at each node of a complete tree. -/
def Mask : ℕ → Type
  | 0 => Choice
  | d+1 => Choice × (Mask d × Mask d)

instance maskFintype : (d : ℕ) → Fintype (Mask d)
  | 0 => inferInstanceAs (Fintype Choice)
  | d+1 => let _ := maskFintype d; inferInstanceAs (Fintype (Choice × (Mask d × Mask d)))

def root : (d : ℕ) → Mask d → Choice
  | 0, c => c
  | _+1, c => c.1

def count : (d : ℕ) → Mask d → ℕ
  | 0, c => occ c
  | d+1, (a,l,r) => occ a + (count d l + count d r)

def shape : (d : ℕ) → Leaves ℕ d → Option (Leaves ℕ d) → Tree
  | 0, v, w => .leaf v w
  | d+1, (v₁,v₂), w => .fork (shape d v₁ (w.map Prod.fst)) (shape d v₂ (w.map Prod.snd))

/-- The census and common selection spaces assign the same two root choices at each node. -/
def maskEquiv : (d : ℕ) → (v : Leaves ℕ d) → (w : Option (Leaves ℕ d)) →
    Mask d ≃ Choice × Tail (shape d v w)
  | 0, _, _ => ⟨fun c => (c, ()), Prod.fst, fun _ => rfl, fun _ => rfl⟩
  | d+1, (v₁,v₂), w => Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr (maskEquiv d v₁ (w.map Prod.fst)) (maskEquiv d v₂ (w.map Prod.snd)))

@[simp] theorem root_map (d : ℕ) (v : Leaves ℕ d) (w : Option (Leaves ℕ d)) (m : Mask d) :
    (maskEquiv d v w m).1 = root d m := by cases d <;> rfl

theorem count_map (d : ℕ) (v : Leaves ℕ d) (w : Option (Leaves ℕ d)) (m : Mask d) :
    fullSize (shape d v w) (maskEquiv d v w m) = count d m := by
  induction d with
  | zero => exact Nat.add_zero _
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    rcases v with ⟨u,v⟩
    change occ a + (fullSize _ (maskEquiv _ _ _ l) + fullSize _ (maskEquiv _ _ _ r)) = _
    rw [ih, ih]
    rfl

/-- All path sums after the current original and rotated occupancies have been added.
Negation exchanges the two occupancies at every sibling pair. -/
def traces : (d : ℕ) → ℕ → ℕ → Mask d → Leaves ℕ d × Leaves ℕ d
  | 0, x, y, _ => (x,y)
  | d+1, x, y, (_,l,r) =>
    let a := occ (root d l)
    let b := occ (root d r)
    let L := traces d (x+a) (y+b) l
    let R := traces d (x+b) (y+a) r
    ((L.1,R.1),(L.2,R.2))

def fits {α : Type*} : Option α → α → Prop
  | none, _ => True
  | some w, z => z = w

theorem accepted_iff (d : ℕ) (v : Leaves ℕ d) (w : Option (Leaves ℕ d)) (x y : ℕ) (m : Mask d) :
    accepted (shape d v w) x y (maskEquiv d v w m).2 = true ↔
      (traces d x y m).1 = v ∧ fits w (traces d x y m).2 := by
  induction d generalizing x y with
  | zero =>
    change ℕ at v
    change Option ℕ at w
    cases w with
    | none =>
      change ((decide (x = v) && true) = true) ↔ x = v ∧ True
      simp
    | some z =>
      change ((decide (x = v) && (z == y)) = true) ↔ x = v ∧ y = z
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact and_congr_right fun _ => eq_comm
  | succ d ih =>
    rcases m with ⟨_,l,r⟩
    rcases v with ⟨u,v⟩
    change (accepted _ (x + occ (maskEquiv d u (w.map Prod.fst) l).1)
        (y + occ (maskEquiv d v (w.map Prod.snd) r).1) (maskEquiv d u (w.map Prod.fst) l).2 &&
      accepted _ (x + occ (maskEquiv d v (w.map Prod.snd) r).1)
        (y + occ (maskEquiv d u (w.map Prod.fst) l).1) (maskEquiv d v (w.map Prod.snd) r).2) = true ↔ _
    simp only [root_map, Bool.and_eq_true, ih]
    let L := traces d (x+occ (root d l)) (y+occ (root d r)) l
    let R := traces d (x+occ (root d r)) (y+occ (root d l)) r
    cases w with
    | none =>
      change ((L.1=u ∧ True) ∧ (R.1=v ∧ True)) ↔ (L.1,R.1)=(u,v) ∧ True
      simp
    | some z =>
      rcases z with ⟨s,t⟩
      change ((L.1=u ∧ L.2=s) ∧ (R.1=v ∧ R.2=t)) ↔ (L.1,R.1)=(u,v) ∧ (L.2,R.2)=(s,t)
      simp only [Prod.mk.injEq]
      tauto

/-- Both physical signatures of the same selection. -/
def signatures (d : ℕ) (m : Mask d) : Leaves ℕ d × Leaves ℕ d :=
  traces d (occ (root d m)) (occ (root d m)) m

open scoped Classical in
/-- The kernel-certified tree census counts actual distinct masks on this common layout. -/
theorem card_signatures (d : ℕ) (v : Leaves ℕ d) (w : Option (Leaves ℕ d)) (s : ℕ) :
    (univ.filter fun m : Mask d => (signatures d m).1=v ∧
      fits w (signatures d m).2 ∧ count d m=s).card = population (shape d v w) s := by
  classical
  apply Finset.card_bij (fun m _ => maskEquiv d v w m)
  · intro m hm
    obtain ⟨ho,hr,hc⟩ := (mem_filter.mp hm).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · unfold fullAccepted
      rw [root_map, accepted_iff]
      exact ⟨ho,hr⟩
    · exact (count_map ..).trans hc
  · intro m hm n hn h
    exact (maskEquiv d v w).injective h
  · intro z hz
    let m := (maskEquiv d v w).symm z
    have e : maskEquiv d v w m = z := (maskEquiv d v w).apply_symm_apply _
    obtain ⟨ha,hs⟩ := (mem_filter.mp hz).2
    refine ⟨m,mem_filter.mpr ⟨mem_univ _,?_⟩,e⟩
    rw [← e] at ha hs
    unfold fullAccepted at ha
    rw [root_map, accepted_iff] at ha
    exact ⟨ha.1, ha.2, (count_map ..).symm.trans hs⟩

/-- Replace just the mask of the inverse pair at the current node. -/
def setRoot : (d : ℕ) → Choice → Mask d → Mask d
  | 0, a, _ => a
  | _+1, a, (_,l,r) => (a,l,r)

@[simp] theorem root_setRoot (d : ℕ) (a : Choice) (m : Mask d) :
    root d (setRoot d a m) = a := by cases d <;> rfl

@[simp] theorem setRoot_setRoot (d : ℕ) (a b : Choice) (m : Mask d) :
    setRoot d a (setRoot d b m) = setRoot d a m := by cases d <;> rfl

@[simp] theorem setRoot_root (d : ℕ) (m : Mask d) : setRoot d (root d m) m = m := by
  cases d <;> rfl

/-- Negation exchanges the occupied inverse pairs of siblings at every level. -/
def rotate : (d : ℕ) → Mask d → Mask d
  | 0, a => a
  | d+1, (a,l,r) => (a, setRoot d (root d r) (rotate d l), setRoot d (root d l) (rotate d r))

@[simp] theorem root_rotate (d : ℕ) (m : Mask d) : root d (rotate d m) = root d m := by
  cases d <;> rfl

@[simp] theorem rotate_setRoot (d : ℕ) (a : Choice) (m : Mask d) :
    rotate d (setRoot d a m) = setRoot d a (rotate d m) := by cases d <;> rfl

@[simp] theorem rotate_rotate (d : ℕ) (m : Mask d) : rotate d (rotate d m) = m := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    simp only [rotate, root_setRoot, rotate_setRoot, ih, setRoot_setRoot, setRoot_root]
    rfl

@[simp] theorem traces_setRoot (d : ℕ) (x y : ℕ) (a : Choice) (m : Mask d) :
    traces d x y (setRoot d a m) = traces d x y m := by cases d <;> rfl

theorem traces_rotate (d : ℕ) (m : Mask d) (x y : ℕ) :
    traces d y x (rotate d m) = (traces d x y m).swap := by
  induction d generalizing x y with
  | zero => rfl
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    simp only [rotate, traces, root_setRoot, traces_setRoot, ih, Prod.swap]

@[simp] theorem signatures_rotate (d : ℕ) (m : Mask d) :
    signatures d (rotate d m) = (signatures d m).swap := by
  unfold signatures
  rw [root_rotate, traces_rotate]

theorem count_setRoot (d : ℕ) (a : Choice) (m : Mask d) :
    count d (setRoot d a m) + occ (root d m) = occ a + count d m := by
  cases d with
  | zero => rfl
  | succ d =>
    rcases m with ⟨b,l,r⟩
    change occ a + (count d l + count d r) + occ b = occ a + (occ b + (count d l + count d r))
    omega

@[simp] theorem count_rotate (d : ℕ) (m : Mask d) : count d (rotate d m) = count d m := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    have hl := count_setRoot d (root d r) (rotate d l)
    have hr := count_setRoot d (root d l) (rotate d r)
    simp only [root_rotate, ih] at hl hr
    change occ a + (_+_) = occ a + (_+_)
    congr 1
    omega

open scoped Classical in
theorem card_rotated (d : ℕ) (v : Leaves ℕ d) (s : ℕ) :
    (univ.filter fun m : Mask d => (signatures d m).2=v ∧ count d m=s).card =
    population (shape d v none) s := by
  classical
  rw [← card_signatures]
  apply card_bij (fun m _ => rotate d m)
  · intro m hm
    simpa [signatures_rotate, fits] using hm
  · intro m hm n hn he
    simpa using congrArg (rotate d) he
  · intro m hm
    exact ⟨rotate d m, by simpa [signatures_rotate, fits] using hm, rotate_rotate ..⟩

#print axioms card_signatures
#print axioms card_rotated
end ProximityGap.QuotientMaskSelections
