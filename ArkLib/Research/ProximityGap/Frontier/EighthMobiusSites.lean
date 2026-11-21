/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseMobius

/-! # Physical sites of the transverse eighth-rate four-head construction

Every site is an exponent `j+32r`. Each residue class has at most two different
tags, separated by the displayed cut. Cardinality calculations use the two
interval lengths in each of the 32 fibers.
-/

namespace ArkLib.ProximityGap.Frontier.EighthMobiusSites
open Finset EighthTransverseMobius
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev s : ℕ := 33554432
abbrev Site := Fin 1073741824
abbrev Grid := Σ _ : Fin 32, Fin s

/-- Tags describe shared roots, pair and marked sites, and private owners. -/
inductive Tag where
  | p01 | p02 | p12 | root | markU | markV | solo0 | solo1 | solo2 | solo3
  deriving DecidableEq, Repr

open Tag

instance : Fintype Tag where
  elems := {p01, p02, p12, root, markU, markV, solo0, solo1, solo2, solo3}
  complete := by intro z; cases z <;> decide

/-- Send the residue and position to the actual exponent in the order-`2^30` group. -/
def index : Grid ≃ Site :=
  (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

def fiber (i : Site) : Fin 32 := (index.symm i).1
def position (i : Site) : Fin s := (index.symm i).2

theorem index_val (j : Fin 32) (r : Fin s) : (index ⟨j, r⟩).val = j.val + 32 * r.val := rfl

theorem fiber_mod (i : Site) : (fiber i).val = i.val % 32 := by
  obtain ⟨⟨j, r⟩, rfl⟩ := index.surjective i
  simp only [fiber, Equiv.symm_apply_apply, index_val]
  omega

/-- Fiber cut, lower tag, upper tag. Equal tags cover the entire residue fiber. -/
private def parts : Fin 32 → ℕ × Tag × Tag := ![
  (0, p01, p01), (1, markU, solo0), (0, p01, p01), (1, markV, solo0),
  (0, p02, p02), (0, solo2, solo2), (0, p12, p12), (0, solo2, solo2),
  (0, solo2, solo2), (0, solo2, solo2), (0, p12, p12), (25165823, solo2, solo3),
  (0, solo3, solo3), (0, solo3, solo3), (0, p12, p12), (0, solo3, solo3),
  (0, p01, p01), (0, solo3, solo3), (0, p02, p02), (0, solo3, solo3),
  (0, p02, p02), (0, solo3, solo3), (0, solo3, solo3), (16777214, solo3, solo1),
  (0, solo0, solo0), (0, solo0, solo0), (25165827, solo0, solo1), (0, solo1, solo1),
  (0, solo1, solo1), (0, solo1, solo1), (0, solo1, solo1), (33554430, root, solo1)]

private def cut (j : Fin 32) := (parts j).1
private def tagAt (j : Fin 32) (upper : Bool) := if upper then (parts j).2.2 else (parts j).2.1

def tag (i : Site) : Tag := tagAt (fiber i) (decide (cut (fiber i) ≤ (position i).val))

def owns : Tag → Fin 4 → Bool
  | p01, h => h != 2
  | p02, h => h == 0 || h == 2
  | p12, h => h == 1 || h == 2
  | root, _ => true
  | markU, h | markV, h => h == 2 || h == 3
  | solo0, h => h == 0
  | solo1, h => h == 1
  | solo2, h => h == 2
  | solo3, h => h == 3

/-- Head providing the actual received pair at a site. -/
def ownerTag : Tag → Fin 4
  | p01 | p02 | root | solo0 => 0
  | p12 | solo1 => 1
  | markU | markV | solo2 => 2
  | solo3 => 3

def owner (i : Site) : Fin 4 := ownerTag (tag i)

/-- The first map is the linear label, the next two have fixed poles, and the
remaining thirteen have poles indexed by their indicated residue class. -/
def scheduled (l : Fin 16) (j : Fin 32) (z : Tag) : Bool :=
  if l = 0 then z != root && z != solo3
  else if l = 1 then z == p02 || z == solo0 || z == solo3
  else if l = 2 then z == p12 || z == solo1 || z == solo3
  else (z == solo2 || z == solo3) && j == variableFiber ⟨l.val - 3, by omega⟩

/-- Fresh head meeting the owner after folding at the scheduled label. -/
def foreignTag (l : Fin 16) (z : Tag) : Fin 4 :=
  if l = 0 then match z with
    | p01 => 2
    | p02 | solo0 => 1
    | _ => 0
  else if z = solo3 then (if l = 1 then 0 else if l = 2 then 1 else 2)
  else 3

def foreign (l : Fin 16) (i : Site) := foreignTag l (tag i)

private def lower (j : Fin 32) : Finset (Fin s) := univ.filter (fun r => r.val < cut j)
private def row (sel : Fin 32 → Tag → Bool) (j : Fin 32) : Finset (Fin s) :=
  (if sel j (tagAt j false) then lower j else ∅) ∪
    (if sel j (tagAt j true) then (lower j)ᶜ else ∅)

private def selected (sel : Fin 32 → Tag → Bool) : Finset Site :=
  (univ.sigma (row sel)).map index.toEmbedding

private theorem mem_selected (sel : Fin 32 → Tag → Bool) (i : Site) :
    i ∈ selected sel ↔ sel (fiber i) (tag i) := by
  obtain ⟨⟨j, r⟩, rfl⟩ := index.surjective i
  change index.toEmbedding ⟨j, r⟩ ∈ (univ.sigma (row sel)).map index.toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [tag, fiber, position, Equiv.symm_apply_apply, mem_sigma, mem_univ, true_and]
  by_cases h : r.val < cut j
  · have h' := Nat.not_le.mpr h
    cases a : sel j (tagAt j false) <;> cases b : sel j (tagAt j true)
      <;> simp [row, lower, h, h', a, b]
  · have h' := Nat.le_of_not_gt h
    cases a : sel j (tagAt j false) <;> cases b : sel j (tagAt j true)
      <;> simp [row, lower, h, h', a, b]

private def count (sel : Fin 32 → Tag → Bool) : ℕ := ∑ j : Fin 32,
  ((if sel j (tagAt j false) then cut j else 0) + (if sel j (tagAt j true) then s - cut j else 0))

private theorem card_selected (sel : Fin 32 → Tag → Bool) : (selected sel).card = count sel := by
  rw [selected, card_map, card_sigma, count]
  apply sum_congr rfl
  intro j _
  have hcuts : ∀ j : Fin 32, cut j ≤ s := by decide
  have hlow : (lower j).card = cut j := by
    rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (hcuts j)]
  cases a : sel j (tagAt j false) <;> cases b : sel j (tagAt j true) <;>
    simp [row, a, b, card_compl, hlow, Nat.add_sub_of_le (hcuts j)]

def core (h : Fin 4) : Finset Site := selected (fun _ z => owns z h)
def roots : Finset Site := selected (fun _ z => z == root)
def loci (l : Fin 16) : Finset Site := selected (scheduled l)

theorem mem_core {h : Fin 4} {i : Site} : i ∈ core h ↔ owns (tag i) h := mem_selected _ _
theorem mem_roots {i : Site} : i ∈ roots ↔ tag i = root := by simp [roots, mem_selected]
theorem mem_loci {l : Fin 16} {i : Site} : i ∈ loci l ↔ scheduled l (fiber i) (tag i) :=
  mem_selected _ _

theorem card_core (h : Fin 4) : (core h).card = 394264575 := by
  rw [core, card_selected]
  exact (by decide : ∀ h : Fin 4, count (fun _ z => owns z h) = 394264575) h

theorem card_roots : roots.card = 33554430 := by rw [roots, card_selected]; decide

theorem total_loci : ∑ l : Fin 16, (loci l).card = 2239758337 := by
  simp_rw [loci, card_selected]
  decide

theorem foreign_outside {l : Fin 16} {i : Site} (hi : i ∈ loci l) : i ∉ core (foreign l i) := by
  rw [mem_core]
  have checked : ∀ (z : Tag) (l : Fin 16) (j : Fin 32),
      scheduled l j z → ¬ owns z (foreignTag l z) := by
    intro z
    cases z <;> decide
  exact checked (tag i) l (fiber i) (mem_loci.mp hi)

theorem variable_fiber {l : Fin 16} {i : Site} (hl : 3 ≤ l.val) (hi : i ∈ loci l) :
    fiber i = variableFiber ⟨l.val - 3, by omega⟩ := by
  have h0 : l ≠ 0 := by intro h; subst l; norm_num at hl
  have h1 : l ≠ 1 := by intro h; subst l; norm_num at hl
  have h2 : l ≠ 2 := by intro h; subst l; norm_num at hl
  have h := mem_loci.mp hi
  simp only [scheduled, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem marks (i : Site) (z : Tag) (j : Fin 32)
    (h : ∀ (a : Fin 32) (b : Bool), tagAt a b = z ↔ a = j ∧ b = false)
    (hcut : cut j = 1) : tag i = z ↔ i.val = j.val := by
  obtain ⟨⟨a, r⟩, rfl⟩ := index.surjective i
  simp only [tag, fiber, position, Equiv.symm_apply_apply, h, index_val, decide_eq_false_iff_not]
  constructor
  · rintro ⟨rfl, hr⟩
    rw [hcut] at hr
    omega
  · intro hi
    have hj := j.isLt
    have ha := a.isLt
    have har : a.val = j.val := by omega
    have he := Fin.ext har
    subst j
    exact ⟨rfl, by rw [hcut]; omega⟩

theorem markU_iff {i : Site} : tag i = markU ↔ i.val = 1 := marks i markU 1 (by decide) (by decide)
theorem markV_iff {i : Site} : tag i = markV ↔ i.val = 3 := marks i markV 3 (by decide) (by decide)

/-- Pair tags occupy whole fibers; all their sites and only their sites receive the indicated tag. -/
theorem pair_tags (i : Site) :
    (tag i = p01 ↔ fiber i ∈ ({0, 2, 16} : Finset (Fin 32))) ∧
    (tag i = p02 ↔ fiber i ∈ ({4, 18, 20} : Finset (Fin 32))) ∧
    (tag i = p12 ↔ fiber i ∈ ({6, 10, 14} : Finset (Fin 32))) := by
  exact (by decide : ∀ (j : Fin 32) (b : Bool),
    (tagAt j b = p01 ↔ j ∈ ({0, 2, 16} : Finset (Fin 32))) ∧
    (tagAt j b = p02 ↔ j ∈ ({4, 18, 20} : Finset (Fin 32))) ∧
    (tagAt j b = p12 ↔ j ∈ ({6, 10, 14} : Finset (Fin 32)))) _ _

/-- Variable fractional directions occur on private third- or fourth-head sites. -/
theorem variable_tag {l : Fin 16} {i : Site} (hl : 3 ≤ l.val) (hi : i ∈ loci l) :
    tag i = solo2 ∨ tag i = solo3 := by
  have all : ∀ (l : Fin 16) (j : Fin 32) (z : Tag),
      3 ≤ l.val → scheduled l j z → z = solo2 ∨ z = solo3 := by decide
  exact all l (fiber i) (tag i) hl (mem_loci.mp hi)

/-- The selected common roots are the first `2^25-2` positions in residue 31. -/
theorem roots_iff {i : Site} : i ∈ roots ↔ fiber i = 31 ∧ (position i).val < 33554430 := by
  have h : ∀ (j : Fin 32) (b : Bool), tagAt j b = root ↔ j = 31 ∧ b = false := by decide
  rw [mem_roots, tag, h, decide_eq_false_iff_not, Nat.not_le]
  constructor <;> rintro ⟨hj, hr⟩
  · exact ⟨hj, by simpa only [hj, show cut 31 = 33554430 by decide] using hr⟩
  · exact ⟨hj, by simpa only [hj, show cut 31 = 33554430 by decide] using hr⟩

/-- Common monic vanisher on the actual second-prime evaluation points. -/
noncomputable def locator : Polynomial SecondPrimeSmoothSeed.F :=
  Lagrange.nodal roots SecondPrimeSmoothSeed.dom

local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

theorem locator_natDegree : locator.natDegree = 33554430 := by
  rw [locator, Lagrange.natDegree_nodal, card_roots]

theorem locator_eval {i : Site} : locator.eval (SecondPrimeSmoothSeed.dom i) = 0 ↔ i ∈ roots := by
  simp [locator, Lagrange.eval_nodal, Finset.prod_eq_zero_iff, sub_eq_zero,
    SecondPrimeSmoothSeed.dom.injective.eq_iff]

/-- Every scheduled incidence lies outside the common locator. -/
theorem locus_nonroot {l : Fin 16} {i : Site} (hi : i ∈ loci l) : i ∉ roots := by
  intro hr
  have outside := foreign_outside hi
  apply outside
  rw [mem_core, mem_roots.mp hr]
  rfl

theorem owner_mem_core (i : Site) : i ∈ core (owner i) := by
  rw [mem_core]
  change owns (tag i) (ownerTag (tag i)) = true
  cases tag i <;> decide

/-- The `2^25` power used to evaluate the cubic rows depends only on the residue. -/
theorem power_fiber {F : Type*} [CommMonoid F] (g : F) (hg : g ^ 1073741824 = 1) (i : Site) :
    (g ^ i.val) ^ s = (g ^ s) ^ (fiber i).val := by
  obtain ⟨⟨j, r⟩, rfl⟩ := index.surjective i
  simp only [fiber, Equiv.symm_apply_apply, index_val, pow_add, mul_pow]
  have ex : 32 * r.val * s = 1073741824 * r.val := by change _ = (32 * s) * _; ac_rfl
  have h := congrArg (fun x : F => x ^ r.val) hg
  rw [← pow_mul, ← ex, pow_mul, one_pow] at h
  rw [h, mul_one, ← pow_mul, Nat.mul_comm, pow_mul]

#print axioms card_core
#print axioms card_roots
#print axioms total_loci
end ArkLib.ProximityGap.Frontier.EighthMobiusSites
