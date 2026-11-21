/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass

/-! # Site selection and label counts on sixteen equal power fibers -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SixteenFiberMass
open _root_.ProximityGap
variable (s : ℕ)

/-- Residue class modulo sixteen, followed by a position in its fiber. -/
abbrev Grid := Σ _ : Fin 16, Fin s
/-- Enumerate the production domain in fiber order. -/
noncomputable def index : Grid s ≃ Fin (16*s) :=
  (Equiv.sigmaEquivProd _ _).trans (((Equiv.prodComm _ _).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm s 16)))


/-- The scaled power is constant on each of the sixteen residue classes. -/
theorem power {F : Type} [Field F] (D : Fin (16*s) ↪ F) (u g : F) (hu : u ≠ 0)
    (hg : orderOf g = 16*s) (hd : ∀ i, D i = u*g^i.val) (z : Grid s) :
    (u⁻¹ * D (index s z))^s = (g^s)^z.1.val := by
  rw [hd, inv_mul_cancel_left₀ hu]
  change (g^(z.1.val + 16*z.2.val))^s = _
  have h : 16*z.2.val*s = 16*s*z.2.val := by ac_rfl
  have hgen : g^(16*s)=1 := hg ▸ pow_orderOf_eq_one g
  have hr : (g^(16*z.2.val))^s = 1 := by rw [← pow_mul, h, pow_mul, hgen, one_pow]
  rw [pow_add, mul_pow, hr, mul_one, ← pow_mul, Nat.mul_comm, pow_mul]

variable (cut : Fin 16 → ℕ)

private noncomputable def lower (j : Fin 16) : Finset (Fin s) :=
  univ.filter (fun r => r.val < cut j)

private theorem card_lower (cut_le : ∀ j, cut j ≤ s) (j : Fin 16) : (lower s cut j).card = cut j := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le j)]

/-- Select independently the two pieces cut from each power fiber. -/
abbrev Selection := Fin 16 → Bool → Bool

private noncomputable def row (take : Selection) (j : Fin 16) : Finset (Fin s) :=
  (if take j false then lower s cut j else ∅) ∪ (if take j true then (lower s cut j)ᶜ else ∅)

/-- Concrete sites selected by the two-piece rule. -/
noncomputable def selected (take : Selection) : Finset (Fin (16*s)) :=
  (univ.sigma (row s cut take)).map (index s).toEmbedding

/-- Count the selected sites in their sixteen disjoint fibers. -/
theorem card_selected (cut_le : ∀ j, cut j ≤ s) (take : Selection) :
    (selected s cut take).card = ∑ j : Fin 16,
      ((if take j false then cut j else 0) + (if take j true then s - cut j else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro j _
  cases h1 : take j false <;> cases h2 : take j true <;>
    simp [row, h1, h2, card_lower s cut cut_le, card_compl, Nat.add_sub_of_le (cut_le j)]

/-- Decide membership directly in residue and fiber coordinates. -/
theorem mem_selected (take : Selection) (u : Grid s) :
    index s u ∈ selected s cut take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) := by
  classical
  change (index s).toEmbedding u ∈ (univ.sigma (row s cut take)).map (index s).toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]


variable {heads : ℕ} (group : Fin 16 → Finset (Fin heads)) (own : Fin 16 → Fin heads)

private def rootSel : Selection := fun _ high => !high
private def coreSel (i : Fin heads) : Selection := fun r high => !high || decide (i∈group r)
/-- Common roots selected by the cut in each fiber. -/
def roots := selected s cut rootSel
/-- Sites where a head is prescribed to agree with the received pair. -/
def core (i : Fin heads) := selected s cut (coreSel group i)
/-- The common roots are the first cut sites in each fiber. -/
theorem card_roots (cut_le : ∀ j, cut j ≤ s) :
    (roots s cut).card = ∑ j, cut j := by
  rw [roots, card_selected s cut cut_le]
  simp [rootSel]

/-- A meeting contributes the entire fiber to its head. Every other fiber contributes its roots. -/
theorem card_core (cut_le : ∀ j, cut j ≤ s) (i : Fin heads) :
    (core s cut group i).card = ∑ j, (if i ∈ group j then s else cut j) := by
  rw [core, card_selected s cut cut_le]
  apply sum_congr rfl
  intro j _
  by_cases h : i ∈ group j <;> simp [coreSel, h, Nat.add_sub_of_le (cut_le j)]

/-- Head assigned to each physical site. -/
def owner (x : Fin (16*s)) : Fin heads := own ((index s).symm x).1

private def sel (u : Grid s) := decide (cut u.1 ≤ u.2.val)
private theorem origin (u : Grid s) : index s u∈roots s cut ↔ sel s cut u=false := by
  rw [roots,mem_selected s]; simp [rootSel,sel]
private theorem inside (u : Grid s) (i : Fin heads) : index s u∈core s cut group i ↔ sel s cut u=false ∨ i∈group u.1 := by
  rw [core,mem_selected s]; simp [coreSel,sel]

/-- Selected off-root sites supplying one fresh scalar for a head. -/
def fresh (labels : Fin 16 → Finset (Fin heads)) (i : Fin heads) : Finset (Fin (16*s)) :=
  selected s cut (fun j high => high && decide (i ∈ labels j))

private theorem outside (labels : Fin 16 → Finset (Fin heads)) (z : Grid s) (i : Fin heads) :
    index s z ∈ fresh s cut labels i ↔ sel s cut z = true ∧ i ∈ labels z.1 := by
  rw [fresh, mem_selected]
  simp [sel]

/-- Convert quotient-level incidences and distinct chosen directions to a bad
stack. A received value may lie outside every head on a selected fiber. -/
theorem selected_mass {F : Type} [Field F] [Fintype F] [NeZero s]
    (D : Fin (16*s) ↪ F) (k d : ℕ) (δ : ℝ≥0) (A B : Fin heads → F[X])
    (U V : Fin heads → Fin 16 → F) (u v : Fin 16 → F) (labels : Fin 16 → Finset (Fin heads))
    (hu : ∀ i (z : Grid s), (A i).eval (D (index s z)) = U i z.1)
    (hv : ∀ i (z : Grid s), (B i).eval (D (index s z)) = V i z.1)
    (agree : ∀ r i, i ∈ group r → U i r = u r ∧ V i r = v r)
    (miss : ∀ r i, i ∈ labels r → V i r ≠ v r)
    (sep : ∀ r i j, i ∈ labels r → j ∈ labels r → i ≠ j →
      (u r-U i r)*(V j r-v r) ≠ (u r-U j r)*(V i r-v r))
    (degree : (roots s cut).card+d+1 < k)
    (da : ∀ i, (A i).natDegree ≤ d) (db : ∀ i, (B i).natDegree ≤ d)
    (large : ∀ i, k ≤ (core s cut group i).card)
    (size : ∀ i, (1-δ) * (Fintype.card (Fin (16*s)) : ℝ≥0) ≤ (((core s cut group i).card+1 : ℕ) : ℝ≥0))
    (field : (∑ i, (fresh s cut labels i).card).choose 2 ≤ Nat.card F) :
    ((∑ i, (fresh s cut labels i).card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code D k : Set (Fin (16*s) → F)) δ := by
  apply PlanarQuartetMass.selected_mass D k d δ A B (roots s cut)
    (fun x => u ((index s).symm x).1) (fun x => v ((index s).symm x).1)
    (core s cut group) (fresh s cut labels) degree da db
  · intro i
    apply Finset.disjoint_left.mpr
    intro x hx hr
    obtain ⟨z, rfl⟩ := (index s).surjective x
    have h₁ := ((outside s cut labels z i).mp hx).1
    have h₂ := (origin s cut z).mp hr
    simp_all
  · intro i x hx hr
    obtain ⟨z, rfl⟩ := (index s).surjective x
    simpa only [hu, hv, Equiv.symm_apply_apply] using
      agree z.1 i (((inside s cut group z i).mp hx).resolve_left (fun h => hr ((origin s cut z).mpr h)))
  · intro i x hx
    obtain ⟨z, rfl⟩ := (index s).surjective x
    simpa only [hv, Equiv.symm_apply_apply] using miss z.1 i (((outside s cut labels z i).mp hx).2)
  · intro x i j hi hj ne
    obtain ⟨z, rfl⟩ := (index s).surjective x
    simpa only [hu, hv, Equiv.symm_apply_apply] using
      sep z.1 i j (((outside s cut labels z i).mp hi).2) (((outside s cut labels z j).mp hj).2) ne
  · exact large
  · exact size
  · exact field

/-- Apply the simultaneous planar label count using only residue-level comparison data. -/
theorem mass {F : Type} [Field F] [Fintype F] [NeZero s] (D : Fin (16*s) ↪ F) (k d : ℕ) (δ : ℝ≥0)
    (A B : Fin heads → F[X]) (U V : Fin heads → Fin 16 → F)
    (hu : ∀ i (z : Grid s), (A i).eval (D (index s z)) = U i z.1)
    (hv : ∀ i (z : Grid s), (B i).eval (D (index s z)) = V i z.1)
    (agree : ∀ r i, i ∈ group r → U i r = U (own r) r ∧ V i r = V (own r) r)
    (miss : ∀ r i, i ∉ group r → V i r ≠ V (own r) r)
    (sep : ∀ r i j, i ∉ group r → j ∉ group r → i ≠ j →
      (U (own r) r - U i r) * (V j r - V (own r) r) ≠
      (U (own r) r - U j r) * (V i r - V (own r) r))
    (degree : (roots s cut).card + d + 1 < k)
    (da : ∀ i, (A i).natDegree ≤ d) (db : ∀ i, (B i).natDegree ≤ d)
    (large : ∀ i, k ≤ (core s cut group i).card)
    (size : ∀ i, (1-δ) * (Fintype.card (Fin (16*s)) : ℝ≥0) ≤ (((core s cut group i).card+1 : ℕ) : ℝ≥0))
    (field : (∑ i, (core s cut group i)ᶜ.card).choose 2 ≤ Nat.card F) :
    ((∑ i, (core s cut group i)ᶜ.card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code D k : Set (Fin (16*s) → F)) δ := by
  let labels (r : Fin 16) := (group r)ᶜ
  have hsets (i : Fin heads) : fresh s cut labels i = (core s cut group i)ᶜ := by
    ext x
    obtain ⟨z, rfl⟩ := (index s).surjective x
    simp only [outside, mem_compl, inside]
    cases sel s cut z <;> simp [labels]
  have h := selected_mass s cut group D k d δ A B U V (fun r => U (own r) r)
    (fun r => V (own r) r) labels hu hv agree (fun r i hi => miss r i (mem_compl.mp hi))
    (fun r i j hi hj => sep r i j (mem_compl.mp hi) (mem_compl.mp hj)) degree da db large size
    (by simpa only [hsets] using field)
  simpa only [hsets] using h

end ArkLib.ProximityGap.Frontier.SixteenFiberMass
