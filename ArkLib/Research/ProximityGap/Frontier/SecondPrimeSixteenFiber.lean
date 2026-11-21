/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass

/-! # Selecting sites in the sixteen power fibers of the second production domain -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeSixteenFiber
open _root_.ProximityGap
open SecondPrimeSmoothSeed (F N dom w)
open PrizeShapePrimeP30Second (P prime_P orderOf_g)
local instance : Fact P.Prime := ⟨prime_P⟩
abbrev S : ℕ := 67108864

/-- Residue class modulo sixteen, followed by a position in its fiber. -/
abbrev Grid := Σ _ : Fin 16, Fin S
/-- Enumerate the production domain in fiber order. -/
noncomputable def index : Grid ≃ Fin N :=
  (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans finProdFinEquiv)


variable (cut : Fin 16 → ℕ)

private noncomputable def lower (j : Fin 16) : Finset (Fin S) :=
  univ.filter (fun r => r.val < cut j)

private theorem card_lower (cut_le : ∀ j, cut j ≤ S) (j : Fin 16) : (lower cut j).card = cut j := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le j)]

/-- Select independently the two pieces cut from each power fiber. -/
abbrev Selection := Fin 16 → Bool → Bool

private noncomputable def row (take : Selection) (j : Fin 16) : Finset (Fin S) :=
  (if take j false then lower cut j else ∅) ∪ (if take j true then (lower cut j)ᶜ else ∅)

/-- Concrete sites selected by the two-piece rule. -/
noncomputable def selected (take : Selection) : Finset (Fin N) :=
  (univ.sigma (row cut take)).map index.toEmbedding

/-- Count the selected sites in their sixteen disjoint fibers. -/
theorem card_selected (cut_le : ∀ j, cut j ≤ S) (take : Selection) :
    (selected cut take).card = ∑ j : Fin 16,
      ((if take j false then cut j else 0) + (if take j true then S - cut j else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro j _
  cases h1 : take j false <;> cases h2 : take j true <;>
    simp [row, h1, h2, card_lower cut cut_le, card_compl, Nat.add_sub_of_le (cut_le j)]

/-- Decide membership directly in residue and fiber coordinates. -/
theorem mem_selected (take : Selection) (u : Grid) :
    index u ∈ selected cut take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) := by
  classical
  change index.toEmbedding u ∈ (univ.sigma (row cut take)).map index.toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]


/-- The power map is constant on a residue fiber. -/
theorem power (u : Grid) : (dom (index u)) ^ S = w ^ u.1.val := by
  change (PrizeShapePrimeP30Second.g ^ (u.1.val + 16*u.2.val)) ^ S=_
  have hg : PrizeShapePrimeP30Second.g ^ N=1 := by
    simpa only [orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30Second.g
  have hr : (PrizeShapePrimeP30Second.g ^ (16*u.2.val)) ^ S=1 := by
    have h : 16*u.2.val*S=N*u.2.val := by change 16*u.2.val*67108864=(16*67108864)*u.2.val; ac_rfl
    rw [← pow_mul,h,pow_mul,hg,one_pow]
  have hw : PrizeShapePrimeP30Second.g ^ S=w := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  rw [pow_add,mul_pow,hr,mul_one,← pow_mul,Nat.mul_comm,pow_mul,hw]


variable {heads : ℕ} (group : Fin 16 → Finset (Fin heads)) (own : Fin 16 → Fin heads)

private def rootSel : Selection := fun _ high => !high
private def coreSel (i : Fin heads) : Selection := fun r high => !high || decide (i∈group r)
/-- Common roots selected by the cut in each fiber. -/
def roots := selected cut rootSel
/-- Sites where a head is prescribed to agree with the received pair. -/
def core (i : Fin heads) := selected cut (coreSel group i)
/-- Head assigned to each physical site. -/
def owner (x : Fin N) : Fin heads := own (index.symm x).1

private def sel (u : Grid) := decide (cut u.1 ≤ u.2.val)
private theorem origin (u : Grid) : index u∈roots cut ↔ sel cut u=false := by
  rw [roots,mem_selected]; simp [rootSel,sel]
private theorem inside (u : Grid) (i : Fin heads) : index u∈core cut group i ↔ sel cut u=false ∨ i∈group u.1 := by
  rw [core,mem_selected]; simp [coreSel,sel]

/-- Selected off-root sites supplying one fresh scalar for a head. -/
def fresh (labels : Fin 16 → Finset (Fin heads)) (i : Fin heads) : Finset (Fin N) :=
  selected cut (fun j high => high && decide (i ∈ labels j))

private theorem outside (labels : Fin 16 → Finset (Fin heads)) (s : Grid) (i : Fin heads) :
    index s ∈ fresh cut labels i ↔ sel cut s = true ∧ i ∈ labels s.1 := by
  rw [fresh, mem_selected]
  simp [sel]

/-- Convert quotient-level incidences and distinct chosen directions to a bad
stack. A received value may lie outside every head on a selected fiber. -/
theorem selected_mass {F : Type} [Field F] [Fintype F]
    (D : Fin N ↪ F) (k d : ℕ) (δ : ℝ≥0) (A B : Fin heads → F[X])
    (U V : Fin heads → Fin 16 → F) (u v : Fin 16 → F) (labels : Fin 16 → Finset (Fin heads))
    (hu : ∀ i (s : Grid), (A i).eval (D (index s)) = U i s.1)
    (hv : ∀ i (s : Grid), (B i).eval (D (index s)) = V i s.1)
    (agree : ∀ r i, i ∈ group r → U i r = u r ∧ V i r = v r)
    (miss : ∀ r i, i ∈ labels r → V i r ≠ v r)
    (sep : ∀ r i j, i ∈ labels r → j ∈ labels r → i ≠ j →
      (u r-U i r)*(V j r-v r) ≠ (u r-U j r)*(V i r-v r))
    (degree : (roots cut).card+d+1 < k)
    (da : ∀ i, (A i).natDegree ≤ d) (db : ∀ i, (B i).natDegree ≤ d)
    (large : ∀ i, k ≤ (core cut group i).card)
    (size : ∀ i, (1-δ) * (Fintype.card (Fin N) : ℝ≥0) ≤ (((core cut group i).card+1 : ℕ) : ℝ≥0))
    (field : (∑ i, (fresh cut labels i).card).choose 2 ≤ Nat.card F) :
    ((∑ i, (fresh cut labels i).card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code D k : Set (Fin N → F)) δ := by
  apply PlanarQuartetMass.selected_mass D k d δ A B (roots cut)
    (fun x => u (index.symm x).1) (fun x => v (index.symm x).1)
    (core cut group) (fresh cut labels) degree da db
  · intro i
    apply Finset.disjoint_left.mpr
    intro x hx hr
    obtain ⟨s, rfl⟩ := index.surjective x
    have h₁ := ((outside cut labels s i).mp hx).1
    have h₂ := (origin cut s).mp hr
    simp_all
  · intro i x hx hr
    obtain ⟨s, rfl⟩ := index.surjective x
    simpa only [hu, hv, Equiv.symm_apply_apply] using
      agree s.1 i (((inside cut group s i).mp hx).resolve_left (fun h => hr ((origin cut s).mpr h)))
  · intro i x hx
    obtain ⟨s, rfl⟩ := index.surjective x
    simpa only [hv, Equiv.symm_apply_apply] using miss s.1 i (((outside cut labels s i).mp hx).2)
  · intro x i j hi hj ne
    obtain ⟨s, rfl⟩ := index.surjective x
    simpa only [hu, hv, Equiv.symm_apply_apply] using
      sep s.1 i j (((outside cut labels s i).mp hi).2) (((outside cut labels s j).mp hj).2) ne
  · exact large
  · exact size
  · exact field

/-- Apply the simultaneous planar label count using only residue-level comparison data. -/
theorem mass {F : Type} [Field F] [Fintype F] (D : Fin N ↪ F) (k d : ℕ) (δ : ℝ≥0)
    (A B : Fin heads → F[X]) (U V : Fin heads → Fin 16 → F)
    (hu : ∀ i (s : Grid), (A i).eval (D (index s)) = U i s.1)
    (hv : ∀ i (s : Grid), (B i).eval (D (index s)) = V i s.1)
    (agree : ∀ r i, i ∈ group r → U i r = U (own r) r ∧ V i r = V (own r) r)
    (miss : ∀ r i, i ∉ group r → V i r ≠ V (own r) r)
    (sep : ∀ r i j, i ∉ group r → j ∉ group r → i ≠ j →
      (U (own r) r - U i r) * (V j r - V (own r) r) ≠
      (U (own r) r - U j r) * (V i r - V (own r) r))
    (degree : (roots cut).card + d + 1 < k)
    (da : ∀ i, (A i).natDegree ≤ d) (db : ∀ i, (B i).natDegree ≤ d)
    (large : ∀ i, k ≤ (core cut group i).card)
    (size : ∀ i, (1-δ) * (Fintype.card (Fin N) : ℝ≥0) ≤ (((core cut group i).card+1 : ℕ) : ℝ≥0))
    (field : (∑ i, (core cut group i)ᶜ.card).choose 2 ≤ Nat.card F) :
    ((∑ i, (core cut group i)ᶜ.card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code D k : Set (Fin N → F)) δ := by
  let labels (r : Fin 16) := (group r)ᶜ
  have hsets (i : Fin heads) : fresh cut labels i = (core cut group i)ᶜ := by
    ext x
    obtain ⟨s, rfl⟩ := index.surjective x
    simp only [outside, mem_compl, inside]
    cases h : sel cut s <;> simp [h, labels]
  have h := selected_mass cut group D k d δ A B U V (fun r => U (own r) r)
    (fun r => V (own r) r) labels hu hv agree (fun r i hi => miss r i (mem_compl.mp hi))
    (fun r i j hi hj => sep r i j (mem_compl.mp hi) (mem_compl.mp hj)) degree da db large size
    (by simpa only [hsets] using field)
  simpa only [hsets] using h

end ArkLib.ProximityGap.Frontier.SecondPrimeSixteenFiber
