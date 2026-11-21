/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.SixteenFiberMass

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

/-- Coordinates in the sixteen fibers of the named production domain. -/
abbrev Grid := SixteenFiberMass.Grid S
/-- Enumeration in fiber order. -/
abbrev index := SixteenFiberMass.index S
/-- Selection of the two pieces in each fiber. -/
abbrev Selection := SixteenFiberMass.Selection
/-- Physical sites for a selection. -/
abbrev selected := SixteenFiberMass.selected S
/-- Count selected sites. -/
theorem card_selected (cut : Fin 16 → ℕ) (cut_le : ∀ j, cut j ≤ S) (take : Selection) :
    (selected cut take).card = ∑ j, ((if take j false then cut j else 0) +
      (if take j true then S - cut j else 0)) := SixteenFiberMass.card_selected S cut cut_le take
/-- Membership in a selected set. -/
theorem mem_selected (cut : Fin 16 → ℕ) (take : Selection) (u : Grid) :
    index u ∈ selected cut take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) :=
  SixteenFiberMass.mem_selected S cut take u

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


variable (cut : Fin 16 → ℕ) {heads : ℕ} (group : Fin 16 → Finset (Fin heads)) (own : Fin 16 → Fin heads)

/-- Selected common roots. -/
abbrev roots := SixteenFiberMass.roots S cut
/-- All defining agreements for a head. -/
abbrev core := SixteenFiberMass.core S cut group
/-- Owner of a physical site. -/
abbrev owner := SixteenFiberMass.owner S own

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
      epsMCA (F := F) (ReedSolomon.code D k : Set (Fin N → F)) δ :=
  SixteenFiberMass.mass S cut group own D k d δ A B U V hu hv agree miss sep degree da db large size field

end ArkLib.ProximityGap.Frontier.SecondPrimeSixteenFiber
