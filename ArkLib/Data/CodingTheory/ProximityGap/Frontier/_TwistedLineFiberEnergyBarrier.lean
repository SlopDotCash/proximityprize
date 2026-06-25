/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.TwistedLineCollisionParseval

set_option linter.style.longLine false

/-!
# Bounded fibers improve twisted-line energy, but only at the L²/counting level

`TwistedLineCollisionParseval` proves that the twisted annihilator-line energy

  `∑ t, ‖∑ x∈S, ψ(t * φ x)‖²`

is exactly `q` times the number of colliding phase pairs `(x,y) ∈ S × S` with
`φ x = φ y`.  This file records the next structural corollary: if every phase fiber over a point
of `S` has size at most `L`, then the collision count is at most `|S| * L`, so the energy is at
most `q * |S| * L`.

This is useful negative information for issue #464.  Bounded-degree or bounded-fold monomial graph
directions really do buy a better *energy* estimate than the crude `q * |S|²`; however the result is
still a collision-count/L² statement.  It does not turn the line-period average into the missing
uniform L∞ bound on a worst offset/frequency.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.TwistedLineCollisionParseval

namespace ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [DecidableEq ι]

/-- The colliding phase pairs for a finite phase map. -/
def phaseCollisionPairs (S : Finset ι) (φ : ι → F) : Finset (ι × ι) :=
  (S ×ˢ S).filter (fun p => φ p.1 = φ p.2)

/-- The fiber, restricted to `S`, through the phase value of `x`. -/
def phaseFiberThrough (S : Finset ι) (φ : ι → F) (x : ι) : Finset ι :=
  S.filter (fun y => φ y = φ x)

/-- **Finite-fiber collision bound.**

If every restricted phase fiber through a point of `S` has at most `L` elements, then the number of
colliding pairs is at most `|S| * L`: choose the first coordinate freely, then choose the second
coordinate inside the fiber through the first. -/
theorem phaseCollisionPairs_card_le_card_mul_fiberCap (S : Finset ι) (φ : ι → F) {L : ℕ}
    (hfiber : ∀ x ∈ S, (phaseFiberThrough S φ x).card ≤ L) :
    (phaseCollisionPairs S φ).card ≤ S.card * L := by
  classical
  let C := phaseCollisionPairs S φ
  have hsplit :
      C.card = ∑ x ∈ S, (C.filter (fun p : ι × ι => p.1 = x)).card := by
    have hmaps : (C : Set (ι × ι)).MapsTo (fun p : ι × ι => p.1) S := by
      intro p hp
      simpa [C, phaseCollisionPairs] using (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    exact Finset.card_eq_sum_card_fiberwise (s := C) (t := S)
      (f := fun p : ι × ι => p.1) hmaps
  rw [hsplit]
  calc
    (∑ x ∈ S, (C.filter (fun p : ι × ι => p.1 = x)).card)
        ≤ ∑ x ∈ S, L := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hfiber_card :
              (C.filter (fun p : ι × ι => p.1 = x)).card ≤
                (phaseFiberThrough S φ x).card := by
            refine Finset.card_le_card_of_injOn (fun p : ι × ι => p.2) ?hmaps ?hinj
            · intro p hp
              rcases Finset.mem_filter.mp hp with ⟨hpC, hp1⟩
              rcases Finset.mem_filter.mp hpC with ⟨hpProd, hcoll⟩
              have hp2 : p.2 ∈ S := (Finset.mem_product.mp hpProd).2
              have hphase : φ p.2 = φ x := by
                rw [← hcoll, hp1]
              exact Finset.mem_filter.mpr ⟨hp2, hphase⟩
            · intro p hp q hq hpq
              rcases Finset.mem_filter.mp hp with ⟨_, hp1⟩
              rcases Finset.mem_filter.mp hq with ⟨_, hq1⟩
              exact Prod.ext (hp1.trans hq1.symm) hpq
          exact hfiber_card.trans (hfiber x hx)
    _ = S.card * L := by
      simp

/-- If a separate argument has bounded the collision count, Parseval immediately converts it into
an energy bound.  This isolates the exact consumer needed from any geometric fiber-counting lemma. -/
theorem twistedLineEnergy_le_of_collisionCount_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) {M : ℕ}
    (hcoll : (phaseCollisionPairs S φ).card ≤ M) :
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 ≤ (Fintype.card F : ℝ) * M := by
  rw [twistedLineEnergy_eq_collisionCount hψ S φ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast hcoll

/-- **Bounded fibers give `q * |S| * L` twisted-line energy.**

This is the sharpened collision-count consequence for bounded-fold directions. -/
theorem twistedLineEnergy_le_card_mul_fiberCap {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) {L : ℕ}
    (hfiber : ∀ x ∈ S, (phaseFiberThrough S φ x).card ≤ L) :
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 ≤
      (Fintype.card F : ℝ) * (S.card : ℝ) * (L : ℝ) := by
  have hcoll := phaseCollisionPairs_card_le_card_mul_fiberCap (S := S) (φ := φ) hfiber
  calc
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2
        ≤ (Fintype.card F : ℝ) * (S.card * L : ℕ) :=
          twistedLineEnergy_le_of_collisionCount_le hψ S φ hcoll
    _ = (Fintype.card F : ℝ) * (S.card : ℝ) * (L : ℝ) := by
      norm_num
      ring

/-- Dividing by the `q` line parameters, bounded fibers give average squared period at most
`|S| * L`.  This is the honest averaged conclusion; it is not a worst-frequency estimate. -/
theorem twistedLineEnergy_average_le_card_mul_fiberCap {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) {L : ℕ}
    (hfiber : ∀ x ∈ S, (phaseFiberThrough S φ x).card ≤ L) (hq : 0 < Fintype.card F) :
    (∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2) / (Fintype.card F : ℝ)
      ≤ (S.card : ℝ) * (L : ℝ) := by
  rw [twistedLineEnergy_eq_collisionCount hψ S φ]
  have hcoll := phaseCollisionPairs_card_le_card_mul_fiberCap (S := S) (φ := φ) hfiber
  have hqne : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    ((Fintype.card F : ℝ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card) /
        (Fintype.card F : ℝ)
        = ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card := by
          field_simp [hqne]
    _ = (phaseCollisionPairs S φ).card := by
      rfl
    _ ≤ (S.card : ℝ) * (L : ℝ) := by
      exact_mod_cast hcoll

/-! ## Monomial graph specialization -/

/-- The monomial-graph phase `x ↦ a*x + b*x^j`. -/
def monomialPhase (a b : F) (j : ℕ) (x : F) : F :=
  a * x + b * x ^ j

/-- The level-set polynomial for the monomial phase.  Its roots are exactly the level set
`a*y + b*y^j = c`. -/
noncomputable def monomialPhaseLevelPoly (a b c : F) (j : ℕ) : F[X] :=
  C b * X ^ j + C a * X - C c

/-- Evaluation of the level-set polynomial gives the phase difference. -/
theorem monomialPhaseLevelPoly_eval (a b : F) (j : ℕ) (x y : F) :
    (monomialPhaseLevelPoly a b (monomialPhase a b j x) j).eval y =
      monomialPhase a b j y - monomialPhase a b j x := by
  simp [monomialPhaseLevelPoly, monomialPhase]
  ring

/-- The level-set polynomial has degree at most `j` once the linear term is no larger than the
monomial term (`1 ≤ j`). -/
theorem monomialPhaseLevelPoly_natDegree_le (a b c : F) {j : ℕ} (hj : 1 ≤ j) :
    (monomialPhaseLevelPoly a b c j).natDegree ≤ j := by
  have hb : (C b * X ^ j : F[X]).natDegree ≤ j := natDegree_C_mul_X_pow_le b j
  have ha : (C a * X : F[X]).natDegree ≤ j := by
    simpa [pow_one] using (natDegree_C_mul_X_pow_le a 1).trans hj
  have hsum : (C b * X ^ j + C a * X : F[X]).natDegree ≤ j :=
    natDegree_add_le_of_degree_le hb ha
  have hc : (C c : F[X]).natDegree ≤ j := by
    simp
  simpa [monomialPhaseLevelPoly] using natDegree_sub_le_of_le hsum hc

/-- For `j ≥ 2`, a nonzero top coefficient makes the level-set polynomial nonzero. -/
theorem monomialPhaseLevelPoly_ne_zero_of_top {a b c : F} {j : ℕ}
    (hj : 2 ≤ j) (hb : b ≠ 0) :
    monomialPhaseLevelPoly a b c j ≠ 0 := by
  intro hzero
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  have hcoeff : (monomialPhaseLevelPoly a b c j).coeff j = b := by
    simp [monomialPhaseLevelPoly, coeff_X_of_ne_one hj1, coeff_C_ne_zero hj0]
  have : b = 0 := by
    rw [← hcoeff, hzero, coeff_zero]
  exact hb this

/-- A monomial phase fiber is bounded by the degree of its level-set polynomial. -/
theorem monomialPhase_fiber_card_le_natDegree (S : Finset F) (a b : F) (j : ℕ) (x : F)
    (hpoly : monomialPhaseLevelPoly a b (monomialPhase a b j x) j ≠ 0) :
    (phaseFiberThrough S (monomialPhase a b j) x).card
      ≤ (monomialPhaseLevelPoly a b (monomialPhase a b j x) j).natDegree := by
  classical
  let P := monomialPhaseLevelPoly a b (monomialPhase a b j x) j
  have hsub : phaseFiberThrough S (monomialPhase a b j) x ⊆ P.roots.toFinset := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨_hyS, hyphase⟩
    rw [Multiset.mem_toFinset, mem_roots]
    · rw [IsRoot, monomialPhaseLevelPoly_eval]
      exact sub_eq_zero.mpr hyphase
    · exact hpoly
  calc
    (phaseFiberThrough S (monomialPhase a b j) x).card
        ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- For a genuine nonlinear monomial term (`j ≥ 2`, `b ≠ 0`), every restricted phase fiber has
size at most `j`. -/
theorem monomialPhase_fiber_card_le_degree (S : Finset F) (a b : F) {j : ℕ}
    (hj : 2 ≤ j) (hb : b ≠ 0) (x : F) :
    (phaseFiberThrough S (monomialPhase a b j) x).card ≤ j := by
  have hj1 : 1 ≤ j := le_trans (by norm_num : 1 ≤ 2) hj
  exact (monomialPhase_fiber_card_le_natDegree S a b j x
    (monomialPhaseLevelPoly_ne_zero_of_top (a := a) (b := b)
      (c := monomialPhase a b j x) hj hb)).trans
    (monomialPhaseLevelPoly_natDegree_le a b (monomialPhase a b j x) hj1)

/-- **Concrete twisted-line energy for monomial graph phases.**

For `φ(x)=a*x+b*x^j` with `j ≥ 2` and `b ≠ 0`, the abstract bounded-fiber barrier gives
`energy ≤ q * |S| * j`. -/
theorem twistedLineEnergy_le_monomialPhase_degree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset F) (a b : F) {j : ℕ} (hj : 2 ≤ j) (hb : b ≠ 0) :
    ∑ t : F, ‖twistedLineEta ψ S (monomialPhase a b j) t‖ ^ 2
      ≤ (Fintype.card F : ℝ) * (S.card : ℝ) * (j : ℝ) :=
  twistedLineEnergy_le_card_mul_fiberCap hψ S (monomialPhase a b j)
    (fun x _hx => monomialPhase_fiber_card_le_degree S a b hj hb x)

/-- The corresponding average squared period is at most `|S| * j`. -/
theorem twistedLineEnergy_average_le_monomialPhase_degree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset F) (a b : F) {j : ℕ} (hj : 2 ≤ j) (hb : b ≠ 0)
    (hq : 0 < Fintype.card F) :
    (∑ t : F, ‖twistedLineEta ψ S (monomialPhase a b j) t‖ ^ 2) /
        (Fintype.card F : ℝ)
      ≤ (S.card : ℝ) * (j : ℝ) :=
  twistedLineEnergy_average_le_card_mul_fiberCap hψ S (monomialPhase a b j)
    (fun x _hx => monomialPhase_fiber_card_le_degree S a b hj hb x) hq

end ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.phaseCollisionPairs_card_le_card_mul_fiberCap
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.twistedLineEnergy_le_of_collisionCount_le
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.twistedLineEnergy_le_card_mul_fiberCap
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.twistedLineEnergy_average_le_card_mul_fiberCap
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.monomialPhaseLevelPoly_eval
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.monomialPhaseLevelPoly_natDegree_le
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.monomialPhaseLevelPoly_ne_zero_of_top
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.monomialPhase_fiber_card_le_natDegree
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.monomialPhase_fiber_card_le_degree
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.twistedLineEnergy_le_monomialPhase_degree
#print axioms ArkLib.ProximityGap.TwistedLineFiberEnergyBarrier.twistedLineEnergy_average_le_monomialPhase_degree
