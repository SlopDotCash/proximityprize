/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry
import Mathlib.Tactic

/-!
# P1 rate-quarter predecessor: exceptional-pair amplification

The six-set Plotkin argument says that six predecessor agreement sets cannot have all fifteen
pair intersections below `K`.  There is a much sharper *stability* statement when fourteen of
the pairs are already below `K`: the exceptional pair must overlap on at least

```text
Z₁ = 469762074.
```

The gain comes from the integer multiplicity inequality

```text
7s ≤ s² + 12,   0 ≤ s ≤ 6,
```

which is exact at multiplicities three and four.  Double counting gives

```text
18T ≤ 6N + sum_{i<j} |Sᵢ ∩ Sⱼ|.
```

If fourteen intersections are at most `K-1`, the fifteenth absorbs the entire excess.  This is
the quantitative bridge from a five-center independent set in the overlap graph to a genuinely
large source-pencil core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset
open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification

open GCXK25SecondMoment

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The sharp affine lower support for the second moment of six-set multiplicities. -/
theorem seven_mul_le_sq_add_twelve {s : Nat} (hs : s ≤ 6) :
    7 * s ≤ s ^ 2 + 12 := by
  interval_cases s <;> norm_num

/-- **Six-set exceptional-pair inequality.**  If all distinct intersections except possibly
`S 0 ∩ S 1` are at most `lambda`, then that exceptional intersection satisfies

`18z ≤ 6|U| + 14 lambda + |S 0 ∩ S 1|`.

Unlike the quadratic Plotkin quotient, this retains the integer multiplicity gain at the exact
six-set scale. -/
theorem sixSet_exceptionalPair_integral_johnson
    (S : Fin 6 → Finset U) {z lambda : Nat}
    (hsize : ∀ i, z ≤ (S i).card)
    (hpair : ∀ i j : Fin 6, i ≠ j →
      ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
        (S i ∩ S j).card ≤ lambda) :
    18 * z ≤
      6 * Fintype.card U + 14 * lambda + (S 0 ∩ S 1).card := by
  classical
  let I : Finset (Fin 6) := Finset.univ
  let mass : Nat := ∑ i : Fin 6, (S i).card
  let second : Nat := ∑ i : Fin 6, ∑ j : Fin 6, (S i ∩ S j).card
  let exceptional : Nat := (S 0 ∩ S 1).card
  have hmassLower : 6 * z ≤ mass := by
    change 6 * z ≤ ∑ i : Fin 6, (S i).card
    rw [show 6 * z = ∑ _i : Fin 6, z by simp]
    exact Finset.sum_le_sum (fun i _ => hsize i)
  have hmultBound : ∀ x : U, mult I S x ≤ 6 := by
    intro x
    calc
      mult I S x = (I.filter fun i => x ∈ S i).card := rfl
      _ ≤ I.card := Finset.card_filter_le _ _
      _ = 6 := by simp [I]
  have hfirstMoment : mass = ∑ x : U, mult I S x := by
    simpa [mass, I] using (sum_card_eq_sum_mult I S)
  have hsecondMoment : second = ∑ x : U, (mult I S x) ^ 2 := by
    simpa [second, I] using (sum_sum_card_inter_eq_sum_mult_sq I S)
  have hintegral : 7 * mass ≤ second + 12 * Fintype.card U := by
    rw [hfirstMoment, Finset.mul_sum]
    calc
      ∑ x : U, 7 * mult I S x
          ≤ ∑ x : U, ((mult I S x) ^ 2 + 12) :=
            Finset.sum_le_sum (fun x _ => seven_mul_le_sq_add_twelve (hmultBound x))
      _ = (∑ x : U, (mult I S x) ^ 2) + 12 * Fintype.card U := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
      _ = second + 12 * Fintype.card U := by rw [hsecondMoment]
  have hinner : ∀ i : Fin 6,
      (∑ j ∈ I.erase i, (S i ∩ S j).card) ≤
        if i = 0 ∨ i = 1 then exceptional + 4 * lambda else 5 * lambda := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      simp only [true_or, if_true]
      rw [← Finset.add_sum_erase (a := (1 : Fin 6)) (I.erase (0 : Fin 6))
        (fun j => (S 0 ∩ S j).card) (by simp [I])]
      apply Nat.add_le_add
      · exact le_rfl
      · calc
          ∑ j ∈ (I.erase 0).erase 1, (S 0 ∩ S j).card
              ≤ ∑ _j ∈ (I.erase 0).erase 1, lambda := by
                apply Finset.sum_le_sum
                intro j hj
                have hj' := Finset.mem_erase.mp hj
                have hj'' := Finset.mem_erase.mp hj'.2
                exact hpair 0 j hj''.1.symm (by
                  rintro (⟨_, hj1⟩ | ⟨h01, _⟩)
                  · exact hj'.1 hj1
                  · exact (by decide : (0 : Fin 6) ≠ 1) h01)
          _ = 4 * lambda := by simp [I]
    · by_cases hi1 : i = 1
      · subst i
        simp only [hi0, false_or, if_true]
        calc
          ∑ j ∈ I.erase (1 : Fin 6), (S 1 ∩ S j).card =
              (S 1 ∩ S 0).card +
                ∑ j ∈ (I.erase 1).erase 0, (S 1 ∩ S j).card :=
            (Finset.add_sum_erase (a := (0 : Fin 6)) (I.erase (1 : Fin 6))
              (fun j => (S 1 ∩ S j).card) (by simp [I])).symm
          _ ≤ exceptional + 4 * lambda := by
            apply Nat.add_le_add
            · dsimp only [exceptional]
              rw [Finset.inter_comm]
            · calc
                ∑ j ∈ (I.erase 1).erase 0, (S 1 ∩ S j).card
                    ≤ ∑ _j ∈ (I.erase 1).erase 0, lambda := by
                      apply Finset.sum_le_sum
                      intro j hj
                      have hj' := Finset.mem_erase.mp hj
                      have hj'' := Finset.mem_erase.mp hj'.2
                      exact hpair 1 j hj''.1.symm (by
                        rintro (⟨h10, _⟩ | ⟨_, hj0⟩)
                        · exact (by decide : (1 : Fin 6) ≠ 0) h10
                        · exact hj'.1 hj0)
                _ = 4 * lambda := by simp [I]
      · simp only [hi0, hi1, or_self, if_false]
        calc
          ∑ j ∈ I.erase i, (S i ∩ S j).card
              ≤ ∑ _j ∈ I.erase i, lambda := by
                apply Finset.sum_le_sum
                intro j hj
                have hji := (Finset.mem_erase.mp hj).1
                exact hpair i j hji.symm (by
                  rintro (⟨hi, _⟩ | ⟨hi, _⟩)
                  · exact hi0 hi
                  · exact hi1 hi)
          _ = 5 * lambda := by simp [I]
  have hoffdiag :
      ∑ i ∈ I, ∑ j ∈ I.erase i, (S i ∩ S j).card ≤
        2 * exceptional + 28 * lambda := by
    calc
      ∑ i ∈ I, ∑ j ∈ I.erase i, (S i ∩ S j).card
          ≤ ∑ i ∈ I,
            (if i = 0 ∨ i = 1 then exceptional + 4 * lambda else 5 * lambda) :=
              Finset.sum_le_sum (fun i _ => hinner i)
      _ = 2 * exceptional + 28 * lambda := by
        let b : Fin 6 → Nat := fun i =>
          if i = 0 ∨ i = 1 then exceptional + 4 * lambda else 5 * lambda
        have h0 : (0 : Fin 6) ∈ I := by simp [I]
        have h1 : (1 : Fin 6) ∈ I.erase 0 := by simp [I]
        have hrest :
            ∑ i ∈ (I.erase 0).erase 1, b i = 4 * (5 * lambda) := by
          calc
            ∑ i ∈ (I.erase 0).erase 1, b i =
                ∑ _i ∈ (I.erase 0).erase 1, 5 * lambda := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hi1 := (Finset.mem_erase.mp hi).1
                  have hi0 := (Finset.mem_erase.mp
                    (Finset.mem_erase.mp hi).2).1
                  simp only [b, hi0, hi1, or_self, if_false]
            _ = 4 * (5 * lambda) := by simp [I]
        change ∑ i ∈ I, b i = 2 * exceptional + 28 * lambda
        rw [← Finset.add_sum_erase (a := (0 : Fin 6)) I b h0,
          ← Finset.add_sum_erase (a := (1 : Fin 6)) (I.erase 0) b h1,
          hrest]
        simp only [b, true_or, or_true, if_true]
        ring
  have hsplit := sum_sum_card_inter_eq_diag_add_offdiag I S
  have hsecondUpper : second ≤ mass + 2 * exceptional + 28 * lambda := by
    have hdiag : ∑ i ∈ I, (S i).card = mass := by simp [I, mass]
    have hsecond :
        ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card = second := by
      simp [I, second]
    rw [hsecond, hdiag] at hsplit
    rw [hsplit]
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hoffdiag mass
  have hsixMass : 6 * mass ≤
      12 * Fintype.card U + 2 * exceptional + 28 * lambda := by
    have hcombined : 7 * mass ≤
        mass + 2 * exceptional + 28 * lambda + 12 * Fintype.card U :=
      hintegral.trans (Nat.add_le_add_right hsecondUpper (12 * Fintype.card U))
    omega
  have hthirtySix : 36 * z ≤ 6 * mass := by nlinarith
  dsimp only [exceptional] at hsixMass
  omega

/-! ## Concrete P1 amplification -/

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter interpolation dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the immediate predecessor. -/
abbrev T : Nat := 592794966

/-- The exceptional-core threshold forced by fourteen ordinary pairs. -/
abbrev Z₁ : Nat := 469762074

/-- The concrete arithmetic identity behind the amplified threshold. -/
theorem exceptional_threshold_eq :
    18 * T - 6 * N - 14 * (K - 1) = Z₁ := by
  norm_num [N, K, T, Z₁]

/-- **Concrete exceptional-pair amplification.**  Six trimmed predecessor agreement sets of
size at least `T`, with fourteen ordinary intersections below `K`, force the distinguished
intersection `S 0 ∩ S 1` to have at least `Z₁ = 469762074` coordinates. -/
theorem exceptionalPair_card_ge_Z₁
    (S : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (S i).card)
    (hpair : ∀ i j : Fin 6, i ≠ j →
      ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
        (S i ∩ S j).card ≤ K - 1) :
    Z₁ ≤ (S 0 ∩ S 1).card := by
  have h := sixSet_exceptionalPair_integral_johnson S hsize hpair
  simp only [Fintype.card_fin] at h
  norm_num [N, K, T, Z₁] at h ⊢
  omega

/-- Two `Z₁`-large subsets of one trimmed `T`-set overlap beyond the interpolation
dimension.  This is the numerical collinearity trigger for two exceptional attachments to the
same center. -/
theorem two_exceptional_attachments_inter_card_ge_K
    (C D E : Finset (Fin N))
    (hC : C.card = T)
    (hD : D ⊆ C) (hE : E ⊆ C)
    (hDcard : Z₁ ≤ D.card) (hEcard : Z₁ ≤ E.card) :
    K ≤ (D ∩ E).card := by
  have hunion : (D ∪ E).card ≤ C.card :=
    Finset.card_le_card (Finset.union_subset hD hE)
  rw [Finset.card_union] at hunion
  norm_num [K, T, Z₁] at hC hDcard hEcard ⊢
  omega

/-! ## Geometric consolidation -/

open HalfPredecessorLineCoreGeometry

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Exceptional attachments collapse to one pencil.**  Fix a trimmed `T`-coordinate agreement
set `C` for one decoded point.  If two other decoded points each meet `C` in at least `Z₁`
agreement coordinates, the three lifted polynomial points are collinear.

Indeed, the two attachments meet one another inside `C` on at least `K` coordinates.  A
noncollinear triple of degree-`<K` polynomials has at most `K-1` common full-agreement roots, so
the two secant directions from the center must coincide. -/
theorem slopePolynomial_eq_of_two_exceptional_trimmed_attachments
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    {gamma beta theta : F} {qgamma qbeta qtheta : F[X]}
    (hgb : gamma ≠ beta) (hgt : gamma ≠ theta)
    (hqgamma : qgamma.natDegree < K)
    (hqbeta : qbeta.natDegree < K)
    (hqtheta : qtheta.natDegree < K)
    (C B E : Finset (Fin N))
    (hCcard : C.card = T)
    (hCsub : C ⊆ fullAgreement dom u₀ u₁ gamma qgamma)
    (hBsub : B ⊆ fullAgreement dom u₀ u₁ beta qbeta)
    (hEsub : E ⊆ fullAgreement dom u₀ u₁ theta qtheta)
    (hCB : Z₁ ≤ (C ∩ B).card)
    (hCE : Z₁ ≤ (C ∩ E).card) :
    slopePolynomial gamma beta qgamma qbeta =
      slopePolynomial gamma theta qgamma qtheta := by
  have hinter : K ≤ ((C ∩ B) ∩ (C ∩ E)).card :=
    two_exceptional_attachments_inter_card_ge_K C (C ∩ B) (C ∩ E)
      hCcard Finset.inter_subset_left Finset.inter_subset_left hCB hCE
  have hsub : (C ∩ B) ∩ (C ∩ E) ⊆
      (fullAgreement dom u₀ u₁ gamma qgamma ∩
        fullAgreement dom u₀ u₁ beta qbeta) ∩
          fullAgreement dom u₀ u₁ theta qtheta := by
    intro i hi
    simp only [Finset.mem_inter] at hi ⊢
    exact ⟨⟨hCsub hi.1.1, hBsub hi.1.2⟩, hEsub hi.2.2⟩
  have hlower := hinter.trans (Finset.card_le_card hsub)
  by_contra hslope
  have hupper := triple_fullAgreement_card_le_pred_of_slope_ne
    dom u₀ u₁ (k := K) (by norm_num [K]) hgb hgt
      hqgamma hqbeta hqtheta hslope
  omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification.sixSet_exceptionalPair_integral_johnson
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification.exceptionalPair_card_ge_Z₁
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification.two_exceptional_attachments_inter_card_ge_K
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterExceptionalPairAmplification.slopePolynomial_eq_of_two_exceptional_trimmed_attachments
