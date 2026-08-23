/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MonicIrreducibleFactorization
import ArkLib.ToMathlib.GSSurfaceEntry

/-!
# Issue #304 — the section `Hypotheses` from the surface alone

Composes the monic-irreducible factorization (`exists_monic_irreducible_factorization_fin`,
any domain, no UFD hypothesis — `MonicIrreducibleFactorization.lean`; see also the UFD route
in `PigeonholeFactorSupply.lean`) with the proven §6 pigeonhole
(`SectionFactor.section_dvd_of_factorization`) into **uniform-input** producers:

* `section_dvd_of_surface` — the section divisibility `(T − C v) ∣ evalX (C x₀) R` from the
  surface facts alone: monicity, positive degree, per-place curve membership, a *uniform*
  per-divisor budget, and the *uniform* count `deg · n ≤ |good|` (the factor count is at most
  the degree since monic irreducible factors have positive degree).  No factorization
  appears in the interface.
* `section_hypotheses_of_surface` — `Hypotheses x₀ R (T − C v)`: the exact section bundle
  input of `GSSurfaceData`, produced.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]

/-- **The section divisibility from the surface alone** (uniform interface): monic positive-
degree specialized surface + per-place curve membership + uniform per-divisor budget +
the count `deg · n ≤ |good|` produce `(T − C v) ∣ evalX (C x₀) R`. -/
theorem section_dvd_of_surface [DecidableEq F] {x₀ : F} {R : F[X][X][Y]}
    (hmon : (Bivariate.evalX (Polynomial.C x₀) R).Monic)
    (h0 : 0 < (Bivariate.evalX (Polynomial.C x₀) R).natDegree)
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet,
      Polynomial.evalEval z (v.eval z) (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    {n : ℕ}
    (hbudget : ∀ H : F[X][Y], H.Monic → Irreducible H →
      H ∣ Bivariate.evalX (Polynomial.C x₀) R → (Polynomial.eval v H).natDegree < n)
    (hcount : (Bivariate.evalX (Polynomial.C x₀) R).natDegree * n ≤ goodSet.card) :
    (Polynomial.X - Polynomial.C v : F[X][Y]) ∣ Bivariate.evalX (Polynomial.C x₀) R := by
  obtain ⟨m, Hf, hfac, hprod⟩ :=
    Polynomial.exists_monic_irreducible_factorization_fin _ hmon h0
  have hne : ∀ i, Hf i ≠ 0 := fun i => (hfac i).1.ne_zero
  have hdegsum : ∑ i, (Hf i).natDegree
      = (Bivariate.evalX (Polynomial.C x₀) R).natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ (fun i _ => hne i)]
  have hone : ∀ i, 1 ≤ (Hf i).natDegree := by
    intro i
    by_contra h
    push_neg at h
    have h00 : (Hf i).natDegree = 0 := by omega
    have h1 : Hf i = 1 := (hfac i).1.natDegree_eq_zero_iff_eq_one.mp h00
    exact (hfac i).2.not_isUnit (h1 ▸ isUnit_one)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [Fin.sum_univ_zero] at hdegsum
      omega
    · exact h
  have hm_le : m ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree := by
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, (Hf i).natDegree := Finset.sum_le_sum (fun i _ => hone i)
      _ = _ := hdegsum
  obtain ⟨i, hi, hdvd⟩ := SectionFactor.section_dvd_of_factorization hprod.symm
    ⟨⟨0, hm0⟩, Finset.mem_univ _⟩ hvan
    (by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact le_trans (Nat.mul_le_mul_right n hm_le) hcount)
    (fun j _ => hbudget _ (hfac j).1 (hfac j).2
      (hprod ▸ Finset.dvd_prod_of_mem Hf (Finset.mem_univ j)))
  exact hdvd.trans (hprod ▸ Finset.dvd_prod_of_mem Hf hi)

/-- **The section `Hypotheses` from the surface alone** — the exact section-bundle input of
`GSSurfaceData`, produced from GS-construction-level facts. -/
theorem section_hypotheses_of_surface [DecidableEq F] {x₀ : F} {R : F[X][X][Y]}
    (hmon : (Bivariate.evalX (Polynomial.C x₀) R).Monic)
    (h0 : 0 < (Bivariate.evalX (Polynomial.C x₀) R).natDegree)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet,
      Polynomial.evalEval z (v.eval z) (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    {n : ℕ}
    (hbudget : ∀ H : F[X][Y], H.Monic → Irreducible H →
      H ∣ Bivariate.evalX (Polynomial.C x₀) R → (Polynomial.eval v H).natDegree < n)
    (hcount : (Bivariate.evalX (Polynomial.C x₀) R).natDegree * n ≤ goodSet.card) :
    Hypotheses x₀ R (Polynomial.X - Polynomial.C v : F[X][Y]) :=
  sectionH_hypotheses hsep (section_dvd_of_surface hmon h0 hvan hbudget hcount)

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.section_dvd_of_surface
#print axioms ArkLib.GSSurfaceKeystone.section_hypotheses_of_surface
