/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionGlobalLift

/-!
# Hypothesis K4: the radical substitution (#304)

**The radical substitution deletes the separability
hypothesis from the branch-certificate production**. The use site
(`branch_ne_zero_of_separable`) only consumes squarefreeness; passing to the radical of the
fiber — which is squarefree unconditionally over the UFD `F[X]` — produces the split and the
branch certificate `(hsplit, hbr)` with NO separability assumption at all. -/

namespace ArkLib

namespace RadicalBranch

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

variable {F : Type} [Field F] [DecidableEq F]

/-- Monic linear `Y − C v` is prime over a domain (the kernel of evaluation). -/
theorem prime_X_sub_C_poly (v : F[X]) : Prime (Polynomial.X - Polynomial.C v : F[X][Y]) :=
  Polynomial.prime_X_sub_C v

/-- **The squarefree-only branch certificate** (hypothesis weakening of
`SectionGlobalLift.branch_ne_zero_of_separable`): squarefreeness of the fiber suffices. -/
theorem branch_ne_zero_of_squarefree {P H G : F[X][Y]} {v : F[X]}
    (hsq : Squarefree P)
    (hsplit : P = H * G)
    (hH0 : H.eval v = 0) :
    G.eval v ≠ 0 := by
  intro hG0
  have hdH : (Polynomial.X - Polynomial.C v) ∣ H := Polynomial.dvd_iff_isRoot.mpr hH0
  have hdG : (Polynomial.X - Polynomial.C v) ∣ G := Polynomial.dvd_iff_isRoot.mpr hG0
  have hsqd : (Polynomial.X - Polynomial.C v) * (Polynomial.X - Polynomial.C v) ∣ P := by
    rw [hsplit]; exact mul_dvd_mul hdH hdG
  exact Polynomial.not_isUnit_X_sub_C v (hsq _ hsqd)

/-- An irreducible divisor of `P ≠ 0` divides the radical. -/
theorem irreducible_dvd_radical {P H : F[X][Y]} (hP : P ≠ 0)
    (hirr : Irreducible H) (hdvd : H ∣ P) :
    H ∣ radical P :=
  (dvd_radical_iff_of_irreducible hirr hP).mpr hdvd

/-- **The radical split-and-branch package (K4)**: for ANY nonzero fiber `P` with an
irreducible factor `H` rooting the section value `v`, the RADICAL of `P` splits as `H * G'`
with the branch certificate `G'.eval v ≠ 0` — no separability or squarefreeness hypothesis
on `P` anywhere. This deletes `hsep`/`hRsep` from the `(hsplit, hbr)` production of the
`Section5GlobalAssembler` lane: run the assembler against `radical P` instead of `P`. -/
theorem exists_radical_split_branch {P H : F[X][Y]} {v : F[X]}
    (hP : P ≠ 0) (hirr : Irreducible H) (hdvd : H ∣ P) (hH0 : H.eval v = 0) :
    ∃ G' : F[X][Y], radical P = H * G' ∧ G'.eval v ≠ 0 := by
  obtain ⟨G', hG'⟩ := irreducible_dvd_radical hP hirr hdvd
  exact ⟨G', hG', branch_ne_zero_of_squarefree
    (squarefree_radical) hG' hH0⟩

/-- The radical preserves the global-surface linear factor: `(Y′ − C w) ∣ R ⟹
(Y′ − C w) ∣ radical R` (the trivariate-level K4 substitution; monic linear is prime, hence
irreducible). -/
theorem section_dvd_radical {R : F[X][X][Y]} {w : F[X][Y]} (hR : R ≠ 0)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C w) ∣ radical R :=
  (dvd_radical_iff_of_irreducible (Polynomial.prime_X_sub_C w).irreducible hR).mpr hdvdR

/-- Radical degree budget: `natDegree (radical P) ≤ natDegree P` (the radical divides). -/
theorem natDegree_radical_le {P : F[X][Y]} (hP : P ≠ 0) :
    (radical P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_le_of_dvd (radical_dvd_self) hP

end RadicalBranch

end ArkLib

#print axioms ArkLib.RadicalBranch.branch_ne_zero_of_squarefree
#print axioms ArkLib.RadicalBranch.exists_radical_split_branch
#print axioms ArkLib.RadicalBranch.section_dvd_radical
#print axioms ArkLib.RadicalBranch.natDegree_radical_le
