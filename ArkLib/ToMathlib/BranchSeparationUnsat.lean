/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedCapstonesCorrected

/-!
# Issue #304 — F7: the rational-branch-separation route is UNSATISFIABLE for `d_H ≥ 2`

Adversarial self-audit of the decoded-roots chain (`DecodedRootSupply`,
`BranchCertificates`, and their corrected variants in `DecodedCapstonesCorrected`).  Those
files produced the per-place branch roots through **branch separation**: at each matching
place, the GS cofactor `G` was required not to vanish at the surface's centre value,
`G(z, w(x₀,z)) ≠ 0`.  This file proves that requirement is **false at every place** whenever
`d_H ≥ 2`:

* the centre fold `(Y′ − C v)` (`v := w.eval (C x₀)`) is **prime** in `F[X][Y]`
  (`Polynomial.prime_X_sub_C` over the domain `F[X]`);
* it divides `evalX (C x₀) R = H · G` (by `DecodedRootSupply.centreFold_dvd`), so it divides
  `H` or `G`;
* dividing the **irreducible** `H` would force `H.natDegree = 1` — excluded for `d_H ≥ 2`
  (`natDegree_eq_one_of_X_sub_C_dvd_irreducible`);
* hence `(Y′ − C v) ∣ G` unconditionally (`centreFold_dvd_G`), i.e. `G(z, w(x₀,z)) = 0` at
  **every** `z` (`branchSep_eq_zero`).

**Consequences (the F7 disposition):**

* `branchCert_eq_zero` — the `BranchCertificates` certificate `G.eval (w.eval (C x₀))` is
  identically `0` for `d_H ≥ 2`: the `hbr` hypothesis of
  `BranchCertificates.gammaGenuine_eq_trunc_global` and
  `DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected` is **unsatisfiable**.
* `matchingSet_eq_empty_of_hbranch` — any matching set satisfying the per-place branch
  separation of `DecodedRootSupply.mpFin_of_decoded_roots` / `hvanish_of_decoded_roots` /
  `gammaGenuine_eq_trunc_of_decoded_roots[_corrected]` is **empty** for `d_H ≥ 2`: those
  capstones are instantiable only vacuously there.

**What survives.**  The mathematics of the refutation is itself the explanation: a rational
section `w` can never lie on an irreducible branch cluster of degree `≥ 2`.  The decoded
surface meets the `H`-branch only **pointwise at the matching places** — the `S_β`-membership
content — never as a rational containment.  The sound surface is therefore
`DecodedProximateRoot.mpFin_of_decoded` (and its `hvanish`/truncation capstones), where the
branch roots `root z` and the base-point agreement
`hbase : w(x₀, z) = (root z).1` are **inputs** carrying the honest per-place matching content,
exactly as [BCIKS20] App A.5.2.6 supplies them.  The route that *produces* those roots must go
through the `H`-branch geometry (algebraic, non-rational), not through rational branch
separation.

## References
* [BCIKS20] §5, Appendix A.5.2; the F-series findings ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace BranchSeparationUnsat

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (0 < H.natDegree)] in
/-- A prime linear factor of an irreducible polynomial forces degree one: if
`(Y − C v) ∣ H` with `H` irreducible, then `H.natDegree = 1`. -/
theorem natDegree_eq_one_of_X_sub_C_dvd_irreducible {v : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C v) ∣ H) : H.natDegree = 1 := by
  obtain ⟨c, hc⟩ := hdvd
  have hirr : Irreducible H := Fact.out
  rcases hirr.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu (Polynomial.not_isUnit_X_sub_C v)
  · have hc0 : c ≠ 0 := fun h => by
      rw [h, mul_zero] at hc
      exact hirr.ne_zero hc
    have hX0 : (Polynomial.X - Polynomial.C v) ≠ 0 := Polynomial.X_sub_C_ne_zero v
    have hcdeg : c.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hXdeg : (Polynomial.X - Polynomial.C v).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C v
    rw [hc, Polynomial.natDegree_mul hX0 hc0, hXdeg, hcdeg]

omit [Fact (0 < H.natDegree)] in
/-- **The centre fold always divides the cofactor (`d_H ≥ 2`).**  The prime linear factor
`(Y − C v)` divides `H · G`; dividing the irreducible `H` is excluded by degree, so it
divides `G`. -/
theorem centreFold_dvd_G {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hd2 : 2 ≤ H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) ∣ G := by
  have hprime : Prime (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) :=
    Polynomial.prime_X_sub_C _
  have hHG : (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) ∣ H * G := by
    rw [← hsplit]
    exact DecodedRootSupply.centreFold_dvd hdvd
  rcases hprime.2.2 _ _ hHG with hH | hG
  · exact absurd (natDegree_eq_one_of_X_sub_C_dvd_irreducible hH) (by omega)
  · exact hG

omit [Fact (0 < H.natDegree)] in
/-- **F7 core: branch separation is false at every place (`d_H ≥ 2`).**
`G(z, w(x₀,z)) = 0` for every `z`. -/
theorem branchSep_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hd2 : 2 ≤ H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F) :
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G = 0 := by
  have hG : G.eval (w.eval (Polynomial.C x₀)) = 0 :=
    Polynomial.dvd_iff_isRoot.mp (centreFold_dvd_G hd2 hsplit hdvd)
  rw [← BranchCertificates.branchCert_eval G w x₀ z, hG, Polynomial.eval_zero]

omit [Fact (0 < H.natDegree)] in
/-- **F7 (certificate form): the `BranchCertificates` certificate is identically zero for
`d_H ≥ 2`** — the `hbr` hypothesis of `gammaGenuine_eq_trunc_global[_corrected]` is
unsatisfiable. -/
theorem branchCert_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hd2 : 2 ≤ H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    G.eval (w.eval (Polynomial.C x₀)) = 0 :=
  Polynomial.dvd_iff_isRoot.mp (centreFold_dvd_G hd2 hsplit hdvd)

omit [Fact (0 < H.natDegree)] in
/-- **F7 (matching-set form): any matching set carrying the branch-separation family is empty
(`d_H ≥ 2`)** — the decoded-roots capstones (`mpFin_of_decoded_roots`,
`hvanish_of_decoded_roots`, `gammaGenuine_eq_trunc_of_decoded_roots[_corrected]`) are
instantiable only vacuously there. -/
theorem matchingSet_eq_empty_of_hbranch {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    {matchingSet : Finset F}
    (hd2 : 2 ≤ H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0) :
    matchingSet = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact hbranch z hz (branchSep_eq_zero hd2 hsplit hdvd z)

end BranchSeparationUnsat

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BranchSeparationUnsat.natDegree_eq_one_of_X_sub_C_dvd_irreducible
#print axioms ArkLib.BranchSeparationUnsat.centreFold_dvd_G
#print axioms ArkLib.BranchSeparationUnsat.branchSep_eq_zero
#print axioms ArkLib.BranchSeparationUnsat.branchCert_eq_zero
#print axioms ArkLib.BranchSeparationUnsat.matchingSet_eq_empty_of_hbranch
