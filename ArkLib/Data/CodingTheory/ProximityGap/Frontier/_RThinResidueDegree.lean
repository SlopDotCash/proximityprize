/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
Scratch: R-thin ragged-excess sharpened by the RESIDUE-FACTOR degree (#407, ESCAPE B1).

Goal: replace `ragged_excess_le_degree` (excess <= deg P - core, VACUOUS since deg P ~ n)
with a bound on the ragged excess by the degree of the RAGGED RESIDUE FACTOR `d` in the
factorization `Q_S = C * d` (C = maximal coset-core factor). When the residue factor's degree
is governed by the codeword degree (< k), this is the n-independent k-governed bound the
numerics show (excess = k-1, flat in n in {16,32,64}).

Provable, axiom-clean. Uses only monic-factorization degree splitting (natDegree_mul) +
the in-tree root-product machinery shape.
-/

namespace ProximityGap.Frontier.RThinResidueDegree

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `∏_{x∈S}(X−x)` has degree exactly `|S|`. (Mirror of in-tree `rootProd_natDegree_eq`.) -/
theorem rootProd_natDegree_eq (S : Finset F) :
    (∏ x ∈ S, (X - C x)).natDegree = S.card := by
  classical
  rw [natDegree_prod _ _ (fun x _ => X_sub_C_ne_zero x)]
  simp

/-- `∏_{x∈S}(X−x)` is monic. -/
theorem rootProd_monic (S : Finset F) : (∏ x ∈ S, (X - C x)).Monic := by
  classical
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

/-- **The residue-factor degree split (the sharpening).**
If the agreement-set root product `Q_S = ∏_{x∈S}(X−x)` factors as `C * d` with `C` monic of
degree `coreDeg` (the coset-core factor) and `d` monic of degree `resDeg` (the ragged residue),
then `|S| = coreDeg + resDeg`, hence the ragged excess over the core is *exactly* `resDeg`:

  `|S| − coreDeg = resDeg`.

This is the realizability lever in clean form: the excess is the degree of the RESIDUE factor
`d`, not `deg P ≈ n`. The open core is only to certify `resDeg < k` (= `deg` of the codeword
contribution); the degree-split itself is unconditional. -/
theorem ragged_excess_eq_residue_natDegree
    {S : Finset F} {C d : F[X]} (hC : C.Monic) (hd : d.Monic)
    (hfact : (∏ x ∈ S, (X - Polynomial.C x)) = C * d) :
    S.card - C.natDegree = d.natDegree := by
  classical
  have hsplit : S.card = C.natDegree + d.natDegree := by
    have h1 : (∏ x ∈ S, (X - Polynomial.C x)).natDegree = S.card := rootProd_natDegree_eq S
    have h2 : (C * d).natDegree = C.natDegree + d.natDegree := hC.natDegree_mul hd
    rw [hfact] at h1; omega
  omega

/-- **Consumer form: ragged excess is bounded by the residue-factor degree.**
Same hypothesis, stated as the inequality `|S| − coreDeg ≤ resDeg` (so a `resDeg < k` certificate
makes the excess `< k`, the n-independent prize-shaped bound). -/
theorem ragged_excess_le_residue_natDegree
    {S : Finset F} {C d : F[X]} (hC : C.Monic) (hd : d.Monic)
    (hfact : (∏ x ∈ S, (X - Polynomial.C x)) = C * d) :
    S.card - C.natDegree ≤ d.natDegree :=
  le_of_eq (ragged_excess_eq_residue_natDegree hC hd hfact)

/-- **The realizability certificate composed (the n-independent k-governed excess).**
If, additionally, the residue factor `d` has degree `< k` (the codeword degree bound the
realizability constraint supplies), then the ragged excess is `< k` — *independent of `n`*.
This is the exact shape the antipodal-descent numerics measured (`excess = k−1`, flat over
`n ∈ {16,32,64}`): the excess is `n`-free, governed by the term/degree budget `k`. -/
theorem ragged_excess_lt_k_of_residue_deg
    {S : Finset F} {C d : F[X]} (hC : C.Monic) (hd : d.Monic) {k : ℕ}
    (hfact : (∏ x ∈ S, (X - Polynomial.C x)) = C * d) (hdk : d.natDegree < k) :
    S.card - C.natDegree < k :=
  lt_of_le_of_lt (ragged_excess_le_residue_natDegree hC hd hfact) hdk

/-- **The coset core has degree `g · (#cosets)`.**
When the core factor `C` is `g`-sparse (a polynomial in `Xᵍ`, i.e. `C = expand F g Cr`), its
degree is `g · Cr.natDegree`, so the core accounts for `Cr.natDegree` cosets of size `g`. Combined
with the residue split this gives `|S| = g·(#cosets) + resDeg`: the full coset-core + ragged-excess
decomposition, with the excess `= resDeg` (the realizability quantity), *not* `deg P`. -/
theorem core_natDegree_eq_expand {g : ℕ} (Cr : F[X]) :
    (expand F g Cr).natDegree = g * Cr.natDegree := by
  rw [natDegree_expand, Nat.mul_comm]

/-- **Full decomposition: `|S| = g·(#cosets) + residueDeg`, excess = residueDeg.**
With `Q_S = (expand F g Cr) * d` (core a `μ_g`-coset-union of `Cr.natDegree` cosets, `d` the
ragged residue), the ragged excess over the core is *exactly* `d.natDegree`, and the core size is
`g · Cr.natDegree`. The excess is governed by the residue degree (the realizability/codeword budget),
not by `n`. -/
theorem full_coset_residue_decomp {S : Finset F} {g : ℕ} {Cr d : F[X]}
    (hCr : (expand F g Cr).Monic) (hd : d.Monic)
    (hfact : (∏ x ∈ S, (X - Polynomial.C x)) = (expand F g Cr) * d) :
    S.card = g * Cr.natDegree + d.natDegree
      ∧ S.card - (g * Cr.natDegree) = d.natDegree := by
  classical
  have hsplit : S.card = (expand F g Cr).natDegree + d.natDegree := by
    have h1 : (∏ x ∈ S, (X - Polynomial.C x)).natDegree = S.card := rootProd_natDegree_eq S
    have h2 : ((expand F g Cr) * d).natDegree = (expand F g Cr).natDegree + d.natDegree :=
      hCr.natDegree_mul hd
    rw [hfact] at h1; omega
  rw [core_natDegree_eq_expand] at hsplit
  exact ⟨hsplit, by omega⟩

end ProximityGap.Frontier.RThinResidueDegree

#print axioms ProximityGap.Frontier.RThinResidueDegree.rootProd_natDegree_eq
#print axioms ProximityGap.Frontier.RThinResidueDegree.ragged_excess_eq_residue_natDegree
#print axioms ProximityGap.Frontier.RThinResidueDegree.ragged_excess_le_residue_natDegree
#print axioms ProximityGap.Frontier.RThinResidueDegree.ragged_excess_lt_k_of_residue_deg
#print axioms ProximityGap.Frontier.RThinResidueDegree.full_coset_residue_decomp
