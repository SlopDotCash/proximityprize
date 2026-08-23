/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance

/-!
# Reed–Solomon encoding injectivity (#82)

For `k ≤ n` the Reed–Solomon evaluation map `evalOnPoints` is injective on degree-`<k` polynomials:
distinct degree-`<k` polynomials yield distinct RS codewords.  A nonzero difference `p − p'` of
degree `< k ≤ n` cannot vanish at all `n` distinct evaluation points (it has `≤ k−1 < n` roots, by
`card_domain_roots_le`).  This is the companion to the RS minimum distance: together they give the
`[n, k, n−k+1]` MDS parameters of the Reed–Solomon code.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon encoding injectivity.**  For `k ≤ n`, `evalOnPoints` is injective on degree-`<k`
polynomials. -/
theorem evalOnPoints_injOn_degreeLT (domain : ι ↪ F) (k : ℕ) (hnk : k ≤ Fintype.card ι)
    (p p' : Polynomial F) (hp : p.natDegree < k) (hp' : p'.natDegree < k)
    (h : ReedSolomon.evalOnPoints domain p = ReedSolomon.evalOnPoints domain p') :
    p = p' := by
  by_contra hne
  have hq : p - p' ≠ 0 := sub_ne_zero.mpr hne
  have hall : (univ.filter (fun i => (p - p').eval (domain i) = 0)) = univ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, iff_true, Polynomial.eval_sub, sub_eq_zero]
    have := congrFun h i
    simpa [ReedSolomon.evalOnPoints] using this
  have h1 := card_domain_roots_le domain (p - p') hq
  rw [hall, card_univ] at h1
  have hdeg : (p - p').natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le p p') (max_lt hp hp')
  omega

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.evalOnPoints_injOn_degreeLT
