/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListAroundBallIntersectionKernel

/-!
# Issue #232 — the list-size reduction to the ball-intersection second moment (the open #82 kernel)

`ListAroundBallIntersectionKernel.lean` proves the second-moment identity
`∑_w |listAround(w,r)|² = ∑_{c,c' ∈ C} |B(c,r) ∩ B(c',r)|`.  This file turns that identity into an
**actual upper bound on the worst-case list size** `|Λ(C,δ)| = max_w |listAround(w,r)|`, and splits the
right-hand side into the explicit **diagonal** and the **off-diagonal**.  The resulting inequality
is a *coarse* bound: as explained below, its diagonal alone already exceeds the prize budget, so it
is not a reduction of the Proximity Prize to the off-diagonal.

The clean chain:

* `listAround_sq_le_ball_inter` — `max_w |listAround(w,r)|² ≤ ∑_{c,c'} |B(c,r) ∩ B(c',r)|`
  (a single non-negative term is `≤` the whole sum, then the kernel identity).

* `sum_ball_inter_diag_offdiag` — `∑_{c,c'} |B(c,r) ∩ B(c',r)| = ∑_c |B(c,r)| + ∑_c ∑_{c'≠c}
  |B(c,r) ∩ B(c',r)|` (split each inner sum at `c' = c`; `B(c,r) ∩ B(c,r) = B(c,r)`).

* `listSize_sq_le_diag_add_offdiag` (HEADLINE) — for every received word `w₀`,
  `|listAround(w₀,r)|² ≤ ∑_c |B(c,r)| + ∑_c ∑_{c'≠c} |B(c,r) ∩ B(c',r)|`.

The diagonal `∑_c |B(c,r)|` is just `|C|` times the (codeword-independent) Hamming ball volume
`V(r)` — explicit, but **not harmless**: it is nonnegative and retained in the bound, and for a
Reed–Solomon code of dimension `k ≥ 2` it is already `|C| = q^k ≥ q²` at `r = 0` (and only grows
with `r`).  So for any `ε* < 1` the right-hand side exceeds `ε*²·q²` *regardless of the
off-diagonal*, and no off-diagonal bound, however strong, makes this raw inequality yield
`listSize ≤ ε*·q` in those regimes.
The off-diagonal `∑_{c ≠ c'} |B(c,r) ∩ B(c',r)|` for Reed–Solomon (an MDS code) equals
`|C| · ∑_{w ≥ d} A_w · I(w,r)`, the weight-enumerator `A_w` weighted by the ball-intersection volumes
`I(w,r) = |B(0,r) ∩ B(e,r)|` (`wt e = w`).  A useful prize reduction would need a normalization or
localization of the second moment (or a different treatment of the diagonal), together with the
separate list-to-MCA dictionary; neither is provided here, and no theorem in this file proves an
equivalence between the off-diagonal sum and the prize threshold.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open scoped Classical
open Finset
open ArkLib.CodingTheory.Round13BallInter

noncomputable section

namespace ArkLib.CodingTheory.Round13Reduction

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The worst-case list size is controlled by the ball-intersection second moment.**  Since
`|listAround(w₀,r)|²` is one (non-negative) term of the sum `∑_w |listAround(w,r)|²`, it is at most the
whole sum, which by the kernel identity equals `∑_{c,c'} |B(c,r) ∩ B(c',r)|`.  Hence
`|Λ(C,δ)|² ≤ ∑_{c,c'} |B(c,r) ∩ B(c',r)|`. -/
theorem listAround_sq_le_ball_inter (C : Finset (Fin n → F)) (r : ℕ) (w₀ : Fin n → F) :
    (listAround C w₀ r).card ^ 2
      ≤ ∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card := by
  rw [← sum_sq_listAround_eq_ball_inter C r]
  exact Finset.single_le_sum (f := fun w => (listAround C w r).card ^ 2)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ w₀)

/-- **Diagonal/off-diagonal split of the ball-intersection second moment.**  Splitting each inner sum
at `c' = c` (where `B(c,r) ∩ B(c,r) = B(c,r)`):
`∑_{c,c'} |B(c,r) ∩ B(c',r)| = ∑_c |B(c,r)| + ∑_c ∑_{c' ∈ C.erase c} |B(c,r) ∩ B(c',r)|`. -/
theorem sum_ball_inter_diag_offdiag (C : Finset (Fin n → F)) (r : ℕ) :
    (∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card)
      = (∑ c ∈ C, (hammingBall c r).card)
        + ∑ c ∈ C, ∑ c' ∈ C.erase c, (hammingBall c r ∩ hammingBall c' r).card := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Finset.add_sum_erase C (fun c' => (hammingBall c r ∩ hammingBall c' r).card) hc,
      Finset.inter_self]

/-- **HEADLINE — coarse list-size bound.**  For every received word `w₀` and radius `r`,
`|listAround(w₀,r)|² ≤ ∑_c |B(c,r)| + ∑_c ∑_{c' ≠ c} |B(c,r) ∩ B(c',r)|`.

The first (diagonal) term is `|C|·V(r)`; it is explicit but not negligible: for Reed–Solomon of
dimension `k ≥ 2` it is at least `q^k ≥ q²`, so for `ε* < 1` it alone exceeds `ε*²·q²` and this raw
bound cannot certify `listSize ≤ ε*·q` however small the off-diagonal is.  The second (off-diagonal)
term is, for Reed–Solomon, `|C|·∑_{w} A_w · I(w,r)` (weight enumerator × ball-intersection volumes).
A prize-relevant reduction would require normalizing/localizing the diagonal and the separate
list-to-MCA dictionary; this theorem is only the coarse second-moment inequality. -/
theorem listSize_sq_le_diag_add_offdiag (C : Finset (Fin n → F)) (r : ℕ) (w₀ : Fin n → F) :
    (listAround C w₀ r).card ^ 2
      ≤ (∑ c ∈ C, (hammingBall c r).card)
        + ∑ c ∈ C, ∑ c' ∈ C.erase c, (hammingBall c r ∩ hammingBall c' r).card := by
  calc (listAround C w₀ r).card ^ 2
      ≤ ∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card :=
        listAround_sq_le_ball_inter C r w₀
    _ = _ := sum_ball_inter_diag_offdiag C r

/-- **Non-degeneracy.**  The reduction is not vacuous: the right-hand side is a genuine bound and the
diagonal `∑_c |B(c,r)|` is the only term present when `C` has a single codeword (the off-diagonal sum
over `C.erase c = ∅` is `0`), recovering `|listAround|² ≤ |B(c,r)|`. -/
theorem listSize_sq_le_singleton (c₀ w₀ : Fin n → F) (r : ℕ) :
    (listAround {c₀} w₀ r).card ^ 2 ≤ (hammingBall c₀ r).card := by
  have h := listSize_sq_le_diag_add_offdiag ({c₀} : Finset (Fin n → F)) r w₀
  simpa using h

end ArkLib.CodingTheory.Round13Reduction

end

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round13Reduction.listAround_sq_le_ball_inter
#print axioms ArkLib.CodingTheory.Round13Reduction.sum_ball_inter_diag_offdiag
#print axioms ArkLib.CodingTheory.Round13Reduction.listSize_sq_le_diag_add_offdiag
#print axioms ArkLib.CodingTheory.Round13Reduction.listSize_sq_le_singleton
