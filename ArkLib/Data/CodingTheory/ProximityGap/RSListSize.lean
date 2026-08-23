/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.CodeGeometry
import ArkLib.Data.CodingTheory.ProximityGap.RSDistinctness

/-! # Reed–Solomon list-size from pairwise distinctness

This file composes the abstract Johnson list-size engine
(`CodeGeometry.card_le_of_johnson_sq`) with the Reed–Solomon distinctness fact
(`RSDistinct.degreeLT_agree_card_lt_of_ne`) into a single, directly consumable
Reed–Solomon list-size corollary.

The geometric engine bounds the size of any family of words that are all close
to a common center and pairwise far apart. For Reed–Solomon codes, "pairwise
far apart" is automatic: two *distinct* degree-`< k` polynomials agree on
strictly fewer than `k` of the evaluation points (RS minimum distance). Hence
their evaluation vectors agree on `≤ k − 1` coordinates, which is precisely the
off-diagonal agreement bound `B := k − 1` consumed by the Johnson cap.

The main theorem `rs_list_size_from_pairwise` states: the number `L` of distinct
degree-`< k` polynomials whose evaluation vectors lie within Hamming distance
`e` of an arbitrary word `w` is `≤ ℓ`, whenever the squared Johnson condition
holds with `A = n − e` and `B = k − 1`. -/

namespace RSListSize

open Finset Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The evaluation vector of a polynomial over the domain. -/
noncomputable def evalVec (domain : ι ↪ F) (p : F[X]) : ι → F :=
  fun i => p.eval (domain i)

omit [Fintype F] [DecidableEq ι] in
/-- The `CodeGeometry.agree` between two evaluation vectors equals the cardinality
of the RS pointwise-agreement set used in `RSDistinct`. -/
theorem agree_evalVec (domain : ι ↪ F) (p q : F[X]) :
    CodeGeometry.agree (evalVec domain p) (evalVec domain q)
      = (Finset.univ.filter
          (fun x => p.eval (domain x) = q.eval (domain x))).card := by
  rfl

omit [Fintype F] [DecidableEq ι] in
/-- **Pairwise RS off-diagonal bound.** Distinct degree-`< k` polynomials have
evaluation vectors agreeing on `≤ k − 1` coordinates. This realizes `B := k − 1`
as the pairwise-agreement bound consumed by the Johnson list-size cap. -/
theorem agree_evalVec_le_of_ne (domain : ι ↪ F) {k : ℕ}
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k)
    (hpq : p ≠ q) :
    CodeGeometry.agree (evalVec domain p) (evalVec domain q) ≤ k - 1 := by
  classical
  have hlt :
      (Finset.univ.filter
        (fun x => p.eval (domain x) = q.eval (domain x))).card < k :=
    RSDistinct.degreeLT_agree_card_lt_of_ne domain hp hq hpq Finset.univ
  rw [agree_evalVec]
  omega

omit [Fintype F] [DecidableEq ι] in
/-- A distance-`e` evaluation vector has at least `n - e` agreements with the center word. -/
theorem agree_evalVec_ge_of_hammingDist_le (domain : ι ↪ F) {p : F[X]} {w : ι → F} {e : ℕ}
    (hclose : hammingDist (evalVec domain p) w ≤ e) :
    Fintype.card ι - e ≤ CodeGeometry.agree (evalVec domain p) w := by
  have hbridge := CodeGeometry.agree_add_hammingDist (evalVec domain p) w
  omega

omit [DecidableEq ι] in
/-- **Reed–Solomon list-size from pairwise distinctness.**

Let `domain : ι ↪ F` be an evaluation domain over a finite field `F`
(`1 < |F|`, `0 < |ι| = n`), let `w : ι → F` be an arbitrary received word, and
let `p : Fin L → F[X]` be an *injective* family of degree-`< k` polynomials
whose evaluation vectors all lie within Hamming distance `e` of `w`.

Then the number `L` of such proximates obeys `L ≤ ℓ` whenever the squared
Johnson condition holds with center-agreement parameter `A = n − e` and
pairwise-agreement bound `B = k − 1`:
`(ℓ+1)·(A − n/q)² > N·(N + ℓ·((k−1) − n/q))`, where `N := n(1 − 1/q)`,
`q := |F|`, `n := |ι|`, and `n/q ≤ A`.

This is the Reed–Solomon-specific instance of ABF26 Theorem 3.2: the pairwise
distance hypothesis of the generic Johnson bound is *discharged automatically*
from RS minimum distance via `agree_evalVec_le_of_ne` (distinct degree-`< k`
polynomials agree on `< k` points, hence `B = k − 1` works). -/
theorem rs_list_size_from_pairwise
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (domain : ι ↪ F) (w : ι → F)
    {L : ℕ} (hL : 0 < L) {k e : ℕ} (ℓ : ℕ)
    (p : Fin L → F[X])
    (hpmem : ∀ i, p i ∈ Polynomial.degreeLT F k)
    (hpinj : Function.Injective p)
    (hclose : ∀ i, hammingDist (evalVec domain (p i)) w ≤ e)
    (hP :
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
        ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - e : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((k - 1 : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    L ≤ ℓ := by
  classical
  -- The family of evaluation vectors, with `w` as the Johnson center.
  set c : Fin L → ι → F := fun i => evalVec domain (p i) with hc
  -- A := n − e lower-bounds each center agreement (from the closeness hypothesis).
  have hA : ∀ i, (Fintype.card ι - e) ≤ CodeGeometry.agree (c i) w := by
    intro i
    simpa [hc] using
      agree_evalVec_ge_of_hammingDist_le domain (p := p i) (w := w) (e := e) (hclose i)
  -- B := k − 1 upper-bounds each pairwise agreement (RS distinctness).
  have hB : ∀ i j, i ≠ j → CodeGeometry.agree (c i) (c j) ≤ (k - 1) := by
    intro i j hij
    have hpij : p i ≠ p j := fun h => hij (hpinj h)
    simpa [hc] using
      agree_evalVec_le_of_ne domain (hpmem i) (hpmem j) hpij
  -- Apply the abstract squared-form Johnson list-size bound with A = n−e, B = k−1.
  exact CodeGeometry.card_le_of_johnson_sq hq1 hn hL w c ℓ hA hB hP hsq

/- Axiom audit against the edited source:
`agree_evalVec_le_of_ne` and `rs_list_size_from_pairwise` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. -/

end RSListSize
