/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GK16Claim16Core
import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12

/-!
# GK16 Claim 16: per-coordinate multiplicity bound (proven engine)

This file proves the **engine** of GK16 Claim 16: at an evaluation point `a`, the root
multiplicity of the folded Wronskian `L := foldedWronskian P ω` is at least the dimension
`d` of the subspace of family members vanishing on the `s`-fold orbit of `a`.

The argument is the column-divisibility one of GK16 §4 (cf. the task spec):

* Pass to a basis `Q` of the underlying polynomial space *adapted* to the vanishing
  subspace — `Q` is an invertible `F`-linear recombination of `P`, and its first `d`
  members `Q l` (for `l` in a card-`d` index set `T`) vanish on the orbit
  `{a · ω^b}`. Such a `Q` is the change-of-basis transport (supplied as data).
* For each `l ∈ T` and every dilation row `b : Fin n` (with `n ≤ s`, so `(b : ℕ) < s` is a
  fold index), the dilation entry `(Q l).comp (C (ω^b) · X)` evaluates to
  `(Q l)(ω^b · a) = 0` at `X = a`, hence `(X - C a)` divides that entry
  (`Polynomial.dvd_iff_isRoot`). So column `l` is `(X - C a)`-divisible.
* `pow_dvd_det_of_col_dvd` (Claim-16 core) factors `(X - C a)^d` out of
  `det [Q l (ω^b X)] = foldedWronskian Q ω`, giving
  `d ≤ rootMultiplicity a (foldedWronskian Q ω)`.
* `foldedWronskian Q ω = C (det c) · foldedWronskian P ω` with `det c ≠ 0`
  (`foldedWronskian_change_basis`), and multiplying by a nonzero constant leaves the root
  multiplicity unchanged, so `d ≤ rootMultiplicity a (foldedWronskian P ω)`.

The two genuine side conditions are made explicit: `n ≤ s` (the folded-Wronskian has only
`n = dim A` dilation rows, which must lie within the `s` folds — exactly the design-relevant
range `dim A ≤ s`) and `foldedWronskian P ω ≠ 0` (GK16 Lemma 12, now a theorem under
admissibility).

Everything here is `sorry`/axiom-clean.
-/

open Polynomial Matrix

namespace ArkLib.FRS.GK16

variable {F : Type*} [Field F]

/-- **Multiplying by a nonzero constant preserves root multiplicity.** For `c ≠ 0`,
`rootMultiplicity a (C c * p) = rootMultiplicity a p`. -/
theorem rootMultiplicity_C_mul {p : F[X]} {c a : F} (hc : c ≠ 0) :
    rootMultiplicity a (Polynomial.C c * p) = rootMultiplicity a p := by
  by_cases hp : p = 0
  · simp [hp]
  · have hCne : (Polynomial.C c) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
    have hmul : Polynomial.C c * p ≠ 0 := mul_ne_zero hCne hp
    rw [rootMultiplicity_mul hmul]
    have hC0 : rootMultiplicity a (Polynomial.C c) = 0 := by
      apply rootMultiplicity_eq_zero
      rw [Polynomial.IsRoot, Polynomial.eval_C]
      exact hc
    rw [hC0, zero_add]

/-- **Each dilation entry of an orbit-vanishing column is `(X - C a)`-divisible.** If a
polynomial `Q` vanishes at every orbit point `a · ω^b` for `b : Fin n` with `(b : ℕ) < s`
(supplied via `hvanish`), then for every dilation row `b : Fin n` the folded-Wronskian
entry `(Q).comp (C (ω^b) · X)` is divisible by `(X - C a)`. -/
theorem X_sub_C_dvd_dilate_entry {n : ℕ} (Q : F[X]) (ω a : F)
    (b : Fin n) (hvanish : Q.eval (a * ω ^ (b : ℕ)) = 0) :
    (X - C a) ∣ Q.comp (Polynomial.C (ω ^ (b : ℕ)) * Polynomial.X) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_comm (ω ^ (b : ℕ)) a]
  exact hvanish

/-- **GK16 Claim 16 engine — per-coordinate multiplicity lower bound.** Let `P : Fin n →
F[X]` be the realizing family of a `dim A = n`-dimensional subspace, `L := foldedWronskian
P ω` its (nonzero) folded Wronskian, and `a : F` an evaluation point. Suppose:

* `Q : Fin n → F[X]` is an *invertible* `F`-linear recombination of `P`
  (`Q l = ∑ i, c l i • P i`, `det c ≠ 0`) — a basis of the same space adapted to the
  `a`-vanishing subspace;
* `T : Finset (Fin n)` has card `d` and indexes members of `Q` that vanish on the orbit of
  `a`: `∀ l ∈ T, ∀ b : Fin n, (Q l).eval (a * ω ^ (b : ℕ)) = 0`.

Then `d ≤ rootMultiplicity a L`. (The orbit-vanishing hypothesis ranges over the `n`
dilation rows; that these are genuine fold-zeros is the caller's `n ≤ s` side condition,
already discharged when `hvanish` is produced from `A_i`-membership.) -/
theorem claim16_rootMultiplicity_ge {n : ℕ} (P Q : Fin n → F[X]) (ω a : F)
    (c : Fin n → Fin n → F) (hc : (Matrix.of c).det ≠ 0)
    (hQ : ∀ l, Q l = ∑ i, c l i • P i)
    (hL : foldedWronskian P ω ≠ 0)
    (T : Finset (Fin n))
    (hvanish : ∀ l ∈ T, ∀ b : Fin n, (Q l).eval (a * ω ^ (b : ℕ)) = 0) :
    T.card ≤ rootMultiplicity a (foldedWronskian P ω) := by
  classical
  -- `foldedWronskian Q ω = C (det c) * foldedWronskian P ω`, nonzero.
  have hcb : foldedWronskian Q ω
      = Polynomial.C ((Matrix.of c).det) * foldedWronskian P ω := by
    rw [show Q = (fun l => ∑ i, c l i • P i) from funext hQ]
    exact foldedWronskian_change_basis P ω c
  have hQW_ne : foldedWronskian Q ω ≠ 0 := by
    rw [hcb]
    exact mul_ne_zero (by rwa [Ne, Polynomial.C_eq_zero]) hL
  -- Columns of the dilation matrix of `Q` in `T` are `(X - C a)`-divisible.
  have hcol : ∀ l ∈ T, ∀ b : Fin n,
      (X - C a) ∣ (dilateMatrix Q (fun b => Polynomial.C (ω ^ (b : ℕ)) * Polynomial.X)) b l := by
    intro l hl b
    change (X - C a) ∣ (Q l).comp (Polynomial.C (ω ^ (b : ℕ)) * Polynomial.X)
    exact X_sub_C_dvd_dilate_entry (Q l) ω a b (hvanish l hl b)
  -- Factor `(X - C a)^d` out of `det = foldedWronskian Q ω`.
  have hmult_Q : T.card ≤ rootMultiplicity a (foldedWronskian Q ω) := by
    have := le_rootMultiplicity_det_of_col_dvd
      (dilateMatrix Q (fun b => Polynomial.C (ω ^ (b : ℕ)) * Polynomial.X)) T a
      (by rw [← foldedWronskian]; exact hQW_ne) hcol
    rwa [← foldedWronskian] at this
  -- Transport the multiplicity across the nonzero-constant factor.
  rwa [hcb, rootMultiplicity_C_mul hc] at hmult_Q

end ArkLib.FRS.GK16
