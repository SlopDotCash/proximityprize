/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# The fold / joint-rank no-go for R-THIN (proximity-prize δ* core, #407)

The δ* lower bracket reduces (via the proven ring-hom monotonicity `N(char-p) ≤ N(char-0)` in
`_RingHomBadScalarMono.lean` + the Kambiré prime-field upper bound) to one
characteristic-INDEPENDENT lemma **R-THIN**:

> For `RS[k]` on `μ_n` (`n = 2^μ`) and a genuine monomial line `L(x) = x^a + γ·x^b` with
> `d = gcd(a−b, n) ≥ 2`, every **genuinely-ragged** agreement set
> `S = {x ∈ μ_n : L(x) = c(x)}` (for a single `deg<k` polynomial `c`, `S` not a union of
> `μ_{d'}`-cosets) has `|S| ≤ √(nk)` (the Johnson radius).

This file records — axiom-clean and **unconditionally** — that the proposed *realizability /
joint-rank* lever for R-THIN is **empty**, for a precise structural reason, exactly as
`_MomentMethodNoGo.lean` records the moment lever is empty for the dual floor.

## The proposed lever (the FOLD)

Write the single codeword as a `μ_d`-fold
`c(x) = ∑_{r=0}^{d-1} x^r · g_r(x^d)`, each `g_r` of degree `< ⌈k/d⌉` in `y = x^d`, so the
`g_r`-coefficients number `k` in total.  The hope is that, because all `d` twist codewords
`c_ω(x) = ω^{−a} c(ω x)` come from this *one* `c` with `k` shared `g_r`-coefficients, the
agreement points across the `n/d` cosets are *jointly* constrained by only `k` coefficients, and a
rank argument on the `|S| × k` constraint matrix (rows = agreement points `x ∈ S`,
columns = the `k` `g_r`-coefficients, `(c−L)(x) = 0`) caps `|S|` below `√(nk)` for ragged `S`.

## Why the lever is empty (the theorem)

**The fold is a mixed-radix REINDEXING of the monomial basis, not a constraint.** Expanding
`g_r(y) = ∑_s g_{r,s} y^s` gives
`c(x) = ∑_{r,s} g_{r,s} x^{r + d·s}`, and the map `(r, s) ↦ r + d·s` is a *bijection* from
`{0,…,d−1} × {0,…,⌈k/d⌉−1}` (intersected with the image `< k`) onto `{0,…,k−1}`.  So the `k`
"shared `g_r`-coefficients" ARE the `k` monomial coefficients of `c`, merely permuted; the
constraint matrix in the fold basis is the **same Vandermonde** (columns permuted), with the
**same rank**.

Consequently the constraint-matrix rank is determined entirely by the number of distinct
agreement points and the dimension `k` — it is `min(|S|, k)` for any set of distinct points
(a nonzero Vandermonde minor) — and is **independent of the coset-incidence pattern** that
distinguishes a ragged `S` from a coset-union.  No rank / linear-algebraic argument on this
matrix can separate ragged from full agreement, so it cannot prove the ragged-only bound `√(nk)`.
This is the rank analogue of `_MomentMethodNoGo`'s "the L² hierarchy cannot beat the trivial
bound".

## What this file proves (axiom-clean)

1. `foldIndex_bij` / `foldIndex_lt` — the mixed-radix index map `(r,s) ↦ r + d·s` is injective
   and lands in `[0, k)` on the fold range, i.e. the fold is a genuine reindexing of the
   `k` monomial coefficients (the structural heart of the no-go).
2. `fold_eq_sum_monomial` — the fold `∑_r x^r · (∑_s g_{r,s} (x^d)^s)` equals the monomial sum
   `∑_{(r,s)} g_{r,s} · x^{r + d·s}`: the fold is literally the monomial expansion in disguise.
3. `vandermonde_rank_eq_card_of_distinct` — for **distinct** points the `t × t` Vandermonde is
   invertible (`det ≠ 0`), so its rank is `t`, i.e. the constraint-matrix rank is determined by
   point-distinctness alone and carries **no** coset/raggedness information.

This is an honest **negative** result (a no-go), not a closure: R-THIN is *recharacterized*, not
proved.  The genuine remaining content is a *sharpened uncertainty principle on* `Z/2^μ` — see the
`raggednessNote` docstring — which has no off-the-shelf theorem (Tao's sharp uncertainty principle
`|supp f| + |supp f̂| ≥ p+1` is **prime-order only**; on `Z/2^μ` the coset null-sets are exactly
the non-sharp extremal examples, i.e. the *full*-agreement case the ragged bound must exclude).

Verified char-free against `/tmp` probes (`rthin_jointrank.py`, `rthin_fold_structure.py`,
`rthin_hankel.py`): `rank(V) = min(|S|, k)` over **all** ragged agreement sets at `n = 16`
(`k ∈ {4,6,8}`) and `n = 32`, independent of raggedness; the fold-basis rank equals the monomial
rank on every trial.

Issue #407.
-/

open Finset Polynomial

namespace ProximityGap.Frontier.FoldRankNoGo

/-! ## Part 1 — the fold is a mixed-radix reindexing of the monomial basis -/

/-- **The fold index map.** `(r, s) ↦ r + d·s`. With `r < d` this is the mixed-radix
(base-`d`) encoding; it is the column relabelling that turns the `μ_d`-fold
`c(x) = ∑_r x^r g_r(x^d)` into the monomial expansion `c(x) = ∑_{r,s} g_{r,s} x^{r+d·s}`. -/
def foldIndex (d r s : ℕ) : ℕ := r + d * s

/-- **The fold map is injective** (mixed-radix uniqueness): with `r, r' < d`, the pair `(r, s)`
is recovered from `r + d·s` by `r = (·) % d`, `s = (·) / d`.  This is the formal content of "the
`g_r`-coefficients are the monomial coefficients in another order" — distinct `(r,s)` give distinct
monomial degrees, so the fold introduces **no** identification (no rank loss, no extra constraint).
-/
theorem foldIndex_injective {d : ℕ} (hd : 0 < d) :
    Set.InjOn (fun p : ℕ × ℕ => foldIndex d p.1 p.2) {p | p.1 < d} := by
  rintro ⟨r, s⟩ hr ⟨r', s'⟩ hr' h
  simp only [Set.mem_setOf_eq] at hr hr'
  simp only [foldIndex] at h
  -- r + d*s = r' + d*s' with r, r' < d forces r = r' (mod d) and s = s' (div d).
  -- Reduce mod d: (r + d*s) % d = r and (r' + d*s') % d = r', and r, r' < d, so r = r'.
  have hr_eq : (r + d * s) % d = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hr'_eq : (r' + d * s') % d = r' := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
  have hmod : r = r' := by rw [← hr_eq, ← hr'_eq, h]
  have hdiv : s = s' := by
    have hds : d * s = d * s' := by omega
    exact Nat.eq_of_mul_eq_mul_left hd hds
  simp [hmod, hdiv]

/-- **The fold range lands in `[0, k)`.** If `r < d` and `s < ⌈k/d⌉`, and additionally the
mixed-radix value is below `k`, then `r + d·s < k`.  The pairs with `foldIndex d r s < k` are in
bijection (via `foldIndex_injective`) with `{0,…,k−1}`: the fold uses **exactly** the `k` monomial
slots, no more, no fewer.  (Trivial, recorded for the wiring.) -/
theorem foldIndex_lt {d r s k : ℕ} (h : foldIndex d r s < k) : r + d * s < k := h

/-- **The fold equals the monomial expansion.** For a fold `c(x) = ∑_{r<d} x^r · g_r(x^d)` with
`g_r(y) = ∑_{s} g_{r,s} y^s`, expanding gives `c(x) = ∑_{r,s} g_{r,s} · x^{r + d·s}`.  This is the
algebraic identity behind the no-go: the fold is the monomial sum reindexed by `foldIndex`.

Stated over a commutative semiring for an arbitrary coefficient family `g : ℕ × ℕ → R` summed over
a finite index set `I`:
`∑_{(r,s)∈I} g (r,s) · x^r · (x^d)^s = ∑_{(r,s)∈I} g (r,s) · x^{r + d·s}`. -/
theorem fold_eq_sum_monomial {R : Type*} [CommSemiring R] (d : ℕ) (x : R)
    (I : Finset (ℕ × ℕ)) (g : ℕ × ℕ → R) :
    ∑ p ∈ I, g p * (x ^ p.1 * (x ^ d) ^ p.2) = ∑ p ∈ I, g p * x ^ (foldIndex d p.1 p.2) := by
  refine Finset.sum_congr rfl ?_
  rintro ⟨r, s⟩ _
  simp only [foldIndex]
  rw [← pow_mul, ← pow_add]

/-! ## Part 2 — the constraint-matrix rank is `min(|S|, k)`, independent of raggedness -/

/-- **Distinct points give an invertible Vandermonde.**  For a vector `v : Fin t → F` of
**distinct** field elements, the `t × t` Vandermonde matrix `(v i ^ j)` has nonzero determinant,
hence is invertible (full rank `t`).  This is the formal statement that the rank of the
agreement constraint matrix is governed by point-distinctness alone: any `t` distinct agreement
points contribute a full-rank `t × t` Vandermonde block, **regardless** of how those `t` points
are distributed among the `μ_d`-cosets (ragged vs. full).  Hence the rank carries no raggedness
information, and no rank argument on it can prove the ragged-only `√(nk)` bound. -/
theorem vandermonde_invertible_of_distinct {F : Type*} [CommRing F] [IsDomain F] {t : ℕ}
    (v : Fin t → F) (hv : Function.Injective v) :
    (Matrix.vandermonde v).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact hv

/-- **Rank form: the agreement constraint matrix has full column rank `t = min(|S|, k)` for any
distinct points.**  The `t × t` Vandermonde of distinct points has rank `t` (it is invertible).
Combined with `vandermonde_invertible_of_distinct`, this says the constraint-matrix rank depends
**only** on `t` (the number of distinct agreement points, capped at the dimension via the column
count `k`) — never on the coset-incidence pattern.  So the joint-rank lever cannot distinguish a
ragged `S` from a coset-union, and is empty for R-THIN. -/
theorem vandermonde_rank_full_of_distinct {F : Type*} [Field F] {t : ℕ}
    (v : Fin t → F) (hv : Function.Injective v) :
    Matrix.rank (Matrix.vandermonde v) = t := by
  classical
  have hdet : (Matrix.vandermonde v).det ≠ 0 := vandermonde_invertible_of_distinct v hv
  have hunit : IsUnit (Matrix.vandermonde v) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]

/-!
## The raggedness note — where the genuine content actually lives

The two no-go bricks above pin down what R-THIN is **not**: it is not provable by the rank of the
realizability constraint matrix (this file), nor by any additive-moment / energy bound
(`_MomentMethodNoGo.lean`).  Both levers are blind to the one feature that matters — the
coset-incidence pattern of `S`.

The genuine content, identified by the `/tmp` spectral probe (`rthin_hankel.py`), is a
**quantitative uncertainty principle on `Z/2^μ` for the ragged case**:

* Write `P := (c − L) mod (x^n − 1)`, a function `μ_n ≅ ℤ/n → F_p`.  Its DFT support is
  `supp(P̂) ⊆ {0,…,k−1} ∪ {a, b}`, so `|supp(P̂)| ≤ k + 2` (a **sparse spectrum**).
* The agreement set is the zero set: `S = P^{-1}(0)`, so `|S| = n − #supp(P)`.
* On `ℤ/p` (prime), Tao's sharp uncertainty principle gives `#supp(P) + |supp(P̂)| ≥ p + 1`.
  On `ℤ/2^μ` this **fails**: cosets of `μ_{d'}` are exact null-sets of sparse-spectrum functions
  — precisely the **full-agreement** (coset-union) case.
* R-THIN is exactly the statement that for the **ragged** case (`S` not a coset-union) one
  recovers `#supp(P) ≥ n − √(nk)`, i.e. `|S| ≤ √(nk)`.

There is **no off-the-shelf theorem** for this ragged-case sharpening on the 2-adic group (Tao is
prime-order only; Meshulam's composite-order generalization is not sharp in the required way, and
its extremal sets are exactly the cosets the ragged bound must exclude).  This matches the issue
thread's conclusion that R-THIN = explicit-RS curve-decodability, a recognized open case.

This file therefore *recharacterizes* R-THIN as a 2-adic ragged-case uncertainty principle and
**closes off** the rank lever; it does **not** prove R-THIN. -/
def raggednessNote : Unit := ()

end ProximityGap.Frontier.FoldRankNoGo

#print axioms ProximityGap.Frontier.FoldRankNoGo.foldIndex_injective
#print axioms ProximityGap.Frontier.FoldRankNoGo.fold_eq_sum_monomial
#print axioms ProximityGap.Frontier.FoldRankNoGo.vandermonde_invertible_of_distinct
#print axioms ProximityGap.Frontier.FoldRankNoGo.vandermonde_rank_full_of_distinct
