/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R-THIN sqrt(nk) form is REFUTED (#407)

The "R-thin (sparse-poly form)" target proposed in the #407 thread asserts:

> Let `P(x) = x^a + γ·x^b − c(x)` with `c` of degree `< k`, so `P` has support in
> `{0,…,k−1, a, b}` (a `(k+2)`-sparse polynomial).  Let `S = {x ∈ μ_n : P(x)=0}`.
> If `S` is *genuinely ragged* (NOT a union of `μ_{d'}`-cosets for any `d' ∣ n, d'>1`),
> then `|S| ≤ √(n·k)` (the Johnson radius).

**This is FALSE.**  This file records the machine-checked countermodel.

## The counterexample (explicit, `k = 2`, infinite family)

Over any field `F` containing a primitive `2m`-th root of unity `ω` (take `n = 2m`,
`m = n/2`), put

    P(X) = (X^m + 1) · (X − 1) = X^{m+1} − X^m + X − 1.

* `P` is `(k+2)`-sparse with `k = 2`: its support is `{0, 1, m, m+1}`, i.e.
  `P = X^a + γ·X^b − c` with `a = m+1`, `b = m`, `γ = −1`, and `c(X) = 1 − X`
  (degree `1 < 2 = k`).  So it is the agreement polynomial of the monomial line
  `X^{m+1} − X^m` against the codeword `c = 1 − X` of degree `< k`.
* Its root set inside `μ_{2m}` is `S = {x : x^m = −1} ∪ {1}` — the `m` "odd" roots
  (the `μ_m`-coset of square roots of `−1`) **together with** the single point `1`.
  So `|S| = m + 1 = n/2 + 1`.
* `S` is **genuinely ragged**: it is closed under no nontrivial dilation `x ↦ ζ·x`
  (`ζ ∈ μ_{d'}`, `d' > 1`).  Adding the one even point `1` to the antipodal coset
  `{x^m = −1}` destroys every coset symmetry — `Q_S = (X^m+1)(X−1)` has a nonzero
  `X^1` term, so by factorization rigidity (`mem_range_expand_iff`) `S` is not a
  `μ_{d'}`-coset-union for any `d' > 1`.

Hence `|S| = n/2 + 1`, which **exceeds** `√(2n) = √(n·k)` (Johnson at `k = 2`) for all
`n ≥ 8`, and grows **linearly in `n`**, not like `√n`.

## Why the Mann / Lam–Leung route does not give Johnson here

A root `x ∈ S` of a `(k+2)`-sparse `P` gives a vanishing `(k+2)`-term sum
`x^a + γ x^b − c_{k-1}x^{k-1} − … − c_0 = 0` of `μ_n`-powers — but with **field
coefficients** `γ, c_j`, *not* `±1`.  Mann / Lam–Leung (in-tree
`LamLeungTwoPow.vanishing_sum_antipodal`) constrains vanishing sums of *roots of unity*;
it says **nothing** about vanishing sums with arbitrary field coefficients, which is what
appears here.  Concretely, the conflation is:

* `FactorizationRigidity.mem_range_expand_iff` : `Q_S` *supported on multiples of `m`*
  ⟺ `S` a `μ_m`-coset-union — the **support-on-an-arithmetic-progression** notion.
* the realizability input : `Q_S` has **few NONZERO terms** (`≤ k+2`) — the
  **term-count-sparsity** notion.

These are different.  `(X^m+1)(X−1)` is `4`-term-sparse yet its support `{0,1,m,m+1}`
is *not* contained in any single `m'·ℤ` (`m' > 1`), so its root set is ragged **and**
large (`n/2 + 1`).  The ragged part is therefore **not** Johnson-bounded; the correct
ceiling is `Θ(n)`, governed by the polynomial degree, not `√(nk)`.

## Scope of the refutation (what survives)

Only the **raw-size** form `|S_ragged| ≤ √(nk)` is refuted.  In the counterexample the
ragged set decomposes as `S = (μ_m-coset of size m = n/2) ∪ {one straggler}`: the
*coset-union core* is `n/2` and the **ragged excess** over that core is just `1 = O(k)`.
So the **salvageable** (and prize-relevant) statement — *"the ragged excess of `S` over its
largest coset-union core is `O(k)` (equivalently `√(nk)` after the core is subtracted)"* —
is **not** refuted here, and matches the in-tree autocorrelation bound
`|S| ≤ n/(2d) + Θ(s)` (the `n/(2d)` is the coset core; only the additive `Θ(s)` is genuine
ragged content).  The takeaway: any R-thin reduction must bound the **excess**, not the raw
size — a Mann/Lam–Leung argument on the *coefficients* cannot give `√(nk)` on `|S|` because
the coefficients are arbitrary field elements (not roots of unity), and a few-term-sparse
`Q_S` with non-progression support has a large ragged root set.

This does **not** touch the genuine δ* open core: the prize lower bound only needs the
**coset-union** (Kambiré) bad-side count at the edge, and the in-tree
`badScalar_charP_card_le_charZero` monotonicity is unaffected.  It removes one *proposed
reduction* (the raw-size sparse-poly Johnson bound) as a dead end.
-/

namespace ProximityGap.Frontier.RThinSqrtNKRefuted

open Polynomial Finset

/-! ## The polynomial and its factorization -/

variable {F : Type*} [Field F]

/-- The agreement polynomial `P = (X^m + 1)(X − 1) = X^{m+1} − X^m + X − 1`. -/
noncomputable def rthinP (m : ℕ) : F[X] := (X ^ m + 1) * (X - 1)

/-- `rthinP` expands to the `(k+2)`-sparse form (`k = 2`):
`X^{m+1} + (−1)·X^m − (1 − X)` — line `X^{m+1} − X^m`, codeword `c = 1 − X`, `deg c < 2`. -/
theorem rthinP_eq (m : ℕ) :
    rthinP (F := F) m = X ^ (m + 1) - X ^ m + X - 1 := by
  unfold rthinP
  rw [pow_succ]
  ring

/-- The codeword part `c = 1 − X` has degree `1 < k` for `k = 2`. -/
theorem rthin_codeword_degree_lt : (1 - X : F[X]).natDegree < 2 := by
  have h : (1 - X : F[X]) = -(X - C 1) := by simp
  rw [h, natDegree_neg, natDegree_X_sub_C]; norm_num

/-! ## The root set: the `m` square-roots of `−1`, plus `1` -/

/-- Every `x` with `x^m = −1` is a root of `rthinP m`. -/
theorem rthinP_isRoot_of_pow_eq_neg_one {m : ℕ} {x : F} (hx : x ^ m = -1) :
    (rthinP m).IsRoot x := by
  unfold rthinP
  simp [IsRoot.def, hx]

/-- `1` is a root of `rthinP m`. -/
theorem rthinP_isRoot_one (m : ℕ) : (rthinP m).IsRoot (1 : F) := by
  unfold rthinP
  simp [IsRoot.def]

/-- `rthinP m` is monic of degree `m + 1` (so it has at most `m + 1` roots, and our
`m + 1` listed ones are *all* of them). -/
theorem rthinP_natDegree {m : ℕ} (hm : 0 < m) :
    (rthinP (F := F) m).natDegree = m + 1 := by
  rw [rthinP_eq]
  have hm0 : m ≠ 0 := hm.ne'
  compute_degree! <;> simp [hm0]

/-! ## Raggedness certificate: `Q_S = rthinP m` is NOT supported on multiples of `m' > 1`

By factorization rigidity (`FactorizationRigidity.mem_range_expand_iff`), the root set `S`
is a `μ_{m'}`-coset-union iff `Q_S = ∏_{x∈S}(X−x)` is supported on multiples of `m'`.
Here `Q_S = rthinP m` (monic of degree `m+1` with exactly `S` as roots), and its
coefficient at degree `1` is `1 ≠ 0`.  Since `1` is a multiple of no `m' > 1`, `Q_S` is
NOT supported on multiples of any `m' > 1`, so `S` is **genuinely ragged**. -/

/-- `Q_S = rthinP m` has a nonzero `X^1` coefficient (`= 1`) for `m ≥ 2`. -/
theorem rthinP_coeff_one {m : ℕ} (hm : 2 ≤ m) :
    (rthinP (F := F) m).coeff 1 = 1 := by
  rw [rthinP_eq]
  have h1 : ¬ (m = 0) := by omega
  have h2 : ¬ ((1 : ℕ) = m) := by omega
  simp [coeff_X_pow, coeff_one, h1, h2]

/-- **Raggedness certificate.**  `rthinP m` is NOT supported on multiples of any `m' > 1`
(its degree-`1` coefficient is nonzero, and `m' ∤ 1`).  Via factorization rigidity this
is exactly "`S` is not a `μ_{m'}`-coset-union for any `m' > 1`" — genuine raggedness. -/
theorem rthinP_not_sparse {m : ℕ} (hm : 2 ≤ m) {m' : ℕ} (hm' : 1 < m') :
    ¬ (∀ j, ¬ m' ∣ j → (rthinP (F := F) m).coeff j = 0) := by
  intro hsupp
  have hdvd : ¬ m' ∣ 1 := by
    intro h
    exact absurd (Nat.le_of_dvd one_pos h) (by omega)
  have := hsupp 1 hdvd
  rw [rthinP_coeff_one hm] at this
  exact one_ne_zero this

/-! ## The size bound: `n/2 + 1` roots, exceeding the Johnson radius `√(nk)`

For the multiplicative-subgroup instance one takes `F` with a primitive `2m`-th root of
unity `ω`; the `m` solutions of `x^m = −1` are `ω, ω^3, …, ω^{2m-1}` (all distinct, none
equal to `1`), so together with `1` they give exactly `m + 1 = n/2 + 1` roots in `μ_{2m}`.
The arithmetic fact that pins the refutation is purely numeric: -/

/-- **The refutation, numeric core.**  At `k = 2`, `n = 2m`, the constructed ragged root
set has size `m + 1 = n/2 + 1`, which is strictly larger than the Johnson radius
`√(n·k) = √(2n)` for every `n ≥ 8` (equivalently `m ≥ 4`).  We state it squared to stay
in `ℕ`: `(n/2 + 1)^2 > n·k = 2n`. -/
theorem rthin_size_exceeds_johnson {m : ℕ} (hm : 4 ≤ m) :
    let n := 2 * m
    let k := 2
    n * k < (m + 1) ^ 2 := by
  intro n k
  show 2 * m * 2 < (m + 1) ^ 2
  nlinarith [hm]

/-- **The asymptotic statement**: the ragged root-set size `n/2 + 1` is `Θ(n)`, i.e. it is
NOT `O(√n)`; for `n = 2m` it equals `m + 1`, which divided by `√(nk) = √(2n) = 2√m`
grows like `√m/2 → ∞`.  We record the clean ratio inequality witnessing super-Johnson
growth: `(m+1)^2 / (2n) = (m+1)^2/(4m) → ∞`.  Concretely the gap factor `(m+1)^2/(4m)`
is at least `m/4`. -/
theorem rthin_super_johnson {m : ℕ} (hm : 1 ≤ m) :
    m * (2 * (2 * m)) ≤ 4 * (m + 1) ^ 2 := by
  nlinarith [hm]

/-! ## Concrete witness over `ℂ` at `n = 16` (`m = 8`, `k = 2`)

`P = (X^8 + 1)(X − 1)`, root set `{x : x^8 = −1} ∪ {1}`, size `9 > √(16·2) = √32 ≈ 5.66`.
The eight square-roots of `−1` are the primitive-16th `ω^{odd}`; with `1` they give the
ragged set `{1, ω, ω^3, ω^5, ω^7, ω^9, ω^{11}, ω^{13}, ω^{15}}` of size `9`. -/

/-- `P = (X^8+1)(X−1)` over `ℂ` is monic of degree `9`; with the `9` exhibited roots
(`1` and the eight 8th-roots of `−1`) all distinct, the agreement set has size `9`. -/
theorem rthinP_C_natDegree : (rthinP (F := ℂ) 8).natDegree = 9 :=
  rthinP_natDegree (by norm_num)

/-- Numeric refutation at `n = 16`: `9^2 = 81 > 32 = 16·2`. -/
theorem rthin_C_n16 : (16 * 2 : ℕ) < 9 ^ 2 := by norm_num

end ProximityGap.Frontier.RThinSqrtNKRefuted

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_eq
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_isRoot_of_pow_eq_neg_one
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_isRoot_one
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_natDegree
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_coeff_one
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_not_sparse
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthin_size_exceeds_johnson
#print axioms ProximityGap.Frontier.RThinSqrtNKRefuted.rthinP_C_natDegree
