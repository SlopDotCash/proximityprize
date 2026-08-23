/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RSDistinctness
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CS25 Claim 4 — the deep-hole distinct-value count (Schwartz–Zippel + Cauchy–Schwarz)

This file proves the *combinatorial heart* of [CS25] (Crites–Stewart, eprint 2025/2046)
Theorem 2 — namely the paper's **Claim 4**, derandomized into a counting statement.

[CS25] Claim 4 states: given `L` distinct degree-`≤ k` polynomials `p^(1), …, p^(L)` and a
sampling set `T = F \ D` of size `s = q - n`, there exists a point `a ∈ T` such that the
number of *distinct values* `|{p^(j)(a) : 1 ≤ j ≤ L}|` is at least
`(L-1)·s / (s + (L-1)·k)`.

We prove the cleaner (strictly stronger) bound `L·s / (s + (L-1)·k)`, which is what falls
out of the Cauchy–Schwarz / collision-count argument when the diagonal `1/L` term is kept
exact (the paper rounds it down to `(L-1)`).  Writing the list size as `L = L0 + 1`, this is
`(L0+1)·s / (s + L0·k) > L0·s / (s + L0·k) = E(L0)`, supplying the *strict* margin that the
in-tree `hClaim3` residual demands at the boundary `E(L0) = εq`.

## Main results

- `card_collide_le_of_ne` — two distinct degree-`< K` polynomials collide on at most `K-1`
  points of any sampling set (RS distinctness, repackaged at `domain = id`).
- `pairCollisions_eq_sum_sq` — the ordered colliding-pair count at a point equals the
  sum over image values of the squared fiber sizes.
- `sq_card_le_card_image_mul_pairCollisions` — Cauchy–Schwarz: `L² ≤ |image| · (pair count)`.
- `sum_pairCollisions_le` — summed over the sampling set, the pair count is at most
  `L·|T| + L·(L-1)·(K-1)`.
- `cs25_claim4_exists_point` — the existence statement: some `a ∈ T` has
  `|image| ≥ L·|T| / (|T| + (L-1)·(K-1))`.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3 / Claim 4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25

open Polynomial Finset

variable {F : Type} [Field F] [DecidableEq F]

/-- **Polynomial collision bound (`= F`-domain instance of RS distinctness).**
Two distinct polynomials of degree `< K` agree on fewer than `K` points of any finite
sampling set `T ⊆ F`. -/
theorem card_collide_lt_of_ne {K : ℕ} {p q : F[X]}
    (hp : p ∈ Polynomial.degreeLT F K) (hq : q ∈ Polynomial.degreeLT F K)
    (hpq : p ≠ q) (T : Finset F) :
    (T.filter (fun a => p.eval a = q.eval a)).card < K := by
  classical
  -- Use RS distinctness with the identity embedding `domain = id` on the subtype `T`.
  -- Direct route: the colliding points are roots of `p - q ≠ 0`, which has `natDegree < K`.
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hdmem : p - q ∈ Polynomial.degreeLT F K := Submodule.sub_mem _ hp hq
  have hdeg : (p - q).natDegree < K := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hd0]
    exact Polynomial.mem_degreeLT.mp hdmem
  set S : Finset F := T.filter (fun a => p.eval a = q.eval a) with hS
  have hroots : ∀ a ∈ S, (p - q).IsRoot a := by
    intro a ha
    have hxe := (Finset.mem_filter.mp ha).2
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, hxe, sub_self]
  have hcard := ProximityGap.card_roots_finset_le_natDegree hd0 hroots
  omega

section Counting

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The number of *ordered* colliding pairs of list-indices at a point `a`:
`#{(j, j') : (p j)(a) = (p j')(a)}`. -/
def pairCollisions (p : ι → F[X]) (a : F) : ℕ :=
  (Finset.univ.filter (fun jj : ι × ι => (p jj.1).eval a = (p jj.2).eval a)).card

/-- The number of *distinct values* `(p j)(a)` over all list-indices `j`. -/
def numDistinct (p : ι → F[X]) (a : F) : ℕ :=
  (Finset.univ.image (fun j => (p j).eval a)).card

/-- **Cauchy–Schwarz step.**  `L² ≤ (#distinct values) · (#colliding pairs)` at any point.
This is the [CS25] Claim-4 application of Cauchy–Schwarz to the fiber-size vector. -/
theorem sq_card_le_numDistinct_mul_pairCollisions (p : ι → F[X]) (a : F) :
    (Fintype.card ι) ^ 2 ≤ numDistinct p a * pairCollisions p a := by
  classical
  set f : ι → F := fun j => (p j).eval a with hf
  set img : Finset F := Finset.univ.image f with himg
  -- fiber size of a value `y`
  set cnt : F → ℕ := fun y => (Finset.univ.filter (fun j => f j = y)).card with hcnt
  -- `∑_{y ∈ img} cnt y = |ι|`.
  have hsum1 : ∑ y ∈ img, cnt y = Fintype.card ι := by
    rw [hcnt, himg]
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ.image f)]
    · simp [Finset.card_univ]
    · intro x _; exact Finset.mem_image_of_mem f (Finset.mem_univ x)
  -- `∑_{y ∈ img} (cnt y)^2 = pairCollisions`.
  have hsum2 : ∑ y ∈ img, (cnt y) ^ 2 = pairCollisions p a := by
    rw [pairCollisions]
    -- count pairs by grouping over the common value
    rw [show (Finset.univ.filter (fun jj : ι × ι => (p jj.1).eval a = (p jj.2).eval a))
          = (Finset.univ.filter (fun jj : ι × ι => f jj.1 = f jj.2)) from by
            simp only [hf]]
    -- pairs with f j1 = f j2 partition by their common value
    have : (Finset.univ.filter (fun jj : ι × ι => f jj.1 = f jj.2)).card
        = ∑ y ∈ img, (Finset.univ.filter (fun j => f j = y)).card ^ 2 := by
      classical
      -- regroup the product set by the shared value
      rw [Finset.card_filter]
      rw [Fintype.sum_prod_type]
      -- ∑_{j1} ∑_{j2} [f j1 = f j2] = ∑_{j1} cnt (f j1)
      have hinner : ∀ j1 : ι, (∑ j2 : ι, if f j1 = f j2 then (1 : ℕ) else 0)
          = cnt (f j1) := by
        intro j1
        simp only [hcnt, Finset.card_filter]
        refine Finset.sum_congr rfl ?_
        intro j2 _
        by_cases h : f j2 = f j1 <;> simp_all [eq_comm]
      rw [Finset.sum_congr rfl (fun j1 _ => hinner j1)]
      -- ∑_{j1 ∈ univ} cnt (f j1) = ∑_{y ∈ img} cnt y • cnt y
      have hcomp := Finset.sum_comp (s := (Finset.univ : Finset ι)) (f := cnt) (g := f)
      rw [hcomp, ← himg]
      refine Finset.sum_congr rfl ?_
      intro y _
      simp only [hcnt, smul_eq_mul]
      ring
    rw [this]
  -- Apply Cauchy–Schwarz over `img`.
  have hcs := sq_sum_le_card_mul_sum_sq (s := img) (f := fun y => (cnt y : ℕ))
  rw [hsum1] at hcs
  rw [numDistinct, ← himg]
  calc (Fintype.card ι) ^ 2 = (Fintype.card ι) ^ 2 := rfl
    _ ≤ img.card * ∑ y ∈ img, (cnt y) ^ 2 := hcs
    _ = numDistinct p a * pairCollisions p a := by rw [hsum2, numDistinct, ← himg]

/-- **Double-counting bound on the total collision count.**  Summed over the sampling set
`T`, the ordered colliding-pair count is at most `L·|T| + (L²-L)·(K-1)`, where `L = |ι|` is
the list size: the `L` diagonal pairs collide everywhere (`|T|` each), and each of the
`L²-L` off-diagonal pairs collides on at most `K-1` points (distinct degree-`< K`
polynomials agree on `< K` points). -/
theorem sum_pairCollisions_le {K : ℕ} (p : ι → F[X])
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F K)
    (hinj : Function.Injective p) (T : Finset F) :
    ∑ a ∈ T, pairCollisions p a
      ≤ Fintype.card ι * T.card
        + (Fintype.card ι ^ 2 - Fintype.card ι) * (K - 1) := by
  classical
  -- Swap the order: ∑_a #{pairs colliding at a} = ∑_{pairs} #{a ∈ T colliding}.
  have hswap : ∑ a ∈ T, pairCollisions p a
      = ∑ jj : ι × ι, (T.filter (fun a => (p jj.1).eval a = (p jj.2).eval a)).card := by
    simp only [pairCollisions, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- Bound each pair's collision count.
  have hbound : ∀ jj : ι × ι,
      (T.filter (fun a => (p jj.1).eval a = (p jj.2).eval a)).card
        ≤ (if jj.1 = jj.2 then T.card else (K - 1)) := by
    intro jj
    by_cases hjj : jj.1 = jj.2
    · simp only [hjj, if_pos]
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    · simp only [if_neg hjj]
      have hne : p jj.1 ≠ p jj.2 := fun h => hjj (hinj h)
      have := card_collide_lt_of_ne (hdeg jj.1) (hdeg jj.2) hne T
      omega
  refine le_trans (Finset.sum_le_sum (fun jj _ => hbound jj)) ?_
  -- Evaluate ∑_{jj} (if jj.1=jj.2 then |T| else K-1).
  rw [Finset.sum_ite]
  -- diagonal pairs: card = L; off-diagonal: card = L² - L.
  have hdiag : (Finset.univ.filter (fun jj : ι × ι => jj.1 = jj.2)).card = Fintype.card ι := by
    rw [show (Finset.univ.filter (fun jj : ι × ι => jj.1 = jj.2))
          = Finset.univ.map ⟨fun j => (j, j), by intro a b h; simpa using h⟩ from by
            ext jj; simp [Prod.ext_iff, eq_comm, and_comm]]
    simp [Finset.card_univ]
  have hoff : (Finset.univ.filter (fun jj : ι × ι => ¬ jj.1 = jj.2)).card
      = Fintype.card ι ^ 2 - Fintype.card ι := by
    have htot : (Finset.univ.filter (fun jj : ι × ι => jj.1 = jj.2)).card
        + (Finset.univ.filter (fun jj : ι × ι => ¬ jj.1 = jj.2)).card
        = Fintype.card (ι × ι) := by
      rw [Finset.filter_card_add_filter_neg_card_eq_card]; rw [Finset.card_univ]
    rw [hdiag] at htot
    rw [Fintype.card_prod] at htot
    have hsq : Fintype.card ι * Fintype.card ι = Fintype.card ι ^ 2 := by ring
    omega
  rw [Finset.sum_const, Finset.sum_const, hdiag, hoff, smul_eq_mul, smul_eq_mul]

/-- **[CS25] Claim 4 (counting form).**  Given `L = |ι| ≥ 1` distinct degree-`< K`
polynomials and a nonempty sampling set `T`, there is a point `a ∈ T` whose number of
distinct evaluation values satisfies the cleared-denominator bound

  `L · |T| ≤ numDistinct p a · (|T| + (L-1)·(K-1))`.

Over `ℝ` this reads `numDistinct ≥ L·|T| / (|T| + (L-1)(K-1))`, the (strengthened) [CS25]
Claim-4 bound. -/
theorem cs25_claim4_exists_point {K : ℕ} (p : ι → F[X])
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F K)
    (hinj : Function.Injective p) (T : Finset F) (hT : T.Nonempty)
    (hL : 1 ≤ Fintype.card ι) :
    ∃ a ∈ T, Fintype.card ι * T.card
      ≤ numDistinct p a * (T.card + (Fintype.card ι - 1) * (K - 1)) := by
  classical
  set L := Fintype.card ι with hLdef
  -- Pick a point minimizing pairCollisions.
  obtain ⟨a₀, ha₀T, ha₀min⟩ := T.exists_min_image (fun a => pairCollisions p a) hT
  refine ⟨a₀, ha₀T, ?_⟩
  -- |T| · pairCollisions(a₀) ≤ ∑_a pairCollisions ≤ L·|T| + (L²-L)(K-1).
  have hmin_sum : T.card * pairCollisions p a₀ ≤ ∑ a ∈ T, pairCollisions p a := by
    calc T.card * pairCollisions p a₀
        = ∑ _a ∈ T, pairCollisions p a₀ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ T, pairCollisions p a :=
          Finset.sum_le_sum (fun a ha => ha₀min a ha)
  have hsum := sum_pairCollisions_le (K := K) p hdeg hinj T
  rw [← hLdef] at hsum
  have hbig : T.card * pairCollisions p a₀ ≤ L * T.card + (L ^ 2 - L) * (K - 1) :=
    le_trans hmin_sum hsum
  -- Cauchy–Schwarz at a₀: L² ≤ numDistinct(a₀) · pairCollisions(a₀).
  have hcs := sq_card_le_numDistinct_mul_pairCollisions p a₀
  rw [← hLdef] at hcs
  -- Combine. Set d := numDistinct, P := pairCollisions.
  set d := numDistinct p a₀ with hddef
  set P := pairCollisions p a₀ with hPdef
  -- hcs : L^2 ≤ d * P;  hbig : |T| * P ≤ L*|T| + (L²-L)(K-1)
  -- Want: L*|T| ≤ d * (|T| + (L-1)(K-1)).
  -- From hbig: |T|*P ≤ L*|T| + (L²-L)(K-1) = L*(|T| + (L-1)(K-1)).
  have hfac : L * T.card + (L ^ 2 - L) * (K - 1) = L * (T.card + (L - 1) * (K - 1)) := by
    have hLL : L ^ 2 - L = L * (L - 1) := by
      rw [pow_two, Nat.mul_sub_one]
    rw [hLL]; ring
  rw [hfac] at hbig
  -- Now |T|*P ≤ L*M where M := |T| + (L-1)(K-1).  And L² ≤ d*P.
  set M := T.card + (L - 1) * (K - 1) with hMdef
  -- Multiply hcs by |T|: |T|*L² ≤ |T|*d*P = d*(|T|*P) ≤ d*(L*M) = L*(d*M).
  -- Hence L*(L*|T|) ≤ L*(d*M).  If L>0 cancel: L*|T| ≤ d*M.
  have step1 : T.card * L ^ 2 ≤ d * (L * M) := by
    calc T.card * L ^ 2 ≤ T.card * (d * P) := by
            exact Nat.mul_le_mul_left _ hcs
      _ = d * (T.card * P) := by ring
      _ ≤ d * (L * M) := Nat.mul_le_mul_left _ hbig
  -- L*(L*|T|) ≤ L*(d*M).
  have step2 : L * (L * T.card) ≤ L * (d * M) := by
    calc L * (L * T.card) = T.card * L ^ 2 := by ring
      _ ≤ d * (L * M) := step1
      _ = L * (d * M) := by ring
  have hLpos : 0 < L := hL
  exact Nat.le_of_mul_le_mul_left step2 hLpos

/-- **[CS25] Claim 4 — real-valued strict deep-hole margin.**

Specialising `cs25_claim4_exists_point` to list size `L = L0 + 1`, polynomial degree budget
`K = k + 1`, and sampling-set size `|T| = s`, there is a point whose distinct-value count
*strictly* exceeds the [CS25] threshold `E(L0) = L0·s / (L0·k + s)`:

  `E(L0) < (numDistinct p a : ℝ)`.

The strictness is the crucial boundary margin demanded by the in-tree `hClaim3` residual: it
comes for free because the clean Cauchy–Schwarz bound keeps the diagonal term, giving the
numerator `(L0+1)·s` rather than the paper's rounded-down `L0·s`. -/
theorem cs25_claim4_strict_margin {k L0 : ℕ} (p : ι → F[X])
    (hcard : Fintype.card ι = L0 + 1)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hinj : Function.Injective p) (T : Finset F) (hT : T.Nonempty)
    (hs_pos : (0 : ℝ) < T.card) :
    ∃ a ∈ T, ((L0 : ℝ) * T.card / ((L0 : ℝ) * k + T.card)) < (numDistinct p a : ℝ) := by
  classical
  have hL : 1 ≤ Fintype.card ι := by rw [hcard]; omega
  obtain ⟨a, haT, hbound⟩ :=
    cs25_claim4_exists_point (K := k + 1) p hdeg hinj T hT hL
  refine ⟨a, haT, ?_⟩
  -- Integer bound: (L0+1)·|T| ≤ numDistinct · (|T| + L0·k).
  rw [hcard] at hbound
  simp only [Nat.add_sub_cancel] at hbound
  -- hbound : (L0+1) * |T| ≤ numDistinct a * (|T| + L0 * k)
  set d : ℕ := numDistinct p a with hddef
  set s : ℝ := (T.card : ℝ) with hsdef
  have hdR : ((L0 : ℝ) + 1) * s ≤ (d : ℝ) * (s + (L0 : ℝ) * k) := by
    have := hbound
    have hcast : (((L0 + 1) * T.card : ℕ) : ℝ) ≤ ((d * (T.card + L0 * k) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    rw [hsdef]; nlinarith [hcast]
  -- Denominator positive.
  have hden : (0 : ℝ) < (L0 : ℝ) * k + s := by
    have : (0 : ℝ) ≤ (L0 : ℝ) * k := by positivity
    rw [hsdef] at hs_pos ⊢; linarith
  rw [div_lt_iff₀ hden]
  -- Want: L0·s < d·(L0·k + s).  Have: (L0+1)·s ≤ d·(s + L0·k).
  have hk0 : (0 : ℝ) ≤ (L0 : ℝ) * k := by positivity
  nlinarith [hdR, hs_pos, hk0]

end Counting

end CodingTheory.CS25
