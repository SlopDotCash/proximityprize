/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Schur/Lagrange bridge (#407, GRIND THREAD T2)

The `z^k`-coefficient (= top coefficient, since `#S = k+1`) of the Lagrange interpolant of
the data `{(v i, (v i)^b)}_{i ∈ S}` over a `(k+1)`-subset `S` is the **divided difference of
the monomial `x^b`**:

  **`(interpolate S v (·^b)).coeff k = Σ_{i ∈ S} (v i)^b / ∏_{j ∈ S \ {i}} (v i − v j)`.**

This is a *character-sum-free*, *list-decoding-free* identity, derived purely from
`Lagrange.interpolate` and `leadingCoeff_basis`. The right-hand side is the classical
**complete homogeneous symmetric polynomial** `h_{b−k}(v_S)` (for `b ≥ k`), via the Schur /
Jacobi–Trudi divided-difference law `[x_{i_0},…,x_{i_k}] x^b = h_{b−k}(x_{i_0},…,x_{i_k})`.
The anchors proven here pin the first three Schur values:
`h_{<0} = 0` (`dividedDifferencePow_eq_zero_of_lt`), `h_0 = 1` (`dividedDifferencePow_eq_one`),
`h_1 = e_1 = Σ v_i` (`dividedDifferencePow_card_eq_sum`).

So the bad-α criterion of a two-monomial pencil `x^k + α x^b` (the Action–Orbit object) — bad
at agreement `k+1` ⟺ the deg-`<k` agreeing codeword has its `z^k`-coefficient cancelling the
pencil's — becomes the **vanishing of a Schur polynomial** `h_{b−k}(v_S) = 0`, i.e. the
elementary/complete-symmetric vanishing the unified open core `K` counts. This file lands the
exact coefficient identity (the general Schur bridge), generalising the special ladder-stack
identity `residual_ladder_schur` (which is the `b = k+1`/`h_1 = e_1` instance — matched here by
`dividedDifferencePow_card_eq_sum`).
-/

open Finset Polynomial

namespace ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- **Top-coefficient of a Lagrange interpolant = sum of weighted values.**
For an injective node map `v` on `s`, the coefficient of degree `#s − 1` of the interpolant of
`r` is `Σ_{i ∈ s} r i · (∏_{j ∈ s.erase i} (v i − v j))⁻¹`. This is the divided-difference /
top-coefficient identity, the substrate of the Schur bridge. -/
theorem interpolate_coeff_top (hvs : Set.InjOn v s) (r : ι → F) :
    (Lagrange.interpolate s v r).coeff (#s - 1)
      = ∑ i ∈ s, r i * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- the basis polynomial `Lagrange.basis s v i` has natDegree `#s − 1`, so the coeff at `#s − 1`
  -- is its leading coefficient
  rw [coeff_C_mul, ← Lagrange.natDegree_basis hvs hi, ← Polynomial.leadingCoeff,
    Lagrange.leadingCoeff_basis hvs hi]

/-- **The divided difference of `x^b` over the node set `s`** (the `0`-th divided-difference
operator applied to `x ↦ x^b`): `[s] x^b := Σ_{i ∈ s} (v i)^b / ∏_{j ∈ s.erase i} (v i − v j)`.
By `interpolate_coeff_top` (with `r i = (v i)^b`) this equals the top (`#s−1`) coefficient of the
Lagrange interpolant of the monomial data `{(v i, (v i)^b)}_{i ∈ s}`. -/
noncomputable def dividedDifferencePow (s : Finset ι) (v : ι → F) (b : ℕ) : F :=
  ∑ i ∈ s, (v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹

/-- **The Schur/Lagrange bridge.** The `z^{#s−1}`-coefficient of the Lagrange interpolant of the
monomial data `{(v i, (v i)^b)}_{i ∈ s}` is the divided difference of `x^b` over `s`. With
`#s = k+1` this is the `z^k`-coefficient; for `b ≥ k` the divided difference is the complete
homogeneous symmetric polynomial `h_{b−k}(v_s)` (Schur / Jacobi–Trudi). This converts the
two-monomial bad-α criterion into Schur-vanishing — character-sum-free. -/
theorem interpolate_pow_coeff_top (hvs : Set.InjOn v s) (b : ℕ) :
    (Lagrange.interpolate s v (fun i => (v i) ^ b)).coeff (#s - 1)
      = dividedDifferencePow s v b :=
  interpolate_coeff_top hvs _

/-- **Bridge anchor, `b < #s − 1`: the divided difference vanishes** (= `h_{b−k}` with the
"negative degree" reading `b < k`). When `b < #s − 1` the monomial `x^b` already has degree
`< #s − 1`, so it is its own interpolant and its top coefficient is `0`. -/
theorem dividedDifferencePow_eq_zero_of_lt (hvs : Set.InjOn v s) {b : ℕ} (hb : b < #s - 1) :
    dividedDifferencePow s v b = 0 := by
  rw [← interpolate_pow_coeff_top hvs b]
  have hdeg : ((X : F[X]) ^ b).degree < #s := lt_of_le_of_lt (degree_X_pow_le b) (by
    have : (#s - 1 : ℕ) < #s := by omega
    exact_mod_cast lt_of_le_of_lt (by exact_mod_cast hb.le) (by exact_mod_cast this))
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ b) = (X : F[X]) ^ b := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i _ => ?_).symm
    simp
  rw [hinterp, coeff_X_pow]
  exact if_neg (by omega)

/-- **Bridge anchor, `b = #s − 1`: the divided difference is `1`** (= `h_0(v_s) = 1`). The
monomial `x^{#s−1}` is its own interpolant (degree `< #s`) and is monic, so its top coefficient
is `1`. -/
theorem dividedDifferencePow_eq_one (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifferencePow s v (#s - 1) = 1 := by
  rw [← interpolate_pow_coeff_top hvs (#s - 1)]
  have hdeg : ((X : F[X]) ^ (#s - 1)).degree < #s := by
    rw [degree_X_pow]
    have : (#s - 1 : ℕ) < #s := Nat.sub_lt (Finset.card_pos.mpr hs) one_pos
    exact_mod_cast this
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ (#s - 1)) = (X : F[X]) ^ (#s - 1) := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i _ => ?_).symm
    simp
  rw [hinterp, coeff_X_pow, if_pos rfl]

/-- **Bridge anchor, `b = #s`: the divided difference is the point sum `e_1(v_s) = h_1(v_s)`.**
This is the first nontrivial Schur value (`h_1 = e_1`) and the exact match to the in-tree
ladder law `residual_ladder_schur` (`e_t(x^{k+1}) = (Σ points) · e_t(x^k)`, here at the top
column). The divided difference of `x^{#s}` over a `#s`-set is `Σ_{i ∈ s} v i`. -/
theorem dividedDifferencePow_card_eq_sum (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifferencePow s v (#s) = ∑ i ∈ s, v i := by
  rw [← interpolate_pow_coeff_top hvs (#s)]
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPdeg : P.natDegree = #s := by
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  -- `X^{#s} − P` has degree `< #s`: both are monic of degree `#s`, so the top terms cancel.
  set R : F[X] := (X : F[X]) ^ (#s) - P with hR
  have hXdeg : ((X : F[X]) ^ (#s)).degree = (#s : WithBot ℕ) := degree_X_pow _
  have hPdeg' : P.degree = (#s : WithBot ℕ) := by
    rw [degree_eq_natDegree hPmonic.ne_zero, hPdeg]
  have hRdeg : R.degree < #s := by
    rw [hR]
    refine lt_of_lt_of_le (degree_sub_lt ?_ (pow_ne_zero _ X_ne_zero) ?_) (le_of_eq hXdeg)
    · rw [hXdeg, hPdeg']
    · rw [(monic_X_pow (#s)).leadingCoeff, hPmonic.leadingCoeff]
  -- `R` agrees with `x^{#s}` on every node (since `P` vanishes there).
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ (#s)) = R := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hRdeg fun i hi => ?_).symm
    have hPz : P.eval (v i) = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero hi (by simp)
    simp [hR, hPz]
  rw [hinterp, hR, coeff_sub, coeff_X_pow,
    if_neg (by have := Finset.card_pos.mpr hs; omega),
    show P.coeff (#s - 1) = -∑ i ∈ s, v i from by
      have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hs); simpa using h]
  ring

/-- **The general Schur recurrence (the `e ↔ h` / Newton engine of the bridge).**
The divided differences of the monomials `x^b` over a fixed node set `s` (`N := #s`) obey the
linear recurrence whose characteristic polynomial is `P = ∏_{i∈s}(X − v i)`: for every `b ≥ N`,

  `[s] x^b  =  − Σ_{m < N} P.coeff m · [s] x^{b − N + m}`.

Since `P.coeff m = (−1)^{N−m} e_{N−m}(v_s)`, this is exactly the elementary↔complete-homogeneous
relation `Σ_{j=0}^{N} (−1)^j e_j(v_s) · h_{d−j}(v_s) = 0`. Together with the anchors
(`dividedDifferencePow_eq_zero_of_lt` = `h_{<0}=0`, `dividedDifferencePow_eq_one` = `h_0=1`) it
pins **every** Schur value `h_{b−N+1}(v_s)`, character-sum-free — the engine driving the
two-monomial bad-α criterion `h_{b−k}(v_S) = 0`. The proof is purely the root identity
`(v i)^N = −Σ_{m<N} P.coeff m (v i)^m` (from `P(v i) = 0`, `P` monic of degree `N`), summed
against the divided-difference weights. -/
theorem dividedDifferencePow_recurrence (b : ℕ) (hb : #s ≤ b) :
    dividedDifferencePow s v b
      = - ∑ m ∈ range #s, (∏ i ∈ s, (X - C (v i))).coeff m
            * dividedDifferencePow s v (b - #s + m) := by
  classical
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPdeg : P.natDegree = #s := by
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hcoeff_top : P.coeff (#s) = 1 := by rw [← hPdeg]; exact hPmonic.coeff_natDegree
  -- root identity: `(v i)^#s = − Σ_{m<#s} P.coeff m · (v i)^m` for every node.
  have hroot : ∀ i ∈ s, (v i) ^ #s = - ∑ m ∈ range #s, P.coeff m * (v i) ^ m := by
    intro i hi
    have hz : P.eval (v i) = 0 := by
      rw [hP, eval_prod]; exact Finset.prod_eq_zero hi (by simp)
    have hsum : P.eval (v i)
        = (∑ m ∈ range #s, P.coeff m * (v i) ^ m) + (v i) ^ #s := by
      rw [eval_eq_sum_range, hPdeg, Finset.sum_range_succ, hcoeff_top, one_mul]
    rw [hz] at hsum
    exact eq_neg_of_add_eq_zero_right hsum.symm
  -- per-node expansion of `(v i)^b`, then weight by `w i` and sum.
  have lhs_eq : ∀ i ∈ s,
      (v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹
        = - ∑ m ∈ range #s,
            P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
    intro i hi
    have hexp : (v i) ^ b = - ∑ m ∈ range #s, P.coeff m * (v i) ^ (b - #s + m) := by
      have h1 : (v i) ^ b = (v i) ^ (b - #s) * (v i) ^ (#s) := by
        rw [← pow_add, Nat.sub_add_cancel hb]
      rw [h1, hroot i hi, mul_neg, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hexp, neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  calc dividedDifferencePow s v b
      = ∑ i ∈ s, - ∑ m ∈ range #s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [dividedDifferencePow]; exact Finset.sum_congr rfl lhs_eq
    _ = - ∑ i ∈ s, ∑ m ∈ range #s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [Finset.sum_neg_distrib]
    _ = - ∑ m ∈ range #s, ∑ i ∈ s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [Finset.sum_comm]
    _ = - ∑ m ∈ range #s, P.coeff m * dividedDifferencePow s v (b - #s + m) := by
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [dividedDifferencePow, Finset.mul_sum]


/-- **Bridge anchor, `b = #s + 1`: the second Schur value `h_2(v_s) = e_1² − e_2`.** A direct
corollary of `dividedDifferencePow_recurrence` + the three anchors: in the recurrence for
`b = #s+1` only the top two summands survive (`[s]x^{1+m} = 0` for `1+m < #s−1`), leaving
`[s]x^{#s+1} = −(P.coeff (#s−2) · h_0 + P.coeff (#s−1) · h_1)` with `h_0 = 1`, `h_1 = Σ v_i`,
`P.coeff (#s−1) = −Σ v_i`. Here `e_2 = P.coeff (#s−2)` (Vieta). This extends the Schur ledger
to the fourth value `h_2`, character-sum-free. -/
theorem dividedDifferencePow_card_add_one (hvs : Set.InjOn v s) (hs : 2 ≤ #s) :
    dividedDifferencePow s v (#s + 1)
      = (∑ i ∈ s, v i) ^ 2 - (∏ i ∈ s, (X - C (v i))).coeff (#s - 2) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  rw [dividedDifferencePow_recurrence (#s + 1) (by omega)]
  rw [← hP]
  -- the dd-index `(#s+1) - #s + m` is `1 + m`
  have hidx : ∀ m, (#s + 1) - #s + m = 1 + m := fun m => by omega
  simp only [hidx]
  -- peel the top two terms of `range #s = range ((#s-2)+1+1)`
  have hrw : (#s : ℕ) = (#s - 2) + 1 + 1 := by omega
  conv_lhs => rw [hrw]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  -- the low block vanishes: for m < #s-2, `[s]x^{1+m} = 0`
  have hlow : ∀ m ∈ Finset.range (#s - 2),
      P.coeff m * dividedDifferencePow s v (1 + m) = 0 := by
    intro m hm
    have : dividedDifferencePow s v (1 + m) = 0 := by
      apply dividedDifferencePow_eq_zero_of_lt hvs
      have := Finset.mem_range.mp hm; omega
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add]
  -- evaluate the two surviving anchors
  have h1 : (1 : ℕ) + (#s - 2) = #s - 1 := by omega
  have h2 : (1 : ℕ) + (#s - 2 + 1) = #s := by omega
  rw [h1, h2, dividedDifferencePow_eq_one hvs hsne,
      dividedDifferencePow_card_eq_sum hvs hsne, mul_one]
  -- `(#s-2)+1 = #s-1`, and `P.coeff (#s-1) = -Σ v_i`
  have hcard_pred : P.coeff (#s - 1) = - ∑ i ∈ s, v i := by
    have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hsne); simpa using h
  have hcc : (#s - 2 + 1) = #s - 1 := by omega
  rw [hcc, hcard_pred]
  ring


/-- **Bridge anchor, `b = #s + 2`: the third Schur value `h_3 = e_1³ − 2 e_1 e_2 + e_3`.**
The recurrence at `b = #s+2` leaves the top **three** summands (anchors `h_0=1`, `h_1=Σv_i`,
`h_2` = `dividedDifferencePow_card_add_one`); with `e_2 = P.coeff (#s−2)`, `e_3 = −P.coeff (#s−3)`,
`P.coeff (#s−1) = −Σv_i` this collapses to
`[s]x^{#s+2} = (Σv_i)³ − 2·(Σv_i)·P.coeff (#s−2) − P.coeff (#s−3)`.
Extends the character-sum-free Schur ledger to the fifth value `h_3`. -/
theorem dividedDifferencePow_card_add_two (hvs : Set.InjOn v s) (hs : 3 ≤ #s) :
    dividedDifferencePow s v (#s + 2)
      = (∑ i ∈ s, v i) ^ 3
        - 2 * (∑ i ∈ s, v i) * (∏ i ∈ s, (X - C (v i))).coeff (#s - 2)
        - (∏ i ∈ s, (X - C (v i))).coeff (#s - 3) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  rw [dividedDifferencePow_recurrence (#s + 2) (by omega), ← hP]
  have hidx : ∀ m, (#s + 2) - #s + m = 2 + m := fun m => by omega
  simp only [hidx]
  have hrw : (#s : ℕ) = (#s - 3) + 1 + 1 + 1 := by omega
  conv_lhs => rw [hrw]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  -- low block vanishes
  have hlow : ∀ m ∈ Finset.range (#s - 3),
      P.coeff m * dividedDifferencePow s v (2 + m) = 0 := by
    intro m hm
    have : dividedDifferencePow s v (2 + m) = 0 := by
      apply dividedDifferencePow_eq_zero_of_lt hvs
      have := Finset.mem_range.mp hm; omega
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add]
  -- normalise the dd-indices to the anchors
  have ha : (2 : ℕ) + (#s - 3) = #s - 1 := by omega
  have hb : (2 : ℕ) + (#s - 3 + 1) = #s := by omega
  have hc : (2 : ℕ) + (#s - 3 + 1 + 1) = #s + 1 := by omega
  rw [ha, hb, hc, dividedDifferencePow_eq_one hvs hsne,
      dividedDifferencePow_card_eq_sum hvs hsne,
      dividedDifferencePow_card_add_one hvs (by omega), mul_one]
  -- normalise the coeff-indices and use Vieta for P.coeff (#s-1)
  have hcc1 : (#s - 3 + 1) = #s - 2 := by omega
  have hcc2 : (#s - 3 + 1 + 1) = #s - 1 := by omega
  have hcard_pred : P.coeff (#s - 1) = - ∑ i ∈ s, v i := by
    have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hsne); simpa using h
  rw [hcc1, hcc2, hcard_pred]
  ring


/-- **Bridge anchor, `b = #s + 3`: the fourth Schur value
`h_4 = e_1⁴ − 3 e_1² e_2 + e_2² + 2 e_1 e_3 − e_4`.**
The recurrence at `b = #s+3` leaves the top **four** summands (anchors `h_0=1`, `h_1=Σv_i`,
`h_2` = `dividedDifferencePow_card_add_one`, `h_3` = `dividedDifferencePow_card_add_two`); with
`e_2 = P.coeff (#s−2)`, `e_3 = −P.coeff (#s−3)`, `e_4 = P.coeff (#s−4)`,
`P.coeff (#s−1) = −Σv_i` this collapses to
`[s]x^{#s+3} = (Σv_i)⁴ − 3·(Σv_i)²·P.coeff (#s−2) + P.coeff (#s−2)² − 2·(Σv_i)·P.coeff (#s−3) − P.coeff (#s−4)`.
Extends the character-sum-free Schur ledger to the sixth value `h_4`. -/
theorem dividedDifferencePow_card_add_three (hvs : Set.InjOn v s) (hs : 4 ≤ #s) :
    dividedDifferencePow s v (#s + 3)
      = (∑ i ∈ s, v i) ^ 4
        - 3 * (∑ i ∈ s, v i) ^ 2 * (∏ i ∈ s, (X - C (v i))).coeff (#s - 2)
        + (∏ i ∈ s, (X - C (v i))).coeff (#s - 2) ^ 2
        - 2 * (∑ i ∈ s, v i) * (∏ i ∈ s, (X - C (v i))).coeff (#s - 3)
        - (∏ i ∈ s, (X - C (v i))).coeff (#s - 4) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  rw [dividedDifferencePow_recurrence (#s + 3) (by omega), ← hP]
  have hidx : ∀ m, (#s + 3) - #s + m = 3 + m := fun m => by omega
  simp only [hidx]
  have hrw : (#s : ℕ) = (#s - 4) + 1 + 1 + 1 + 1 := by omega
  conv_lhs => rw [hrw]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  -- low block vanishes
  have hlow : ∀ m ∈ Finset.range (#s - 4),
      P.coeff m * dividedDifferencePow s v (3 + m) = 0 := by
    intro m hm
    have : dividedDifferencePow s v (3 + m) = 0 := by
      apply dividedDifferencePow_eq_zero_of_lt hvs
      have := Finset.mem_range.mp hm; omega
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add]
  -- normalise the dd-indices to the anchors
  have ha : (3 : ℕ) + (#s - 4) = #s - 1 := by omega
  have hb : (3 : ℕ) + (#s - 4 + 1) = #s := by omega
  have hc : (3 : ℕ) + (#s - 4 + 1 + 1) = #s + 1 := by omega
  have hd : (3 : ℕ) + (#s - 4 + 1 + 1 + 1) = #s + 2 := by omega
  rw [ha, hb, hc, hd, dividedDifferencePow_eq_one hvs hsne,
      dividedDifferencePow_card_eq_sum hvs hsne,
      dividedDifferencePow_card_add_one hvs (by omega),
      dividedDifferencePow_card_add_two hvs (by omega), mul_one]
  -- normalise the coeff-indices and use Vieta for P.coeff (#s-1)
  have hcc1 : (#s - 4 + 1) = #s - 3 := by omega
  have hcc2 : (#s - 4 + 1 + 1) = #s - 2 := by omega
  have hcc3 : (#s - 4 + 1 + 1 + 1) = #s - 1 := by omega
  have hcard_pred : P.coeff (#s - 1) = - ∑ i ∈ s, v i := by
    have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hsne); simpa using h
  rw [hcc1, hcc2, hcc3, hcard_pred]
  ring


/-- **`dividedDifferencePow` is invariant under relabeling the node set by an equivalence.**
Reindexing the nodes by an `Equiv` `e : ι' ≃ ι` (transporting the value function to `v ∘ e`)
leaves the divided difference of `x^b` unchanged: it is a symmetric function of the node values.
Proof: unfold the sum, push the `Finset.map e.toEmbedding` through the outer `∑` (`Finset.sum_map`),
through each inner `erase` (`Finset.map_erase`, using injectivity of the embedding) and inner `∏`
(`Finset.prod_map`); the integrands match termwise since `(v ∘ e) i = v (e i)`. -/
theorem dividedDifferencePow_reindex {ι' : Type*} [DecidableEq ι'] (e : ι' ≃ ι)
    (s' : Finset ι') (b : ℕ) :
    dividedDifferencePow (s'.map e.toEmbedding) v b = dividedDifferencePow s' (v ∘ e) b := by
  unfold dividedDifferencePow
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
  congr 2
  rw [show (e i) = e.toEmbedding i from rfl, ← Finset.map_erase, Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk]


/-- **Local complete-homogeneous surrogate `schurH`.** Mathlib has no complete-homogeneous
symmetric polynomial, so we define the sequence pinned by the *same* backward recurrence the
divided differences obey: `schurH s v b` is `1` if `b = #s − 1`, `0` if `b < #s − 1`, and for
`b ≥ #s` it is `− Σ_{m<#s} P.coeff m · schurH s v (b − #s + m)` (`P = ∏(X − v i)`). Indexing by
the *raw monomial degree* `b` keeps the recurrence strictly backward (`b − #s + m < b` for
`m < #s`), so this is a well-founded definition; the recursion is taken over `(range #s).attach`
so each summand carries its membership proof `m < #s`, certifying the descent. -/
noncomputable def schurH (s : Finset ι) (v : ι → F) : ℕ → F
  | b =>
    if _hlt : b < #s - 1 then 0
    else if _heq : b = #s - 1 then 1
    else
      - ∑ m ∈ (range #s).attach, (∏ i ∈ s, (X - C (v i))).coeff m.1 *
          schurH s v (b - #s + m.1)
  decreasing_by
    have hm : m.1 < #s := Finset.mem_range.mp m.2
    omega

/-- **The general Schur bridge (`schurH` form).** For every monomial degree `b` and nonempty
node set `s`, the divided difference of `x^b` over `s` equals the local complete-homogeneous
surrogate: `[s] x^b = schurH s v b`. Proved by strong induction on `b`: the three regimes of
`schurH` are discharged by `dividedDifferencePow_eq_zero_of_lt` (`b < #s−1`),
`dividedDifferencePow_eq_one` (`b = #s−1`), and `dividedDifferencePow_recurrence` (`b ≥ #s`,
with the induction hypothesis applied at each strictly-smaller index `b − #s + m`). This is the
full character-sum-free bridge: it turns the two-monomial bad-α criterion into the vanishing of
a Schur value `schurH s v b = h_{b−#s+1}(v_s) = 0`. -/
theorem dividedDifferencePow_eq_schurH (hvs : Set.InjOn v s) (hs : s.Nonempty) (b : ℕ) :
    dividedDifferencePow s v b = schurH s v b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rw [schurH]
    split_ifs with hlt heq
    · exact dividedDifferencePow_eq_zero_of_lt hvs hlt
    · subst heq; exact dividedDifferencePow_eq_one hvs hs
    · have hb : #s ≤ b := by omega
      rw [dividedDifferencePow_recurrence b hb]
      have hattach : (∑ m ∈ (range #s).attach,
            (∏ i ∈ s, (X - C (v i))).coeff m.1 * schurH s v (b - #s + m.1))
          = ∑ m ∈ range #s, (∏ i ∈ s, (X - C (v i))).coeff m * schurH s v (b - #s + m) :=
        Finset.sum_attach (range #s)
          (fun m => (∏ i ∈ s, (X - C (v i))).coeff m * schurH s v (b - #s + m))
      rw [hattach]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun m hm => ?_)
      have hmlt : m < #s := Finset.mem_range.mp hm
      have hlt2 : b - #s + m < b := by omega
      rw [ih (b - #s + m) hlt2]


/-- **`schurH` is invariant under relabeling the node set by an equivalence.**
The complete-homogeneous surrogate `schurH` is a symmetric function of the node values: reindexing
the nodes of `s'` by an `Equiv` `e : ι' ≃ ι` (transporting values to `v ∘ e`) leaves it unchanged.
Proof: chain `dividedDifferencePow_eq_schurH` backward (needs `Set.InjOn v ↑(s'.map e)` and
`(s'.map e).Nonempty`, both derived from the hypotheses on `s'` plus `e.injective`), then
`dividedDifferencePow_reindex` (unconditional), then `dividedDifferencePow_eq_schurH` forward. -/
theorem schurH_reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] (e : ι' ≃ ι)
    (s' : Finset ι') (v : ι → F) (hvs : Set.InjOn (v ∘ e) s') (hs : s'.Nonempty) (b : ℕ) :
    schurH (s'.map e.toEmbedding) v b = schurH s' (v ∘ e) b := by
  -- Nonemptiness of the mapped set.
  have hsmap : (s'.map e.toEmbedding).Nonempty := hs.map
  -- Injectivity of `v` on the image `↑(s'.map e.toEmbedding)`.
  have hvmap : Set.InjOn v ↑(s'.map e.toEmbedding) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Equiv.coe_toEmbedding] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    -- `v (e i) = v (e j)` means `(v ∘ e) i = (v ∘ e) j`, so by `hvs`, `i = j`.
    have : (v ∘ e) i = (v ∘ e) j := hxy
    rw [hvs hi hj this]
  -- Backward bridge on the mapped set.
  rw [← dividedDifferencePow_eq_schurH hvmap hsmap b]
  -- Reindex the divided difference.
  rw [dividedDifferencePow_reindex e s' b]
  -- Forward bridge on `s'` with transported values.
  rw [dividedDifferencePow_eq_schurH hvs hs b]


/-- **`schurH` vanishing anchor, `b < #s − 1`.** The complete-homogeneous surrogate `schurH`
inherits the divided-difference vanishing anchor: for `b < #s − 1` the surrogate is `0`. Proved
by pushing the general bridge `dividedDifferencePow_eq_schurH` backward and applying the proven
dd anchor `dividedDifferencePow_eq_zero_of_lt`. -/
theorem schurH_eq_zero_of_lt (hvs : Set.InjOn v s) (hs : s.Nonempty) {b : ℕ}
    (hb : b < #s - 1) : schurH s v b = 0 := by
  rw [← dividedDifferencePow_eq_schurH hvs hs b]
  exact dividedDifferencePow_eq_zero_of_lt hvs hb

/-- **`schurH` unit anchor, `b = #s − 1` (`h_0 = 1`).** The surrogate at degree `#s − 1` is `1`,
read off the proven dd anchor `dividedDifferencePow_eq_one` through the general bridge. -/
theorem schurH_eq_one (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    schurH s v (#s - 1) = 1 := by
  rw [← dividedDifferencePow_eq_schurH hvs hs (#s - 1)]
  exact dividedDifferencePow_eq_one hvs hs

/-- **`schurH` first Schur value, `b = #s` (`h_1 = e_1 = Σ v_i`).** The surrogate at degree `#s`
is the point sum `Σ_{i ∈ s} v i`, pushed onto `schurH` from the proven dd anchor
`dividedDifferencePow_card_eq_sum` via the general bridge. -/
theorem schurH_card_eq_sum (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    schurH s v (#s) = ∑ i ∈ s, v i := by
  rw [← dividedDifferencePow_eq_schurH hvs hs (#s)]
  exact dividedDifferencePow_card_eq_sum hvs hs


end ProximityGap.SchurLagrange

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SchurLagrange.interpolate_coeff_top
#print axioms ProximityGap.SchurLagrange.interpolate_pow_coeff_top
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_zero_of_lt
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_one
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_eq_sum
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_recurrence
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_add_one
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_add_two
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_add_three
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_reindex
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_schurH
#print axioms ProximityGap.SchurLagrange.schurH_reindex
#print axioms ProximityGap.SchurLagrange.schurH_eq_zero_of_lt
#print axioms ProximityGap.SchurLagrange.schurH_eq_one
#print axioms ProximityGap.SchurLagrange.schurH_card_eq_sum
