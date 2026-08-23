/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# The Hasse `Δ_Y` index-shift degree drop (Johnson E1′, transcription item (a))

DISPROOF_LOG O154 finding 7: the per-term weight bound of the Claim A.2 structured
induction needs, for the `B`-coefficient estimate, the **index-shift** property of the
`Y`-Hasse derivative — the `j`-th coefficient of `Δ_Y^{m} R` is `C(j+m, m) • R.coeff (j+m)`
(Mathlib's `hasseDeriv_coeff`), so its inner degree is bounded by that of the *shifted*
coefficient. In the total-degree shape (`deg coeff_i ≤ D_R − i`) this yields the drop
`deg ((Δ_Y^m R).coeff j) ≤ (D_R − m) − j` — the `−m` that finding 7's arithmetic consumes.

* `hasseDerivY_coeff_cast` — the coefficient identity, specialized to the in-tree `hasseDerivY`;
* `hasseDerivY_coeff_natDegree_le` — the per-coefficient degree bound (shift form);
* `hasseDerivY_coeff_natDegree_le_of_total` — the total-degree-shape drop.

All char-free (the binomial scalar may vanish in positive characteristic; degree bounds
survive since `natDegree (n • p) ≤ natDegree p` unconditionally).
-/

open Polynomial Polynomial.Bivariate

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]

/-- The coefficient identity for the in-tree `Δ_Y`: the `j`-th coefficient of
`Δ_Y^{m} R` is the binomial multiple of the `(j+m)`-th coefficient of `R`. -/
theorem hasseDerivY_coeff_cast (m j : ℕ) (R : F[X][X][Y]) :
    (hasseDerivY m R).coeff j = ((j + m).choose m : F[X][X]) * R.coeff (j + m) := by
  unfold hasseDerivY
  exact Polynomial.hasseDeriv_coeff (k := m) (f := R) j

/-- **The index-shift degree bound:** the `j`-th coefficient of `Δ_Y^{m} R` has inner
degree at most that of `R.coeff (j + m)`. -/
theorem hasseDerivY_coeff_natDegree_le (m j : ℕ) (R : F[X][X][Y]) :
    ((hasseDerivY m R).coeff j).natDegree ≤ (R.coeff (j + m)).natDegree := by
  rw [hasseDerivY_coeff_cast]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp [Polynomial.natDegree_natCast]

/-- **The total-degree-shape drop** (the form finding 7 consumes): if `R`'s coefficients
satisfy the total-degree bound `deg (R.coeff i) ≤ D_R − i`, then the `m`-th `Y`-Hasse
derivative satisfies `deg ((Δ_Y^m R).coeff j) ≤ (D_R − m) − j`: the whole budget drops
by `m`. -/
theorem hasseDerivY_coeff_natDegree_le_of_total {R : F[X][X][Y]} {DR : ℕ}
    (htotal : ∀ i, (R.coeff i).natDegree ≤ DR - i) (m j : ℕ) :
    ((hasseDerivY m R).coeff j).natDegree ≤ (DR - m) - j := by
  calc ((hasseDerivY m R).coeff j).natDegree
      ≤ (R.coeff (j + m)).natDegree := hasseDerivY_coeff_natDegree_le m j R
    _ ≤ DR - (j + m) := htotal (j + m)
    _ = (DR - m) - j := by omega

/-! ## Item (b): the top-coefficient W-divisibility read-off -/


/-- **The top Hasse coefficient is W-divisible** (finding 7's final credit, paper line
3955): under `Hypotheses x₀ R H`, the coefficient at the top index `d − m`
(`d := deg_Y (R(x₀,·,·))`, `m ≤ d`) of the specialized `m`-th `Y`-Hasse derivative is the
binomial multiple of the leading coefficient of `R(x₀,·,·)` — which `W = leadingCoeff H`
divides (the proven `leadingCoeff_dvd_evalX_leadingCoeff`). -/
theorem leadingCoeff_dvd_evalX_hasseDerivY_top {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H) {m : ℕ}
    (hm : m ≤ (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).natDegree) :
    H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀) (hasseDerivY m R)).coeff
        ((Polynomial.Bivariate.evalX (Polynomial.C x₀) R).natDegree - m) := by
  set d : ℕ := (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).natDegree with hd
  -- `evalX` is a coefficient-wise map, so it commutes with the coefficient extraction
  -- and with the `Y`-Hasse derivative's coefficient identity.
  have hcomm : (Polynomial.Bivariate.evalX (Polynomial.C x₀) (hasseDerivY m R)).coeff (d - m)
      = Polynomial.eval (Polynomial.C x₀) ((hasseDerivY m R).coeff (d - m)) := by
    rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rfl
  rw [hcomm, hasseDerivY_coeff_cast]
  have hidx : d - m + m = d := by omega
  rw [hidx]
  -- the evaluated top coefficient is the binomial multiple of the leading coefficient
  have htop : Polynomial.eval (Polynomial.C x₀)
      (((d).choose m : F[X][X]) * R.coeff d)
      = ((d).choose m : F[X]) *
        (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).coeff d := by
    rw [Polynomial.eval_mul, Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
    simp [Polynomial.eval_natCast]
  rw [htop]
  have hlead : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).coeff d
      = (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := rfl
  rw [hlead]
  exact Dvd.dvd.mul_left
    (BCIKS20AppendixA.ClaimA2.leadingCoeff_dvd_evalX_leadingCoeff hHyp) _

/-! ## Item (c): the joint-monomial weight estimate -/

open BCIKS20AppendixA in
/-- **The joint-monomial `Λ` sup-estimate** (finding 7's B-bound shape): a `(T,Z)`-polynomial
whose support is capped at `dT` and whose coefficients carry the total-degree shape
`deg_Z (coeff j) ≤ DQ − j` has weight at most `DQ + dT·(D − d_H)`: per monomial,
`j·(D+1−d_H) + (DQ − j) = DQ + j·(D−d_H)`, maximized at `j = dT`. -/
theorem weight_Λ_le_of_shape {H : F[X][Y]} {f : F[X][Y]} {dT DQ D : ℕ}
    (hD : Polynomial.Bivariate.natDegreeY H ≤ D)
    (hsupp : ∀ j ∈ f.support, j ≤ dT)
    (hshape : ∀ j ∈ f.support, (f.coeff j).natDegree ≤ DQ - j)
    (hDQ : ∀ j ∈ f.support, j ≤ DQ) :
    weight_Λ f H D
      ≤ WithBot.some (DQ + dT * (D - Polynomial.Bivariate.natDegreeY H)) := by
  unfold weight_Λ
  refine Finset.sup_le ?_
  intro j hj
  have h1 := hsupp j hj
  have h2 := hshape j hj
  have h3 := hDQ j hj
  refine WithBot.coe_le_coe.mpr ?_
  set w : ℕ := D - Polynomial.Bivariate.natDegreeY H with hw
  have hexp : D + 1 - Polynomial.Bivariate.natDegreeY H = w + 1 := by omega
  rw [hexp]
  calc j * (w + 1) + (f.coeff j).natDegree
      ≤ j * (w + 1) + (DQ - j) := by omega
    _ = j * w + j + (DQ - j) := by ring_nf
    _ = DQ + j * w := by omega
    _ ≤ DQ + dT * w := by
        have := Nat.mul_le_mul_right w h1
        omega

/-! ## Item (d): the assembled Hasse-coefficient weight bound -/

open BCIKS20AppendixA

/-- **The assembled `𝒪`-weight bound for the iterated Hasse coefficient** (E1′'s B-bound,
composing the proven `weight_Λ_over_𝒪_le_of_mk_eq` reduction-monotonicity with the
joint-monomial estimate): under the support cap and total-degree shape of the specialized
Hasse polynomial, `Λ_𝒪(hasseCoeffRepr𝒪 x₀ R i1 m) ≤ DQ + dT·(D − d_H)`. With the proven
`Y`-drop (`hasseCoeffRepr𝒪_natDegreeY_le`) supplying `dT = d_R − m` and the index-shift
drop (`hasseDerivY_coeff_natDegree_le_of_total`) supplying the shape, this is finding 7's
`Λ(B) ≤ (D_R − m) + (d_R − m)·Λ_W` instance. -/
theorem hasseCoeffRepr𝒪_weight_le_of_shape
    {H : F[X][Y]} (hH : 0 < H.natDegree) {D : ℕ}
    (hD : Polynomial.Bivariate.totalDegree H ≤ D)
    (hDY : Polynomial.Bivariate.natDegreeY H ≤ D)
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) {dT DQ : ℕ}
    (hsupp : ∀ j ∈ (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).support, j ≤ dT)
    (hshape : ∀ j ∈ (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).support,
      ((Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).coeff j).natDegree ≤ DQ - j)
    (hDQ : ∀ j ∈ (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).support, j ≤ DQ) :
    weight_Λ_over_𝒪 hH (hasseCoeffRepr𝒪 H x₀ R i1 m) D
      ≤ WithBot.some (DQ + dT * (D - Polynomial.Bivariate.natDegreeY H)) := by
  refine le_trans
    (weight_Λ_over_𝒪_le_of_mk_eq hD hH (rfl :
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX i1 (hasseDerivY m R))) : 𝒪 H)
        = hasseCoeffRepr𝒪 H x₀ R i1 m)) ?_
  exact weight_Λ_le_of_shape hDY hsupp hshape hDQ

/-! ## The three-layer shape supplier (finding 9): the per-cell B-budget value -/

/-- **Constant-evaluation degree bound:** evaluating the middle `X`-layer at the constant
`C x₀` keeps the inner degree within the shape budget: if `deg (q.coeff i) ≤ B − i` for
all `i`, then `deg (q.eval (C x₀)) ≤ B`. -/
theorem eval_constX_natDegree_le_of_shape {x₀ : F} {q : Polynomial (Polynomial F)} {B : ℕ}
    (hshape : ∀ i, (q.coeff i).natDegree ≤ B - i) :
    (q.eval (Polynomial.C x₀)).natDegree ≤ B := by
  rw [Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i _
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : ((Polynomial.C x₀ : Polynomial F) ^ i).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C]
    ring
  rw [h1]
  have h2 := hshape i
  omega

/-- **The composed three-layer shape drop** (finding 9): if `R`'s trivariate coefficients
satisfy the total-degree shape `deg_Z ((R.coeff n).coeff i) ≤ D_R − n − i`, then the
specialized iterated Hasse polynomial — exactly the `hasseCoeffRepr` payload of the
`(i1, λ)` cell with `m = σ(λ)` — satisfies
`deg_Z ((evalX (C x₀) (Δ_X^{i1} Δ_Y^{m} R)).coeff n) ≤ (D_R − m − i1) − n`: the budget
drops by `m + i1` through the two Hasse shifts, and the constant evaluation collapses the
`X`-layer within budget. -/
theorem specializedHasse_coeff_natDegree_le_of_total {x₀ : F} {R : F[X][X][Y]} {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (i1 m n : ℕ) :
    ((Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).coeff n).natDegree
      ≤ (DR - m - i1) - n := by
  have hcomm : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX i1 (hasseDerivY m R))).coeff n
      = Polynomial.eval (Polynomial.C x₀) ((hasseDerivX i1 (hasseDerivY m R)).coeff n) := by
    rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rfl
  rw [hcomm, hasseDerivX_coeff]
  refine eval_constX_natDegree_le_of_shape ?_
  intro i
  -- the `X`-layer Hasse shift drops the budget by `i1`
  rw [Polynomial.hasseDeriv_coeff]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have hc1 : ((((i + i1).choose i1 : ℕ) : Polynomial F)).natDegree = 0 :=
    Polynomial.natDegree_natCast _
  -- the `Y`-layer Hasse shift drops the budget by `m` (binomial scalar is degree-free)
  have hc2 : (((hasseDerivY m R).coeff n).coeff (i + i1)).natDegree
      ≤ ((R.coeff (n + m)).coeff (i + i1)).natDegree := by
    rw [hasseDerivY_coeff_cast, ← nsmul_eq_mul, Polynomial.coeff_smul]
    exact Polynomial.natDegree_smul_le _ _
  have hc3 := htotal (n + m) (i + i1)
  omega

/-- **The vanishing tail of the specialized Hasse polynomial:** if `R`'s trivariate
monomials vanish beyond total budget `D_R`, every `Y`-coefficient of
`evalX (C x₀) (Δ_X^{i1} Δ_Y^{m} R)` beyond index `D_R − m − i1` is zero — the support
genuinely lives inside the dropped budget (the `hDQ` input of item (d)). -/
theorem specializedHasse_coeff_eq_zero_of_vanish {x₀ : F} {R : F[X][X][Y]} {DR : ℕ}
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (i1 m : ℕ) {n : ℕ} (hn : DR - m - i1 < n) :
    (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).coeff n = 0 := by
  have hcomm : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX i1 (hasseDerivY m R))).coeff n
      = Polynomial.eval (Polynomial.C x₀) ((hasseDerivX i1 (hasseDerivY m R)).coeff n) := by
    rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rfl
  rw [hcomm, hasseDerivX_coeff]
  have hz : Polynomial.hasseDeriv i1 ((hasseDerivY m R).coeff n) = 0 := by
    refine Polynomial.ext fun i => ?_
    have hinner : ((hasseDerivY m R).coeff n).coeff (i + i1) = 0 := by
      rw [hasseDerivY_coeff_cast, ← nsmul_eq_mul, Polynomial.coeff_smul,
        hvanish (n + m) (i + i1) (by omega), smul_zero]
    rw [Polynomial.hasseDeriv_coeff, hinner, mul_zero, Polynomial.coeff_zero]
  rw [hz, Polynomial.eval_zero]

/-- **The per-cell B-budget VALUE** (finding 9's `nB`, fully composed): under the
total-degree shape and vanishing of `R` at budget `D_R`, the iterated Hasse coefficient
representative of the `(i1, λ)` cell (with `m = σ(λ)`) satisfies

`Λ_𝒪(hasseCoeffRepr𝒪 x₀ R i1 m) ≤ (D_R − m − i1) + (d_{R,Y} − m) · (D − d_H)`,

composing the proven item (d) with the three-layer shape drop, the vanishing tail, and
the in-tree `Y`-cap. This is the concrete `nB` the capstone's `hbudget` hypothesis
consumes for every cell. -/
theorem hasseCoeffRepr𝒪_weight_le_of_total
    {H : F[X][Y]} (hH : 0 < H.natDegree) {D : ℕ}
    (hD : Polynomial.Bivariate.totalDegree H ≤ D)
    (hDY : Polynomial.Bivariate.natDegreeY H ≤ D)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (i1 m : ℕ) :
    weight_Λ_over_𝒪 hH (hasseCoeffRepr𝒪 H x₀ R i1 m) D
      ≤ WithBot.some ((DR - m - i1)
          + (Polynomial.Bivariate.natDegreeY R - m)
            * (D - Polynomial.Bivariate.natDegreeY H)) := by
  refine hasseCoeffRepr𝒪_weight_le_of_shape hH hD hDY x₀ R i1 m ?_ ?_ ?_
  · -- the support cap `dT = d_{R,Y} − m` via the in-tree `Y`-cap
    intro j hj
    have h1 : j ≤ (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX i1 (hasseDerivY m R))).natDegree :=
      Polynomial.le_natDegree_of_mem_supp j hj
    have h2 := hasseCoeffRepr𝒪_natDegreeY_le x₀ R i1 m
    exact le_trans h1 h2
  · -- the three-layer shape drop supplies `DQ = D_R − m − i1`
    intro j _
    exact specializedHasse_coeff_natDegree_le_of_total htotal i1 m j
  · -- the vanishing tail supplies the support-within-budget cap
    intro j hj
    by_contra hcon
    push_neg at hcon
    exact (Polynomial.mem_support_iff.mp hj)
      (specializedHasse_coeff_eq_zero_of_vanish hvanish i1 m (by omega))

/-- Coefficient extraction for the cleared representative: the `b`-th coefficient of
`hasseCoeffRepr𝒪_cleared H x₀ R i1 m k` is `p.coeff b · W^{k−b}` for `b ≤ k` and `0`
beyond the clearing degree. -/
theorem hasseCoeffRepr𝒪_cleared_coeff (H : F[X][Y]) (x₀ : F) (R : F[X][X][Y])
    (i1 m k b : ℕ) :
    (hasseCoeffRepr𝒪_cleared H x₀ R i1 m k).coeff b
      = if b ≤ k then
          ((Polynomial.Bivariate.evalX (Polynomial.C x₀)
            (hasseDerivX i1 (hasseDerivY m R))).coeff b) * H.leadingCoeff ^ (k - b)
        else 0 := by
  classical
  rw [hasseCoeffRepr𝒪_cleared, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (k + 1))]
  simp [Finset.mem_range, Nat.lt_succ_iff]

/-- **The ANCHORED cleared-form budget** (finding 14's repair supplier): at the anchor
`D ≤ d_H + degW`, the cleared representative at clearing power `k` has weight at most
`(D_R − m − i1) + k·degW` — every `T`-power's cost is fully absorbed by its cleared
`W`-deficit, so the budget is uniform across monomials. At `k = d_R − 1 − m` (the δ-saved
clearing) this is exactly the paper's `i1 = 0` saved budget. -/
theorem hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored
    {H : F[X][Y]} (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Polynomial.Bivariate.totalDegree H ≤ D)
    (htight : D ≤ Polynomial.Bivariate.natDegreeY H + (H.leadingCoeff).natDegree)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (i1 m k : ℕ) :
    weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m k) : 𝒪 H) D
      ≤ WithBot.some ((DR - m - i1) + k * (H.leadingCoeff).natDegree) := by
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
  rw [weight_Λ]
  refine Finset.sup_le fun b hb => ?_
  refine WithBot.coe_le_coe.mpr ?_
  -- the coefficient at `b`: zero beyond `k`, the cleared product within
  have hcoef := hasseCoeffRepr𝒪_cleared_coeff H x₀ R i1 m k b
  by_cases hbk : b ≤ k
  · -- within the clearing degree: the support lives inside the shape budget
    have hbDQ : b ≤ DR - m - i1 := by
      by_contra hcon
      push_neg at hcon
      have hz : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX i1 (hasseDerivY m R))).coeff b = 0 :=
        specializedHasse_coeff_eq_zero_of_vanish hvanish i1 m hcon
      have : (hasseCoeffRepr𝒪_cleared H x₀ R i1 m k).coeff b = 0 := by
        rw [hcoef, if_pos hbk, hz, zero_mul]
      exact (Polynomial.mem_support_iff.mp hb) this
    rw [hcoef, if_pos hbk]
    -- inner degree: shape + clearing power
    have hshape := specializedHasse_coeff_natDegree_le_of_total (x₀ := x₀) htotal i1 m b
    have hdeg : (((Polynomial.Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX i1 (hasseDerivY m R))).coeff b)
            * H.leadingCoeff ^ (k - b)).natDegree
        ≤ ((DR - m - i1) - b) + (k - b) * (H.leadingCoeff).natDegree := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have hpow : (H.leadingCoeff ^ (k - b)).natDegree
          ≤ (k - b) * (H.leadingCoeff).natDegree :=
        Polynomial.natDegree_pow_le
      omega
    -- the anchor absorbs the T-cost: b·(D+1−d_H) ≤ b·(degW+1)
    have hanchor : b * (D + 1 - Polynomial.Bivariate.natDegreeY H)
        ≤ b * ((H.leadingCoeff).natDegree + 1) :=
      Nat.mul_le_mul_left b (by omega)
    have hb1 : b * ((H.leadingCoeff).natDegree + 1)
        = b * (H.leadingCoeff).natDegree + b := by
      rw [Nat.mul_add, Nat.mul_one]
    have hsplit : (k - b) * (H.leadingCoeff).natDegree
        + b * (H.leadingCoeff).natDegree ≤ k * (H.leadingCoeff).natDegree := by
      have : (k - b) + b ≤ k := by omega
      calc (k - b) * (H.leadingCoeff).natDegree + b * (H.leadingCoeff).natDegree
          = ((k - b) + b) * (H.leadingCoeff).natDegree := (Nat.add_mul _ _ _).symm
        _ ≤ k * (H.leadingCoeff).natDegree :=
            Nat.mul_le_mul_right _ this
    omega
  · -- beyond the clearing degree the coefficient is zero, contradicting support
    exfalso
    have : (hasseCoeffRepr𝒪_cleared H x₀ R i1 m k).coeff b = 0 := by
      rw [hcoef, if_neg hbk]
    exact (Polynomial.mem_support_iff.mp hb) this

/-! ## Source audit -/

#print axioms hasseDerivY_coeff_cast
#print axioms hasseDerivY_coeff_natDegree_le
#print axioms hasseDerivY_coeff_natDegree_le_of_total
#print axioms leadingCoeff_dvd_evalX_hasseDerivY_top
#print axioms weight_Λ_le_of_shape
#print axioms hasseCoeffRepr𝒪_weight_le_of_shape
#print axioms eval_constX_natDegree_le_of_shape
#print axioms specializedHasse_coeff_natDegree_le_of_total
#print axioms specializedHasse_coeff_eq_zero_of_vanish
#print axioms hasseCoeffRepr𝒪_weight_le_of_total
#print axioms hasseCoeffRepr𝒪_cleared_coeff
#print axioms hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored

end BCIKS20.HenselNumerator
