/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovS2
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22SuperellipticIndependence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20StepanovScaffold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24DBlockIndependence

/-!
# LANE SUPERS2 (#466 round 24): d-block Stepanov S2 for the superelliptic faces

Transfer of the round-22 rank–nullity / Hasse-derivative auxiliary-polynomial machinery
(`_R22StepanovS2.lean`) from the quadratic case (`d = 2`, `e = (q−1)/2`, cubic `f`) to the
GENERAL `d`-block superelliptic case: order-`d` multiplicative characters of `f = g`
(any monic `g`, in the application `g = L₁L₂L₃^{d−1}`), exponent step `e_d = (q−1)/d`,
`d` coefficient blocks
`P = ∑_{j<J} (∑_{t<d} g^{m+t·e}·a_{tj}) · X^{qj}`.

## The d-independence audit of `_R22StepanovS2` (verified by reading every proof)

Lemmas that NEVER use `e = (q−1)/2` or the block count 2 in their mathematical content:
`cast_choose_prime_pow_mul_eq_zero`, `hasseDeriv_X_card_mul_eq_zero`,
`hasseDeriv_mul_X_card_pow`, `pow_sub_dvd_hasseDeriv_pow(_mul)`, `divByMonic_exact`,
`add_divByMonic`, `smul_divByMonic`, `polyOf_*`, `liftY_*`, `subq_liftY`, and the round-20
engine `hasseDeriv_stepanov_degree_count`.  They are consumed here VERBATIM (imported).

The only `d = 2`-specific ingredients of round 22 were:
1. the hard-coded TWO blocks in `Unknowns`/`redWitness`/`auxP` — generalized here to `d`;
2. the cubic degree 3 in the budgets — generalized to `g.natDegree` (quotient degree bound
   `D + (deg g − 1)·k` replaces `D + 2k`);
3. `auxP_ne_zero` via the S1 quadratic independence — replaced by the NAMED round-22 Prop
   `DBlockIndependence F d q D g` (proven for `d = 2`; `d ≥ 4` = the NORMFOLD lane).

## New here (all proven, no sorry)

* the general-fiber factorization: at any `s` with `g(s)^e = ζ` (ζ an arbitrary target
  value, not just 1!), `(D^{(k)}P)(s) = g(s)^{m−k} · W_k^ζ(s)` where the reduced witness
  `W_k^ζ` carries `ζ^t` block weights — the same ONE auxiliary polynomial serves every
  fiber class of the order-`d` power map, only the linear condition system rotates by ζ;
* d-block rank–nullity: nonzero kernel when `m(D + (deg g − 1)m + J) < d·J·(D+1)`;
* nonzeroness from `DBlockIndependence` (the norm-fold Prop) at `e = (q−1)/d`;
* the capstone per-fiber count: for EVERY ζ,
  `m · #{s : g(s)^e = ζ} ≤ deg g·(m + (d−1)e) + D + q(J−1)`,
  conditional ONLY on `DBlockIndependence F d q D g`.

## The character-sum assembly (arithmetic, recorded for the parameter lane)

With `N_ζ = #{s : g(s)^{e_d} = ζ}` (ζ ∈ μ_d), `Z = #{g = 0}`: `∑_ζ N_ζ = q − Z`; Stepanov
gives `N_ζ ≤ q/d + C√q` each, hence `N_ζ ≥ q/d − Z − (d−1)C√q`; for χ of exact order d,
`∑_{g(s)≠0} χ(g(s)) = ∑_ζ χ̂(ζ)·N_ζ = ∑_ζ χ̂(ζ)(N_ζ − q/d)` (since `∑_ζ χ̂(ζ) = 0`), so
`|∑ χ(g(s))| ≤ ∑_ζ |N_ζ − q/d| ≤ d·(C√q + Z)`.  That step is bookkeeping over ℤ; it is the
round-24 analogue of `cubic_charSum_eq_two_pos_add_three_sub_card` and belongs to the
parameter-choice lane (mimic `_R23ParameterChoice`).

## What stalls (honest scope)

EXACTLY ONE input: `DBlockIndependence F d (card F) D g` for the desired 2-power order.
It is proven below for `d = 4`; the `d = 8` norm-fold endpoint is proven in
`_R25OcticNormFold` and exposed to this S2 API by `_R147OcticSuperellipticS2Consumer`.
Higher doublings (`d = 16, 32, ...`) remain the norm-fold construction.  Everything else in
the order-`d` Stepanov chain through the per-fiber count is machine-checked below.  No prize
closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R24SuperellipticS2

open Polynomial Finset
open ArkLib.ProximityGap.Frontier.R22StepanovS2
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The d-block unknowns, ζ-weighted reduced witnesses, and the auxiliary `P` -/

/-- The unknown vector: `d` blocks of `J × (D+1)` field elements (flat function type,
so rank–nullity is a single `finrank` computation). -/
@[reducible] def UnknownsD (F : Type*) (d J D : ℕ) : Type _ :=
  (Fin d × Fin J × Fin (D + 1)) → F

/-- The `k`-th ζ-weighted reduced witness
`W_k^ζ = ∑_j (∑_t ζ^t · D^{(k)}(g^{m+te}·a_{tj})/g^{m+te−k}) · X^j`.
On the fiber `{g^e = ζ}` the evaluated Hasse derivative of `P` factors through it. -/
noncomputable def redWitnessD (g : F[X]) (ζ : F) (d m e J D k : ℕ)
    (x : UnknownsD F d J D) : F[X] :=
  ∑ j : Fin J,
    (∑ t : Fin d, ζ ^ (t : ℕ) •
      (hasseDeriv k (g ^ (m + (t : ℕ) * e) * polyOf D (fun i => x (t, j, i)))
        /ₘ g ^ (m + (t : ℕ) * e - k))) * X ^ (j : ℕ)

/-- The `d`-block auxiliary polynomial `P = ∑_j (∑_t g^{m+te}·a_{tj})·X^{qj}`.
NOTE: `P` does not depend on ζ — one polynomial serves all `d` fiber classes. -/
noncomputable def auxPD (g : F[X]) (q d m e J D : ℕ) (x : UnknownsD F d J D) : F[X] :=
  ∑ j : Fin J,
    (∑ t : Fin d, g ^ (m + (t : ℕ) * e) * polyOf D (fun i => x (t, j, i))) * X ^ (q * (j : ℕ))

/-! ## 2. Linearity of the witnesses -/

theorem redWitnessD_add (g : F[X]) (hg : g.Monic) (ζ : F) (d m e J D k : ℕ)
    (x y : UnknownsD F d J D) :
    redWitnessD g ζ d m e J D k (x + y)
      = redWitnessD g ζ d m e J D k x + redWitnessD g ζ d m e J D k y := by
  rw [redWitnessD, redWitnessD, redWitnessD, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_mul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hP : polyOf D (fun i => (x + y) (t, j, i))
      = polyOf D (fun i => x (t, j, i)) + polyOf D (fun i => y (t, j, i)) := by
    rw [← polyOf_add]; rfl
  rw [hP, mul_add, map_add, add_divByMonic (hg.pow _), smul_add]

theorem redWitnessD_smul (g : F[X]) (hg : g.Monic) (ζ : F) (d m e J D k : ℕ) (r : F)
    (x : UnknownsD F d J D) :
    redWitnessD g ζ d m e J D k (r • x) = r • redWitnessD g ζ d m e J D k x := by
  rw [redWitnessD, redWitnessD, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_mul_assoc]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hP : polyOf D (fun i => (r • x) (t, j, i)) = r • polyOf D (fun i => x (t, j, i)) := by
    rw [← polyOf_smul]; rfl
  rw [hP, mul_smul_comm, map_smul, smul_divByMonic (hg.pow _), smul_comm]

/-- The ζ-rotated condition system as a linear map: unknowns ↦ the first `B` coefficients
of each `W_k^ζ`, `k < m` (in use `B = D + (deg g − 1)·m + J`, kept symbolic so the map's
type does not mention `g`). -/
noncomputable def condMapD (g : F[X]) (hg : g.Monic) (ζ : F) (d m e J D B : ℕ) :
    UnknownsD F d J D →ₗ[F] ((Fin m × Fin B) → F) where
  toFun x := fun ki => (redWitnessD g ζ d m e J D (ki.1 : ℕ) x).coeff (ki.2 : ℕ)
  map_add' x y := by
    funext ki
    rw [redWitnessD_add g hg]
    simp [coeff_add]
  map_smul' r x := by
    funext ki
    rw [redWitnessD_smul g hg]
    simp

/-! ## 3. Rank–nullity: nonzero kernel under the d-block count -/

theorem exists_kernel_vector_D (g : F[X]) (hg : g.Monic) (ζ : F) (d m e J D B : ℕ)
    (hcount : m * B < d * (J * (D + 1))) :
    ∃ x : UnknownsD F d J D, x ≠ 0 ∧ condMapD g hg ζ d m e J D B x = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (condMapD g hg ζ d m e J D B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    exact hcon x hne hx
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hle
  omega

/-! ## 4. Degree control -/

theorem natDegree_monic_pow (g : F[X]) (hg : g.Monic) (n : ℕ) :
    (g ^ n).natDegree = n * g.natDegree := by
  rw [hg.natDegree_pow]

/-- Generic quotient degree bound: `deg(D^{(k)}(g^N·a)/g^{N−k}) ≤ Da + (deg g − 1)·k`
(the `d`-generic replacement of the round-22 cubic `Da + 2k`). -/
theorem quotient_natDegree_le_D (g : F[X]) (hg : g.Monic) (hdg : 0 < g.natDegree)
    (a : F[X]) {Da : ℕ} (ha : a.natDegree ≤ Da) (N k : ℕ) (hk : k ≤ N) :
    (hasseDeriv k (g ^ N * a) /ₘ g ^ (N - k)).natDegree
      ≤ Da + (g.natDegree - 1) * k := by
  rw [natDegree_divByMonic _ (hg.pow _)]
  have h1 : (hasseDeriv k (g ^ N * a)).natDegree ≤ (g ^ N * a).natDegree - k :=
    natDegree_hasseDeriv_le _ _
  have h2 : (g ^ N * a).natDegree ≤ N * g.natDegree + Da := by
    refine natDegree_mul_le.trans ?_
    rw [natDegree_monic_pow g hg]
    omega
  have h3 : ((g ^ (N - k)).natDegree) = (N - k) * g.natDegree := natDegree_monic_pow g hg _
  have h4 : N * g.natDegree = (N - k) * g.natDegree + k * g.natDegree := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hk]
  have h5 : k * g.natDegree = k * (g.natDegree - 1) + k := by
    have hsplit : (g.natDegree - 1) + 1 = g.natDegree := Nat.sub_add_cancel hdg
    calc k * g.natDegree = k * ((g.natDegree - 1) + 1) := by rw [hsplit]
    _ = k * (g.natDegree - 1) + k := by rw [Nat.mul_add, Nat.mul_one]
  have h6 : k * (g.natDegree - 1) = (g.natDegree - 1) * k := Nat.mul_comm _ _
  omega

theorem redWitnessD_natDegree_le (g : F[X]) (hg : g.Monic) (hdg : 0 < g.natDegree)
    (ζ : F) (d m e J D k : ℕ) (x : UnknownsD F d J D) (hk : k ≤ m) (hJ : 0 < J) :
    (redWitnessD g ζ d m e J D k x).natDegree
      ≤ D + (g.natDegree - 1) * k + (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have hsum : ((∑ t : Fin d, ζ ^ (t : ℕ) •
      (hasseDeriv k (g ^ (m + (t : ℕ) * e) * polyOf D (fun i => x (t, j, i)))
        /ₘ g ^ (m + (t : ℕ) * e - k)))).natDegree ≤ D + (g.natDegree - 1) * k := by
    refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    refine (natDegree_smul_le _ _).trans ?_
    exact quotient_natDegree_le_D g hg hdg _ (polyOf_natDegree_le _ _) _ k (by omega)
  have hjlt : (j : ℕ) ≤ J - 1 := by omega
  omega

theorem redWitnessD_eq_zero_of_kernel (g : F[X]) (hg : g.Monic) (hdg : 0 < g.natDegree)
    (ζ : F) (d m e J D k : ℕ) (x : UnknownsD F d J D)
    (hk : k < m) (hJ : 0 < J)
    (hx : condMapD g hg ζ d m e J D (D + (g.natDegree - 1) * m + J) x = 0) :
    redWitnessD g ζ d m e J D k x = 0 := by
  ext n
  rw [coeff_zero]
  rcases Nat.lt_or_ge n (D + (g.natDegree - 1) * m + J) with hn | hn
  · exact congrFun hx (⟨k, hk⟩, ⟨n, hn⟩)
  · refine coeff_eq_zero_of_natDegree_lt ?_
    have hle := redWitnessD_natDegree_le g hg hdg ζ d m e J D k x (by omega) hJ
    have hmono : (g.natDegree - 1) * k ≤ (g.natDegree - 1) * m :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## 5. The pointwise factorization on an ARBITRARY fiber `{g^e = ζ}` -/

/-- **The d-block S2 vanishing identity, general fiber value.** For `k ≤ m`,
`k < q = |F|`, at any `s` with `g(s)^e = ζ`:
`(D^{(k)}P)(s) = g(s)^{m−k} · W_k^ζ(s)`.  (For `d = 2`, `ζ = 1` this is verbatim
round 22 `eval_hasseDeriv_auxP`; the ζ-weights are the ONLY new content.) -/
theorem eval_hasseDeriv_auxPD (g : F[X]) (hg : g.Monic) (ζ : F)
    (d m e J D k : ℕ) (x : UnknownsD F d J D) (hkm : k ≤ m) (hkq : k < Fintype.card F)
    (s : F) (hse : (g.eval s) ^ e = ζ) :
    (hasseDeriv k (auxPD g (Fintype.card F) d m e J D x)).eval s
      = (g.eval s) ^ (m - k) * (redWitnessD g ζ d m e J D k x).eval s := by
  rw [auxPD, map_sum, eval_finset_sum, redWitnessD, eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_mul_X_card_pow _ (j : ℕ) k hkq, map_sum]
  have hsq : s ^ (Fintype.card F * (j : ℕ)) = s ^ (j : ℕ) := by
    rw [mul_comm, pow_mul, FiniteField.pow_card]
  simp only [eval_mul, eval_pow, eval_X, eval_finset_sum, eval_smul, smul_eq_mul]
  rw [hsq, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  set Pa := polyOf D (fun i => x (t, j, i)) with hPa
  have hd1 : g ^ (m + (t : ℕ) * e - k)
        * (hasseDeriv k (g ^ (m + (t : ℕ) * e) * Pa) /ₘ g ^ (m + (t : ℕ) * e - k))
      = hasseDeriv k (g ^ (m + (t : ℕ) * e) * Pa) :=
    divByMonic_exact (hg.pow _)
      (pow_sub_dvd_hasseDeriv_pow_mul g Pa (m + (t : ℕ) * e) k (by omega))
  have heval : (hasseDeriv k (g ^ (m + (t : ℕ) * e) * Pa)).eval s
      = (g.eval s) ^ (m + (t : ℕ) * e - k)
        * (hasseDeriv k (g ^ (m + (t : ℕ) * e) * Pa) /ₘ g ^ (m + (t : ℕ) * e - k)).eval s := by
    conv_lhs => rw [← hd1]
    rw [eval_mul, eval_pow]
  have hpow : (g.eval s) ^ (m + (t : ℕ) * e - k)
      = (g.eval s) ^ (m - k) * ζ ^ (t : ℕ) := by
    have hexp : m + (t : ℕ) * e - k = (m - k) + (t : ℕ) * e := by omega
    rw [hexp, pow_add, mul_comm ((t : ℕ)) e, pow_mul, hse]
  rw [heval, hpow]
  ring

/-! ## 6. Nonzeroness from the d-block independence Prop, and the degree budget -/

/-- `P = g^m · ∑_t g^{te}·A_t(X, X^q)` — the bridge to `DBlockIndependence`. -/
theorem auxPD_eq_mul (g : F[X]) (q d m e J D : ℕ) (x : UnknownsD F d J D) :
    auxPD g q d m e J D x
      = g ^ m * ∑ t : Fin d, g ^ ((t : ℕ) * e)
          * ArkLib.ProximityGap.StepanovNonVanishing.subq q
              (liftY (fun j => polyOf D (fun i => x (t, j, i)))) := by
  rw [auxPD]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [subq_liftY, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

/-- **Nonzeroness from the norm-fold Prop.**  If `DBlockIndependence F d q D g` holds and
`e = (q−1)/d`, then a nonzero unknown vector yields a nonzero auxiliary polynomial.
For `d = 2` this is discharged by `dBlockIndependence_two`; `d ≥ 4` is the NORMFOLD lane. -/
theorem auxPD_ne_zero (g : F[X]) (hg0 : g ≠ 0) {q d m e J D : ℕ}
    (hind : DBlockIndependence F d q D g) (he : e = (q - 1) / d)
    (x : UnknownsD F d J D) (hx : x ≠ 0) :
    auxPD g q d m e J D x ≠ 0 := by
  intro hzero
  apply hx
  rw [auxPD_eq_mul, he] at hzero
  rcases mul_eq_zero.mp hzero with hgm | hsum
  · exact absurd hgm (pow_ne_zero _ hg0)
  · have hAzero : ∀ t : Fin d, liftY (fun j => polyOf D (fun i => x (t, j, i))) = 0 := by
      refine hind (fun t => liftY (fun j => polyOf D (fun i => x (t, j, i)))) ?_ hsum
      intro t jn
      rw [liftY_coeff]
      split_ifs
      · exact polyOf_natDegree_le _ _
      · simp
    funext tji
    obtain ⟨t, j, i⟩ := tji
    have hc := congrArg (fun p => (p.coeff (j : ℕ)).coeff (i : ℕ)) (hAzero t)
    simp only [liftY_coeff, Polynomial.coeff_zero] at hc
    rw [dif_pos j.isLt] at hc
    rw [Fin.eta] at hc
    rw [polyOf_coeff] at hc
    exact hc

theorem auxPD_natDegree_le (g : F[X]) (hg : g.Monic) (q d m e J D : ℕ)
    (x : UnknownsD F d J D) (hJ : 0 < J) :
    (auxPD g q d m e J D x).natDegree
      ≤ g.natDegree * (m + (d - 1) * e) + D + q * (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have hsum : ((∑ t : Fin d, g ^ (m + (t : ℕ) * e)
      * polyOf D (fun i => x (t, j, i)))).natDegree
        ≤ g.natDegree * (m + (d - 1) * e) + D := by
    refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    refine natDegree_mul_le.trans ?_
    have h1 := polyOf_natDegree_le D (fun i => x (t, j, i))
    rw [natDegree_monic_pow g hg]
    have ht : (t : ℕ) ≤ d - 1 := by omega
    have hle1 : m + (t : ℕ) * e ≤ m + (d - 1) * e := by
      have h := Nat.mul_le_mul_right e ht
      omega
    have hmul : (m + (t : ℕ) * e) * g.natDegree
        ≤ (m + (d - 1) * e) * g.natDegree := Nat.mul_le_mul_right _ hle1
    have hcomm : (m + (d - 1) * e) * g.natDegree
        = g.natDegree * (m + (d - 1) * e) := Nat.mul_comm _ _
    omega
  have hjq : q * (j : ℕ) ≤ q * (J - 1) := Nat.mul_le_mul_left q (by omega)
  omega

/-! ## 7. THE d-BLOCK S2 THEOREM and the per-fiber capstone -/

/-- **d-block S2 (auxiliary-polynomial existence), general fiber value ζ.**  Under the
d-block budget `m(D + (deg g − 1)m + J) < d·J·(D+1)` and `DBlockIndependence`, there is a
NONZERO `P` of degree `≤ deg g·(m + (d−1)e) + D + q(J−1)` all of whose Hasse derivatives
of order `< m` vanish at every point of the fiber `N_ζ = {s : g(s)^e = ζ}`. -/
theorem superelliptic_stepanov_S2 (g : F[X]) (hg : g.Monic) (hdg : 0 < g.natDegree)
    {d m e J D : ℕ} (hJ : 0 < J)
    (hind : DBlockIndependence F d (Fintype.card F) D g)
    (he : e = (Fintype.card F - 1) / d)
    (hmq : m < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < d * (J * (D + 1)))
    (ζ : F) :
    ∃ P : F[X], P ≠ 0 ∧
      P.natDegree ≤ g.natDegree * (m + (d - 1) * e) + D + Fintype.card F * (J - 1) ∧
      ∀ s : F, (g.eval s) ^ e = ζ →
        ∀ k < m, (hasseDeriv k P).eval s = 0 := by
  obtain ⟨x, hx0, hxker⟩ := exists_kernel_vector_D g hg ζ d m e J D
    (D + (g.natDegree - 1) * m + J) hcount
  have hg0 : g ≠ 0 := hg.ne_zero
  refine ⟨auxPD g (Fintype.card F) d m e J D x,
    auxPD_ne_zero g hg0 hind he x hx0,
    auxPD_natDegree_le g hg (Fintype.card F) d m e J D x hJ, ?_⟩
  intro s hs k hk
  have hkq : k < Fintype.card F := by omega
  rw [eval_hasseDeriv_auxPD g hg ζ d m e J D k x (le_of_lt hk) hkq s hs,
    redWitnessD_eq_zero_of_kernel g hg hdg ζ d m e J D k x hk hJ hxker,
    eval_zero, mul_zero]

/-- **The round-24 capstone**: the per-fiber Stepanov count bound for order-`d`
superelliptic fibers, for EVERY fiber value ζ and every admissible `(m,J,D)`:
`m · #N_ζ ≤ deg g·(m + (d−1)e) + D + q(J−1)`,
conditional ONLY on the round-22 norm-fold Prop `DBlockIndependence` (proven for `d = 2`).
The character-sum assembly `|∑ χ(g(s))| ≤ d·(C√q + #{g=0})` from these `d` fiber counts is
recorded in the header; instantiating `(m,J,D)` is the `_R23ParameterChoice` pattern. -/
theorem superelliptic_stepanov_fiber_bound (g : F[X]) (hg : g.Monic)
    (hdg : 0 < g.natDegree)
    {d m e J D : ℕ} (hJ : 0 < J)
    (hind : DBlockIndependence F d (Fintype.card F) D g)
    (he : e = (Fintype.card F - 1) / d)
    (hmq : m < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < d * (J * (D + 1)))
    (ζ : F) :
    m * (Finset.univ.filter fun s : F => (g.eval s) ^ e = ζ).card
      ≤ g.natDegree * (m + (d - 1) * e) + D + Fintype.card F * (J - 1) := by
  obtain ⟨P, hP0, hPdeg, hPvan⟩ :=
    superelliptic_stepanov_S2 g hg hdg hJ hind he hmq hcount ζ
  refine le_trans ?_ hPdeg
  refine hasseDeriv_stepanov_degree_count hP0 ?_
  intro s hs
  rw [Finset.mem_filter] at hs
  exact hPvan s hs.2

/-- **Round-22 consistency check**: for `d = 2` and squarefree `g` the independence input
is PROVEN, so the fiber bound is unconditional — recovering (and generalizing from the
cubic to arbitrary squarefree `g`) the shape of round 22's
`cubic_stepanov_positive_fiber_bound`, now for BOTH fibers `ζ = ±1`. -/
theorem squarefree_two_block_fiber_bound (g : F[X]) (hg : g.Monic)
    (hsf : Squarefree g) (hdg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    {m e J D : ℕ} (hJ : 0 < J)
    (he : e = (Fintype.card F - 1) / 2)
    (hmq : m < Fintype.card F)
    (hD : 2 * D + g.natDegree < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < 2 * (J * (D + 1)))
    (ζ : F) :
    m * (Finset.univ.filter fun s : F => (g.eval s) ^ e = ζ).card
      ≤ g.natDegree * (m + (2 - 1) * e) + D + Fintype.card F * (J - 1) :=
  superelliptic_stepanov_fiber_bound g hg hdg hJ
    (dBlockIndependence_two g hsf hdg hq_odd hD) he hmq hcount ζ

/-- **Round-24 norm-fold corollary**: for `d = 4` and squarefree `g`, the newly proven
quartic norm-fold independence input makes the order-4 superelliptic fiber bound
unconditional.  This is the first `d > 2` instance of the d-block Stepanov S2 machine. -/
theorem squarefree_four_block_fiber_bound (g : F[X]) (hg : g.Monic)
    (hsf : Squarefree g) (hdg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (h4 : 4 ∣ (Fintype.card F - 1))
    {m e J D : ℕ} (hJ : 0 < J)
    (he : e = (Fintype.card F - 1) / 4)
    (hmq : m < Fintype.card F)
    (hD : 4 * D + 3 * g.natDegree < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < 4 * (J * (D + 1)))
    (ζ : F) :
    m * (Finset.univ.filter fun s : F => (g.eval s) ^ e = ζ).card
      ≤ g.natDegree * (m + (4 - 1) * e) + D + Fintype.card F * (J - 1) :=
  superelliptic_stepanov_fiber_bound g hg hdg hJ
    (dBlockIndependence_four g hsf hdg hq_odd h4 hD) he hmq hcount ζ

end ArkLib.ProximityGap.Frontier.R24SuperellipticS2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.exists_kernel_vector_D
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.quotient_natDegree_le_D
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.redWitnessD_eq_zero_of_kernel
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.eval_hasseDeriv_auxPD
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.auxPD_eq_mul
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.auxPD_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.auxPD_natDegree_le
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.superelliptic_stepanov_S2
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.superelliptic_stepanov_fiber_bound
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.squarefree_two_block_fiber_bound
#print axioms ArkLib.ProximityGap.Frontier.R24SuperellipticS2.squarefree_four_block_fiber_bound
