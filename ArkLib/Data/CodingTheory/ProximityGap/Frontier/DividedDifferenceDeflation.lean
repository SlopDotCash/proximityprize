/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Divided-difference deflation: the j>=2 Schur-minor CONVERSE (#407)

DRAFT brick for the lever `dd-deflation-converse`.

Builds the deflation lemma Mathlib lacks, proving the OPEN converse of the Schur-minor binder
(the residual of `SchurMinorStaircase`):

  If for EVERY `(k+1)`-subset `R' ⊆ R` the divided difference `dividedDifferencePow R' v b`
  vanishes, then `x^b` agrees with SOME degree-`<k` codeword on `R` (membership).

Mechanism (deflation): the order-`k` divided differences vanishing on every `(k+1)`-subset
propagate UP the divided-difference recursion to every higher-order subset DD, so the leading
coefficient of the full interpolant vanishes; iterating, the interpolant of `x^b` over `R` has
degree `< k`, hence IS the agreeing codeword.

All theorems reference the REAL in-tree `dividedDifferencePow` (from `SchurLagrangeBridge`) and
`Lagrange.interpolate`.
-/

open Finset Polynomial

namespace ProximityGap.DDDeflation

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-! ## Part 1 — the general value-function divided difference and its recursion. -/

/-- **Value-function divided difference.** The top (`#R−1`) coefficient of the Lagrange
interpolant of the data `{(v i, r i)}_{i∈R}`: `ddVal R v r = Σ_{i∈R} r i / ∏_{j∈R.erase i}(v i − v j)`.
Specialises to `dividedDifferencePow` at `r = (·^b)`. -/
noncomputable def ddVal (R : Finset ι) (v : ι → F) (r : ι → F) : F :=
  ∑ i ∈ R, r i * (∏ j ∈ R.erase i, (v i - v j))⁻¹

/-- `dividedDifferencePow` is the value-function divided difference at the monomial data. -/
theorem ddVal_pow (R : Finset ι) (v : ι → F) (b : ℕ) :
    ddVal R v (fun i => (v i) ^ b) = dividedDifferencePow R v b := rfl

/-- **`ddVal` is the top coefficient of the interpolant.** Direct restatement of the
in-tree `interpolate_coeff_top`. -/
theorem ddVal_eq_interpolate_coeff_top {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R)
    (r : ι → F) :
    (Lagrange.interpolate R v r).coeff (#R - 1) = ddVal R v r :=
  interpolate_coeff_top hvs r

/-- **Top coefficient of a product with a (degree-`≤1`) factor.** If `A.natDegree ≤ d` and
`B.natDegree ≤ 1`, then `(A*B).coeff (d+1) = A.coeff d * B.coeff 1`. The cross term that would
contribute at `d+1` from below is killed by the degree caps. -/
theorem coeff_mul_top_linear {A B : F[X]} {d : ℕ} (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ 1) :
    (A * B).coeff (d + 1) = A.coeff d * B.coeff 1 := by
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- range (d+2): only the pair (d,1) survives (q=1, p=d); q≥2 ⇒ B.coeff q = 0; q=0,p=d+1 ⇒ A=0.
  rw [Finset.sum_eq_single d]
  · -- the surviving term is at p = d, q = d+1-d = 1
    have : d + 1 - d = 1 := by omega
    simp [this]
  · intro p hp hpd
    simp only
    rcases Nat.lt_or_ge p d with hlt | hge
    · -- p < d ⇒ q = d+1-p ≥ 2 ⇒ B.coeff q = 0
      have hBz : B.coeff (d + 1 - p) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB (by omega))
      rw [hBz, mul_zero]
    · -- p > d ⇒ A.coeff p = 0
      have hpgt : d < p := lt_of_le_of_ne hge (Ne.symm hpd)
      have hAz : A.coeff p = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA hpgt)
      rw [hAz, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

/-- **`basisDivisor` is a monic-scaled linear factor: its degree-1 coefficient.**
`(basisDivisor x y).coeff 1 = (x − y)⁻¹`. -/
theorem coeff_one_basisDivisor (x y : F) :
    (Lagrange.basisDivisor x y).coeff 1 = (x - y)⁻¹ := by
  rw [Lagrange.basisDivisor, mul_comm, Polynomial.coeff_mul_C, Polynomial.coeff_sub,
    Polynomial.coeff_X_one, Polynomial.coeff_C, if_neg (by norm_num), sub_zero, one_mul]

/-- **The divided-difference recursion (value-function form).** For distinct nodes `i, j ∈ R`
(with `#R ≥ 2`), the order-`(#R−1)` divided difference deflates to the two order-`(#R−2)`
divided differences over the erased subsets:

  `ddVal R v r = (ddVal (R.erase j) v r − ddVal (R.erase i) v r) · (v i − v j)⁻¹`.

This is the standard Newton divided-difference recursion, derived by reading off the top
coefficient of the in-tree polynomial recursion `interpolate_eq_add_interpolate_erase`. -/
theorem ddVal_recursion {R : Finset ι} {v : ι → F} (r : ι → F) (hvs : Set.InjOn v R)
    {i j : ι} (hi : i ∈ R) (hj : j ∈ R) (hij : i ≠ j) :
    ddVal R v r
      = (ddVal (R.erase j) v r - ddVal (R.erase i) v r) * (v i - v j)⁻¹ := by
  have hcard2 : 2 ≤ #R := by
    have : ({i, j} : Finset ι) ⊆ R := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = #({i, j} : Finset ι) := by rw [Finset.card_pair hij]
    _ ≤ #R := Finset.card_le_card this
  -- injectivity on erased sets
  have hvsj : Set.InjOn v (R.erase j) := hvs.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  have hvsi : Set.InjOn v (R.erase i) := hvs.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  -- cards of erased sets
  have hcj : #(R.erase j) = #R - 1 := Finset.card_erase_of_mem hj
  have hci : #(R.erase i) = #R - 1 := Finset.card_erase_of_mem hi
  -- the polynomial recursion
  have hpoly := Lagrange.interpolate_eq_add_interpolate_erase (r := r) hvs hi hj hij
  -- read off coeff (#R - 1) of both sides
  have hlhs : (Lagrange.interpolate R v r).coeff (#R - 1) = ddVal R v r := by
    rw [ddVal_eq_interpolate_coeff_top hvs]
  -- natDegree bounds of the two erased interpolants: ≤ #R - 2
  have hAdeg : (Lagrange.interpolate (R.erase j) v r).natDegree ≤ #R - 2 := by
    have := Lagrange.degree_interpolate_lt (r := r) hvsj
    rw [hcj] at this
    have hnd := Polynomial.natDegree_lt_iff_degree_lt
      (p := Lagrange.interpolate (R.erase j) v r) (n := #R - 1)
    by_cases hz : Lagrange.interpolate (R.erase j) v r = 0
    · rw [hz]; simp
    · have : (Lagrange.interpolate (R.erase j) v r).natDegree < #R - 1 := (hnd hz).mpr this
      omega
  have hBdeg : (Lagrange.interpolate (R.erase i) v r).natDegree ≤ #R - 2 := by
    have := Lagrange.degree_interpolate_lt (r := r) hvsi
    rw [hci] at this
    have hnd := Polynomial.natDegree_lt_iff_degree_lt
      (p := Lagrange.interpolate (R.erase i) v r) (n := #R - 1)
    by_cases hz : Lagrange.interpolate (R.erase i) v r = 0
    · rw [hz]; simp
    · have : (Lagrange.interpolate (R.erase i) v r).natDegree < #R - 1 := (hnd hz).mpr this
      omega
  -- degree-1 of the basisDivisors
  have hBD1 : (Lagrange.basisDivisor (v i) (v j)).natDegree ≤ 1 := by
    rcases eq_or_ne (v i) (v j) with h | h
    · rw [h, Lagrange.basisDivisor_self]; simp
    · exact le_of_eq (Lagrange.natDegree_basisDivisor_of_ne h)
  have hBD2 : (Lagrange.basisDivisor (v j) (v i)).natDegree ≤ 1 := by
    rcases eq_or_ne (v j) (v i) with h | h
    · rw [h, Lagrange.basisDivisor_self]; simp
    · exact le_of_eq (Lagrange.natDegree_basisDivisor_of_ne h)
  -- index bookkeeping
  have hidx : (#R - 1) = (#R - 2) + 1 := by omega
  -- compute coeff (#R-1) of RHS using coeff_mul_top_linear
  have hrhs : (Lagrange.interpolate (R.erase j) v r * Lagrange.basisDivisor (v i) (v j)
        + Lagrange.interpolate (R.erase i) v r * Lagrange.basisDivisor (v j) (v i)).coeff (#R - 1)
      = ddVal (R.erase j) v r * (v i - v j)⁻¹
        + ddVal (R.erase i) v r * (v j - v i)⁻¹ := by
    rw [Polynomial.coeff_add, hidx,
      coeff_mul_top_linear hAdeg hBD1, coeff_mul_top_linear hBdeg hBD2,
      coeff_one_basisDivisor, coeff_one_basisDivisor]
    have hAcoeff : (Lagrange.interpolate (R.erase j) v r).coeff (#R - 2) = ddVal (R.erase j) v r := by
      have := ddVal_eq_interpolate_coeff_top hvsj r
      rwa [hcj, show #R - 1 - 1 = #R - 2 from by omega] at this
    have hBcoeff : (Lagrange.interpolate (R.erase i) v r).coeff (#R - 2) = ddVal (R.erase i) v r := by
      have := ddVal_eq_interpolate_coeff_top hvsi r
      rwa [hci, show #R - 1 - 1 = #R - 2 from by omega] at this
    rw [hAcoeff, hBcoeff]
  -- take coeff (#R-1) of the polynomial recursion
  have hcoeff := congrArg (fun p : F[X] => p.coeff (#R - 1)) hpoly
  simp only at hcoeff
  rw [hlhs, hrhs] at hcoeff
  rw [hcoeff]
  -- (v j - v i)⁻¹ = -(v i - v j)⁻¹
  have hneg : (v j - v i)⁻¹ = -(v i - v j)⁻¹ := by
    rw [← neg_sub (v i) (v j), inv_neg]
  rw [hneg]; ring

/-! ## Part 2 — deflation: vanishing of order-`k` DDs propagates to all higher orders. -/

/-- **Deflation propagation.** If every `(k+1)`-subset `R' ⊆ R` has vanishing divided difference
`ddVal R' v r = 0`, then EVERY subset `S ⊆ R` with `#S ≥ k+1` has `ddVal S v r = 0`. The order-`k`
divided differences vanishing on all `(k+1)`-subsets propagate up through `ddVal_recursion`:
the order-`m` divided difference over an `(m+1)`-subset is a combination of two order-`(m−1)`
divided differences over its `m`-subsets, which vanish by induction. -/
theorem ddVal_subset_vanish_of_base
    {R : Finset ι} {v : ι → F} {r : ι → F} (hvs : Set.InjOn v R) {k : ℕ}
    (hbase : ∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → ddVal R' v r = 0) :
    ∀ S : Finset ι, S ⊆ R → k + 1 ≤ #S → ddVal S v r = 0 := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hSR hScard
    rcases Nat.eq_or_lt_of_le hScard with heq | hlt
    · -- #S = k+1: base hypothesis
      exact hbase S hSR heq.symm
    · -- #S ≥ k+2: pick two distinct nodes, deflate
      have hScard2 : k + 2 ≤ #S := hlt
      have hSnonempty : 2 ≤ #S := by omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < #S)
      have hvsS : Set.InjOn v S := hvs.mono (Finset.coe_subset.mpr hSR)
      rw [ddVal_recursion r hvsS hi hj hij]
      -- both erased subsets have size #S - 1 ≥ k+1 and are ⊆ R
      have hejR : S.erase j ⊆ R := (Finset.erase_subset _ _).trans hSR
      have heiR : S.erase i ⊆ R := (Finset.erase_subset _ _).trans hSR
      have hejcard : #(S.erase j) = #S - 1 := Finset.card_erase_of_mem hj
      have heicard : #(S.erase i) = #S - 1 := Finset.card_erase_of_mem hi
      have hejssub : S.erase j ⊂ S := Finset.erase_ssubset hj
      have heissub : S.erase i ⊂ S := Finset.erase_ssubset hi
      have hejv : ddVal (S.erase j) v r = 0 :=
        ih (S.erase j) hejssub hejR (by omega)
      have heiv : ddVal (S.erase i) v r = 0 :=
        ih (S.erase i) heissub heiR (by omega)
      rw [hejv, heiv, sub_zero, zero_mul]

/-! ## Part 3 — the deflation theorem: full interpolant has degree `< k`. -/

/-- **The deflation theorem.** If every `(k+1)`-subset `R' ⊆ R` has vanishing divided difference
`ddVal R' v r = 0`, then the full Lagrange interpolant of `r` over `R` has `degree < k`. This is
the Newton forward-difference deflation: all order-`k` divided differences vanishing forces the
interpolant to be a polynomial of degree `< k`. Proof: strong induction on `#R`. If `#R ≤ k` the
interpolant already has degree `< #R ≤ k`. Otherwise the leading coefficient (the order-`(#R−1)`
divided difference) vanishes by `ddVal_subset_vanish_of_base`, so the interpolant has degree
`< #R − 1`, hence equals the interpolant over `R.erase a` (size `#R − 1`), to which the inductive
hypothesis applies. -/
theorem degree_interpolate_lt_of_subsets_vanish
    {R : Finset ι} {v : ι → F} {r : ι → F} (hvs : Set.InjOn v R) {k : ℕ}
    (hbase : ∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → ddVal R' v r = 0) :
    (Lagrange.interpolate R v r).degree < (k : WithBot ℕ) := by
  -- revert the data so the strong-induction hypothesis carries them
  induction R using Finset.strongInduction with
  | _ R ih =>
    by_cases hsmall : #R ≤ k
    · -- degree < #R ≤ k
      refine lt_of_lt_of_le (Lagrange.degree_interpolate_lt (r := r) hvs) ?_
      exact_mod_cast hsmall
    · -- #R ≥ k+1
      have hkR : k + 1 ≤ #R := by omega
      -- the leading (order #R-1) divided difference vanishes
      have htop : ddVal R v r = 0 :=
        ddVal_subset_vanish_of_base hvs hbase R (subset_refl R) hkR
      -- so the interpolant has degree < #R - 1
      have hcoeff_top : (Lagrange.interpolate R v r).coeff (#R - 1) = 0 := by
        rw [ddVal_eq_interpolate_coeff_top hvs]; exact htop
      have hdeglt : (Lagrange.interpolate R v r).degree < ((#R - 1 : ℕ) : WithBot ℕ) := by
        have hltR := Lagrange.degree_interpolate_lt (r := r) hvs
        -- degree < #R and coeff (#R-1) = 0 ⇒ degree < #R - 1
        rw [Polynomial.degree_lt_iff_coeff_zero] at hltR ⊢
        intro m hm
        rcases Nat.lt_or_ge m (#R) with hmR | hmR
        · -- m in [#R-1, #R): so m = #R-1
          have : m = #R - 1 := by
            have hge : #R - 1 ≤ m := by exact_mod_cast hm
            omega
          rw [this]; exact hcoeff_top
        · exact hltR m (by exact_mod_cast hmR)
      -- pick a node to erase
      obtain ⟨a, ha⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
      have hacard : #(R.erase a) = #R - 1 := Finset.card_erase_of_mem ha
      have hvsa : Set.InjOn v (R.erase a) := hvs.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
      -- the interpolant over R equals the interpolant over R.erase a (deg < #R-1, agrees on erase)
      have heq_interp : Lagrange.interpolate R v r = Lagrange.interpolate (R.erase a) v r := by
        refine Lagrange.eq_interpolate_of_eval_eq r (f := Lagrange.interpolate R v r) hvsa ?_ ?_
        · rw [hacard]; exact hdeglt
        · intro b hb
          have hbR : b ∈ R := Finset.mem_of_mem_erase hb
          exact Lagrange.eval_interpolate_at_node r hvs hbR
      -- apply IH to R.erase a
      have hbase' : ∀ R' : Finset ι, R' ⊆ R.erase a → #R' = k + 1 → ddVal R' v r = 0 := by
        intro R' hR' hcard'
        exact hbase R' (hR'.trans (Finset.erase_subset _ _)) hcard'
      have hssub : R.erase a ⊂ R := Finset.erase_ssubset ha
      have hIH := ih (R.erase a) hssub hvsa hbase'
      rw [heq_interp]; exact hIH

/-! ## Part 4 — the Schur-minor CONVERSE, wired to the real `dividedDifferencePow`. -/

/-- **The deflation theorem specialised to the monomial `x^b` and the REAL `dividedDifferencePow`.**
If for every `(k+1)`-subset `R' ⊆ R` the in-tree divided difference `dividedDifferencePow R' v b`
vanishes, then the Lagrange interpolant of `x^b` over `R` has `degree < k`. (Pure restatement of
`degree_interpolate_lt_of_subsets_vanish` at `r = (·^b)`, using `ddVal_pow`.) -/
theorem degree_interpolate_pow_lt_of_dividedDifferencePow_vanish
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) {k b : ℕ}
    (hvanish : ∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → dividedDifferencePow R' v b = 0) :
    (Lagrange.interpolate R v (fun i => (v i) ^ b)).degree < (k : WithBot ℕ) := by
  refine degree_interpolate_lt_of_subsets_vanish hvs (k := k) ?_
  intro R' hR' hcard
  rw [ddVal_pow]
  exact hvanish R' hR' hcard

/-- **THE SCHUR-MINOR CONVERSE (membership form).** The OPEN residual of `SchurMinorStaircase`,
now PROVEN: if every `(k+1)`-subset divided difference `dividedDifferencePow R' v b` vanishes,
then `x^b` agrees on the radius-`m` set `R` with SOME codeword `g` of `degree < k` (it lands in
`RS[R,k]`). The witnessing codeword is the Lagrange interpolant of `x^b` over `R`, whose degree is
`< k` by deflation. This is the converse to the in-tree forward direction
`SchurMinorStaircase.dividedDifference_vanishes_of_agrees`; together they make the deployed
`j`-fold minor binder an IFF — a real closure of the binder STRUCTURE. -/
theorem agrees_with_deg_lt_of_dividedDifferencePow_vanish
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) {k b : ℕ}
    (hvanish : ∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → dividedDifferencePow R' v b = 0) :
    ∃ g : F[X], g.degree < k ∧ ∀ i ∈ R, g.eval (v i) = (v i) ^ b := by
  refine ⟨Lagrange.interpolate R v (fun i => (v i) ^ b), ?_, ?_⟩
  · exact_mod_cast degree_interpolate_pow_lt_of_dividedDifferencePow_vanish hvs hvanish
  · intro i hi
    exact Lagrange.eval_interpolate_at_node (fun i => (v i) ^ b) hvs hi

/-- **The deployed `j`-fold Schur-minor binder is an IFF.** Combining the in-tree forward
direction (`x^b ∈ RS[R,k]` ⟹ all `(k+1)`-subset divided differences vanish) with the deflation
converse proved here: `x^b` agrees with a degree-`<k` codeword on `R` IF AND ONLY IF every
`(k+1)`-subset divided difference `dividedDifferencePow R' v b` vanishes. References the REAL
in-tree `dividedDifferencePow`. (The forward arrow is `dividedDifference_vanishes_of_agrees` in
`SchurMinorStaircase`; restated here inline so this file stays import-light.) -/
theorem agrees_iff_dividedDifferencePow_vanish
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) {k b : ℕ} :
    (∃ g : F[X], g.degree < k ∧ ∀ i ∈ R, g.eval (v i) = (v i) ^ b)
      ↔ (∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → dividedDifferencePow R' v b = 0) := by
  constructor
  · -- forward: agreement ⇒ all subset divided differences vanish
    rintro ⟨g, hgdeg, hagree⟩ R' hR' hk
    have hvs' : Set.InjOn v R' := hvs.mono (Finset.coe_subset.mpr hR')
    have hgdeg' : g.degree < #R' := by
      rw [hk]; exact lt_of_lt_of_le hgdeg (by exact_mod_cast Nat.le_succ k)
    have hginterp : Lagrange.interpolate R' v (fun i => (v i) ^ b) = g := by
      refine (Lagrange.eq_interpolate_of_eval_eq _ hvs' hgdeg' fun i hi => ?_).symm
      exact hagree i (hR' hi)
    have hkk : k = #R' - 1 := by omega
    rw [← ddVal_pow, ← ddVal_eq_interpolate_coeff_top hvs', hginterp, ← hkk]
    exact Polynomial.coeff_eq_zero_of_degree_lt hgdeg
  · -- converse: deflation
    exact agrees_with_deg_lt_of_dividedDifferencePow_vanish hvs

end ProximityGap.DDDeflation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DDDeflation.coeff_mul_top_linear
#print axioms ProximityGap.DDDeflation.coeff_one_basisDivisor
#print axioms ProximityGap.DDDeflation.ddVal_recursion
#print axioms ProximityGap.DDDeflation.ddVal_subset_vanish_of_base
#print axioms ProximityGap.DDDeflation.degree_interpolate_lt_of_subsets_vanish
#print axioms ProximityGap.DDDeflation.degree_interpolate_pow_lt_of_dividedDifferencePow_vanish
#print axioms ProximityGap.DDDeflation.agrees_with_deg_lt_of_dividedDifferencePow_vanish
#print axioms ProximityGap.DDDeflation.agrees_iff_dividedDifferencePow_vanish
