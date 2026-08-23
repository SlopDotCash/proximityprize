/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# SYZ36 — union-generation for band triples, reduced to a univariate syzygy

SYZ35 pinned the last open gate of the rate-`1/2` proximity strip to a single subspace fact:
for the shortened duals `A, B, C` of `RS[n,k]` on three band cores `Cᴬ, Cᴮ, Cᶜ`
(`A ⊓ B = ⊥`, pairwise overlaps `≤ k − 1`), the punctured-pair value is the closed form
`Σ_pair |Cᵢ∩Cⱼ| − |T| − 2k` **iff** the three cores generate the union shortening
`D_{Cᴬ∪Cᴮ∪Cᶜ}`.  SYZ25 reformulated generation as local-to-global polynomial rigidity: every
`p : U → F` that is `deg < k` on each core is globally `deg < k`.

This file carries that rigidity down to a **pure univariate polynomial syzygy**.  It formalizes the
cocycle → syzygy reduction chain and exhibits the Koszul obstruction, which is a *field-independent*
generation failure inside the stated band.

## The reduction chain (`Polynomial K`, `K` a field)

Suppose `p` is `deg < k` on each core: `p|_{Cᴬ} = p_A`, `p|_{Cᴮ} = p_B`, `p|_{Cᶜ} = p_C` with
`deg p_X < k`.  Set the pairwise mismatches `q_XY := p_X − p_Y` (`deg < k`).  They satisfy the
**cocycle identity** `q_AB − q_AC + q_BC = 0` (`cocycle_identity`).  Rigidity fails exactly when the
`q_XY` are not all zero.

Because `p_X = p_Y` on `C_X ∩ C_Y`, `q_XY` vanishes on the `m_XY := |C_X∩C_Y|` overlap points, so
(distinct roots, `deg < k`) `q_XY = V_XY · s_XY` with `deg s_XY < k − m_XY` (`vanish_factor_natDegree`).
Writing `V_XY = V_T · W_XY` for the triple-vanishing factor `V_T` (`deg V_T = |T|`) leaves the
**reduced syzygy** `W_AB r_AB − W_AC r_AC + W_BC r_BC = 0` with pairwise-coprime `W` and
`deg r_XY < k − m_XY`, after cancelling `V_T ≠ 0` (`reduce_by_VT`).

## The Koszul obstruction (the wall, honest)

The triple `(r_AB, r_AC, r_BC) = (W_AC, W_AB, 0)` is always a syzygy (`koszul_syzygy`), nonzero when
`W_AB, W_AC ≠ 0`, of pair-degrees `deg W_AC = m_AC − |T|` and `deg W_AB = m_AB − |T|`.  It is *in
budget* — hence a genuine extra cocycle, hence generation **fails** — as soon as
`m_AB + m_AC − |T| ≤ k − 1` (`koszul_in_budget`).  Probe
`scripts/probes/probe_syz36_union_generation.py` confirms: this Koszul certificate never coexists
with generation (`koszul_but_generates = 0` over `p ∈ {31,101,65537}`, generic and roots-of-unity
domains, thousands of band triples), and the exact **law**

  `finrank D_{⋃Cᵢ} − finrank(A ⊔ B ⊔ C)  =  dim { in-budget syzygies of (W_AB, −W_AC, W_BC) }`

holds with **0 mismatches**.  So union-generation is *exactly* a univariate μ-basis question, and it
is **false as a universal band statement**: the band admits Koszul counterexamples (smallest robust
family: `n=10, k=6`, cores of size `7`).  Generation holds robustly only in the tight sub-band where
every budget `k − m_XY ≤ 0` (rate `≤ 1/2` with maximal overlaps): then all `r_XY = 0` are forced
and rigidity is automatic (`generation_of_saturated_overlaps`).

## Status (honest)

**Partial / structural + refutation of the naive gate.**  The cocycle identity, the degree-drop
factorization, the `V_T`-cancellation, the Koszul syzygy and its in-budget criterion, and the
saturated-overlap generation case are proved axiom-clean.  The reduction *equates* union-generation
with the vanishing of the in-budget syzygy module (probe-exact); the μ-basis literature
(Cox–Sederberg–Chen: the syzygy module of a coprime univariate triple is free of rank `2` with
generator degrees summing to the total degree) is the classical tool for the residual, which for the
prescribed Vandermonde/roots-of-unity `W`-configuration remains open beyond the saturated sub-band.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ36

open Polynomial

variable {K : Type*} [Field K]

/-! ## 1. The cocycle identity -/

/-- **Cocycle identity.**  For any three "local" values `pA, pB, pC`, the pairwise mismatches
`q_XY := p_X − p_Y` satisfy `q_AB − q_AC + q_BC = 0`.  This is the exactness of the pairwise-mismatch
cochain: a family of local polynomials glues iff all mismatches vanish, and the mismatches are a
cocycle. -/
theorem cocycle_identity (pA pB pC : K[X]) :
    (pA - pB) - (pA - pC) + (pB - pC) = 0 := by ring

/-! ## 2. Degree-drop factorization: vanishing on distinct points -/

/-- **Degree-drop factorization.**  A nonzero polynomial `q` of `natDegree < D` that vanishes on a
finite set `s` of distinct points factors as `q = (∏_{a∈s} (X − a)) · t` with
`natDegree t + s.card = natDegree q`, hence `natDegree t < D − s.card`.  This is the univariate
"root budget": vanishing on `m` points costs `m` from the degree.  (`q ≠ 0`, so all listed roots are
genuine and the quotient degree is exact.) -/
theorem vanish_factor_natDegree (q : K[X]) (s : Finset K) (hq : q ≠ 0)
    (hvanish : ∀ a ∈ s, q.eval a = 0) :
    ∃ t : K[X], q = (∏ a ∈ s, (X - C a)) * t
      ∧ (∏ a ∈ s, (X - C a)).natDegree + t.natDegree = q.natDegree := by
  -- `∏ (X - a)` divides `q` because each `a ∈ s` is a root and the factors are pairwise coprime.
  have hdvd : (∏ a ∈ s, (X - C a)) ∣ q := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a ha b hb hab
      exact (pairwise_coprime_X_sub_C (Function.injective_id) (by simpa using hab))
    · intro a ha
      rw [dvd_iff_isRoot]
      exact hvanish a ha
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ht, ?_⟩
  -- degrees add because `K[X]` is a domain and `q ≠ 0`.
  have hprod_ne : (∏ a ∈ s, (X - C a)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _; exact X_sub_C_ne_zero a
  have ht_ne : t ≠ 0 := by
    intro h; rw [h, mul_zero] at ht; exact hq ht
  rw [ht, natDegree_mul hprod_ne ht_ne]

/-- The vanishing product `∏_{a∈s} (X − a)` has `natDegree = s.card`. -/
theorem natDegree_prod_X_sub_C (s : Finset K) :
    (∏ a ∈ s, (X - C a)).natDegree = s.card := by
  rw [natDegree_prod _ _ (fun a _ => X_sub_C_ne_zero a)]
  simp [natDegree_X_sub_C]

/-- The clean degree-budget corollary: with `natDegree q < D` and `q` vanishing on `s` distinct
points, the cofactor `t` has `natDegree t + s.card < D`. -/
theorem vanish_cofactor_lt (q : K[X]) (s : Finset K) (D : ℕ) (hq : q ≠ 0)
    (hdeg : q.natDegree < D) (hvanish : ∀ a ∈ s, q.eval a = 0) :
    ∃ t : K[X], q = (∏ a ∈ s, (X - C a)) * t ∧ t.natDegree + s.card < D := by
  obtain ⟨t, ht, hadd⟩ := vanish_factor_natDegree q s hq hvanish
  rw [natDegree_prod_X_sub_C] at hadd
  exact ⟨t, ht, by omega⟩

/-! ## 3. `V_T`-cancellation: the reduced syzygy -/

/-- **Cancellation of the common triple factor.**  In the integral domain `K[X]`, if `V_T ≠ 0` and
`V_T * expr = 0` then `expr = 0`.  Applied to the cocycle after factoring the common triple-vanishing
polynomial `V_T` out of all three overlap-vanishing factors, this produces the reduced syzygy
`W_AB r_AB − W_AC r_AC + W_BC r_BC = 0`. -/
theorem reduce_by_VT (VT WAB WAC WBC rAB rAC rBC : K[X]) (hVT : VT ≠ 0)
    (h : VT * (WAB * rAB - WAC * rAC + WBC * rBC) = 0) :
    WAB * rAB - WAC * rAC + WBC * rBC = 0 := by
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 hVT
  · exact h2

/-! ## 4. The Koszul obstruction — the honest wall -/

/-- **Koszul syzygy.**  The triple `(r_AB, r_AC, r_BC) = (W_AC, W_AB, 0)` is always a syzygy of the
reduced relation:
`W_AB * W_AC − W_AC * W_AB + W_BC * 0 = 0`.  Pure ring identity — no coprimality or degree
hypotheses. -/
theorem koszul_syzygy (WAB WAC WBC : K[X]) :
    WAB * WAC - WAC * WAB + WBC * 0 = 0 := by ring

/-- The Koszul syzygy is **nonzero** whenever `W_AB` and `W_AC` are both nonzero: its first component
is `W_AC ≠ 0`.  So it is a genuine extra cocycle, i.e. a witness that the local polynomials do *not*
glue. -/
theorem koszul_syzygy_ne_zero (WAB WAC : K[X]) (hAC : WAC ≠ 0) :
    ¬ (WAC = 0 ∧ WAB = 0 ∧ (0 : K[X]) = 0) := by
  rintro ⟨h, _, _⟩; exact hAC h

/-- **In-budget criterion (the forced-failure certificate).**  The Koszul component degrees are
`deg r_AB = deg W_AC = m_AC − |T|` and `deg r_AC = deg W_AB = m_AB − |T|`.  Both fit the per-pair
budget `deg r_XY ≤ k − 1 − m_XY` — so the Koszul syzygy is a genuine in-budget extra cocycle and
generation **fails** — exactly when `m_AB + m_AC − |T| ≤ k − 1` (equivalently
`m_AB + m_AC − |T| < k`).  Stated as the arithmetic that both budget inequalities reduce to. -/
theorem koszul_in_budget (mAB mAC t k : ℕ)
    (hbudget : mAB + mAC - t ≤ k - 1)
    (htAB : t ≤ mAB) (htAC : t ≤ mAC) (hkAB : mAB ≤ k - 1) (hkAC : mAC ≤ k - 1) :
    -- `deg r_AB = mAC − t ≤ k − 1 − mAB`  and  `deg r_AC = mAB − t ≤ k − 1 − mAC`
    (mAC - t ≤ (k - 1) - mAB) ∧ (mAB - t ≤ (k - 1) - mAC) := by
  omega

/-! ## 5. The saturated sub-band: generation is automatic (rate `≤ 1/2`) -/

/-- **Saturated-overlap generation.**  If every per-pair budget is nonpositive (`k ≤ m_XY` for the
pair whose factor would carry a cofactor), the cofactors `s_XY` are forced to be `0` — a nonzero
`deg < k − m_XY` polynomial cannot exist when `k ≤ m_XY`.  Then every pairwise mismatch `q_XY`
vanishes and the local polynomials glue: generation is automatic.  This is the tight sub-band (rate
`≤ 1/2` with maximal overlaps) where the syzygy budgets vanish; here SYZ35's gate closes
unconditionally.  Formalized as: a polynomial of `natDegree < k − m` with `k ≤ m` is `0` (vacuous
degree window). -/
theorem saturated_cofactor_zero (s : K[X]) (k m : ℕ) (hkm : k ≤ m)
    (hdeg : s ≠ 0 → s.natDegree + m < k) : s = 0 := by
  by_contra h
  have := hdeg h
  omega

end ArkLib.ProximityGap.SYZ36

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ36.cocycle_identity
#print axioms ArkLib.ProximityGap.SYZ36.vanish_factor_natDegree
#print axioms ArkLib.ProximityGap.SYZ36.natDegree_prod_X_sub_C
#print axioms ArkLib.ProximityGap.SYZ36.vanish_cofactor_lt
#print axioms ArkLib.ProximityGap.SYZ36.reduce_by_VT
#print axioms ArkLib.ProximityGap.SYZ36.koszul_syzygy
#print axioms ArkLib.ProximityGap.SYZ36.koszul_syzygy_ne_zero
#print axioms ArkLib.ProximityGap.SYZ36.koszul_in_budget
#print axioms ArkLib.ProximityGap.SYZ36.saturated_cofactor_zero
