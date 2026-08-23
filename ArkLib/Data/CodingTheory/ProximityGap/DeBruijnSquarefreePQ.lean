/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTPacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.CRTExponentGridSum
import Mathlib.Tactic

/-!
# Issue #232 — de Bruijn at squarefree `pq`: the two-sided IFF classification of
# vanishing 0/1 sums, in product / packet-union / cardinality form

Sibling brick to `DeBruijnIndicatorDisjointness` (the O87 step-(3) lane, landed first,
whose headline `debruijn_squarefree_two_prime` is the FORWARD implication in
shift-closure form): this file gives the **two-sided IFF** at the squarefree base case
`n = p·q`, in the explicit **product form** on the CRT grid and the **packet-union
form** in exponent space (with the `gridSet`/`gridMap` reconstruction lemmas needed to
move between them), plus the **cardinality corollary**. The converse direction (every
pure form vanishes) is what makes the census counts `2^p + 2^q − 2` a theorem-shaped
statement, and the iff is the API downstream counting consumers want:

* `subset_sum_rigidity` — **the new dichotomy engine**: two subsets of `μ_p`
  (`p` prime, char 0) with EQUAL subset sums are equal, or are `{∅, μ_p}`.
  Engine: the indicator difference is a `{−1,0,1}`-coefficient polynomial of degree
  `< p` vanishing at `ξ`, hence a constant multiple of `Φ_p = 1 + X + ⋯ + X^{p−1}`
  (`minpoly.dvd` + degree pinch), and the constant is the common difference value.
* `grid_vanishing_iff_pure` — **the classification on the CRT grid**: for `I` inside
  `[0,p) × [0,q)`, the double sum `Σ_{(j,c)∈I} ξ^j·η^c` vanishes **iff** `I` is a
  product `A ×ˢ [0,q)` (a union of full `q`-packets) or `[0,p) ×ˢ T` (a union of full
  `p`-packets). Forward: the O83 fiber-slice invariance
  (`crt_fiber_slice_coprimePrimePowers` at `a = b = 1`) makes all column fibers have
  equal `ξ`-sums, and the rigidity dichotomy forces all fibers equal (a product) or
  all fibers ∈ {∅, full} (the transpose product). Backward: the geometric sum
  `Σ_{c<q} η^c = 0` (resp. `Σ_{j<p} ξ^j = 0`) kills each product form.
* `vanishing_subset_sum_iff_pure_packets` — **the headline**, in subset-sum form via
  the O82 bijection: for `S ⊆ ZMod (p·q)` and `ζ` a primitive `pq`-th root of unity,
  `Σ_{e∈S} ζ^e = 0` iff the CRT grid set of `S` is one of the two pure products.
* `vanishing_subset_sum_iff_packet_union` — the same in **exponent space**: `S` IS the
  image of a pure product under the CRT grid map — i.e. a DISJOINT union of rotated
  `μ_q`-packets, or a disjoint union of rotated `μ_p`-packets. Disjointness is
  automatic (distinct packets of the same prime are disjoint cosets); PURITY (no
  mixing of `p`- and `q`-packets) is the genuinely squarefree phenomenon: at `n = pq`
  every `p`-packet meets every `q`-packet (CRT), so mixed disjoint unions cannot
  exist — in contrast to `p^a q^b` with `a + b > 2`, where mixing is possible and the
  divisor-coset law (O70) governs. Cardinality corollary `card_of_vanishing_subset_sum`:
  `|S| ∈ qℕ ∪ pℕ` — Lam–Leung at `pq` with the full structure attached.

Falsified first: `scripts/probes/probe_debruijn_squarefree_pq.py` (exact `ℤ[x]/Φ_n`
arithmetic, no floats; exit 0): the rigidity dichotomy exhaustively at
`p ∈ {3,5,7,11,13}` (zero violations over all `2^p` subsets), the classification
exhaustively at `n = 6` (10 vanishing subsets `= 2^2 + 2^3 − 2`, all pure) and
`n = 15` (all `2^15` subsets; 38 vanishing `= 2^3 + 2^5 − 2`), and at `n = 35` all
`2^5 + 2^7` pure forms vanish + 200 000 random + 2 000 single-toggle adversarial
non-pure subsets all non-vanishing. The counts matching `2^p + 2^q − 2` exactly
confirms the classification is tight.

This file consumes `CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers` (step 1) and
`CRTExponentGridSum.subset_sum_eq_grid_double_sum`/`gridMap` (step 2). The mixed-radix
case `p^a q^b` (`a·b > 1`) is genuinely different — the pure dichotomy proven here is
FALSE there (mixtures exist; measured exactly by the O87 probe: 24/100 at `n = 12`,
432/1000 at `n = 18`) and the target shape is the O70 divisor-coset law via the
O90 packet-combination descent engine (`PacketCombinationDivisibility`) and the
`DeBruijnTwoPrime` double-slice tiers.

Literature pin (full report on #232): the forward content at `pq` is de Bruijn 1953 §3
as modernized by Lam–Leung (J. Algebra 224 (2000), Thm 3.3 + Cor 3.4); the multiset
disjointness phrasing at `p^a q^b` is Malikiosis (arXiv:2005.05800, Thm 5.2). No prior
formalization of this theory exists in any proof assistant (mathlib4/AFP/Coq searched,
2026-06-09); the `t > 1` window law (O70) does not appear in the literature at all.
-/

namespace DeBruijnSquarefreePQ

open Polynomial Finset

variable {L : Type*} [Field L] [CharZero L]

/-- **Coefficient rigidity at a prime**: any vanishing `ℚ`-combination of
`1, ξ, …, ξ^{p−1}` (`ξ` a primitive `p`-th root of unity, `p` prime, char 0) has all
coefficients equal. The relation module of `μ_p` is spanned by the all-ones vector:
the combination, read as a polynomial of degree `< p` vanishing at `ξ`, is divisible
by `minpoly ℚ ξ = Φ_p` of degree `p − 1`, hence is a constant multiple of
`Φ_p = 1 + X + ⋯ + X^{p−1}`. -/
lemma vanishing_combination_const {p : ℕ} (hp : p.Prime) {ξ : L}
    (hξ : IsPrimitiveRoot ξ p) (a : ℕ → ℚ)
    (h : ∑ j ∈ Finset.range p, algebraMap ℚ L (a j) * ξ ^ j = 0) :
    ∃ c : ℚ, ∀ j < p, a j = c := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : ℚ[X] := ∑ j ∈ Finset.range p, C (a j) * X ^ j with hP
  have hcoeff : ∀ j < p, P.coeff j = a j := by
    intro j hj
    rw [hP, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range p) j a]
    simp [hj]
  have haev : (aeval ξ) P = 0 := by
    rw [hP, map_sum]
    simpa only [map_mul, aeval_C, map_pow, aeval_X] using h
  by_cases hP0 : P = 0
  · refine ⟨0, fun j hj => ?_⟩
    have := hcoeff j hj
    rw [hP0, coeff_zero] at this
    exact this.symm
  · have hdeg : P.natDegree ≤ p - 1 := by
      rw [hP]
      refine natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
      exact le_trans (natDegree_C_mul_X_pow_le _ _)
        (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj))
    have hmin : minpoly ℚ ξ = cyclotomic p ℚ :=
      (cyclotomic_eq_minpoly_rat hξ hp.pos).symm
    have hdvd : cyclotomic p ℚ ∣ P := hmin ▸ minpoly.dvd ℚ ξ haev
    obtain ⟨Q, hQ⟩ := hdvd
    have hΦne : (cyclotomic p ℚ) ≠ 0 := cyclotomic_ne_zero p ℚ
    have hQ0 : Q ≠ 0 := fun hq0 => hP0 (by rw [hQ, hq0, mul_zero])
    have hdegΦ : (cyclotomic p ℚ).natDegree = p - 1 := by
      rw [natDegree_cyclotomic, Nat.totient_prime hp]
    have hdegQ : Q.natDegree = 0 := by
      have hmul := natDegree_mul hΦne hQ0
      rw [← hQ, hdegΦ] at hmul
      omega
    obtain ⟨u, hu⟩ : ∃ u : ℚ, Q = C u := ⟨Q.coeff 0, eq_C_of_natDegree_eq_zero hdegQ⟩
    refine ⟨u, fun j hj => ?_⟩
    have h1 : P.coeff j = u := by
      rw [hQ, hu, cyclotomic_prime ℚ p, coeff_mul_C, finset_sum_coeff]
      simp only [coeff_X_pow]
      rw [Finset.sum_ite_eq (Finset.range p) j (fun _ => (1 : ℚ))]
      simp [hj]
    rw [← hcoeff j hj, h1]

/-- **Subset-sum rigidity at a prime** — the dichotomy engine for the de Bruijn
disjointness step: two subsets of exponents `U, V ⊆ [0,p)` with equal subset sums
`Σ_{j∈U} ξ^j = Σ_{j∈V} ξ^j` are EQUAL, or are `∅` and the full `[0,p)` (whose common
sum is `0`). No other collisions exist — subset sums of `μ_p` are rigid. -/
theorem subset_sum_rigidity {p : ℕ} (hp : p.Prime) {ξ : L}
    (hξ : IsPrimitiveRoot ξ p) {U V : Finset ℕ}
    (hU : U ⊆ Finset.range p) (hV : V ⊆ Finset.range p)
    (h : ∑ j ∈ U, ξ ^ j = ∑ j ∈ V, ξ ^ j) :
    U = V ∨ (U = Finset.range p ∧ V = ∅) ∨ (U = ∅ ∧ V = Finset.range p) := by
  classical
  have key : ∀ W : Finset ℕ, W ⊆ Finset.range p →
      ∑ j ∈ Finset.range p, (if j ∈ W then (1 : L) else 0) * ξ ^ j = ∑ j ∈ W, ξ ^ j := by
    intro W hW
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    exact ⟨fun hj => hj.2, fun hj => ⟨hW hj, hj⟩⟩
  have hsum0 : ∑ j ∈ Finset.range p,
      algebraMap ℚ L ((if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0))
        * ξ ^ j = 0 := by
    simp only [map_sub, apply_ite (algebraMap ℚ L), map_one, map_zero, sub_mul,
      Finset.sum_sub_distrib]
    rw [key U hU, key V hV, h, sub_self]
  obtain ⟨c, hc⟩ := vanishing_combination_const hp hξ
    (fun j => (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0)) hsum0
  -- a sharing lemma for the two `c = 0` branches
  have hUV : (∀ j, j < p →
      ((if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0)) = 0) → U = V := by
    intro h0
    ext j
    by_cases hjp : j < p
    · have hj := h0 j hjp
      constructor
      · intro hjU
        by_contra hjV
        rw [if_pos hjU, if_neg hjV] at hj
        norm_num at hj
      · intro hjV
        by_contra hjU
        rw [if_neg hjU, if_pos hjV] at hj
        norm_num at hj
    · exact ⟨fun hj' => absurd (Finset.mem_range.mp (hU hj')) hjp,
        fun hj' => absurd (Finset.mem_range.mp (hV hj')) hjp⟩
  have h0c : (if (0 : ℕ) ∈ U then (1 : ℚ) else 0) - (if (0 : ℕ) ∈ V then 1 else 0) = c :=
    hc 0 hp.pos
  by_cases h0U : (0 : ℕ) ∈ U <;> by_cases h0V : (0 : ℕ) ∈ V
  · -- difference at 0 is 0: all indicators agree
    left
    rw [if_pos h0U, if_pos h0V] at h0c
    refine hUV (fun j hjp => ?_)
    have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
    rw [hcj, ← h0c]
    norm_num
  · -- difference at 0 is 1: U = [0,p), V = ∅
    right; left
    rw [if_pos h0U, if_neg h0V] at h0c
    constructor
    · refine Finset.Subset.antisymm hU (fun j hj => ?_)
      have hjp := Finset.mem_range.mp hj
      have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
      rw [← h0c] at hcj
      by_contra hjU
      rw [if_neg hjU] at hcj
      by_cases hjV : j ∈ V
      · rw [if_pos hjV] at hcj; norm_num at hcj
      · rw [if_neg hjV] at hcj; norm_num at hcj
    · refine Finset.eq_empty_of_forall_notMem (fun j hj => ?_)
      have hjp := Finset.mem_range.mp (hV hj)
      have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
      rw [← h0c, if_pos hj] at hcj
      by_cases hjU : j ∈ U
      · rw [if_pos hjU] at hcj; norm_num at hcj
      · rw [if_neg hjU] at hcj; norm_num at hcj
  · -- difference at 0 is −1: U = ∅, V = [0,p)
    right; right
    rw [if_neg h0U, if_pos h0V] at h0c
    constructor
    · refine Finset.eq_empty_of_forall_notMem (fun j hj => ?_)
      have hjp := Finset.mem_range.mp (hU hj)
      have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
      rw [← h0c, if_pos hj] at hcj
      by_cases hjV : j ∈ V
      · rw [if_pos hjV] at hcj; norm_num at hcj
      · rw [if_neg hjV] at hcj; norm_num at hcj
    · refine Finset.Subset.antisymm hV (fun j hj => ?_)
      have hjp := Finset.mem_range.mp hj
      have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
      rw [← h0c] at hcj
      by_contra hjV
      rw [if_neg hjV] at hcj
      by_cases hjU : j ∈ U
      · rw [if_pos hjU] at hcj; norm_num at hcj
      · rw [if_neg hjU] at hcj; norm_num at hcj
  · -- difference at 0 is 0 again
    left
    rw [if_neg h0U, if_neg h0V] at h0c
    refine hUV (fun j hjp => ?_)
    have hcj : (if j ∈ U then (1 : ℚ) else 0) - (if j ∈ V then 1 else 0) = c := hc j hjp
    rw [hcj, ← h0c]
    norm_num

/-- **The complete classification on the CRT grid (de Bruijn step 3, squarefree
base case)**: for distinct primes `p ≠ q`, primitive roots `ξ` (order `p`) and `η`
(order `q`) in a characteristic-zero field, and `I ⊆ [0,p) ×ˢ [0,q)`, the grid double
sum vanishes **iff** `I` is a pure product: a union of full columns `A ×ˢ [0,q)` or a
union of full rows `[0,p) ×ˢ T`. Forward: O83 fiber-slice invariance + subset-sum
rigidity; backward: the full geometric sum vanishes. -/
theorem grid_vanishing_iff_pure {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    {I : Finset (ℕ × ℕ)} (hI : I ⊆ Finset.range p ×ˢ Finset.range q) :
    ∑ x ∈ I, ξ ^ x.1 * η ^ x.2 = 0 ↔
      (∃ A ⊆ Finset.range p, I = A ×ˢ Finset.range q) ∨
      (∃ T ⊆ Finset.range q, I = Finset.range p ×ˢ T) := by
  classical
  constructor
  · intro hsum
    -- O83: all column fibers have equal ξ-sums
    have hfib : ∀ i i', i < q → i' < q →
        (∑ j ∈ Finset.range p, if (j, i) ∈ I then ξ ^ j else 0)
          = ∑ j ∈ Finset.range p, if (j, i') ∈ I then ξ ^ j else 0 := by
      intro i i' hi hi'
      have hξ1 : IsPrimitiveRoot ξ (p ^ 1) := by rwa [pow_one]
      have hη1 : IsPrimitiveRoot η (q ^ 1) := by rwa [pow_one]
      have hI1 : I ⊆ Finset.range (p ^ 1) ×ˢ Finset.range (q ^ 1) := by simpa using hI
      have h := CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers (a := 1) (b := 1)
        hp hq hpq one_pos hξ1 hη1 I hI1 hsum (i := i) (i' := i') (s := 0) hi hi'
        (by norm_num)
      simpa using h
    set fiber : ℕ → Finset ℕ := fun c => (Finset.range p).filter (fun j => (j, c) ∈ I)
      with hfiber
    have hfibsub : ∀ c, fiber c ⊆ Finset.range p := fun c => Finset.filter_subset _ _
    have hfibsum : ∀ c c', c < q → c' < q →
        ∑ j ∈ fiber c, ξ ^ j = ∑ j ∈ fiber c', ξ ^ j := by
      intro c c' hc hc'
      rw [hfiber]
      simp only [Finset.sum_filter]
      exact hfib c c' hc hc'
    have hrig : ∀ c c', c < q → c' < q →
        fiber c = fiber c' ∨ (fiber c = Finset.range p ∧ fiber c' = ∅) ∨
        (fiber c = ∅ ∧ fiber c' = Finset.range p) := fun c c' hc hc' =>
      subset_sum_rigidity hp hξ (hfibsub c) (hfibsub c') (hfibsum c c' hc hc')
    by_cases hdeg : ∀ c, c < q → fiber c = ∅ ∨ fiber c = Finset.range p
    · -- all fibers degenerate: union of full rows
      right
      refine ⟨(Finset.range q).filter (fun c => fiber c = Finset.range p),
        Finset.filter_subset _ _, ?_⟩
      ext ⟨j, c⟩
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hjc
        have hx := hI hjc
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
        have hjf : j ∈ fiber c := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hx.1, hjc⟩
        rcases hdeg c hx.2 with h0 | hful
        · rw [h0] at hjf; exact absurd hjf (Finset.notMem_empty j)
        · exact ⟨hx.1, hx.2, hful⟩
      · rintro ⟨hj, hc, hful⟩
        have hjf : j ∈ fiber c := hful ▸ Finset.mem_range.mpr hj
        exact (Finset.mem_filter.mp hjf).2
    · -- some genuine fiber: all fibers equal it — union of full columns
      left
      obtain ⟨c0, hc0, h0ne, hfulne⟩ : ∃ c0, c0 < q ∧ fiber c0 ≠ ∅ ∧
          fiber c0 ≠ Finset.range p := by
        by_contra hcon
        refine hdeg (fun c hc => ?_)
        by_contra hcor
        exact hcon ⟨c, hc, fun h => hcor (Or.inl h), fun h => hcor (Or.inr h)⟩
      refine ⟨fiber c0, hfibsub c0, ?_⟩
      have hall : ∀ c, c < q → fiber c = fiber c0 := by
        intro c hc
        rcases hrig c c0 hc hc0 with heq | ⟨_, h0⟩ | ⟨_, hful⟩
        · exact heq
        · exact absurd h0 h0ne
        · exact absurd hful hfulne
      ext ⟨j, c⟩
      simp only [Finset.mem_product, Finset.mem_range]
      constructor
      · intro hjc
        have hx := hI hjc
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
        have hjf : j ∈ fiber c := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hx.1, hjc⟩
        rw [hall c hx.2] at hjf
        exact ⟨hjf, hx.2⟩
      · rintro ⟨hjf, hc⟩
        rw [← hall c hc] at hjf
        exact (Finset.mem_filter.mp hjf).2
  · -- pure products vanish: factor out the full geometric sum
    rintro (⟨A, _, rfl⟩ | ⟨T, _, rfl⟩)
    · have h0 : ∑ c ∈ Finset.range q, η ^ c = 0 := hη.geom_sum_eq_zero hq.one_lt
      rw [Finset.sum_product]
      simp [← Finset.mul_sum, h0]
    · have h0 : ∑ j ∈ Finset.range p, ξ ^ j = 0 := hξ.geom_sum_eq_zero hp.one_lt
      rw [Finset.sum_product]
      simp [← Finset.mul_sum, ← Finset.sum_mul, h0]

/-! ## The weighted squarefree converse -/

section WeightedConverse

variable {K : Type*} [Field K]

/-- **Weighted packet-combination sufficiency at `pq`**: any ℕ-combination of full
row and column packets on the CRT grid has vanishing weighted sum.  The weight at
`(j,c)` is `A j + B c`, where `A j` is the multiplicity of the full `q`-packet in
row `j` and `B c` is the multiplicity of the full `p`-packet in column `c`.

This is the easy/converse half of the weighted squarefree de Bruijn theorem: the
double sum factors into two terms, each killed by one full geometric sum. -/
theorem weighted_grid_packet_combination_sum_eq_zero {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) {ξ η : K} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (A : ℕ → ℕ) (B : ℕ → ℕ) :
    ∑ x ∈ Finset.range p ×ˢ Finset.range q,
        (((A x.1 : K) + (B x.2 : K)) * (ξ ^ x.1 * η ^ x.2)) = 0 := by
  classical
  have hηsum : ∑ c ∈ Finset.range q, η ^ c = 0 := hη.geom_sum_eq_zero hq.one_lt
  have hξsum : ∑ j ∈ Finset.range p, ξ ^ j = 0 := hξ.geom_sum_eq_zero hp.one_lt
  rw [Finset.sum_product]
  calc
    ∑ j ∈ Finset.range p, ∑ c ∈ Finset.range q,
        (((A j : K) + (B c : K)) * (ξ ^ j * η ^ c))
        = (∑ j ∈ Finset.range p, ∑ c ∈ Finset.range q,
            (A j : K) * (ξ ^ j * η ^ c))
          + (∑ j ∈ Finset.range p, ∑ c ∈ Finset.range q,
            (B c : K) * (ξ ^ j * η ^ c)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
    _ = (∑ j ∈ Finset.range p,
            ((A j : K) * ξ ^ j) * (∑ c ∈ Finset.range q, η ^ c))
          + (∑ j ∈ Finset.range p,
            ξ ^ j * (∑ c ∈ Finset.range q, (B c : K) * η ^ c)) := by
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            calc
              ∑ c ∈ Finset.range q, (A j : K) * (ξ ^ j * η ^ c)
                  = (A j : K) * (∑ c ∈ Finset.range q, ξ ^ j * η ^ c) := by
                    rw [← Finset.mul_sum]
              _ = (A j : K) * (ξ ^ j * (∑ c ∈ Finset.range q, η ^ c)) := by
                    rw [← Finset.mul_sum]
              _ = ((A j : K) * ξ ^ j) * (∑ c ∈ Finset.range q, η ^ c) := by
                    ring
          · refine Finset.sum_congr rfl fun j _ => ?_
            calc
              ∑ c ∈ Finset.range q, (B c : K) * (ξ ^ j * η ^ c)
                  = ∑ c ∈ Finset.range q, ξ ^ j * ((B c : K) * η ^ c) := by
                    refine Finset.sum_congr rfl fun c _ => ?_
                    ring
              _ = ξ ^ j * (∑ c ∈ Finset.range q, (B c : K) * η ^ c) := by
                    rw [← Finset.mul_sum]
    _ = (∑ j ∈ Finset.range p,
            ((A j : K) * ξ ^ j) * (∑ c ∈ Finset.range q, η ^ c))
          + (∑ j ∈ Finset.range p, ξ ^ j)
            * (∑ c ∈ Finset.range q, (B c : K) * η ^ c) := by
          congr 1
          rw [Finset.sum_mul]
    _ = 0 := by
          rw [hηsum, hξsum]
          simp

end WeightedConverse

/-- **The headline (subset-sum form)**: for distinct primes `p ≠ q` and a primitive
`pq`-th root of unity `ζ` in a characteristic-zero field, a subset sum of `μ_{pq}`
vanishes **iff** its CRT grid set (O82 `gridSet`) is a pure product — a union of full
`q`-packet columns or a union of full `p`-packet rows. This is de Bruijn step (3) at
the squarefree base case, composed from steps (1) `CRTPacketMinpoly` and (2)
`CRTExponentGridSum`. -/
theorem vanishing_subset_sum_iff_pure_packets {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q))
    (S : Finset (ZMod (p * q))) :
    ∑ e ∈ S, ζ ^ e.val = 0 ↔
      (∃ A ⊆ Finset.range p, CRTExponentGridSum.gridSet p q S = A ×ˢ Finset.range q) ∨
      (∃ T ⊆ Finset.range q, CRTExponentGridSum.gridSet p q S
        = Finset.range p ×ˢ T) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hn : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hξ : IsPrimitiveRoot (ζ ^ q) p := hζ.pow hn (mul_comm p q)
  have hη : IsPrimitiveRoot (ζ ^ p) q := hζ.pow hn rfl
  rw [CRTExponentGridSum.subset_sum_eq_grid_double_sum hp.pos hq.pos hcop
    hζ.pow_eq_one S]
  exact grid_vanishing_iff_pure hp hq hpq hξ hη
    (CRTExponentGridSum.gridSet_subset p q S)

/-- Reconstruction: the CRT grid map carries the grid set of `S` back onto `S`
(surjectivity of `gridMap` + the `gridSet` filter). -/
lemma image_gridMap_gridSet {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hcop : Nat.Coprime N M) (S : Finset (ZMod (N * M))) :
    (CRTExponentGridSum.gridSet N M S).image (CRTExponentGridSum.gridMap N M) = S := by
  classical
  ext e
  simp only [Finset.mem_image, CRTExponentGridSum.gridSet, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨_, hxS⟩, rfl⟩
    exact hxS
  · intro he
    obtain ⟨x, hx, hxe⟩ := CRTExponentGridSum.gridMap_surj hN hM hcop e
    exact ⟨x, ⟨hx, hxe ▸ he⟩, hxe⟩

/-- Injectivity of the grid map transports pure products through `gridSet`:
if `S` is the image of a grid subset `J ⊆ [0,N) ×ˢ [0,M)`, then `gridSet S = J`. -/
lemma gridSet_image_gridMap {N M : ℕ} (hcop : Nat.Coprime N M)
    {J : Finset (ℕ × ℕ)} (hJ : J ⊆ Finset.range N ×ˢ Finset.range M) :
    CRTExponentGridSum.gridSet N M (J.image (CRTExponentGridSum.gridMap N M)) = J := by
  classical
  ext ⟨j, c⟩
  simp only [CRTExponentGridSum.gridSet, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hjc, ⟨j', c'⟩, hj'c', heq⟩
    obtain ⟨hj'N, hc'M⟩ : j' < N ∧ c' < M := by
      have h1 := hJ hj'c'
      simp only [Finset.mem_product, Finset.mem_range] at h1
      exact h1
    obtain ⟨hjN, hcM⟩ : j < N ∧ c < M := by
      simp only [Finset.mem_product, Finset.mem_range] at hjc
      exact hjc
    obtain ⟨h2, h3⟩ := CRTExponentGridSum.gridMap_inj hcop hj'N hc'M hjN hcM heq
    exact h2 ▸ h3 ▸ hj'c'
  · intro hjc
    exact ⟨hJ hjc, ⟨(j, c), hjc, rfl⟩⟩

/-- **De Bruijn at squarefree `pq`, exponent-space form**: a subset sum of `pq`-th
roots of unity vanishes **iff** the exponent set is the CRT image of a pure product —
i.e. a DISJOINT union of rotated `μ_q`-packets (cosets of `p·ZMod(pq)`), or a disjoint
union of rotated `μ_p`-packets. Mixing is impossible at squarefree `n`: every
`p`-packet meets every `q`-packet by CRT, so disjointness forces purity. -/
theorem vanishing_subset_sum_iff_packet_union {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q))
    (S : Finset (ZMod (p * q))) :
    ∑ e ∈ S, ζ ^ e.val = 0 ↔
      (∃ A ⊆ Finset.range p,
        S = (A ×ˢ Finset.range q).image (CRTExponentGridSum.gridMap p q)) ∨
      (∃ T ⊆ Finset.range q,
        S = (Finset.range p ×ˢ T).image (CRTExponentGridSum.gridMap p q)) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [vanishing_subset_sum_iff_pure_packets hp hq hpq hζ S]
  constructor
  · rintro (⟨A, hA, hgrid⟩ | ⟨T, hT, hgrid⟩)
    · exact Or.inl ⟨A, hA, by
        rw [← image_gridMap_gridSet hp.pos hq.pos hcop S, hgrid]⟩
    · exact Or.inr ⟨T, hT, by
        rw [← image_gridMap_gridSet hp.pos hq.pos hcop S, hgrid]⟩
  · rintro (⟨A, hA, rfl⟩ | ⟨T, hT, rfl⟩)
    · refine Or.inl ⟨A, hA, gridSet_image_gridMap hcop ?_⟩
      exact Finset.product_subset_product hA (Finset.Subset.refl _)
    · refine Or.inr ⟨T, hT, gridSet_image_gridMap hcop ?_⟩
      exact Finset.product_subset_product (Finset.Subset.refl _) hT

/-- **Cardinality corollary (Lam–Leung at `pq`, with structure)**: a vanishing subset
sum of `pq`-th roots of unity has size a multiple of `q` or a multiple of `p` — and
not just numerically: the witnessing multiple counts whole packets. -/
theorem card_of_vanishing_subset_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q))
    {S : Finset (ZMod (p * q))} (h : ∑ e ∈ S, ζ ^ e.val = 0) :
    q ∣ S.card ∨ p ∣ S.card := by
  classical
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hinj : ∀ (J : Finset (ℕ × ℕ)), J ⊆ Finset.range p ×ˢ Finset.range q →
      (J.image (CRTExponentGridSum.gridMap p q)).card = J.card := by
    intro J hJ
    refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
    obtain ⟨hx1, hx2⟩ : x.1 < p ∧ x.2 < q := by
      have hx' := hJ hx
      simp only [Finset.mem_product, Finset.mem_range] at hx'
      exact hx'
    obtain ⟨hy1, hy2⟩ : y.1 < p ∧ y.2 < q := by
      have hy' := hJ hy
      simp only [Finset.mem_product, Finset.mem_range] at hy'
      exact hy'
    obtain ⟨h1, h2⟩ := CRTExponentGridSum.gridMap_inj hcop hx1 hx2 hy1 hy2 hxy
    exact Prod.ext h1 h2
  rcases (vanishing_subset_sum_iff_packet_union hp hq hpq hζ S).mp h with
    ⟨A, hA, rfl⟩ | ⟨T, hT, rfl⟩
  · left
    rw [hinj _ (Finset.product_subset_product hA (Finset.Subset.refl _)),
      Finset.card_product, Finset.card_range]
    exact dvd_mul_left q A.card
  · right
    rw [hinj _ (Finset.product_subset_product (Finset.Subset.refl _) hT),
      Finset.card_product, Finset.card_range]
    exact dvd_mul_right p T.card

/-! ## Non-vacuity witnesses -/

/-- The rigidity dichotomy at a genuinely satisfiable point: `ξ = −1` is a primitive
square root of unity in `ℚ`, and the only equal-sum collision among subsets of
`{0, 1}` exponents is `∅` vs `{0, 1}` (both summing to `0`) — kernel-checked through
the theorem. -/
example : ({0, 1} : Finset ℕ) = (∅ : Finset ℕ) ∨
    (({0, 1} : Finset ℕ) = Finset.range 2 ∧ (∅ : Finset ℕ) = ∅) ∨
    (({0, 1} : Finset ℕ) = ∅ ∧ (∅ : Finset ℕ) = Finset.range 2) := by
  have hξ : IsPrimitiveRoot (-1 : ℚ) 2 := by
    constructor
    · norm_num
    · intro l hl
      rcases Nat.even_or_odd l with he | ho
      · exact he.two_dvd
      · rw [ho.neg_one_pow] at hl; norm_num at hl
  have h := subset_sum_rigidity Nat.prime_two hξ
    (U := {0, 1}) (V := ∅)
    (by intro x hx; fin_cases hx <;> norm_num)
    (Finset.empty_subset _)
    (by norm_num)
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end DeBruijnSquarefreePQ

#print axioms DeBruijnSquarefreePQ.vanishing_combination_const
#print axioms DeBruijnSquarefreePQ.subset_sum_rigidity
#print axioms DeBruijnSquarefreePQ.grid_vanishing_iff_pure
#print axioms DeBruijnSquarefreePQ.weighted_grid_packet_combination_sum_eq_zero
#print axioms DeBruijnSquarefreePQ.vanishing_subset_sum_iff_pure_packets
#print axioms DeBruijnSquarefreePQ.vanishing_subset_sum_iff_packet_union
#print axioms DeBruijnSquarefreePQ.card_of_vanishing_subset_sum
