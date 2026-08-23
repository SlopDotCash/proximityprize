/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowTwoLayerThreshold
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ConstrainedCensusLaw

/-!
# Depth-1 cleanliness of the adjacent-pair family: the O141/O144 weld

Campaign #357. This file welds the two halves that grew in separate lanes:

* the **constrained census law** (`constrainedSubsetSum_of_badScalar`,
  `KKH26ConstrainedCensusLaw.lean`): a bad scalar for the adjacent monomial pair
  `(X^a, X^{a−1})` against degree-`< k` codes over an evaluation set `H` yields an
  `a`-subset `T ⊆ H` with the constrained band of its vanishing polynomial zero — at
  **depth 1** (`k = a − 2`) the single constraint is `e₂(T) = 0`;
* the **two-layer threshold law** (`e2_ne_zero_of_production_dim`,
  `WindowTwoLayerThreshold.lean`): for exponent sets of size `≡ 2 (mod 4)` over a smooth
  domain `μ_{2^m} ⊆ F_p`, the `e₂` statistic cannot vanish at any prime above the explicit
  resultant threshold `(2^(m−1)·a²)^(2^(m−1))` (O144 parity forces char-0 nonvanishing,
  the threshold forces char-p qualification down to char 0).

The weld is Vieta: the census law speaks of the coefficient of the vanishing polynomial at
degree `a − 2`, the threshold law of the pair sum `∑_{i<j} g^(i+j)`; the bridge is
`coeff (a−2) (∏_{x∈T}(X − C x)) = e₂(T)` (`Multiset.prod_X_sub_C_coeff` ∘
`Finset.esymm_map_val` ∘ the `powersetCard 2 ↔ upperPairs` bijection), plus the exponent-set
pullback through `IsPrimitiveRoot.pow_inj`.

## Headline

`oddRow_no_badScalar`: for `a ≡ 2` or `3 (mod 4)` — the rows with an odd pair count
`C(a,2)`, i.e. **half of all window rows** — at **every** depth (`1 ≤ k ≤ a − 2`), over
**any** subset `H` of a smooth domain `μ_{2^m} ⊆ F_p` with `p` above the explicit
threshold: **no scalar is bad for the adjacent pair** — no polynomial of degree `≤ k − 1`
agrees with the line `X^a + λ·X^{a−1}` on `a` points of `H`, for any `λ`. The mechanism:
any bad witness forces its entire constrained band to vanish, in particular `e₂ = 0`,
impossible on an odd row above the threshold. `depthOne_no_badScalar` is the `k = a − 2`
production instance (`a = k + 2`, `k ≡ 0 (mod 4)` — all `k = 2^j`, `j ≥ 2`). This is the
formal, uniform-in-`n`, zero-enumeration form of the O141 verdict "the mid-window rows are
clean at every prime above the finite spectrum": the spectrum is bounded by the explicit
resultant threshold, at every smooth scale `2^m` simultaneously.

## Honest scope

This is a **per-stack negative**: it empties the bad-scalar set of one (conjecturally
extremal, per O137/O138) stack family; it does not by itself bound `ε_mca` (a sup over all
stacks). The O141 finite spectrum below the threshold is exact at specific instances by
probe; this theorem gives the all-`p`-above-threshold half at all scales. All results are
`sorry`-free and axiom-clean.

## References

* Probes O138–O144, `DISPROOF_LOG`; issue #357.
* [KKH26] ePrint 2026/782 (resultant machinery).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-! ## The pair-census bridge: `powersetCard 2` sums are `upperPairs` sums -/

/-- Summing a product over the 2-element subsets equals summing over strictly-ordered
pairs: the bijection `(i, j) ↦ {i, j}` (with inverse `t ↦ (min t, max t)`). -/
theorem sum_powersetCard_two_eq {R : Type*} [CommRing R] (A : Finset ℕ) (f : ℕ → R) :
    ∑ t ∈ A.powersetCard 2, ∏ i ∈ t, f i = ∑ q ∈ upperPairs A, f q.1 * f q.2 := by
  symm
  refine Finset.sum_nbij (fun q => ({q.1, q.2} : Finset ℕ)) ?_ ?_ ?_ ?_
  · -- maps into the 2-subsets
    intro q hq
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair (Nat.ne_of_lt hlt)⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h1
    · exact (Finset.mem_singleton.mp hx) ▸ h2
  · -- injective on ordered pairs
    intro q hq q' hq' heq
    have hlt : q.1 < q.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have hlt' : q'.1 < q'.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    have heq' : ({q.1, q.2} : Finset ℕ) = ({q'.1, q'.2} : Finset ℕ) := heq
    have h1 : q.1 = q'.1 ∨ q.1 = q'.2 := by
      have hx : q.1 ∈ ({q'.1, q'.2} : Finset ℕ) := heq' ▸ Finset.mem_insert_self _ _
      simpa using hx
    have h2 : q.2 = q'.1 ∨ q.2 = q'.2 := by
      have hx : q.2 ∈ ({q'.1, q'.2} : Finset ℕ) :=
        heq' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simpa using hx
    exact Prod.ext (by omega) (by omega)
  · -- surjective onto the 2-subsets
    intro t ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp ht)
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hx : x ∈ A := hsub (Finset.mem_insert_self _ _)
    have hy : y ∈ A := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨(x, y), Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, h⟩), rfl⟩
    · have h' : y < x := by omega
      exact ⟨(y, x), Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hy, hx⟩, h'⟩), Finset.pair_comm y x⟩
  · -- summand match
    intro q hq
    have hlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    exact (Finset.prod_pair (Nat.ne_of_lt hlt)).symm

/-! ## Vieta at depth 1 -/

/-- **The depth-1 Vieta bridge.** The coefficient of the vanishing polynomial
`∏_{i∈A}(X − f i)` at degree `|A| − 2` is exactly the pair census `∑_{i<j∈A} f i · f j`. -/
theorem coeff_prod_X_sub_C_sub_two {R : Type*} [CommRing R] (A : Finset ℕ) (f : ℕ → R)
    (ha : 2 ≤ A.card) :
    (∏ i ∈ A, (X - C (f i))).coeff (A.card - 2) = ∑ q ∈ upperPairs A, f q.1 * f q.2 := by
  have hcard : Multiset.card (A.val.map f) = A.card := by simp
  have hk : A.card - 2 ≤ Multiset.card (A.val.map f) := by rw [hcard]; omega
  have h1 : ∏ i ∈ A, (X - C (f i)) = ((A.val.map f).map (fun r => X - C r)).prod := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    rfl
  have h2 : Multiset.card (A.val.map f) - (A.card - 2) = 2 := by rw [hcard]; omega
  rw [h1, Multiset.prod_X_sub_C_coeff _ hk, h2, neg_one_sq, one_mul,
    Finset.esymm_map_val]
  exact sum_powersetCard_two_eq A f

/-! ## The exponent pullback -/

/-- Pull a witness subset of a smooth domain back to its exponent set: a vanished
`a − 2` coefficient of the vanishing polynomial becomes a vanished pair census of the
exponents. -/
theorem exponent_census_of_witness {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m))
    {T : Finset (ZMod p)} (hTH : T ⊆ (Finset.range (2 ^ m)).image (g ^ ·))
    {a : ℕ} (ha2 : 2 ≤ a) (hTcard : T.card = a)
    (hcoeff : (∏ x ∈ T, (X - C x)).coeff (a - 2) = 0) :
    ∃ A ⊆ Finset.range (2 ^ m), A.card = a ∧ T = A.image (g ^ ·) ∧
      ∑ qq ∈ upperPairs A, g ^ (qq.1 + qq.2) = 0 := by
  set A : Finset ℕ := (Finset.range (2 ^ m)).filter (fun i => g ^ i ∈ T) with hA
  have hinj : ∀ i ∈ A, ∀ j ∈ A, g ^ i = g ^ j → i = j := by
    intro i hi j hj hij
    exact hg.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
  have hT : T = A.image (g ^ ·) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hTH hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
  have hAcard : A.card = a := by
    rw [← hTcard, hT]
    exact (Finset.card_image_of_injOn fun i hi j hj hij =>
      hinj i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij).symm
  have hprod : ∏ x ∈ T, (X - C x) = ∏ i ∈ A, (X - C (g ^ i)) := by
    rw [hT]
    exact Finset.prod_image hinj
  refine ⟨A, Finset.filter_subset _ _, hAcard, hT, ?_⟩
  have hv := coeff_prod_X_sub_C_sub_two A (g ^ ·) (by rw [hAcard]; omega)
  rw [hAcard] at hv
  calc ∑ qq ∈ upperPairs A, g ^ (qq.1 + qq.2)
      = ∑ qq ∈ upperPairs A, g ^ qq.1 * g ^ qq.2 :=
        Finset.sum_congr rfl fun qq _ => pow_add g qq.1 qq.2
    _ = (∏ i ∈ A, (X - C (g ^ i))).coeff (a - 2) := hv.symm
    _ = (∏ x ∈ T, (X - C x)).coeff (a - 2) := by rw [hprod]
    _ = 0 := hcoeff

/-! ## The headline: the odd rows are clean at every depth -/

/-- **The odd rows of the adjacent-pair window profile are clean at EVERY depth
(O141/O144, formal).** For `a ≡ 2` or `3 (mod 4)` (the rows with an odd pair count) and
any depth — any code degree bound `k` with `1 ≤ k ≤ a − 2` — over any subset `H` of the
smooth domain `μ_{2^m} = {g^i} ⊆ F_p` with `p` above the explicit resultant threshold:
**no scalar `λ` is bad for the adjacent pair `(X^a, X^{a−1})`** — no polynomial of degree
`≤ k − 1` agrees with the line `X^a + λ·X^{a−1}` on `a` points of `H`. Uniform in the
scale `m`, zero enumeration. The mechanism: any bad witness forces the full constrained
band to vanish, in particular `e₂ = 0` — impossible above the threshold on an odd row. -/
theorem oddRow_no_badScalar {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {H : Finset (ZMod p)} (hH : H ⊆ (Finset.range (2 ^ m)).image (g ^ ·))
    {a k : ℕ} (ha4 : a % 4 = 2 ∨ a % 4 = 3) (ha3 : 3 ≤ a)
    (hk1 : 1 ≤ k) (hk2 : k ≤ a - 2)
    (hp : (2 ^ (m - 1) * (a * a)) ^ 2 ^ (m - 1) < p) (lam : ZMod p) :
    ¬ ∃ q : Polynomial (ZMod p), q.natDegree ≤ k - 1 ∧
        a ≤ (lineAgreeSet H a lam q).card := by
  rintro ⟨q, hq, hagree⟩
  obtain ⟨T, hTH, hTcard, hband, _⟩ :=
    constrainedSubsetSum_of_badScalar (H := H) (a := a) (k := k)
      hk1 (by omega) hq hagree
  obtain ⟨A, hAsub, hAcard, hT, he2⟩ := exponent_census_of_witness hg
    (hTH.trans hH) (by omega) hTcard (hband 2 le_rfl (by omega))
  exact e2_ne_zero_of_odd_row hm hg A (by rw [hAcard]; exact ha4)
    (by rw [hAcard]; exact hp) he2

/-- **Depth-1 cleanliness at production dimensions** — the `k = a − 2` instance of the
odd-row theorem (every production depth-1 row `a = k + 2`, `k ≡ 0 (mod 4)`). -/
theorem depthOne_no_badScalar {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {H : Finset (ZMod p)} (hH : H ⊆ (Finset.range (2 ^ m)).image (g ^ ·))
    {a : ℕ} (ha4 : a % 4 = 2) (ha3 : 3 ≤ a)
    (hp : (2 ^ (m - 1) * (a * a)) ^ 2 ^ (m - 1) < p) (lam : ZMod p) :
    ¬ ∃ q : Polynomial (ZMod p), q.natDegree ≤ a - 2 - 1 ∧
        a ≤ (lineAgreeSet H a lam q).card :=
  oddRow_no_badScalar hm hg hH (Or.inl ha4) ha3 (by omega) le_rfl hp lam

/-- The full smooth domain instance: over `μ_{2^m}` itself, every odd row of the
adjacent-pair family is empty at every depth, at every prime above the threshold. -/
theorem oddRow_no_badScalar_smoothDomain {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {a k : ℕ} (ha4 : a % 4 = 2 ∨ a % 4 = 3) (ha3 : 3 ≤ a)
    (hk1 : 1 ≤ k) (hk2 : k ≤ a - 2)
    (hp : (2 ^ (m - 1) * (a * a)) ^ 2 ^ (m - 1) < p) (lam : ZMod p) :
    ¬ ∃ q : Polynomial (ZMod p), q.natDegree ≤ k - 1 ∧
        a ≤ (lineAgreeSet ((Finset.range (2 ^ m)).image (g ^ ·)) a lam q).card :=
  oddRow_no_badScalar hm hg (Finset.Subset.refl _) ha4 ha3 hk1 hk2 hp lam

/-! ## The two-sided depth-1 dictionary: the bad set is a characteristic-zero object -/

/-- **The complete two-layer law at depth 1 (two-sided).** For `p` above the explicit
resultant threshold, a scalar `λ` is bad for the adjacent pair `(X^a, X^{a−1})` at depth 1
(`k = a − 2`) over the smooth domain `μ_{2^m} ⊆ F_p` **iff** `λ = −∑_{i∈A} g^i` for an
`a`-element exponent set `A ⊆ {0, …, 2^m − 1}` whose folded `e₂` polynomial vanishes **in
characteristic zero** (`e2Folded m A = 0` in `ℤ[X]`). The depth-1 bad-scalar set is
therefore a *p-independent* object above the threshold: one census in `ℤ[ζ_{2^m}]`
describes every large prime at once — the formal O141/O143 'two-layer' statement with the
surplus layer provably empty. -/
theorem depthOne_badScalar_iff_char0 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {a : ℕ} (ha3 : 3 ≤ a)
    (hp : (2 ^ (m - 1) * (a * a)) ^ 2 ^ (m - 1) < p) (lam : ZMod p) :
    (∃ q : Polynomial (ZMod p), q.natDegree ≤ a - 2 - 1 ∧
        a ≤ (lineAgreeSet ((Finset.range (2 ^ m)).image (g ^ ·)) a lam q).card)
      ↔ ∃ A ⊆ Finset.range (2 ^ m), A.card = a ∧ e2Folded m A = 0 ∧
          lam = -∑ i ∈ A, g ^ i := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    obtain ⟨T, hTH, hTcard, hband, hlam⟩ :=
      constrainedSubsetSum_of_badScalar (a := a) (k := a - 2)
        (by omega) (by omega) hq hagree
    obtain ⟨A, hAsub, hAcard, hT, he2⟩ := exponent_census_of_witness hg hTH
      (by omega) hTcard (hband 2 le_rfl (by omega))
    have hinj : ∀ i ∈ A, ∀ j ∈ A, g ^ i = g ^ j → i = j := fun i hi j hj hij =>
      hg.pow_inj (Finset.mem_range.mp (hAsub hi)) (Finset.mem_range.mp (hAsub hj)) hij
    refine ⟨A, hAsub, hAcard,
      qualifying_implies_char0_vanishing hm hg A (by rw [hAcard]; exact hp) he2, ?_⟩
    rw [hlam, hT, Finset.sum_image hinj]
  · rintro ⟨A, hAsub, hAcard, hchar0, rfl⟩
    have hinj : ∀ i ∈ A, ∀ j ∈ A, g ^ i = g ^ j → i = j := fun i hi j hj hij =>
      hg.pow_inj (Finset.mem_range.mp (hAsub hi)) (Finset.mem_range.mp (hAsub hj)) hij
    set T : Finset (ZMod p) := A.image (g ^ ·) with hT
    have hTH : T ⊆ (Finset.range (2 ^ m)).image (g ^ ·) :=
      Finset.image_subset_image hAsub
    have hTcard : T.card = a := by
      rw [hT, Finset.card_image_of_injOn fun i hi j hj hij =>
        hinj i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij]
      exact hAcard
    -- char-0 vanishing descends to the pair census mod `p`
    have he2 : ∑ qq ∈ upperPairs A, g ^ (qq.1 + qq.2) = 0 := by
      rw [← e2Folded_eval hm hg A, hchar0]
      simp
    -- which is exactly the constrained band at depth 1
    have hband : ConstrainedBandZero T a (a - 2) := by
      intro j hj2 hjle
      have hj : j = 2 := by omega
      subst hj
      have hprod : ∏ x ∈ T, (X - C x) = ∏ i ∈ A, (X - C (g ^ i)) := by
        rw [hT]
        exact Finset.prod_image hinj
      have hv := coeff_prod_X_sub_C_sub_two A (g ^ ·) (by rw [hAcard]; omega)
      rw [hAcard] at hv
      rw [hprod, hv]
      calc ∑ qq ∈ upperPairs A, g ^ qq.1 * g ^ qq.2
          = ∑ qq ∈ upperPairs A, g ^ (qq.1 + qq.2) :=
            Finset.sum_congr rfl fun qq _ => (pow_add g qq.1 qq.2).symm
        _ = 0 := he2
    have hbad := badScalar_of_constrainedSubsetSum (k := a - 2)
      (by omega) (by omega) hTH hTcard hband
    rwa [hT, Finset.sum_image hinj] at hbad

/-! ## Source audit -/

#print axioms sum_powersetCard_two_eq
#print axioms coeff_prod_X_sub_C_sub_two
#print axioms exponent_census_of_witness
#print axioms oddRow_no_badScalar
#print axioms depthOne_no_badScalar
#print axioms oddRow_no_badScalar_smoothDomain
#print axioms depthOne_badScalar_iff_char0

end ArkLib.ProximityGap.WindowTwoLayer
