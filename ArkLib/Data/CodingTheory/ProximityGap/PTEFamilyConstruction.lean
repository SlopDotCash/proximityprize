/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.CosetExactCount

/-!
# Round 22 (Issue #232) — the CONSTRUCTIVE PTE FAMILY inside the smooth domain: `expand` lifts
# every base subset to an equal-symmetric-window support

The open core's final form (O44): do distinct `w`-subsets of `μ_n` with equal `e₁,…,e_t` exist and
abound (the PTE/cyclic deficiency mechanism of Conjecture 41 = the multi-symmetric concentration of
rounds 4–8)? This file gives the **general constructive answer below the depth threshold**:

For `d > 0` and a base set `A` (`|A| = s`), the **lifted polynomial**

  `P_A := expand_d (∏_{a∈A} (X − a)) = ∏_{a∈A} (X^d − a)`

is monic of degree `d·s`, and — being a polynomial in `X^d` — **every coefficient at an index not
divisible by `d` vanishes** (`liftedPoly_coeff_eq_zero_of_not_dvd`, via `Polynomial.coeff_expand`).
In particular the entire top window below the leading coefficient is identically zero
(`liftedPoly_top_window_zero`). Distinct bases give distinct lifted *polynomials*
(`liftedPoly_injective`), so the `C(|B|, s)` lifts of `s`-subsets of a base `B` are pairwise
distinct polynomials with equal (zero) coefficients at depths `1, …, d−1`, over every field. The
root set of `P_A` in `F` is exactly the power-map preimage `{x : x^d ∈ A}`
(`liftedPoly_eval_eq_zero_iff`).

**Polynomials versus supports.** Over an arbitrary field these polynomials need not be supports:
`P_A` need not split, and if `char F ∣ d` its roots repeat. E.g. over `F₃` with `d = 2`, `A = {2}`,
`P_A = X² + 1` has no root at all (`liftedPoly_two_singleton_two_no_root_zmod3`), so the distinct
lifts of `{1}` and `{2}` do not give two equal-size root supports. The support reading holds on a
genuine full split domain: if `F` has a primitive `n`-th root of unity (so `char F ∤ n`),
`d ∣ n` and `A ⊆ μ_{n/d}`, then the root support `S_A := {x ∈ μ_n : x^d ∈ A}` has exactly `d·|A|`
elements (`liftedSupport_card`, via `CosetExactCount.fiber_card_eq`),
`P_A = ∏_{x∈S_A} (X − x)` (`liftedPoly_eq_prod_liftedSupport`), and `A ↦ S_A` is injective on
subsets of `μ_{n/d}` (`liftedSupport_injOn`). Under exactly these hypotheses `pte_support_family`
gives `C(n/d, s)` distinct `d·s`-subsets of `μ_n` whose `e₁ = ⋯ = e_{d−1} = 0`.

## The threshold arithmetic (what this settles)

* PTE families at depth `t ≤ d−1`, `d ∣ n`, inside `μ_n` (primitive `n`-th root in `F`): size
  `C(n/d, s)`, support size `w = d·s` — constructive, verified (`pte_support_family`). The
  polynomial-only statement `pte_family` holds over every field.
* The Conjecture-41 deficiency window (equal `e₁,…,e_{w−c}`) requires `w − c ≤ d − 1`, i.e.
  `d ≥ w−c+1`, forcing `s = w/d ≤ w/(w−c+1)`. At **deployment codimension** (`c, w−c = Θ(n)`):
  `d = Θ(n)`, `s = O(1)`, family `C(n/d, s) = O(1)` — consistent with the conjecture's `M = O(1)`
  prediction. Near **capacity** (`c = O(1)`) the same inequality gives
  `s ≤ w/(w−c+1) = 1 + O(1/w)`, so (`s` being a positive integer) `s = 1` once `w ≥ 2c − 1`;
  e.g. `c = 2`, `w = 100` forces `d ≥ 99`, `d ∣ 100`, hence `d = 100`, `s = 1`. With `w = Θ(n)`
  the lifted family then has size `C(n/d, 1) = n/d = O(1)`. So this shallow construction does
  **NOT** explain the exponential `c = 2` phase of the 2026/858 empirical phase diagram; that
  phase needs a different mechanism (not supplied here). The construction accounts only for the
  `O(1)` deployment-codimension floor.
* **Honest residue:** whether non-lifted PTE families can beat `C(n/d, s)` in the deep window
  (non-cyclic deficiency at large `p`) is the open core — unchanged, with its constructive floor
  now verified.
-/

open Polynomial Finset

namespace Round22PTE

variable {F : Type*} [Field F]

/-- The base nodal polynomial `∏_{a∈A} (X − a)`. -/
noncomputable def baseNodal (A : Finset F) : F[X] :=
  ∏ a ∈ A, (X - C a)

/-- **The lifted polynomial** `P_A = expand_d (baseNodal A) = ∏_{a∈A} (X^d − a)`. -/
noncomputable def liftedPoly (d : ℕ) (A : Finset F) : F[X] :=
  Polynomial.expand F d (baseNodal A)

/-- `expand` of the nodal product is the product of `(X^d − a)`. -/
theorem liftedPoly_eq_prod (d : ℕ) (A : Finset F) :
    liftedPoly d A = ∏ a ∈ A, (X ^ d - C a) := by
  unfold liftedPoly baseNodal
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]

theorem baseNodal_natDegree (A : Finset F) : (baseNodal A).natDegree = A.card := by
  unfold baseNodal
  rw [Polynomial.natDegree_prod _ _ (fun a _ => X_sub_C_ne_zero a)]
  simp

/-- The lift has degree `|A|·d`. -/
theorem liftedPoly_natDegree (d : ℕ) (A : Finset F) :
    (liftedPoly d A).natDegree = A.card * d := by
  unfold liftedPoly
  rw [Polynomial.natDegree_expand, baseNodal_natDegree]

/-! ## 1. The vanishing window -/

/-- **Lattice vanishing:** `P_A` is a polynomial in `X^d`; every coefficient at an index not
divisible by `d` is zero. -/
theorem liftedPoly_coeff_eq_zero_of_not_dvd {d : ℕ} (hd : 0 < d) (A : Finset F) {i : ℕ}
    (hi : ¬ d ∣ i) :
    (liftedPoly d A).coeff i = 0 := by
  unfold liftedPoly
  rw [Polynomial.coeff_expand hd, if_neg hi]

/-- **The zero top window (the PTE property):** for a nonempty base and `1 ≤ j ≤ d−1`, the
coefficient at `|A|·d − j` vanishes — the symmetric functions `e₁, …, e_{d−1}` of the lifted
support are identically zero, for EVERY base set. -/
theorem liftedPoly_top_window_zero {d : ℕ} (hd : 0 < d) {A : Finset F} (hA : A.Nonempty)
    {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d - 1) :
    (liftedPoly d A).coeff (A.card * d - j) = 0 := by
  apply liftedPoly_coeff_eq_zero_of_not_dvd hd
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hjlt : j < d := by omega
  have hjsd : j < A.card * d := lt_of_lt_of_le hjlt (Nat.le_mul_of_pos_left d hApos)
  rintro ⟨q, hq⟩
  -- j = d·(|A| − q) with 1 ≤ j < d: divisibility forces j ≥ d, contradiction.
  have hqlt : q < A.card := by
    by_contra hge
    push Not at hge
    have hmul : A.card * d ≤ d * q := by
      calc A.card * d = d * A.card := Nat.mul_comm _ _
        _ ≤ d * q := Nat.mul_le_mul_left d hge
    omega
  have hj_eq : j = d * (A.card - q) := by
    have hexp : d * (A.card - q) = d * A.card - d * q := Nat.mul_sub d _ _
    have hcomm : d * A.card = A.card * d := Nat.mul_comm _ _
    omega
  have hdj : d ≤ j := by
    rw [hj_eq]
    calc d = d * 1 := (Nat.mul_one d).symm
      _ ≤ d * (A.card - q) := Nat.mul_le_mul_left d (by omega)
  omega

/-! ## 2. Distinctness: the lift is injective -/

/-- The base nodal recovers its root set: `(baseNodal A).eval x = 0 ↔ x ∈ A`. -/
theorem baseNodal_eval_eq_zero_iff (A : Finset F) (x : F) :
    (baseNodal A).eval x = 0 ↔ x ∈ A := by
  unfold baseNodal
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a, ha, hax⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hax
    rwa [hax]
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- `baseNodal` is injective on finsets (the root sets are recovered). -/
theorem baseNodal_injective : Function.Injective (baseNodal (F := F)) := by
  intro A A' h
  ext x
  rw [← baseNodal_eval_eq_zero_iff A x, ← baseNodal_eval_eq_zero_iff A' x, h]

/-- **The lift is injective** (for `d > 0`): distinct bases give distinct lifted polynomials —
hence the family `{P_A : A ⊆ B, |A| = s}` has exactly `C(|B|, s)` distinct members. -/
theorem liftedPoly_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (liftedPoly (F := F) d) := by
  intro A A' h
  exact baseNodal_injective (Polynomial.expand_injective hd h)

/-! ## 3. The lifted support is the power-map fiber -/

/-- **Root characterization:** `P_A(x) = 0 ↔ x^d ∈ A` — the root set of `P_A` in `F` is exactly
the preimage of the base under the `d`-th power map. It has `d·|A|` elements only under extra
hypotheses (a primitive `n`-th root of unity in `F`, `d ∣ n`, `A ⊆ μ_{n/d}`): see
`liftedSupport_card`; over a general field it can be smaller, even empty. -/
theorem liftedPoly_eval_eq_zero_iff (d : ℕ) (A : Finset F) (x : F) :
    (liftedPoly d A).eval x = 0 ↔ x ^ d ∈ A := by
  unfold liftedPoly
  rw [Polynomial.expand_eval, baseNodal_eval_eq_zero_iff]

/-! ## 4. The family count -/

/-- **THE PTE POLYNOMIAL FAMILY.** For any base finset `B`, `s ≥ 1`, `d > 0`: the lifts of the
`s`-subsets of `B` form `C(|B|, s)` pairwise-distinct degree-`sd` polynomials whose coefficients
agree (all zero) on the ENTIRE top window `{sd−1, …, sd−(d−1)}`. This is a statement about
polynomials only: over a general field they need not split into `sd` distinct roots (see
`liftedPoly_two_singleton_two_no_root_zmod3`). The support version — `C(n/d, s)` distinct
`d·s`-subsets of `μ_n` with equal `e₁, …, e_{d−1}` — is `pte_support_family`, under a primitive
`n`-th root of unity and `d ∣ n`. -/
theorem pte_family (d s : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (B : Finset F) :
    ∃ Ps : Finset F[X], Ps.card = B.card.choose s ∧
      (∀ P ∈ Ps, P.natDegree = s * d) ∧
      (∀ P ∈ Ps, ∀ j, 1 ≤ j → j ≤ d - 1 → P.coeff (s * d - j) = 0) := by
  classical
  refine ⟨(B.powersetCard s).image (liftedPoly d), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (Function.Injective.injOn (liftedPoly_injective hd)),
        Finset.card_powersetCard]
  · intro P hP
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.mem_powersetCard] at hA
    rw [liftedPoly_natDegree, hA.2]
  · intro P hP j hj1 hjd
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.mem_powersetCard] at hA
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    have := liftedPoly_top_window_zero hd hAne hj1 hjd
    rwa [hA.2] at this

/-! ## 5. Polynomials are not supports over a general field -/

/-- **Counterexample to the universal support reading.** Over `F₃`, `d = 2`, `A = {2}`: the lift
`P_A = X² − 2 = X² + 1` has degree `2` but no root in `F₃`, so its root support is empty, not a
`2`-element set. Hence distinct lifts (here of `{1}` and `{2}`) need not give equal-size supports
without the split-domain hypotheses of `liftedSupport_card`. -/
theorem liftedPoly_two_singleton_two_no_root_zmod3 :
    ∀ x : ZMod 3, (liftedPoly 2 ({2} : Finset (ZMod 3))).eval x ≠ 0 := by
  intro x
  rw [Ne, liftedPoly_eval_eq_zero_iff, Finset.mem_singleton]
  revert x
  decide

/-! ## 6. The support bridge on a genuine split domain `μ_n` -/

section Support

open ArkLib.ProximityGap.Rigidity

variable [DecidableEq F]

/-- The **lifted support** of `A` inside `μ_n`: the `n`-th roots of unity whose `d`-th power lies
in `A`. -/
noncomputable def liftedSupport (n d : ℕ) (A : Finset F) : Finset F :=
  (nthRootsFinset n (1 : F)).filter (fun x => x ^ d ∈ A)

theorem mem_liftedSupport {n d : ℕ} (hn : 0 < n) {A : Finset F} {x : F} :
    x ∈ liftedSupport n d A ↔ x ^ n = 1 ∧ x ^ d ∈ A := by
  rw [liftedSupport, Finset.mem_filter, mem_nthRootsFinset hn (1 : F)]

/-- **Support cardinality.** If `F` has a primitive `n`-th root of unity, `d ∣ n` and
`A ⊆ μ_{n/d}`, the lifted support has exactly `d·|A|` elements (each power-map fiber over `μ_n`
has `d` elements, `CosetExactCount.fiber_card_eq`). -/
theorem liftedSupport_card {ζ : F} {n d : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hζ : IsPrimitiveRoot ζ n) {A : Finset F} (hA : ∀ a ∈ A, a ^ (n / d) = 1) :
    (liftedSupport n d A).card = d * A.card := by
  have hS : liftedSupport n d A = A.biUnion (fun c => fiber n d c) := by
    ext x
    rw [mem_liftedSupport hn, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h2, (mem_fiber hn).mpr ⟨h1, rfl⟩⟩
    · rintro ⟨c, hc, hx⟩
      rw [mem_fiber hn] at hx
      exact ⟨hx.1, hx.2 ▸ hc⟩
  rw [hS, Finset.card_biUnion]
  · rw [Finset.sum_const_nat (m := d), Nat.mul_comm]
    intro c hc
    obtain ⟨g, hgn, hgc⟩ := exists_pow_eq_of_mem hn hdvd hζ (hA c hc)
    exact fiber_card_eq hn hdvd hζ hgn hgc
  · intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [mem_fiber hn] at hx hx'
    exact hcc' (hx.2.symm.trans hx'.2)

/-- **The lift splits over its support.** Under the hypotheses of `liftedSupport_card`,
`P_A = ∏_{x ∈ S_A} (X − x)`; so the vanishing coefficient window of `P_A` is a statement about the
elementary symmetric functions of the `d·|A|`-element support `S_A`. -/
theorem liftedPoly_eq_prod_liftedSupport {ζ : F} {n d : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hζ : IsPrimitiveRoot ζ n) {A : Finset F} (hA : ∀ a ∈ A, a ^ (n / d) = 1) :
    liftedPoly d A = ∏ x ∈ liftedSupport n d A, (X - C x) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  have hmonic : (liftedPoly d A).Monic :=
    Monic.expand hd (monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a)
  have hp0 : liftedPoly d A ≠ 0 := hmonic.ne_zero
  have hle : (liftedSupport n d A).val ≤ (liftedPoly d A).roots := by
    rw [Multiset.le_iff_subset (liftedSupport n d A).nodup]
    intro x hx
    rw [mem_roots hp0, IsRoot.def, liftedPoly_eval_eq_zero_iff]
    exact ((mem_liftedSupport hn).mp hx).2
  have hdeg : (liftedPoly d A).natDegree = Multiset.card (liftedSupport n d A).val := by
    rw [Finset.card_val, liftedSupport_card hn hdvd hζ hA, liftedPoly_natDegree, Nat.mul_comm]
  have hcard : Multiset.card (liftedPoly d A).roots ≤ Multiset.card (liftedSupport n d A).val :=
    hdeg ▸ card_roots' _
  have hroots : (liftedPoly d A).roots = (liftedSupport n d A).val :=
    (Multiset.eq_of_le_of_card_le hle hcard).symm
  rw [Finset.prod_eq_multiset_prod, ← hroots]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hroots, hdeg])).symm

/-- **Distinct bases give distinct supports** on `μ_{n/d}` (the `d`-th power map from `μ_n` onto
`μ_{n/d}` is surjective, `CosetExactCount.exists_pow_eq_of_mem`). -/
theorem liftedSupport_injOn {ζ : F} {n d : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hζ : IsPrimitiveRoot ζ n) {A A' : Finset F} (hA : ∀ a ∈ A, a ^ (n / d) = 1)
    (hA' : ∀ a ∈ A', a ^ (n / d) = 1) (h : liftedSupport n d A = liftedSupport n d A') :
    A = A' := by
  have key : ∀ {A A' : Finset F}, (∀ a ∈ A, a ^ (n / d) = 1) →
      liftedSupport n d A = liftedSupport n d A' → A ⊆ A' := by
    intro A A' hA h c hc
    obtain ⟨g, hgn, hgc⟩ := exists_pow_eq_of_mem hn hdvd hζ (hA c hc)
    have hg : g ∈ liftedSupport n d A := (mem_liftedSupport hn).mpr ⟨hgn, hgc ▸ hc⟩
    rw [h] at hg
    exact hgc ▸ ((mem_liftedSupport hn).mp hg).2
  exact Finset.Subset.antisymm (key hA h) (key hA' h.symm)

/-- **THE PTE SUPPORT FAMILY (headline).** If `F` has a primitive `n`-th root of unity and
`d ∣ n`, then for `s ≥ 1` there are `C(n/d, s)` pairwise-distinct `d·s`-subsets `S` of `μ_n` whose
nodal polynomials `∏_{x∈S} (X − x)` have zero coefficients on the top window
`{sd−1, …, sd−(d−1)}`, i.e. equal `e₁ = ⋯ = e_{d−1} = 0`. -/
theorem pte_support_family {ζ : F} {n d s : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hζ : IsPrimitiveRoot ζ n) (hs : 1 ≤ s) :
    ∃ Ss : Finset (Finset F), Ss.card = (n / d).choose s ∧
      (∀ S ∈ Ss, S ⊆ nthRootsFinset n (1 : F) ∧ S.card = d * s ∧
        ∀ j, 1 ≤ j → j ≤ d - 1 → (∏ x ∈ S, (X - C x)).coeff (s * d - j) = 0) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
  have hζd : IsPrimitiveRoot (ζ ^ d) (n / d) :=
    IsPrimitiveRoot.pow hn hζ (by rw [Nat.mul_div_cancel' hdvd])
  set B : Finset F := nthRootsFinset (n / d) (1 : F) with hB
  have hBcard : B.card = n / d := hζd.card_nthRootsFinset
  have hsub : ∀ A ∈ B.powersetCard s, ∀ a ∈ A, a ^ (n / d) = 1 := by
    intro A hA a ha
    exact (mem_nthRootsFinset hnd (1 : F)).mp ((Finset.mem_powersetCard.mp hA).1 ha)
  refine ⟨(B.powersetCard s).image (liftedSupport n d), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_powersetCard, hBcard]
    intro A hA A' hA' h
    exact liftedSupport_injOn hn hdvd hζ (hsub A hA) (hsub A' hA') h
  · intro S hS
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    have hAs : A.card = s := (Finset.mem_powersetCard.mp hA).2
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · rw [liftedSupport_card hn hdvd hζ (hsub A hA), hAs]
    · intro j hj1 hjd
      rw [← liftedPoly_eq_prod_liftedSupport hn hdvd hζ (hsub A hA), ← hAs]
      exact liftedPoly_top_window_zero hd (Finset.card_pos.mp (by omega)) hj1 hjd

end Support

end Round22PTE

#print axioms Round22PTE.liftedPoly_coeff_eq_zero_of_not_dvd
#print axioms Round22PTE.liftedPoly_top_window_zero
#print axioms Round22PTE.liftedPoly_injective
#print axioms Round22PTE.liftedPoly_eval_eq_zero_iff
#print axioms Round22PTE.pte_family
#print axioms Round22PTE.liftedPoly_two_singleton_two_no_root_zmod3
#print axioms Round22PTE.liftedSupport_card
#print axioms Round22PTE.liftedPoly_eq_prod_liftedSupport
#print axioms Round22PTE.liftedSupport_injOn
#print axioms Round22PTE.pte_support_family
