/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetThreePowUpper

/-!
# The exact `3^{n/4}` char-0 subset-sum image of the index-2 subgroup `μ_{n/2}`  (thread L3-3pow)

Wave 1 (thread T09 follow-up) *measured* that the char-0 distinct-subset-sum image of the
index-`2` multiplicative subgroup `μ_{n/2}` of `μ_n` is **exactly** `3^{n/4}`
(`81 = 3^4` at `n/2 = 8`, `6561 = 3^8` at `n/2 = 16`).  This file turns that measurement into
an **exact, axiom-clean cyclotomic theorem**.

## The statement

Let `ζ` be a primitive `2^m`-th root of unity (`m ≥ 1`) in a characteristic-`0` field `K`
(so `G = {ζ^0, …, ζ^{2^m−1}}` is the order-`2^m` subgroup, and `h := 2^{m−1}` is its number of
antipodal classes).  Then the set of **distinct subset sums** of `G` has cardinality
**exactly `3^{2^{m−1}}`**:

  `subsetSumset_twoPow_card_eq_three_pow :`
    `(univ.image (fun S : Finset (Fin (2^{m-1} + 2^{m-1})) => ∑ i ∈ S, ζ ^ (i:ℕ))).card`
      `= 3 ^ 2^{m−1}`.

Applied to the **index-2 subgroup** `μ_{n/2}` of `μ_n` (`n = 2^μ`, `μ ≥ 2`, so `2^m = n/2`,
`m = μ−1`, `h = 2^{m−1} = 2^{μ−2} = n/4`): the image size is exactly `3^{n/4}`
(`subsetSumset_muHalf_card_eq_three_pow`).

## Why `3^{2^{m−1}}` (the antipodal mechanism, now a proof)

`ζ^{2^{m−1}} = −1` (`ζ^{2^{m−1}}` is a primitive square root of unity), so the `2^m` group
elements split into `2^{m−1}` antipodal classes `{ζ^j, −ζ^j}` (`j < 2^{m−1}`).  In a subset sum
each class contributes a coefficient `ε_j ∈ {−1, 0, +1}` (take only `−ζ^j`, neither/both, or
only `ζ^j`).  So every subset sum is a `{−1,0,1}`-combination `∑_{j} ε_j ζ^j`.

* **`≤ 3^h`** (in-tree, any field): the sum factors through the `Fin 3`-code
  `code : Finset (Fin (h+h)) → (Fin h → Fin 3)` (`subsetSumset_full_le_three_pow`),
  and `|Fin h → Fin 3| = 3^h`.
* **`≥ 3^h`** (this file, char `0`): the `3^h` codes are (i) **all realized** by an actual
  subset (`code_surjective`), and (ii) give **distinct** sums, because
  `{1, ζ, …, ζ^{h−1}}` are `ℤ`-linearly independent (`h = φ(2^m)`, `cyclo_noRelation` via
  `minpoly`) — and a code difference has coefficients in `{−2,…,2} ⊂ ℤ`.  The two meet:
  `= 3^h`.

This is **strictly sharper** than the `2^h`-box bound
(`card_subsetSumset_isPrimitiveRoot_two_pow_ge`, Loop50): the `{−1,0,1}` cube has `3^h` points,
not the `2^h` of the `{0,1}` box.  A clean exact cyclotomic input to the halo /
representation-mass face: the close-set count of the §7 curve-decodability route is the
subset-sum image, here pinned exactly at the index-2 subgroup.

## References

* [KKH26] Krachun–Kazanin–Haböck, *Failure of proximity gaps close to capacity*, ePrint 2026/782.
* In-tree: `SubgroupSumsetThreePowUpper.lean` (the `≤ 3^h` cap + `code`/`codeVal` machinery),
  `SubsetSumLowerLoop50.lean` (the `2^h` box bound + cyclotomic no-relation engine),
  `TwoPowerSubsetSumSpectrum.lean` (the stratum law `∑_a 2^a C(h,a) = 3^h`).
-/

open Finset

namespace ArkLib.ProximityGap.WF407W2_L3_3pow

open ArkLib.ProximityGap.Round3SubgroupSumsetDirect
open ArkLib.ProximityGap.SubsetSumLowerLoop50

variable {K : Type*} [Field K]

/-! ### The cyclotomic no-relation engine (char 0)

A vanishing `ℤ`-combination of `{1, ζ, …, ζ^{N−1}}` with `N ≤ φ(n)` is forced to be the zero
combination.  Same minimal-polynomial argument as
`SubsetSumLowerLoop50.subsetSum_injective_of_isPrimitiveRoot`, extracted here as the *no-relation*
statement over **arbitrary** integer coefficients (not just `{0,1}`), which is what the
`{−1,0,1}`-code injectivity needs (code *differences* have coefficients in `{−2,…,2}`). -/

/-- **Cyclotomic `ℤ`-no-relation.**  For a primitive `n`-th root `ζ` in a char-`0` field and
`N ≤ φ(n)`, any integer combination `∑_{j<N} (g j) · ζ^j = 0` has all coefficients zero. -/
theorem cyclo_noRelation [CharZero K] {n : ℕ} (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {N : ℕ} (hN : N ≤ Nat.totient n)
    (g : Fin N → ℤ) (hg : (∑ j, (g j : K) * ζ ^ (j : ℕ)) = 0) (j : Fin N) : g j = 0 := by
  classical
  set p : Polynomial ℤ := ∑ j : Fin N, Polynomial.monomial (j : ℕ) (g j) with hp
  -- `aeval ζ p = ∑ (g j : K) ζ^j = 0`
  have haeval : (Polynomial.aeval ζ) p = 0 := by
    rw [hp, map_sum]
    simp only [Polynomial.aeval_monomial, eq_intCast]
    exact hg
  -- coefficient extraction: `coeff p (i:ℕ) = g i`
  have hcoeff : ∀ i : Fin N, p.coeff (i : ℕ) = g i := by
    intro i
    rw [hp, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg]
      exact fun h => hb (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ i) h
  -- `p = 0` via the minimal-polynomial degree bound
  have hp0 : p = 0 := by
    by_contra hpne
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0; exact hpne (by rw [hp]; simp)
    have hdvd : minpoly ℤ ζ ∣ p :=
      (minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) haeval)
    have h1 : (minpoly ℤ ζ).natDegree ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hdvd hpne
    have h2 : Nat.totient n ≤ (minpoly ℤ ζ).natDegree := hζ.totient_le_degree_minpoly
    have h3 : p.natDegree < N := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hpne, hp]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe N)).mpr ?_
      intro j _
      exact lt_of_le_of_lt (Polynomial.degree_monomial_le _ _)
        (WithBot.coe_lt_coe.mpr j.isLt)
    omega
  have := hcoeff j
  rw [hp0, Polynomial.coeff_zero] at this
  exact this.symm

/-! ### The code is surjective: every `{−1,0,1}`-code is realized by an honest subset -/

/-- The realizing subset of a code `c : Fin N → Fin 3`: take `ζ^j` (low index `castAdd N j`)
on the `+1` classes, take `−ζ^j` (high index `natAdd N j`) on the `−1` classes. -/
noncomputable def codeSubset {N : ℕ} (c : Fin N → Fin 3) : Finset (Fin (N + N)) := by
  classical
  exact (Finset.univ.filter fun i : Fin (N + N) =>
    (∃ j : Fin N, i = Fin.castAdd N j ∧ c j = 1) ∨
    (∃ j : Fin N, i = Fin.natAdd N j ∧ c j = 2))

private lemma castAdd_ne_natAdd {N : ℕ} (j k : Fin N) :
    Fin.castAdd N j ≠ Fin.natAdd N k := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
  omega

/-- `code (codeSubset c) = c`: the code machinery recovers any prescribed `Fin 3`-code. -/
theorem code_codeSubset {N : ℕ} (c : Fin N → Fin 3) :
    code (codeSubset c) = c := by
  classical
  funext j
  have hmem_cast : (Fin.castAdd N j) ∈ codeSubset c ↔ c j = 1 := by
    unfold codeSubset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨k, hk, hck⟩ | ⟨k, hk, hck⟩)
      · have : j = k := Fin.castAdd_injective N N hk
        rw [this]; exact hck
      · exact absurd hk (castAdd_ne_natAdd j k)
    · intro h; exact Or.inl ⟨j, rfl, h⟩
  have hmem_nat : (Fin.natAdd N j) ∈ codeSubset c ↔ c j = 2 := by
    unfold codeSubset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨k, hk, hck⟩ | ⟨k, hk, hck⟩)
      · exact absurd hk.symm (castAdd_ne_natAdd k j)
      · have : j = k := Fin.natAdd_injective hk
        rw [this]; exact hck
    · intro h; exact Or.inr ⟨j, rfl, h⟩
  unfold code
  by_cases hc1 : c j = 1
  · simp [hmem_cast.mpr hc1, hmem_nat, hc1, show (1 : Fin 3) ≠ 2 by decide]
  · by_cases hc2 : c j = 2
    · have hcast_not : (Fin.castAdd N j) ∉ codeSubset c := fun h => hc1 (hmem_cast.mp h)
      simp [hmem_nat.mpr hc2, hcast_not, hc2]
    · have hcast_not : (Fin.castAdd N j) ∉ codeSubset c := fun h => hc1 (hmem_cast.mp h)
      have hnat_not : (Fin.natAdd N j) ∉ codeSubset c := fun h => hc2 (hmem_nat.mp h)
      have hc0 : c j = 0 := by fin_cases hcj : c j <;> simp_all
      simp [hcast_not, hnat_not, hc0]

/-- **Code surjectivity.**  Every `c : Fin N → Fin 3` is the code of some subset. -/
theorem code_surjective {N : ℕ} : Function.Surjective (code (N := N)) :=
  fun c => ⟨codeSubset c, code_codeSubset c⟩

/-! ### The lower bound `3^h ≤ |subset-sum image|` in char 0, and the exact equality -/

/-- The code-value sum `c ↦ ∑_{j<h} codeVal (c j) · ζ^j` is **injective** for a primitive
`2^m`-th root `ζ` over a char-`0` field (`h = 2^{m−1} = φ(2^m)`): a coincidence is a vanishing
`ℤ`-combination with coefficients `codeVal (c₁ j) − codeVal (c₂ j) ∈ {−2,…,2}`, killed by
`cyclo_noRelation`. -/
theorem codeVal_sum_injective [CharZero K] {m : ℕ} (hm : 1 ≤ m) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    Function.Injective
      (fun c : Fin (2 ^ (m - 1)) → Fin 3 => ∑ j, codeVal (c j) * ζ ^ (j : ℕ)) := by
  classical
  intro c₁ c₂ hc
  -- integer coefficient differences
  set d : Fin (2 ^ (m - 1)) → ℤ := fun j =>
    (if c₁ j = 1 then 1 else if c₁ j = 2 then -1 else 0)
      - (if c₂ j = 1 then 1 else if c₂ j = 2 then -1 else 0) with hd
  have hcast : ∀ j, ((d j : ℤ) : K) = codeVal (c₁ j) - codeVal (c₂ j) := by
    intro j
    simp only [hd, codeVal, Int.cast_sub]
    by_cases h1 : c₁ j = 1 <;> by_cases h1' : c₁ j = 2 <;>
      by_cases h2 : c₂ j = 1 <;> by_cases h2' : c₂ j = 2 <;>
      simp_all
  have hsum0 : (∑ j, (d j : K) * ζ ^ (j : ℕ)) = 0 := by
    have : (∑ j, (d j : K) * ζ ^ (j : ℕ))
        = (∑ j, codeVal (c₁ j) * ζ ^ (j : ℕ)) - (∑ j, codeVal (c₂ j) * ζ ^ (j : ℕ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hcast j]; ring
    rw [this, hc, sub_self]
  -- kill the relation: all `d j = 0`
  have htot : 2 ^ (m - 1) ≤ Nat.totient (2 ^ m) := le_of_eq (totient_two_pow hm).symm
  have hd0 : ∀ j, d j = 0 :=
    cyclo_noRelation (by positivity) hζ htot d hsum0
  -- `d j = 0` forces `c₁ j = c₂ j` (codes are determined by their `{−1,0,1}` value)
  funext j
  have := hd0 j
  simp only [hd, sub_eq_zero] at this
  -- the map `Fin 3 → {−1,0,1}` (1↦1, 2↦−1, else 0) is injective on `Fin 3`
  fin_cases hc1 : c₁ j <;> fin_cases hc2 : c₂ j <;> simp_all <;> omega

/-- **The `≥ 3^h` lower bound (char 0).**  For a primitive `2^m`-th root `ζ` over a char-`0`
field, the distinct-subset-sum image of the order-`2^m` subgroup has at least `3^{2^{m−1}}`
elements: the `3^{2^{m−1}}` codes are all realized (`code_surjective`) and give distinct sums
(`codeVal_sum_injective`). -/
theorem subsetSumset_twoPow_ge_three_pow [CharZero K] [DecidableEq K] {m : ℕ} (hm : 1 ≤ m)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    3 ^ (2 ^ (m - 1)) ≤
      (Finset.univ.image
        (fun S : Finset (Fin (2 ^ (m - 1) + 2 ^ (m - 1))) => ∑ i ∈ S, ζ ^ (i : ℕ))).card := by
  classical
  set N := 2 ^ (m - 1) with hN
  have hpow : ζ ^ N = -1 := by
    have h2N : 2 * N = 2 ^ m := by
      rw [hN, ← pow_succ']
      congr 1
      omega
    have hζ' : IsPrimitiveRoot ζ (2 * N) := by rw [h2N]; exact hζ
    have hNpos : 0 < N := by positivity
    have hsq : IsPrimitiveRoot (ζ ^ N) 2 := hζ'.pow (by positivity) (by ring)
    exact hsq.eq_neg_one_of_two_right
  -- the codeVal-sum map factors through the subset-sum image (via `code`)
  -- and is injective; surjectivity of `code` makes its range hit `3^N` distinct sums.
  have hfactor : ∀ c : Fin N → Fin 3,
      (∑ j, codeVal (c j) * ζ ^ (j : ℕ))
        ∈ Finset.univ.image
          (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ)) := by
    intro c
    obtain ⟨S, hS⟩ := code_surjective c
    rw [Finset.mem_image]
    refine ⟨S, Finset.mem_univ _, ?_⟩
    rw [subsetSum_eq_codeValue hpow S, hS]
  -- build the injection: `Fin N → Fin 3` ↪ image
  have hinj := codeVal_sum_injective (K := K) hm hζ
  calc 3 ^ N
      = (Finset.univ : Finset (Fin N → Fin 3)).card := by
        rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]
    _ = (Finset.univ.image (fun c : Fin N → Fin 3 => ∑ j, codeVal (c j) * ζ ^ (j : ℕ))).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ (Finset.univ.image
          (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
        exact hfactor c

/-- **★ The exact `3^{2^{m−1}}` count (char 0).**  For a primitive `2^m`-th root `ζ` over a
characteristic-`0` field, the distinct-subset-sum image of the order-`2^m` subgroup
`G = {ζ^0, …, ζ^{2^m−1}}` has cardinality **exactly** `3^{2^{m−1}}` — the `≤ 3^h` antipodal cap
meets the `≥ 3^h` char-`0` realization+independence bound. -/
theorem subsetSumset_twoPow_card_eq_three_pow [CharZero K] [DecidableEq K] {m : ℕ} (hm : 1 ≤ m)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    (Finset.univ.image
      (fun S : Finset (Fin (2 ^ (m - 1) + 2 ^ (m - 1))) => ∑ i ∈ S, ζ ^ (i : ℕ))).card
      = 3 ^ (2 ^ (m - 1)) := by
  classical
  have hNpos : 0 < 2 ^ (m - 1) := by positivity
  have h2N : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']; congr 1; omega
  have hζ' : IsPrimitiveRoot ζ (2 * 2 ^ (m - 1)) := by rw [h2N]; exact hζ
  refine le_antisymm ?_ (subsetSumset_twoPow_ge_three_pow hm hζ)
  exact subsetSumset_full_le_three_pow hNpos hζ'

/-! ### Specialization: the index-2 subgroup `μ_{n/2}` of `μ_n`  (`n = 2^μ`, `μ ≥ 2`)

`μ_{n/2}` is the order-`n/2 = 2^{μ−1}` subgroup; set `m = μ − 1` so `2^m = n/2` and the
antipodal-class count is `2^{m−1} = 2^{μ−2} = n/4`. -/

/-- **★ The index-2 subgroup `μ_{n/2}` has subset-sum image of size exactly `3^{n/4}`.**
For `n = 2^μ` with `μ ≥ 2`, a primitive `(n/2)`-th root `ζ` over a char-`0` field generates the
index-2 subgroup `μ_{n/2}` (order `2^{μ−1}`); its distinct-subset-sum image has cardinality
exactly `3^{2^{μ−2}} = 3^{n/4}`. -/
theorem subsetSumset_muHalf_card_eq_three_pow [CharZero K] [DecidableEq K] {μ : ℕ} (hμ : 2 ≤ μ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (μ - 1))) :
    (Finset.univ.image
      (fun S : Finset (Fin (2 ^ (μ - 2) + 2 ^ (μ - 2))) => ∑ i ∈ S, ζ ^ (i : ℕ))).card
      = 3 ^ (2 ^ (μ - 2)) := by
  have hm : 1 ≤ μ - 1 := by omega
  have hmm : μ - 1 - 1 = μ - 2 := by omega
  have key := subsetSumset_twoPow_card_eq_three_pow (K := K) (m := μ - 1) hm
    (by rw [hmm] at *; exact hζ)
  rw [hmm] at key
  exact key

/-! ### Sanity: the closed-form values the probe measured

`3^{n/4}` at the enumerated half-sizes (`n/2 = 4, 8, 16`, i.e. `n = 8, 16, 32`):
the antipodal-class count is `h = n/4 = 2, 4, 8`, giving `3^2 = 9`, `3^4 = 81`, `3^8 = 6561`. -/

/-- `n = 8` (`μ = 3`): `μ_{n/2} = μ_4`, antipodal classes `h = n/4 = 2`, image `= 3^2 = 9`. -/
example : (3 : ℕ) ^ (2 ^ (3 - 2)) = 9 := by decide

/-- `n = 16` (`μ = 4`): `μ_{n/2} = μ_8`, antipodal classes `h = n/4 = 4`, image `= 3^4 = 81`. -/
example : (3 : ℕ) ^ (2 ^ (4 - 2)) = 81 := by decide

/-- `n = 32` (`μ = 5`): `μ_{n/2} = μ_16`, antipodal classes `h = n/4 = 8`, image `= 3^8 = 6561`. -/
example : (3 : ℕ) ^ (2 ^ (5 - 2)) = 6561 := by decide

/-- The stratum law `∑_{a=0}^{h} 2^a · C(h,a) = 3^h` (binomial theorem `(1+2)^h`); the per-weight
decomposition `TwoPowerSubsetSumSpectrum` sums to the closed form proven above.  Anchor `h = 4`:
`1 + 8 + 24 + 32 + 16 = 81 = 3^4`. -/
example : ∑ a ∈ Finset.range 5, 2 ^ a * Nat.choose 4 a = 3 ^ 4 := by decide

/-- General stratum identity `∑_{a=0}^{h} 2^a · C(h,a) = 3^h` (binomial theorem). -/
theorem sum_two_pow_choose_eq_three_pow (h : ℕ) :
    ∑ a ∈ Finset.range (h + 1), 2 ^ a * Nat.choose h a = 3 ^ h := by
  have := (add_pow 1 2 h).symm
  -- `(1+2)^h = ∑ 1^{h-a} 2^a C(h,a)`; specialize over ℕ
  have hkey : (1 + 2 : ℕ) ^ h = ∑ a ∈ Finset.range (h + 1), 1 ^ (h - a) * 2 ^ a * Nat.choose h a :=
    add_pow 1 2 h
  rw [show (1 + 2 : ℕ) = 3 from rfl] at hkey
  rw [hkey]
  exact Finset.sum_congr rfl fun a _ => by rw [one_pow, one_mul]

end ArkLib.ProximityGap.WF407W2_L3_3pow

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.cyclo_noRelation
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.code_surjective
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.codeVal_sum_injective
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.subsetSumset_twoPow_card_eq_three_pow
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.subsetSumset_muHalf_card_eq_three_pow
#print axioms ArkLib.ProximityGap.WF407W2_L3_3pow.sum_two_pow_choose_eq_three_pow
