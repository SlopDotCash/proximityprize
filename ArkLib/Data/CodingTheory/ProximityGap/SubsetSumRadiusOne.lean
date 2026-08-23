/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RadiusOneExact
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# An UNCONDITIONAL subset-sum floor for the radius-one MCA error `ε_mca(RS, 1)`

`GrandChallengeRadiusOneExact.lean` proves the *exact* value `ε_mca(RS, 1) = C(n, k+1)/q`,
but only in the large-field regime `q > C(C(n, k+1), 2)`. `MCAEndpointLower.lean` proves the
spike floor `min(n-k, q)/q ≤ ε_mca(RS, 1)`, which has no additive content. This file fills the
middle band with a *new* unconditional lower bound

  `ε_mca(RS, 1) ≥ |Σ_{k+1}(L)| / q`   (`epsMCA_one_ge_card_subsetSums`)

where `Σ_{k+1}(L) := { ∑_{i ∈ T} L i : T ⊆ ι, |T| = k+1 }` is the **(k+1)-subset-sum set** of
the evaluation domain `L = domain`. There is *no* hypothesis on `q`.

## Strategy

Take the first word `u₀ := (X^{k+1} ∘ domain)` (the deep-hole word one degree higher) and the
second word `u₁ := (X^k ∘ domain)`. The key new identity is the **divided-difference value**

  `c_T(X^{k+1}-evaluations) = ∑_{i ∈ T} domain i`   (`cT_deepHole_succ`)

for every `(k+1)`-subset `T`: the polynomial `I := X^{k+1} - ∏_{i∈T}(X - domain i)` has degree
`≤ k`, agrees with `X^{k+1}` on `T` (the product vanishes there), hence equals the degree-`< |T|`
interpolant, so `c_T(u₀) = I.coeff k = -(∏(X - domain i)).coeff k = ∑_{i∈T} domain i` by Vieta.

`mcaEvent_at_gammaT` (proved in the sibling file for *any* `u₀`) then realises every
`γ_T = -c_T(u₀) = -∑_{i∈T} domain i` as a bad scalar. The negated subset sums are distinct (as
many as the subset sums themselves), so the bad `γ`-set has cardinality at least `|Σ_{k+1}(L)|`,
giving `Pr_γ[mcaEvent] ≥ |Σ_{k+1}(L)|/q` and hence the floor on `ε_mca`.

Over domains with additive structure (e.g. `𝔽₂`-subspaces) the subset-sum set can be *smaller*
than `n - k`, so this is genuinely different from the spike floor; over prime fields
Dias da Silva–Hamidoune makes `|Σ_{k+1}(L)|` of order `(k+1)(n-k-1)`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial ReedSolomon
open scoped ProbabilityTheory BigOperators

section SubsetSum

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The first elementary symmetric function of a multiset is its sum. -/
lemma esymm_one_eq_sum (s : Multiset F) : s.esymm 1 = s.sum := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp

/-- **New divided-difference identity.** For a `(k+1)`-subset `T`, the `Xᵏ`-coefficient of the
Lagrange interpolant through `T` of the *one-degree-higher* deep-hole word `deepHole (k+1)`
(evaluations of `X^{k+1}`) equals the `(k+1)`-subset sum `∑_{i ∈ T} domain i`. -/
lemma cT_deepHole_succ (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1) :
    cT domain k T (deepHole domain (k + 1)) = ∑ i ∈ T, domain i := by
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  -- The candidate interpolant `I := X^{k+1} - ∏_{i∈T}(X - C (domain i))`.
  set P : F[X] := ∏ i ∈ T, (X - C (domain i)) with hP
  set I : F[X] := X ^ (k + 1) - P with hI
  -- `P` is monic of degree `k+1 = T.card`, so the leading terms cancel and `deg I ≤ k`.
  have hPmonic : P.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (domain i))
  have hPnatdeg : P.natDegree = k + 1 := by
    rw [hP, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (domain i))]
    simp [hT]
  have hXmonic : (X ^ (k + 1) : F[X]).Monic := monic_X_pow (k + 1)
  have hIdeg : I.degree < (T.card : WithBot ℕ) := by
    rw [hT]
    -- `X^{k+1}` and `P` are both monic of degree `k+1`; their difference has degree `< k+1`.
    have hXdeg : (X ^ (k + 1) : F[X]).degree = ((k + 1 : ℕ) : WithBot ℕ) := degree_X_pow (k + 1)
    have hdegeq : (X ^ (k + 1) : F[X]).degree = P.degree := by
      rw [degree_eq_natDegree hXmonic.ne_zero, degree_eq_natDegree hPmonic.ne_zero,
        natDegree_X_pow, hPnatdeg]
    have hsub : (X ^ (k + 1) - P).degree < (X ^ (k + 1) : F[X]).degree := by
      apply Polynomial.degree_sub_lt hdegeq hXmonic.ne_zero
      rw [hXmonic.leadingCoeff, hPmonic.leadingCoeff]
    rw [hXdeg] at hsub
    rw [hI]
    exact hsub
  -- `I` agrees with `deepHole (k+1)` on `T`, since `P` vanishes there.
  have hIval : ∀ i ∈ T, I.eval (domain i) = deepHole domain (k + 1) i := by
    intro i hi
    have hPzero : P.eval (domain i) = 0 := by
      rw [hP, eval_prod]
      apply Finset.prod_eq_zero hi
      simp
    rw [hI, eval_sub, hPzero, sub_zero, eval_pow, eval_X, deepHole]
  -- Therefore the interpolant of `deepHole (k+1)` through `T` is `I`.
  have hinterp : Lagrange.interpolate T (fun i => domain i) (deepHole domain (k + 1)) = I := by
    refine (Lagrange.eq_interpolate_of_eval_eq (deepHole domain (k + 1)) hinj hIdeg ?_).symm
    intro i hi
    exact hIval i hi
  -- Read off the `k`-th coefficient: `(X^{k+1}).coeff k = 0`, and `P.coeff k = -(∑ domain i)`.
  rw [cT_apply, hinterp, hI, coeff_sub, coeff_X_pow, if_neg (by omega), zero_sub]
  -- Vieta: `P.coeff k = (-1)^((k+1)-k) * (T.val.map domain).esymm ((k+1)-k)`.
  have hPmap : P = ((T.val.map (fun i => domain i)).map (fun t => X - C t)).prod := by
    rw [hP, ← Finset.prod_map_val]
    rw [Multiset.map_map]
    rfl
  have hcard : Multiset.card (T.val.map (fun i => domain i)) = k + 1 := by
    rw [Multiset.card_map]; exact hT
  have hPcoeff : P.coeff k = -(∑ i ∈ T, domain i) := by
    rw [hPmap]
    rw [Multiset.prod_X_sub_C_coeff (T.val.map (fun i => domain i)) (by rw [hcard]; omega)]
    rw [hcard]
    have h1 : (k + 1) - k = 1 := by omega
    rw [h1, pow_one, esymm_one_eq_sum]
    -- `(T.val.map domain).sum = ∑ i ∈ T, domain i`
    rw [show (T.val.map (fun i => domain i)).sum = ∑ i ∈ T, domain i from Finset.sum_map_val T _]
    ring
  rw [hPcoeff]
  ring

/-- The set of `(k+1)`-subset sums of the evaluation domain `L = domain`. -/
noncomputable def subsetSumsKplus1 (domain : ι ↪ F) (k : ℕ) : Finset F :=
  (Finset.univ.powersetCard (k + 1)).image (fun T => ∑ i ∈ T, domain i)

/-- **Unconditional subset-sum floor.** For `C := RS[F, domain, k]` with `k + 1 ≤ n`:

  `ε_mca(C, 1) ≥ |Σ_{k+1}(L)| / q`,

where `Σ_{k+1}(L)` is the `(k+1)`-subset-sum set of the evaluation domain. No hypothesis on `q`. -/
theorem epsMCA_one_ge_card_subsetSums (domain : ι ↪ F) {k : ℕ}
    (_hk : k + 1 ≤ Fintype.card ι) :
    ((subsetSumsKplus1 domain k).card : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  classical
  set u₀ : ι → F := deepHole domain (k + 1) with hu₀
  set u₁ : ι → F := deepHole domain k with hu₁
  -- The bad-γ filter for this fixed pair.
  set Bad : Finset F := Finset.univ.filter
    (fun γ : F => mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ) with hBad
  -- The negated subset sums all lie in `Bad`.
  have hcontain : (subsetSumsKplus1 domain k).image (fun s => -s) ⊆ Bad := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨s, hs, rfl⟩ := hγ
    rw [subsetSumsKplus1, Finset.mem_image] at hs
    obtain ⟨T, hT, rfl⟩ := hs
    rw [Finset.mem_powersetCard] at hT
    have hT : T.card = k + 1 := hT.2
    rw [hBad, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- `-(∑ domain) = -c_T(u₀)` and `mcaEvent_at_gammaT` realises it.
    have hval : -(∑ i ∈ T, domain i) = -cT domain k T u₀ := by
      rw [hu₀, cT_deepHole_succ domain hT]
    rw [hval]
    exact mcaEvent_at_gammaT domain hT u₀
  -- Cardinality: negation is injective, so the negated image has the same card.
  have hcard_img : ((subsetSumsKplus1 domain k).image (fun s => -s)).card
      = (subsetSumsKplus1 domain k).card :=
    Finset.card_image_of_injective _ neg_injective
  have hcard_le : (subsetSumsKplus1 domain k).card ≤ Bad.card := by
    calc (subsetSumsKplus1 domain k).card
        = ((subsetSumsKplus1 domain k).image (fun s => -s)).card := hcard_img.symm
      _ ≤ Bad.card := Finset.card_le_card hcontain
  -- Translate to a probability lower bound.
  have hpr : ((subsetSumsKplus1 domain k).card : ENNReal) / (Fintype.card F : ENNReal) ≤
      Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ ] := by
    rw [prob_uniform_eq_card_filter_div_card]
    have hnum : (↑((subsetSumsKplus1 domain k).card) : ENNReal)
        ≤ (↑(↑Bad.card : ℝ≥0) : ENNReal) := by
      exact_mod_cast hcard_le
    have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
      push_cast; rfl
    rw [hden]
    gcongr
  -- And the per-pair probability is below the supremum `ε_mca`.
  refine le_trans hpr ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 (u 0) (u 1) γ ])
    (Code.finMapTwoWords u₀ u₁)

/-- **Refutation of the §1 MCA prize via subset sums.** If `q < 2^128 · |Σ_{k+1}(L)|` then
`ε* = 2^(-128) < ε_mca(RS[F, domain, k], 1)`. Unconditional in `q`; uses only `k + 1 ≤ n`. -/
theorem epsStar_lt_epsMCA_one_of_subsetSums (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  classical
  set q := Fintype.card F with hq_def
  set m := (subsetSumsKplus1 domain k).card with hm_def
  have hq_pos : 0 < q := Fintype.card_pos
  have hm_pos : 0 < m := by
    -- `q < 2^128 * m` with `q ≥ 1` forces `m ≥ 1`.
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0, Nat.mul_zero] at hsmall; omega
    · exact hm0
  -- `epsStar = 2^(-128)`.
  have hepsStar : (ProximityGap.epsStar : ENNReal) = (2 ^ (128 : ℕ) : ENNReal)⁻¹ := by
    rw [ProximityGap.epsStar]
    push_cast
    rw [one_div]
  rw [hepsStar]
  have hfloor := epsMCA_one_ge_card_subsetSums (F := F) domain hk
  rw [← hm_def, ← hq_def] at hfloor
  refine lt_of_lt_of_le ?_ hfloor
  -- `2^(-128) < m/q ⟺ 2^(-128)·q < m ⟺ q < 2^128·m`.
  have hqne : (q : ENNReal) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hqne) (Or.inl hqtop)]
  -- goal: `(2^128)⁻¹ * q < m`
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ENNReal) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ENNReal) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  -- goal: `q < m * 2^128`
  have hcast : (q : ENNReal) < ((2 ^ (128 : ℕ) * m : ℕ) : ENNReal) := by exact_mod_cast hsmall
  calc (q : ENNReal) < ((2 ^ (128 : ℕ) * m : ℕ) : ENNReal) := hcast
    _ = (m : ENNReal) * (2 ^ (128 : ℕ) : ENNReal) := by push_cast; ring

end SubsetSum

end ProximityGap
