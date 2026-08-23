/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainEngine

/-!
# The exact jump value (#357): `ε_mca(RS[F, D, n−2], 1/n) = n/q` under nondegeneracy

The antichain engine capped the granularity jump at `n/q` for every linear code; the family
file supplied `2` bad scalars. This file produces the **remaining `n − 2` bad scalars** of
the flat-`n` law and pins the exact jump value, conditional on an explicit per-point
nondegeneracy.

## The per-excluded-point construction (`k = n − 2`)

Fix the marked pair `B = {b₁, b₂}` and the indicator stack `(𝟙_{b₂}, 𝟙_{b₁,b₂})`. For each
third point `j ∉ B`, let `Z_j` be the evaluation word of the vanishing polynomial of
`T_j = univ ∖ {j, b₁, b₂}` (degree `n−3 < n−2`, hence a codeword; `Z_j(b₁), Z_j(b₂) ≠ 0`).
If the **nondegeneracy** `Z_j(b₂) ≠ Z_j(b₁)` holds, then

  `γ_j := Z_j(b₁) / (Z_j(b₂) − Z_j(b₁))`

is a bad scalar with witness `univ ∖ {j}` (`mcaEvent_perPoint`): the codeword
`(Z_j(b₂) − Z_j(b₁))⁻¹ • Z_j` matches the line (`perPoint_agree`), while a joint second
row would (by the forced-zero brick) be proportional to `Z_j` and need
`Z_j(b₁) = Z_j(b₂)` — the same nondegeneracy, refuted.

## Distinctness — the bad set has exactly `n` elements

`γ_j ∉ {0, −1}` unconditionally; and `γ_j ≠ γ_{j'}` for `j ≠ j'`: equal scalars would
make the *same* line point agree with codewords on `univ∖{j}` and `univ∖{j'}`, which
agree on the `n−2 ≥ k` common points hence are equal (`rs_eq_of_agree`) — so the point is
close on all of `univ`, and the nesting collapse (`bad_scalar_eq_of_witness_subset`)
would force the bad set to a singleton, contradicting `0 ≠ −1` both bad
(`no_univ_closeness_of_two_bad`).

## The headline

`epsMCA_rs_jump_eq` — under nondegeneracy at every third point,

  `ε_mca(RS[F, D, n−2], 1/n) = n/q`  **exactly**

(lower: the `n`-element bad set through the witness-spread engine; upper: the antichain
engine). The flat-`n` law, both halves. Stage B (registered): the `x^n − 1` derivative
identity turns the nondegeneracy into the closed form `j·(b₁+b₂) ≠ b₁² + b₂²` over
subgroup domains, which the antipodal choice `b₂ = −b₁` satisfies vacuously in odd
characteristic.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-2 jump-value mechanism comment); `MCAAntichainEngine.lean`,
  `MCADeltaStarHighRateFamily.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCADeltaStarHighRateFamily
open ProximityGap.MCAAntichainEngine

namespace ProximityGap.MCAJumpValueExact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The vanishing-product codeword -/

/-- The evaluation word of the vanishing polynomial of `T`: `Z_T(x) = ∏_{t∈T} (x − D t)`. -/
noncomputable def vanishWord (domain : ι ↪ F) (T : Finset ι) : ι → F :=
  fun i => ∏ t ∈ T, (domain i - domain t)

theorem vanishWord_eq_zero (domain : ι ↪ F) {T : Finset ι} {i : ι} (hi : i ∈ T) :
    vanishWord domain T i = 0 :=
  Finset.prod_eq_zero hi (by simp)

theorem vanishWord_ne_zero (domain : ι ↪ F) {T : Finset ι} {i : ι} (hi : i ∉ T) :
    vanishWord domain T i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  rw [sub_ne_zero]
  exact fun h => hi ((domain.injective h) ▸ ht)

/-- The vanishing word is a codeword whenever `|T| < k`. -/
theorem vanishWord_mem_code (domain : ι ↪ F) {T : Finset ι} {k : ℕ} (hk : T.card < k) :
    vanishWord domain T ∈ ReedSolomon.code domain k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  refine ⟨∏ t ∈ T, (Polynomial.X - Polynomial.C (domain t)), ?_, ?_⟩
  · have hne : ∀ t ∈ T, (Polynomial.X - Polynomial.C (domain t)) ≠ (0 : Polynomial F) :=
      fun t _ => Polynomial.X_sub_C_ne_zero (domain t)
    have hdeg : (∏ t ∈ T, (Polynomial.X - Polynomial.C (domain t))).natDegree = T.card := by
      rw [Polynomial.natDegree_prod _ _ hne,
        Finset.sum_congr rfl (fun t _ => Polynomial.natDegree_X_sub_C (domain t))]
      simp
    have h0 : (∏ t ∈ T, (Polynomial.X - Polynomial.C (domain t))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hne
    rw [← Polynomial.natDegree_lt_iff_degree_lt h0, hdeg]
    exact hk
  · funext i
    simp [vanishWord, ReedSolomon.evalOnPoints, Polynomial.eval_prod]

/-! ## The per-excluded-point bad scalar -/

section PerPoint

variable (domain : ι ↪ F) {b₁ b₂ j : ι}

/-- The three-point complement `T_j = univ ∖ {j, b₁, b₂}`. -/
noncomputable def Tset (j b₁ b₂ : ι) : Finset ι :=
  ((Finset.univ.erase j).erase b₁).erase b₂

theorem mem_Tset {j b₁ b₂ i : ι} :
    i ∈ Tset j b₁ b₂ ↔ i ≠ b₂ ∧ i ≠ b₁ ∧ i ≠ j := by
  simp [Tset, Finset.mem_erase, and_assoc]

theorem Tset_card {j b₁ b₂ : ι} (hb : b₁ ≠ b₂) (hj1 : j ≠ b₁) (hj2 : j ≠ b₂) :
    (Tset j b₁ b₂).card = Fintype.card ι - 3 := by
  rw [Tset,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hb.symm,
      Finset.mem_erase.mpr ⟨hj2.symm, Finset.mem_univ b₂⟩⟩),
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ b₁⟩),
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  omega

/-- The per-point bad scalar. -/
noncomputable def gammaOf (domain : ι ↪ F) (b₁ b₂ j : ι) : F :=
  vanishWord domain (Tset j b₁ b₂) b₁ /
    (vanishWord domain (Tset j b₁ b₂) b₂ - vanishWord domain (Tset j b₁ b₂) b₁)

/-- The per-point witness codeword. -/
noncomputable def wOf (domain : ι ↪ F) (b₁ b₂ j : ι) : ι → F :=
  (vanishWord domain (Tset j b₁ b₂) b₂ - vanishWord domain (Tset j b₁ b₂) b₁)⁻¹ •
    vanishWord domain (Tset j b₁ b₂)

/-- **The agreement law:** the witness codeword matches the line at `γ_j` on
`univ ∖ {j}`. -/
theorem perPoint_agree (hb : b₁ ≠ b₂) (hj1 : j ≠ b₁) (hj2 : j ≠ b₂)
    (hnd : vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁) :
    ∀ i ∈ Finset.univ.erase j,
      wOf domain b₁ b₂ j i = ind1 b₂ i + gammaOf domain b₁ b₂ j • ind2 b₁ b₂ i := by
  have hDj0 : vanishWord domain (Tset j b₁ b₂) b₂
      - vanishWord domain (Tset j b₁ b₂) b₁ ≠ 0 := sub_ne_zero.mpr hnd
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  by_cases h1 : i = b₁
  · subst h1
    have e1 : ind1 (F := F) b₂ i = 0 := if_neg hb
    have e2 : ind2 (F := F) i b₂ i = 1 := if_pos (Or.inl rfl)
    rw [e1, e2]
    simp only [wOf, gammaOf, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
    ring
  · by_cases h2 : i = b₂
    · subst h2
      have e1 : ind1 (F := F) i i = 1 := if_pos rfl
      have e2 : ind2 (F := F) b₁ i i = 1 := if_pos (Or.inr rfl)
      rw [e1, e2]
      simp only [wOf, gammaOf, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · have hiT : i ∈ Tset j b₁ b₂ := mem_Tset.mpr ⟨h2, h1, hij⟩
      have e1 : ind1 (F := F) b₂ i = 0 := if_neg h2
      have e2 : ind2 (F := F) b₁ b₂ i = 0 := if_neg (by
        rintro (h | h)
        · exact h1 h
        · exact h2 h)
      rw [e1, e2]
      simp only [wOf, Pi.smul_apply, smul_eq_mul]
      rw [vanishWord_eq_zero domain hiT]
      ring

/-- **The per-point bad event.** Under nondegeneracy, `γ_j` fires `mcaEvent` with witness
`univ ∖ {j}` for the code `RS[F, D, n−2]`. -/
theorem mcaEvent_perPoint (hn : 4 ≤ Fintype.card ι)
    (hb : b₁ ≠ b₂) (hj1 : j ≠ b₁) (hj2 : j ≠ b₂)
    (hnd : vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁) :
    mcaEvent (F := F)
      (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0)) (ind1 b₂) (ind2 b₁ b₂) (gammaOf domain b₁ b₂ j) := by
  set Z := vanishWord domain (Tset j b₁ b₂) with hZ
  have hb1T : b₁ ∉ Tset j b₁ b₂ := fun h => (mem_Tset.mp h).2.1 rfl
  have hb2T : b₂ ∉ Tset j b₁ b₂ := fun h => (mem_Tset.mp h).1 rfl
  have hTcard : (Tset j b₁ b₂).card = Fintype.card ι - 3 := Tset_card hb hj1 hj2
  have hZmem : Z ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    vanishWord_mem_code domain (by omega)
  refine ⟨Finset.univ.erase j, erase_card_clause j,
    ⟨wOf domain b₁ b₂ j, Submodule.smul_mem _ _ hZmem,
      perPoint_agree domain hb hj1 hj2 hnd⟩, ?_⟩
  -- no joint explanation
  rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
  have hv₁b₁ : v₁ b₁ = 1 := by
    have h := (hag b₁ (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ b₁⟩)).2
    rw [show ind2 (F := F) b₁ b₂ b₁ = 1 from if_pos (Or.inl rfl)] at h
    exact h
  have hv₁b₂ : v₁ b₂ = 1 := by
    have h := (hag b₂ (Finset.mem_erase.mpr ⟨hj2.symm, Finset.mem_univ b₂⟩)).2
    rw [show ind2 (F := F) b₁ b₂ b₂ = 1 from if_pos (Or.inr rfl)] at h
    exact h
  have hv₁T : ∀ i ∈ Tset j b₁ b₂, v₁ i = 0 := by
    intro i hiT
    obtain ⟨h2, h1, hij⟩ := mem_Tset.mp hiT
    have h := (hag i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)).2
    rw [show ind2 (F := F) b₁ b₂ i = 0 from if_neg (by
      rintro (h' | h')
      · exact h1 h'
      · exact h2 h')] at h
    exact h
  -- W := Z(b₁)•v₁ − Z vanishes on T_j ∪ {b₁} (n−2 points) ⟹ zero
  set W : ι → F := Z b₁ • v₁ - Z with hW
  have hWmem : W ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hv₁) hZmem
  have hWvan : ∀ i ∈ insert b₁ (Tset j b₁ b₂), W i = 0 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hiT
    · simp only [hW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv₁b₁, mul_one, sub_self]
    · have h1 := hv₁T i hiT
      have h2 : Z i = 0 := vanishWord_eq_zero domain hiT
      simp only [hW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, mul_zero, h2,
        sub_zero]
  have hWcard : Fintype.card ι - 2 ≤ (insert b₁ (Tset j b₁ b₂)).card := by
    rw [Finset.card_insert_of_notMem hb1T, hTcard]
    omega
  have hWzero : W = 0 := rs_vanish_forced_zero domain hWmem hWcard hWvan
  have hWb₂ := congrFun hWzero b₂
  simp only [hW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv₁b₂, mul_one,
    Pi.zero_apply, sub_eq_zero] at hWb₂
  exact hnd hWb₂.symm

end PerPoint

/-! ## Distinctness -/

section Distinct

variable (domain : ι ↪ F) {b₁ b₂ : ι}

/-- Two codewords agreeing on `≥ k` coordinates are equal. -/
theorem rs_eq_of_agree {k : ℕ} {v w : ι → F}
    (hv : v ∈ ReedSolomon.code domain k) (hw : w ∈ ReedSolomon.code domain k)
    {T : Finset ι} (hT : k ≤ T.card) (hag : ∀ i ∈ T, v i = w i) : v = w := by
  have hzero : v - w = 0 := rs_vanish_forced_zero domain
    (Submodule.sub_mem _ hv hw) hT (by
      intro i hi
      simp [hag i hi])
  funext i
  have h := congrFun hzero i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
  exact h

/-- If two distinct scalars are bad on the indicator stack, no scalar's line point is
`univ`-close: closeness on `univ` would (via the nesting collapse) identify every bad
scalar with it. -/
theorem no_univ_closeness_of_two_bad (hb : b₁ ≠ b₂)
    {γ γ' γu : F} (hne : γ ≠ γ')
    (hγ : mcaEvent (F := F)
      (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0)) (ind1 b₂) (ind2 b₁ b₂) γ)
    (hγ' : mcaEvent (F := F)
      (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0)) (ind1 b₂) (ind2 b₁ b₂) γ')
    (hu : ∃ w ∈ ReedSolomon.code domain (Fintype.card ι - 2),
      ∀ i, w i = ind1 b₂ i + γu • ind2 b₁ b₂ i) :
    False := by
  obtain ⟨S, hcard, hline, hno⟩ := hγ
  obtain ⟨S', hcard', hline', hno'⟩ := hγ'
  obtain ⟨w, hw, hagw⟩ := hu
  have h1 : γ = γu := bad_scalar_eq_of_witness_subset
    (ReedSolomon.code domain (Fintype.card ι - 2)) (Finset.subset_univ S) hline hno
    ⟨w, hw, fun i _ => hagw i⟩
  have h2 : γ' = γu := bad_scalar_eq_of_witness_subset
    (ReedSolomon.code domain (Fintype.card ι - 2)) (Finset.subset_univ S') hline' hno'
    ⟨w, hw, fun i _ => hagw i⟩
  exact hne (h1.trans h2.symm)

/-- **Pairwise distinctness of the per-point scalars.** Equal scalars at distinct third
points would merge the two explicit witnesses into `univ`-closeness, collapsing the bad
set — contradicting `0` and `−1` both bad. -/
theorem gammaOf_injOn (hn : 4 ≤ Fintype.card ι) (hb : b₁ ≠ b₂)
    {j j' : ι} (hj1 : j ≠ b₁) (hj2 : j ≠ b₂) (hj1' : j' ≠ b₁) (hj2' : j' ≠ b₂)
    (hjj : j ≠ j')
    (hnd : vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁)
    (hnd' : vanishWord domain (Tset j' b₁ b₂) b₂
      ≠ vanishWord domain (Tset j' b₁ b₂) b₁) :
    gammaOf domain b₁ b₂ j ≠ gammaOf domain b₁ b₂ j' := by
  intro hcon
  set γ := gammaOf domain b₁ b₂ j with hγdef
  -- both explicit witness codewords match the SAME line on their erased sets
  have hag := perPoint_agree domain hb hj1 hj2 hnd
  have hag' := perPoint_agree domain hb hj1' hj2' hnd'
  rw [← hcon] at hag'
  -- they agree on univ ∖ {j, j'} (n−2 ≥ k points) ⟹ equal codewords
  have hTj : (Tset j b₁ b₂).card = Fintype.card ι - 3 := Tset_card hb hj1 hj2
  have hZmem : vanishWord domain (Tset j b₁ b₂)
      ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    vanishWord_mem_code domain (by omega)
  have hTj' : (Tset j' b₁ b₂).card = Fintype.card ι - 3 := Tset_card hb hj1' hj2'
  have hZmem' : vanishWord domain (Tset j' b₁ b₂)
      ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    vanishWord_mem_code domain (by omega)
  have hwmem : wOf domain b₁ b₂ j ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    Submodule.smul_mem _ _ hZmem
  have hwmem' : wOf domain b₁ b₂ j' ∈ ReedSolomon.code domain (Fintype.card ι - 2) :=
    Submodule.smul_mem _ _ hZmem'
  have hcommon : Fintype.card ι - 2 ≤ ((Finset.univ.erase j).erase j').card := by
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hjj.symm, Finset.mem_univ j'⟩),
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
    omega
  have hww : wOf domain b₁ b₂ j = wOf domain b₁ b₂ j' := by
    apply rs_eq_of_agree domain hwmem hwmem' hcommon
    intro i hi
    have hi' : i ∈ Finset.univ.erase j' := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hi).1, Finset.mem_univ i⟩
    have hi'' : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
    rw [hag i hi'', hag' i hi']
  -- the merged codeword matches the line on all of univ
  have hall : ∀ i, wOf domain b₁ b₂ j i = ind1 b₂ i + γ • ind2 b₁ b₂ i := by
    intro i
    by_cases hij : i = j
    · subst hij
      have hij' : i ∈ Finset.univ.erase j' := Finset.mem_erase.mpr
        ⟨hjj, Finset.mem_univ i⟩
      rw [hww]
      exact hag' i hij'
    · exact hag i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  -- univ-closeness collapses the bad set, contradicting 0 ≠ −1 both bad
  exact no_univ_closeness_of_two_bad domain hb
    (show (0 : F) ≠ -1 from fun h => one_ne_zero (by linear_combination h))
    (mcaEvent_highRate_zero domain le_rfl hb)
    (mcaEvent_highRate_negOne domain le_rfl hb)
    ⟨wOf domain b₁ b₂ j, hwmem, hall⟩

/-- The per-point scalars avoid `{0, −1}`. -/
theorem gammaOf_ne_zero_negOne {j : ι} (hj1 : j ≠ b₁) (hj2 : j ≠ b₂)
    (hnd : vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁) :
    gammaOf domain b₁ b₂ j ≠ 0 ∧ gammaOf domain b₁ b₂ j ≠ -1 := by
  have hb1T : b₁ ∉ Tset j b₁ b₂ := fun h => (mem_Tset.mp h).2.1 rfl
  have hb2T : b₂ ∉ Tset j b₁ b₂ := fun h => (mem_Tset.mp h).1 rfl
  have hZb1 : vanishWord domain (Tset j b₁ b₂) b₁ ≠ 0 := vanishWord_ne_zero domain hb1T
  have hZb2 : vanishWord domain (Tset j b₁ b₂) b₂ ≠ 0 := vanishWord_ne_zero domain hb2T
  have hD : vanishWord domain (Tset j b₁ b₂) b₂
      - vanishWord domain (Tset j b₁ b₂) b₁ ≠ 0 := sub_ne_zero.mpr hnd
  constructor
  · exact div_ne_zero hZb1 hD
  · intro hcon
    rw [gammaOf, div_eq_iff hD] at hcon
    apply hZb2
    linear_combination hcon

end Distinct

/-! ## The exact jump value -/

open Classical in
/-- **THE EXACT JUMP VALUE (conditional form).** If `Z_j(b₂) ≠ Z_j(b₁)` at every third
point `j`, then

  `ε_mca(RS[F, D, n−2], 1/n) = n/q`  **exactly**.

Lower: the `n`-element bad set `{0, −1} ∪ {γ_j : j ∉ {b₁,b₂}}`; upper: the antichain
engine. The flat-`n` law, both halves. -/
theorem epsMCA_rs_jump_eq (domain : ι ↪ F) (hn : 4 ≤ Fintype.card ι)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂)
    (hnd : ∀ j, j ≠ b₁ → j ≠ b₂ →
      vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
        (1 / (Fintype.card ι : ℝ≥0))
      = ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm
    (epsMCA_le_card_div_at_granularity (ReedSolomon.code domain (Fintype.card ι - 2)))
    ?_
  -- the n-element bad set
  set J : Finset ι := (Finset.univ.erase b₁).erase b₂ with hJ
  have hJcard : J.card = Fintype.card ι - 2 := by
    rw [hJ, Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ b₂⟩),
      Finset.card_erase_of_mem (Finset.mem_univ b₁), Finset.card_univ]
    omega
  have hmemJ : ∀ j ∈ J, j ≠ b₁ ∧ j ≠ b₂ := by
    intro j hj
    rw [hJ, Finset.mem_erase, Finset.mem_erase] at hj
    exact ⟨hj.2.1, hj.1⟩
  set G : Finset F := insert 0 (insert (-1) (J.image (gammaOf domain b₁ b₂))) with hG
  have hGcard : G.card = Fintype.card ι := by
    have himg : (J.image (gammaOf domain b₁ b₂)).card = Fintype.card ι - 2 := by
      rw [← hJcard]
      apply Finset.card_image_of_injOn
      intro j hj j' hj' hcon
      by_contra hjj
      obtain ⟨hj1, hj2⟩ := hmemJ j (Finset.mem_coe.mp hj)
      obtain ⟨hj1', hj2'⟩ := hmemJ j' (Finset.mem_coe.mp hj')
      exact gammaOf_injOn domain hn hb hj1 hj2 hj1' hj2' hjj
        (hnd j hj1 hj2) (hnd j' hj1' hj2') hcon
    have hneg_notin : (-1 : F) ∉ J.image (gammaOf domain b₁ b₂) := by
      rw [Finset.mem_image]
      rintro ⟨j, hj, hje⟩
      obtain ⟨hj1, hj2⟩ := hmemJ j hj
      exact (gammaOf_ne_zero_negOne domain hj1 hj2 (hnd j hj1 hj2)).2 hje
    have hzero_notin : (0 : F) ∉ insert (-1) (J.image (gammaOf domain b₁ b₂)) := by
      rw [Finset.mem_insert]
      rintro (h | h)
      · exact one_ne_zero (by linear_combination h)
      · rw [Finset.mem_image] at h
        obtain ⟨j, hj, hje⟩ := h
        obtain ⟨hj1, hj2⟩ := hmemJ j hj
        exact (gammaOf_ne_zero_negOne domain hj1 hj2 (hnd j hj1 hj2)).1 hje
    rw [hG, Finset.card_insert_of_notMem hzero_notin,
      Finset.card_insert_of_notMem hneg_notin, himg]
    omega
  -- every member of G is bad
  have hGbad : ∀ γ ∈ G, mcaEvent (F := F)
      (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0))
      ((indStack b₁ b₂ : WordStack F (Fin 2) ι) 0) (indStack b₁ b₂ 1) γ := by
    have h0 : (indStack (F := F) b₁ b₂) 0 = ind1 b₂ := rfl
    have h1 : (indStack (F := F) b₁ b₂) 1 = ind2 b₁ b₂ := by
      show (if (1 : Fin 2) = 0 then ind1 b₂ else ind2 b₁ b₂) = ind2 b₁ b₂
      norm_num
    intro γ hγ
    rw [h0, h1]
    rw [hG, Finset.mem_insert, Finset.mem_insert] at hγ
    rcases hγ with rfl | rfl | hγ
    · exact mcaEvent_highRate_zero domain le_rfl hb
    · exact mcaEvent_highRate_negOne domain le_rfl hb
    · rw [Finset.mem_image] at hγ
      obtain ⟨j, hj, rfl⟩ := hγ
      obtain ⟨hj1, hj2⟩ := hmemJ j hj
      exact mcaEvent_perPoint domain hn hb hj1 hj2 (hnd j hj1 hj2)
  -- assemble through the witness-spread engine
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F) (A := F)
    (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
    (1 / (Fintype.card ι : ℝ≥0)) (indStack b₁ b₂) G hGbad
  rwa [hGcard] at h

/-! ## Source audit -/

#print axioms vanishWord_mem_code
#print axioms perPoint_agree
#print axioms mcaEvent_perPoint
#print axioms gammaOf_injOn
#print axioms gammaOf_ne_zero_negOne
#print axioms epsMCA_rs_jump_eq

end ProximityGap.MCAJumpValueExact
