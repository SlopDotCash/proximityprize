/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw
-/

import ArkLib.ToMathlib.L46DiffStackRS

/-!
# The GS witness for Reed–Solomon codes: `GSWitnessLowerBound` constructed

This file **constructs** the BCIKS20 Prop 1.1-style witness `L46GS.GSWitnessLowerBound` for
Reed–Solomon codes, closing the single named residual that the ABF26 Lemma 4.6 hard-direction
chain (`L46GSLowerBound.lean` + `L46DiffStackRS.lean`) terminates at. With the witness in hand,
both `diffStackMCAResidualBelowUDR (ReedSolomon.code domain deg) δ` and the full L4.6 collapse
`ε_mca = ε_ca` below the unique-decoding radius become **unconditional** theorems for RS codes,
with one explicit arithmetic hypothesis

  `hub : deg + 2·⌊δ·n⌋ < n`   (`n = |ι|`)

— the strict-by-one-unit form of the unique-decoding regime `2·δ·n < n − deg + 1` (and `hub` in
fact *implies* that UDR inequality, since `2·δ·n < 2·(⌊δ·n⌋ + 1) ≤ n − deg + 1`).

## The construction (`gsWitnessLowerBound_rs_holds`)

Set `m := ⌊δ·n⌋`. Choose `m + 1` distinct evaluation points `e 0, …, e m ∈ ι` (possible since
`2m < n` forces `m + 1 ≤ n`) and `m` distinct combiners `g 0, …, g (m−1) ∈ F` (possible since
`m < n ≤ |F|` via the domain embedding). Define the stack `u = (w₀, w₁)`:

* `w₁ := 𝟙_{e 0, …, e m}` — the indicator of the `m + 1` support points;
* `w₀ := −(g j)` at `e j` for `j < m`, and `0` elsewhere (the last point `e m` is left unpaired).

**Lines are close.** For `γ = g j` the line `w₀ + γ·w₁` vanishes off the support (both rows are
zero there) *and* at the paired point `e j` (where it is `−g j + g j·1 = 0`), so its support has
size `≤ (m+1) − 1 = m = ⌊δ·n⌋`: the line is `δ`-close to the codeword `0 ∈ RS`. Each of the `m`
distinct combiners is good.

**The stack is jointly far.** Suppose an interleaved codeword `V` agreed with `(w₀, w₁)`
column-wise on a set `S` with `|S| ≥ n − m`. Row 1 of `V` is `evalOnPoints domain q` with
`deg q < deg`. On `S` minus the `m + 1` support points — at least `n − m − (m+1) = n − 2m − 1 ≥
deg` points by `hub` — the row-1 agreement forces `q` to vanish, so `q = 0`
(`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`). But then row-1 agreement reads
`w₁ = 0` on `S`, while `w₁ = 1` on the whole support: `S` must avoid all `m + 1` support points,
giving `|S| ≤ n − (m+1) < n − m ≤ |S|` — a contradiction. This is why the support has `m + 1`
points and not `m`: the extra unpaired point is exactly what pushes the stack past the `⌊δ·n⌋`
joint-disagreement budget while each *individual* line still cancels its paired point back down
to `m`.

This is the affine-line case of [BCIKS20, Prop 1.1]: the "one good `γ` per close codeword"
structure realised by an explicit `m`-combiner pencil through `m + 1` deep-hole coordinates.

## Deliverables

* `gsWitnessLowerBound_rs_holds` — **the witness, constructed** (axiom-clean): for any RS code
  with `deg + 2·⌊δ·n⌋ < n`, `GSWitnessLowerBound (RS[domain, deg]) δ ⌊δ·n⌋` holds.
* `two_mul_lt_card_sub_of_floor_lt` — `hub` implies the numeric UDR form
  `2·δ·n < (n − deg + 1 : ℕ)`.
* `diffStackMCAResidualBelowUDR_rs_unconditional` — the `Errors.lean` difference-stack residual
  for RS codes, **with no GS-witness hypothesis left** (only `hub`).
* `epsMCA_eq_epsCA_below_udr_rs_unconditional` — ABF26 Lemma 4.6 for Reed–Solomon, `ε_mca = ε_ca`
  below UDR, **unconditional** modulo the explicit arithmetic regime `hub`.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
  Proposition 1.1 (tightness of the unique-decoding-regime error `⌊δ·n⌋/|F|`).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial
open scoped ProbabilityTheory BigOperators

namespace L46GS

section

-- Same universe/instance discipline as `ProximityGap.Errors` (PMF forces `Type 0`).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The GS witness for Reed–Solomon codes (CONSTRUCTED).**

For `C = RS[domain, deg]` with `deg + 2·⌊δ·n⌋ < n`, the BCIKS20 Prop 1.1-style witness
`GSWitnessLowerBound C δ ⌊δ·n⌋` holds: there is a word stack that is *not* jointly `δ`-close to
`C` together with `⌊δ·n⌋` distinct combiners at each of which the line is `δ`-close to `C`.

The witness is the `(m+1)`-point pencil (`m := ⌊δ·n⌋`): row 1 is the indicator of `m + 1`
distinct evaluation points, row 0 carries `−γ_j` at the `j`-th point for `m` distinct combiners
`γ_j`, so each line `w₀ + γ_j·w₁` cancels its paired point (support `≤ m`, hence `δ`-close to
`0`), while the stack itself disagrees column-wise with *every* codeword pair on all `m + 1`
support points (a degree-`< deg` polynomial matching row 1 on `n − 2m − 1 ≥ deg` off-support
agreement points must vanish, and then `S` must avoid the entire support). -/
theorem gsWitnessLowerBound_rs_holds (domain : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hub : deg + 2 * Nat.floor (δ * (Fintype.card ι : ℝ≥0)) < Fintype.card ι) :
    GSWitnessLowerBound (F := F)
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0))) := by
  classical
  have hm1n : Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1 ≤ Fintype.card ι := by omega
  have hmF : Nat.floor (δ * (Fintype.card ι : ℝ≥0)) ≤ Fintype.card F :=
    le_trans (by omega) (Fintype.card_le_of_embedding domain)
  -- The (m+1)-point support and the m distinct combiners.
  obtain ⟨e⟩ : Nonempty (Fin (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1) ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm1n)
  obtain ⟨g⟩ : Nonempty (Fin (Nat.floor (δ * (Fintype.card ι : ℝ≥0))) ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hmF)
  -- The witness rows: `w₁ = 𝟙_{range e}`, `w₀ = −(g j)` at `e j.castSucc` (last point unpaired).
  set w0 : ι → F :=
    Function.extend (fun j : Fin (Nat.floor (δ * (Fintype.card ι : ℝ≥0))) => e j.castSucc)
      (fun j => -(g j)) 0 with hw0def
  set w1 : ι → F :=
    Function.extend (fun j : Fin (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1) => e j)
      (fun _ => (1 : F)) 0 with hw1def
  have hinj0 : Function.Injective
      (fun j : Fin (Nat.floor (δ * (Fintype.card ι : ℝ≥0))) => e j.castSucc) :=
    fun a b hab => Fin.castSucc_injective _ (e.injective hab)
  have hw0_at : ∀ j, w0 (e j.castSucc) = -(g j) := fun j => hinj0.extend_apply _ _ j
  have hw1_at : ∀ j, w1 (e j) = 1 := fun j => e.injective.extend_apply _ _ j
  have hw0_off : ∀ i : ι, (∀ j, e j ≠ i) → w0 i = 0 := by
    intro i hi
    rw [hw0def, Function.extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi j.castSucc rfl)]
    rfl
  have hw1_off : ∀ i : ι, (∀ j, e j ≠ i) → w1 i = 0 := by
    intro i hi
    rw [hw1def, Function.extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi j rfl)]
    rfl
  refine ⟨![w0, w1], (Finset.univ).image g, ?_, ?_, ?_⟩
  · -- ¬ jointProximity: the stack is far from every interleaved codeword.
    rw [jointProximity]
    intro hclose
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hclose
    obtain ⟨V, hVmem, hVdist⟩ := hclose
    rw [relCloseToWord_iff_exists_agreementCols] at hVdist
    obtain ⟨S, hScard, hSagree⟩ := hVdist
    -- Row 1 of the stack agrees with `V`'s column 1 on `S`.
    have hrow1 : ∀ i ∈ S, w1 i = V i 1 := by
      intro i hiS
      have hcol := (hSagree i).1 hiS
      have := congrFun hcol 1
      simpa [interleave_wordStack_eq, Matrix.transpose_apply] using this
    -- `V`'s column 1 is an RS codeword: an evaluated polynomial of degree `< deg`.
    have hq1mem : (Matrix.transpose V 1) ∈ ReedSolomon.code domain deg := hVmem 1
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hq1mem
    obtain ⟨q, hqdeg, hqeval⟩ := hq1mem
    have hVeval : ∀ i : ι, V i 1 = q.eval (domain i) := by
      intro i
      have hT1 : Matrix.transpose V 1 i = q.eval (domain i) := by
        rw [hqeval]; simp [ReedSolomon.evalOnPoints]
      simpa [Matrix.transpose_apply] using hT1
    -- `q` vanishes on the (large) part of `S` off the support.
    have hTcard : ((Finset.univ).image e).card
        = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1 := by
      rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]
    have hS'card : Fintype.card ι - (2 * Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1)
        ≤ (S \ (Finset.univ).image e).card := by
      have h1 := Finset.le_card_sdiff ((Finset.univ).image e) S
      omega
    have hvanish : ∀ x ∈ (S \ (Finset.univ).image e).image domain, q.eval x = 0 := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hiS', rfl⟩ := hx
      have hiS : i ∈ S := (Finset.mem_sdiff.mp hiS').1
      have hiT : i ∉ (Finset.univ).image e := (Finset.mem_sdiff.mp hiS').2
      have hoff : ∀ j, e j ≠ i := by
        intro j hj
        exact hiT (hj ▸ Finset.mem_image_of_mem e (Finset.mem_univ j))
      have h0 : w1 i = 0 := hw1_off i hoff
      have := hrow1 i hiS
      rw [h0] at this
      rw [← hVeval i, ← this]
    have hq0 : q = 0 := by
      by_cases hq : q = 0
      · exact hq
      · refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q
          ((S \ (Finset.univ).image e).image domain) hvanish ?_
        have himg : ((S \ (Finset.univ).image e).image domain).card
            = (S \ (Finset.univ).image e).card :=
          Finset.card_image_of_injective _ domain.injective
        have hdeg' : q.natDegree < deg := by
          rwa [Polynomial.natDegree_lt_iff_degree_lt hq]
        omega
    -- But row 1 equals `1` on the whole support, which `S` must therefore avoid entirely…
    have hST : ∀ i ∈ (Finset.univ).image e, i ∉ S := by
      intro i hiT hiS
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hiT
      have h1 : (1 : F) = V (e j) 1 := (hw1_at j) ▸ hrow1 (e j) hiS
      rw [hVeval (e j), hq0] at h1
      simp at h1
    -- …making `S` too small: `|S| ≤ n − (m+1) < n − m ≤ |S|`.
    have hdisj : Disjoint S ((Finset.univ).image e) :=
      Finset.disjoint_right.mpr hST
    have hcardle : S.card + ((Finset.univ).image e).card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]
      simpa using Finset.card_le_card
        (Finset.subset_univ (S ∪ (Finset.univ).image e))
    omega
  · -- `|Γ| ≥ m`: the `m` combiners are distinct.
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
  · -- Every `γ = g j` makes the line `δ`-close to the code (to the codeword `0`).
    intro γ hγ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hγ
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
    refine ⟨0, SetLike.mem_coe.mpr (Submodule.zero_mem _), ?_⟩
    rw [relCloseToWord_iff_exists_possibleDisagreeCols]
    -- Possible-disagreement set: the support minus the paired point `e j.castSucc`.
    refine ⟨((Finset.univ).image e).erase (e j.castSucc), ?_, ?_⟩
    · have hTcard : ((Finset.univ).image e).card
          = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1 := by
        rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]
      have := Finset.card_erase_of_mem
        (Finset.mem_image_of_mem e (Finset.mem_univ j.castSucc))
      omega
    · intro i hi
      show (![w0, w1] 0 + g j • ![w0, w1] 1) i = (0 : ι → F) i
      by_cases hrange : ∃ j' : Fin _, e j' = i
      · -- On the support, only the paired point can be outside the disagreement set,
        -- and there the line cancels: `−g j + g j · 1 = 0`.
        obtain ⟨j', rfl⟩ := hrange
        have hj' : j' = j.castSucc := by
          by_contra hne
          exact hi (Finset.mem_erase.mpr
            ⟨fun h => hne (e.injective h), Finset.mem_image_of_mem e (Finset.mem_univ j')⟩)
        subst hj'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [hw0_at j, hw1_at j.castSucc, mul_one, neg_add_cancel]
      · -- Off the support both rows vanish.
        push Not at hrange
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [hw0_off i hrange, hw1_off i hrange, mul_zero, add_zero]

/-- The arithmetic regime `deg + 2·⌊δ·n⌋ < n` implies the numeric unique-decoding-radius
inequality `2·δ·n < (n − deg + 1 : ℕ)` (the RS-distance form of UDR), since
`2·δ·n < 2·(⌊δ·n⌋ + 1) ≤ n − deg + 1`. -/
theorem two_mul_lt_card_sub_of_floor_lt {deg : ℕ} (δ : ℝ≥0)
    (hub : deg + 2 * Nat.floor (δ * (Fintype.card ι : ℝ≥0)) < Fintype.card ι) :
    2 * δ * (Fintype.card ι : ℝ≥0) < ((Fintype.card ι - deg + 1 : ℕ) : ℝ≥0) := by
  have hfloor : δ * (Fintype.card ι : ℝ≥0) <
      ((Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.lt_floor_add_one (δ * (Fintype.card ι : ℝ≥0))
  calc 2 * δ * (Fintype.card ι : ℝ≥0)
      = 2 * (δ * (Fintype.card ι : ℝ≥0)) := by ring
    _ < 2 * ((Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1 : ℕ) : ℝ≥0) := by
        exact mul_lt_mul_of_pos_left hfloor two_pos
    _ = ((2 * (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1) : ℕ) : ℝ≥0) := by
        push_cast; ring
    _ ≤ ((Fintype.card ι - deg + 1 : ℕ) : ℝ≥0) := by
        have hnat : 2 * (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) + 1)
            ≤ Fintype.card ι - deg + 1 := by omega
        exact Nat.cast_le.mpr hnat

/-- **The `Errors.lean` difference-stack residual, discharged for Reed–Solomon codes
(UNCONDITIONAL).** The only hypothesis is the explicit arithmetic regime
`deg + 2·⌊δ·n⌋ < n` (strict-by-one unique decoding); the GS witness is *constructed*
(`gsWitnessLowerBound_rs_holds`), no named-Prop input remains. -/
theorem diffStackMCAResidualBelowUDR_rs_unconditional {deg : ℕ} [NeZero deg]
    (domain : ι ↪ F) (δ : ℝ≥0)
    (hub : deg + 2 * Nat.floor (δ * (Fintype.card ι : ℝ≥0)) < Fintype.card ι) :
    diffStackMCAResidualBelowUDR (F := F) (A := F) (ReedSolomon.code domain deg) δ :=
  diffStackMCAResidualBelowUDR_rs_of_two_mul_lt_card_sub domain (by omega) δ
    (two_mul_lt_card_sub_of_floor_lt δ hub)
    (gsWitnessLowerBound_rs_holds domain deg δ hub)

/-- **ABF26 Lemma 4.6 for Reed–Solomon codes (UNCONDITIONAL).** Below the unique-decoding radius
(in the strict-by-one form `deg + 2·⌊δ·n⌋ < n`), `ε_mca = ε_ca` for `RS[domain, deg]` — with the
GS witness constructed, no hypothesis beyond the arithmetic regime remains. -/
theorem epsMCA_eq_epsCA_below_udr_rs_unconditional {deg : ℕ} [NeZero deg]
    (domain : ι ↪ F) (δ : ℝ≥0)
    (hub : deg + 2 * Nat.floor (δ * (Fintype.card ι : ℝ≥0)) < Fintype.card ι) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ =
      epsCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ δ :=
  epsMCA_eq_epsCA_below_udr_rs_of_two_mul_lt_card_sub domain (by omega) δ
    (two_mul_lt_card_sub_of_floor_lt δ hub)
    (gsWitnessLowerBound_rs_holds domain deg δ hub)

end

end L46GS

end ProximityGap

#print axioms ProximityGap.L46GS.gsWitnessLowerBound_rs_holds
#print axioms ProximityGap.L46GS.two_mul_lt_card_sub_of_floor_lt
#print axioms ProximityGap.L46GS.diffStackMCAResidualBelowUDR_rs_unconditional
#print axioms ProximityGap.L46GS.epsMCA_eq_epsCA_below_udr_rs_unconditional
