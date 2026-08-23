/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GK16FrsTransport

/-!
# Deriving the FRS subspace-design side conditions from `Admissible`

ABF26 Theorem 2.18 (FRS half) is proven in `frs_is_subspaceDesign_gk16_of_injective`
(`SubspaceDesign.lean`) from two side conditions on the folding element `ω`:

* `hEinj` — injectivity of the FRS encoder `frsEvalOnPoints domain s ω`, and
* `hω_sep` — the GK16 Lemma-12 degree-separation property.

This file derives the *genuinely-true* forms of both from the standard
`ReedSolomon.Folded.Admissible L s ω` structure together with the genuinely-minimal
arithmetic side conditions, and assembles the bounded budget that the FRS subspace-design
profile actually consumes.

## Statement-bug found (F-class), kernel-refuted

The literal hypothesis `hEinj : Function.Injective (frsEvalOnPoints domain s ω)` over the
**whole** polynomial ring `F[X]` is **unconditionally false**: the source `F[X]` is
infinite-dimensional and the target `ι → Fin s → F` is finite-dimensional, so the kernel is
never trivial (the product `∏_{x,j} (X − domain x · ω^j)` is a nonzero kernel element).
This is recorded as `ReedSolomon.Folded.frsEvalOnPoints_not_injective`.

The mathematically correct and useful statement is injectivity **restricted to the
degree-`<k` polynomials**, which holds under `Admissible` plus `k ≤ s · |ι|` (enough
distinct fold points). This is `ReedSolomon.Folded.frsEvalOnPoints_injOn_degreeLT`.

Likewise the literal `hω_sep` quantifying over *arbitrary-degree* families is false in any
finite field (take degrees `0` and `orderOf ω`: then `ω^0 = ω^(orderOf ω) = 1`). The
genuinely-true, and the only one the consumer needs, is the bounded version
`pow_natDegree_injective_of_lt_orderOf`: degree separation for families whose degrees stay
below `orderOf ω`, which under `k ≤ orderOf ω` covers all the recombinations the budget
engine produces (their degrees are `< k`).

## Main results

* `ReedSolomon.Folded.mulPow_injective_of_admissible` — `Admissible` (+ `ω ≠ 0`) makes the
  fold-point map `(x, j) ↦ domain x · ω^j` injective on `ι × Fin s`.
* `ReedSolomon.Folded.frsEvalOnPoints_injOn_degreeLT` — restricted encoder injectivity.
* `ReedSolomon.Folded.pow_natDegree_injective_of_lt_orderOf` — bounded degree separation.
* `ReedSolomon.Folded.frs_degreeBudget_of_finrank_le_admissible` — the GK16 §4 budget on the
  `finrank A ≤ s` range, from `Admissible` + `k ≤ s·|ι|` + `k ≤ orderOf ω`.

The final subspace-design assembly `frs_is_subspaceDesign_gk16_of_admissible` lives in
`SubspaceDesign.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Polynomial Module

namespace ReedSolomon.Folded

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-! ## The full-encoder injectivity statement is false (kernel-refutation) -/

/-- **F-class statement bug, kernel-refuted.** The FRS encoder is *not* injective on the
whole polynomial ring: `F[X]` is infinite-dimensional, the target is finite-dimensional,
so the vanishing polynomial over the (finitely many) fold points is a nonzero kernel
element. The genuinely-true statement is injectivity restricted to `degreeLT F k`, below. -/
theorem frsEvalOnPoints_not_injective [Nonempty ι]
    (domain : ι ↪ F) (s : ℕ) (ω : F) :
    ¬ Function.Injective (frsEvalOnPoints domain s ω) := by
  classical
  intro hinj
  set pts : Finset F :=
    Finset.image (fun q : ι × Fin s => domain q.1 * ω ^ (q.2 : ℕ)) Finset.univ with hpts
  set v : Polynomial F := ∏ a ∈ pts, (X - C a) with hv
  have hv_ne : v ≠ 0 := by
    rw [hv]
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)
  have hv_eval : ∀ (x : ι) (j : Fin s), v.eval (domain x * ω ^ (j : ℕ)) = 0 := by
    intro x j
    have hmem : domain x * ω ^ (j : ℕ) ∈ pts := by
      rw [hpts]
      exact Finset.mem_image.mpr ⟨(x, j), Finset.mem_univ _, rfl⟩
    rw [hv, eval_prod]
    exact Finset.prod_eq_zero hmem (by simp)
  have h0 : frsEvalOnPoints domain s ω v = frsEvalOnPoints domain s ω 0 := by
    rw [map_zero]; ext x j
    simp only [frsEvalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
    exact hv_eval x j
  exact hv_ne (hinj h0)

/-! ## Fold-point injectivity from `Admissible` -/

/-- **`Admissible` + `ω ≠ 0` ⟹ distinct fold points.** Under `(L, s)`-admissibility with
every `domain i ∈ L` *and* `ω ≠ 0`, the fold-point map
`(x, j) ↦ domain x · ω^j : ι × Fin s → F` is injective.

**Why `ω ≠ 0` is genuinely needed (F-class fix of the `Admissible` docstring).** The
docstring of `Admissible` claims its two conjuncts already make this map injective, but they
do **not**: with `ω = 0` and `s ≥ 2`, every fold index `j ≥ 1` sends *all* base points to
`0`, so the map collapses, yet `Admissible` can still hold (e.g. `L = {1,2} ⊆ GF 5`, `s = 2`,
`ω = 0` satisfies both conjuncts). The minimal repair is `ω ≠ 0`, which both restores the
cancellations below and is exactly the `orderOf ω > 0` regime used for `hω_sep`.

The proof: a coincidence `domain x · ω^i = domain y · ω^j` (wlog `i ≤ j`) cancels the
nonzero `ω^i`, giving `domain x = domain y · ω^{j-i}` with `j - i < s`. If `domain x ≠
domain y` this contradicts the inter-orbit clause (the intra clause first forces
`domain y ≠ 0`); if `domain x = domain y` it gives `domain x · ω^{j-i} = domain x` with
`0 < j - i < s`, contradicting the intra-orbit clause. -/
theorem mulPow_injective_of_admissible
    {domain : ι ↪ F} {s : ℕ} {ω : F} {L : Finset F}
    (hL : ∀ i : ι, domain i ∈ L) (hω0 : ω ≠ 0) (hadm : Admissible L s ω) :
    Function.Injective (fun q : ι × Fin s => domain q.1 * ω ^ (q.2 : ℕ)) := by
  obtain ⟨hinter, hintra⟩ := hadm
  -- A uniform "wlog `i ≤ j`" core: derive a contradiction (or equality) from
  -- `domain a · ω^p = domain b · ω^q` with `p ≤ q`.
  have core : ∀ (a b : ι) (p q : ℕ), p < s → q < s → p ≤ q →
      domain a * ω ^ p = domain b * ω ^ q → a = b ∧ p = q := by
    intro a b p q hp hq hpq heq
    -- cancel the nonzero factor `ω^p`.
    have hωp : ω ^ p ≠ 0 := pow_ne_zero _ hω0
    have hsplit : ω ^ q = ω ^ p * ω ^ (q - p) := by rw [← pow_add]; congr 1; omega
    rw [hsplit, ← mul_assoc, mul_comm (domain b) (ω ^ p), mul_assoc] at heq
    -- `heq : domain a * ω^p = ω^p * (domain b * ω^(q-p))`
    rw [mul_comm (domain a) (ω ^ p)] at heq
    have hcancel : domain a = domain b * ω ^ (q - p) := mul_left_cancel₀ hωp heq
    by_cases hab : domain a = domain b
    · -- same base point: must have `p = q`.
      have hab' : a = b := domain.injective hab
      refine ⟨hab', ?_⟩
      by_contra hpq'
      have hlt : p < q := lt_of_le_of_ne hpq hpq'
      -- `domain b * ω^(q-p) = domain b`, with `0 < q - p < s`.
      rw [hab] at hcancel
      exact hintra (domain b) (hL b) (q - p) (by omega) (by omega) hcancel.symm
    · -- distinct base points: contradicts the inter-orbit clause.
      exfalso
      have hd0 : q - p ≠ 0 := by
        intro h0; rw [h0, pow_zero, mul_one] at hcancel; exact hab hcancel
      -- `domain b * ω^(q-p) = domain a`, distinct, `0 < q-p < s`.
      exact hinter (domain b) (hL b) (domain a) (hL a)
        (fun h => hab h.symm) (q - p) (by omega) hcancel.symm
  rintro ⟨x, i⟩ ⟨y, j⟩ heq
  simp only at heq
  rcases le_total (i : ℕ) (j : ℕ) with hij | hij
  · obtain ⟨hxy, hij'⟩ := core x y i j i.2 j.2 hij heq
    rw [Prod.mk.injEq]; exact ⟨hxy, Fin.ext hij'⟩
  · obtain ⟨hxy, hij'⟩ := core y x j i j.2 i.2 hij heq.symm
    rw [Prod.mk.injEq]; exact ⟨hxy.symm, Fin.ext hij'.symm⟩

/-! ## Restricted-encoder injectivity (the genuinely-true `hEinj`) -/

/-- **`Admissible` + `ω ≠ 0` + `k ≤ s·|ι|` ⟹ the FRS encoder is injective on `degreeLT`.**
A degree-`< k` polynomial whose folded evaluations all vanish is zero: it vanishes on the
`s · |ι|` distinct fold points (distinct by `mulPow_injective_of_admissible`), and a nonzero
degree-`< k` polynomial has fewer than `k ≤ s·|ι|` roots.

Stated as injectivity of the domain-restricted map `frsEvalOnPoints.domRestrict
(degreeLT F k)` — the correct replacement for the (false) global-injectivity `hEinj`. -/
theorem frsEvalOnPoints_injOn_degreeLT
    {domain : ι ↪ F} {k s : ℕ} {ω : F} {L : Finset F}
    (hL : ∀ i : ι, domain i ∈ L) (hω0 : ω ≠ 0) (hadm : Admissible L s ω)
    (hk : k ≤ s * Fintype.card ι) :
    Function.Injective
      ((frsEvalOnPoints domain s ω).domRestrict (Polynomial.degreeLT F k)) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  rintro ⟨p, hp_mem⟩ hp_ker
  rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hp_ker
  -- `p` vanishes on every fold point.
  have heval : ∀ q : ι × Fin s, p.eval (domain q.1 * ω ^ (q.2 : ℕ)) = 0 := by
    intro q
    have := congrFun (congrFun hp_ker q.1) q.2
    simpa [frsEvalOnPoints] using this
  -- the fold-point map is injective, with `Fintype.card (ι × Fin s) = s · |ι|`.
  have hinj := mulPow_injective_of_admissible (domain := domain) (s := s) (ω := ω) hL hω0 hadm
  have hcard : Fintype.card (ι × Fin s) = s * Fintype.card ι := by
    rw [Fintype.card_prod, Fintype.card_fin]; ring
  -- bound the degree.
  have hp0 : p = 0 := by
    rcases eq_or_ne p 0 with h0 | h0
    · exact h0
    · -- `natDegree p < k ≤ s·|ι| = card (ι × Fin s)`.
      have hnd : p.natDegree < k := by
        have hdeg : p.degree < (k : WithBot ℕ) := (Polynomial.mem_degreeLT).mp hp_mem
        have : (p.natDegree : WithBot ℕ) < (k : WithBot ℕ) := by
          rwa [Polynomial.degree_eq_natDegree h0] at hdeg
        exact_mod_cast this
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj heval ?_
      rw [hcard]; omega
  exact Subtype.ext (by simpa using hp0)

/-! ## Bounded degree-separation (the genuinely-true `hω_sep`) -/

/-- **Bounded `hω_sep`.** For a family `Q` of polynomials each of degree `< orderOf ω`, with
distinct natDegrees, the values `ω ^ (Q j).natDegree` are distinct. This is the genuinely-true
core of the GK16 Lemma-12 degree-separation hypothesis.

The unbounded `hω_sep` (over arbitrary-degree families) is **false** in any finite field:
the family `{1, X^(orderOf ω)}` has distinct natDegrees `0 ≠ orderOf ω` yet
`ω^0 = ω^(orderOf ω) = 1`. The bound `(Q j).natDegree < orderOf ω` is exactly what makes the
power map injective (`pow_injOn_Iio_orderOf`). -/
theorem pow_natDegree_injective_of_lt_orderOf
    {n : ℕ} {ω : F} (Q : Fin n → Polynomial F)
    (hQ_lt : ∀ j, (Q j).natDegree < orderOf ω)
    (hQ_deg : Function.Injective (fun j => (Q j).natDegree)) :
    Function.Injective (fun j => ω ^ (Q j).natDegree) := by
  intro a b hab
  exact hQ_deg (pow_injOn_Iio_orderOf (hQ_lt a) (hQ_lt b) hab)

/-! ## InjOn finrank transport helper -/

/-- **Finrank is preserved under a map injective on a containing submodule.** If `E` is
injective on `T` (i.e. `E.domRestrict T` is injective) and `p ≤ T`, then
`finrank (p.map E) = finrank p`. This is the InjOn replacement for
`Submodule.equivMapOfInjective` (which needs *global* injectivity), used to transport the
FRS pullback/orbit-vanishing dimensions across the encoder, which is only injective on
`degreeLT F k`. -/
lemma finrank_map_eq_of_le_of_injOn {M M₂ : Type*}
    [AddCommGroup M] [Module F M] [AddCommGroup M₂] [Module F M₂]
    (E : M →ₗ[F] M₂) (T : Submodule F M)
    (hEinj : Function.Injective (E.domRestrict T))
    (p : Submodule F M) (hp : p ≤ T) :
    Module.finrank F (p.map E) = Module.finrank F p := by
  -- Transport across the restricted map, which IS injective.
  have hmap_eq : (p.comap T.subtype).map (E.domRestrict T) = p.map E := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.domRestrict_apply,
      Submodule.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨(z : M), hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hp hx⟩, by simpa using hx, rfl⟩
  have e := Submodule.equivMapOfInjective (E.domRestrict T) hEinj (p.comap T.subtype)
  calc Module.finrank F (p.map E)
      = Module.finrank F ((p.comap T.subtype).map (E.domRestrict T)) := by rw [hmap_eq]
    _ = Module.finrank F (p.comap T.subtype) := e.finrank_eq.symm
    _ = Module.finrank F p := (Submodule.comapSubtypeEquivOfLe hp).finrank_eq

/-! ## InjOn-based pullback/orbit-vanishing finrank facts -/

variable {domain : ι ↪ F} {k s : ℕ} {ω : F}

/-- `finrank (frsPullback …) = finrank A`, from injectivity *on `degreeLT F k`* (the genuine
hypothesis), replacing the global-injectivity `finrank_frsPullback_eq`. -/
lemma finrank_frsPullback_eq_injOn {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective
      ((frsEvalOnPoints domain s ω).domRestrict (Polynomial.degreeLT F k)))
    (hA : A ≤ frsCode domain k s ω) :
    Module.finrank F (frsPullback domain k s ω A) = Module.finrank F A := by
  have hle : frsPullback domain k s ω A ≤ Polynomial.degreeLT F k := inf_le_right
  calc Module.finrank F (frsPullback domain k s ω A)
      = Module.finrank F ((frsPullback domain k s ω A).map (frsEvalOnPoints domain s ω)) :=
        (finrank_map_eq_of_le_of_injOn _ _ hEinj _ hle).symm
    _ = Module.finrank F A := by rw [frsPullback_map_eq hA]

/-- `finrank (frsVanish … i) = finrank (A ⊓ ker(proj i))`, from injectivity on `degreeLT`. -/
lemma finrank_frsVanish_eq_injOn {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective
      ((frsEvalOnPoints domain s ω).domRestrict (Polynomial.degreeLT F k)))
    (hA : A ≤ frsCode domain k s ω) (i : ι) :
    Module.finrank F (frsVanish domain k s ω A i) =
      Module.finrank F (↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := by
  have hle : frsVanish domain k s ω A i ≤ Polynomial.degreeLT F k :=
    le_trans (inf_le_left) (inf_le_right)
  calc Module.finrank F (frsVanish domain k s ω A i)
      = Module.finrank F ((frsVanish domain k s ω A i).map (frsEvalOnPoints domain s ω)) :=
        (finrank_map_eq_of_le_of_injOn _ _ hEinj _ hle).symm
    _ = Module.finrank F (↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := by
        rw [frsVanish_map_eq hA i]

/-- In a finite field, a nonzero element has positive multiplicative order. -/
lemma orderOf_pos_of_ne_zero [Fintype F] {ω : F} (hω0 : ω ≠ 0) : 0 < orderOf ω := by
  have : orderOf ω = orderOf (Units.mk0 ω hω0) := by
    rw [← orderOf_units]; rfl
  rw [this]
  exact orderOf_pos _

/-! ## Bounded GK16 Lemma 12 (hard direction) -/

/-- **GK16 Lemma 12, hard direction, with a degree bound (the genuinely-true form).** For a
linearly independent family `P` whose every degree is `< orderOf ω`, the folded Wronskian is
nonzero. This is `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent` with its
*unbounded* `hω_sep` replaced by the bounded degree-separation, which is the only true form
in a finite field: the distinct-degree recombination of `P` (Gaussian elimination on
degrees) only ever has degrees `≤ max P-degrees < orderOf ω`, so the bounded separation
suffices. -/
theorem foldedWronskian_ne_zero_of_linearIndependent_of_natDegree_lt
    {n : ℕ} (P : Fin n → Polynomial F) (ω : F)
    (hindep : LinearIndependent F P)
    (hP_lt : ∀ j, (P j).natDegree < orderOf ω) :
    ArkLib.FRS.GK16.foldedWronskian P ω ≠ 0 := by
  classical
  -- `n = 0`: the folded Wronskian is the determinant of the empty matrix, namely `1 ≠ 0`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp [ArkLib.FRS.GK16.foldedWronskian, Matrix.det_fin_zero]
  -- `n > 0`: extract `0 < orderOf ω` from any degree bound, then run the bounded engine.
  have horder : 0 < orderOf ω := lt_of_le_of_lt (Nat.zero_le _) (hP_lt ⟨0, hnpos⟩)
  obtain ⟨Q, c, hc_det, hQ_rec, hQ_ne, hQ_deg⟩ :=
    ArkLib.FRS.GK16.gk16Lemma12HardResidual_holds F _ n P hindep
  -- Each recombination `Q j = ∑ c j i • P i` has degree `≤ max P-degrees < orderOf ω`.
  have hQ_lt : ∀ j, (Q j).natDegree < orderOf ω := by
    intro j
    rw [hQ_rec j]
    have hbound : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (c j i • P i).natDegree ≤ orderOf ω - 1 := by
      intro i _
      refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
      have := hP_lt i; omega
    calc (∑ i, c j i • P i).natDegree
        ≤ orderOf ω - 1 :=
          Polynomial.natDegree_sum_le_of_forall_le _ _ hbound
      _ < orderOf ω := by omega
  -- Nonvanishing for the distinct-degree `Q`.
  have hQW : ArkLib.FRS.GK16.foldedWronskian Q ω ≠ 0 :=
    ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_distinct_natDegree Q ω hQ_ne
      (pow_natDegree_injective_of_lt_orderOf Q hQ_lt hQ_deg)
  -- Transfer along the change of basis.
  have hcb : ArkLib.FRS.GK16.foldedWronskian Q ω
      = Polynomial.C ((Matrix.of c).det) * ArkLib.FRS.GK16.foldedWronskian P ω := by
    rw [show Q = (fun j => ∑ i, c j i • P i) from funext hQ_rec]
    exact ArkLib.FRS.GK16.foldedWronskian_change_basis P ω c
  intro hPzero
  rw [hPzero, mul_zero] at hcb
  exact hQW hcb

/-! ## The GK16 §4 degree budget on the `finrank A ≤ s` range, from `Admissible` -/

/-- **Encoder-transport GK16 §4 budget, from `Admissible` only.** For `A ≤ frsCode` with
`finrank A ≤ s`, under `(L, s)`-admissibility (`domain i ∈ L`, `ω ≠ 0`), enough fold points
`k ≤ s·|ι|`, and degrees-below-order `k ≤ orderOf ω`, the per-coordinate vanishing dimensions
sum to at most `(finrank A)·(k-1)`:

  `∑_i dim (A ⊓ ker(eval_i)) ≤ (finrank A)·(k - 1)`.

This is `ReedSolomon.Folded.frs_degreeBudget_of_finrank_le` re-derived with the *genuine*
side conditions: the false global encoder-injectivity is replaced by injectivity on
`degreeLT F k` (`frsEvalOnPoints_injOn_degreeLT`), and the false unbounded `hω_sep` is
replaced by the bounded degree-separation (`pow_natDegree_injective_of_lt_orderOf`), valid
because every recombination of the realizing degree-`<k` family again has degree `< k ≤
orderOf ω`. -/
theorem frs_degreeBudget_of_finrank_le_admissible [Fintype F]
    (A : Submodule F (ι → Fin s → F)) {L : Finset F}
    (hL : ∀ i : ι, domain i ∈ L) (hω0 : ω ≠ 0) (hadm : Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hA : A ≤ frsCode domain k s ω)
    (hAs : Module.finrank F A ≤ s) :
    (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))))
      ≤ Module.finrank F A * (k - 1) := by
  classical
  have hEinj : Function.Injective
      ((frsEvalOnPoints domain s ω).domRestrict (Polynomial.degreeLT F k)) :=
    frsEvalOnPoints_injOn_degreeLT hL hω0 hadm hkLs
  set n := Module.finrank F A with hn
  set U := frsPullback domain k s ω A with hU
  haveI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F k).symm
  haveI : FiniteDimensional F U :=
    Submodule.finiteDimensional_of_le (S₂ := Polynomial.degreeLT F k) inf_le_right
  have hUrank : Module.finrank F U = n := finrank_frsPullback_eq_injOn hEinj hA
  let bU : Basis (Fin n) F U := by
    rw [← hUrank]; exact Module.finBasis F U
  let P : Fin n → Polynomial F := fun j => (bU j : Polynomial F)
  have hP_deg : ∀ j, (P j).natDegree ≤ k - 1 := fun j =>
    natDegree_le_of_mem_frsPullback (bU j).2
  have hP_indep : LinearIndependent F P := by
    have hbi : LinearIndependent F (fun j => bU j) := bU.linearIndependent
    exact hbi.map' U.subtype (Submodule.ker_subtype U)
  -- The folded Wronskian is nonzero by the *bounded* Lemma 12 (degrees `< k ≤ orderOf ω`).
  have hord_pos : 0 < orderOf ω := orderOf_pos_of_ne_zero hω0
  have hP_lt : ∀ j, (P j).natDegree < orderOf ω := fun j =>
    lt_of_le_of_lt (hP_deg j) (by omega)
  have hL_ne : ArkLib.FRS.GK16.foldedWronskian P ω ≠ 0 :=
    foldedWronskian_ne_zero_of_linearIndependent_of_natDegree_lt P ω hP_indep hP_lt
  -- Per coordinate: `dim A_i ≤ rootMultiplicity (domain i) (foldedWronskian P ω)`.
  have hclaim16 : ∀ i : ι,
      Module.finrank F (↥(A ⊓ (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)))
      ≤ Polynomial.rootMultiplicity (domain i)
          (ArkLib.FRS.GK16.foldedWronskian P ω) := by
    intro i
    have hWi_le : frsVanish domain k s ω A i ≤ U := inf_le_left
    set d := Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))) with hd
    have hWcomap_rank :
        Module.finrank F ((frsVanish domain k s ω A i).comap U.subtype) = d := by
      rw [(Submodule.comapSubtypeEquivOfLe hWi_le).finrank_eq, hd]
      exact finrank_frsVanish_eq_injOn hEinj hA i
    obtain ⟨Q, c, T, hc_det, hQ_rec, hT_card, hT_mem⟩ :=
      ArkLib.FRS.GK16.exists_adapted_recombination bU
        ((frsVanish domain k s ω A i).comap U.subtype) hWcomap_rank
    let Qpoly : Fin n → Polynomial F := fun l => (Q l : Polynomial F)
    have hQpoly_rec : ∀ l, Qpoly l = ∑ m, c l m • P m := by
      intro l
      have hcoe := congrArg (fun u : U => (u : Polynomial F)) (hQ_rec l)
      simpa [Qpoly, P, Submodule.coe_sum, Submodule.coe_smul] using hcoe
    have hvanish : ∀ l ∈ T, ∀ b : Fin n,
        (Qpoly l).eval (domain i * ω ^ (b : ℕ)) = 0 := by
      intro l hl b
      have hmem : (Q l : Polynomial F) ∈ frsVanish domain k s ω A i :=
        (Submodule.mem_comap).mp (hT_mem l hl)
      have hker : evalAtCoord domain s ω i (Q l : Polynomial F) = 0 :=
        (LinearMap.mem_ker).mp hmem.2
      have hbs : (b : ℕ) < s := lt_of_lt_of_le b.2 hAs
      have hcg := congrFun hker ⟨(b : ℕ), hbs⟩
      simpa [Qpoly, evalAtCoord_apply] using hcg
    have hbound := ArkLib.FRS.GK16.claim16_rootMultiplicity_ge
      P Qpoly ω (domain i) c hc_det hQpoly_rec hL_ne T hvanish
    rwa [hT_card] at hbound
  -- Chain the per-coordinate bounds with the verified degree-budget spine.
  calc (∑ i : ι, Module.finrank F (↥(A ⊓ (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))))
      ≤ ∑ i : ι, Polynomial.rootMultiplicity (domain i)
          (ArkLib.FRS.GK16.foldedWronskian P ω) :=
        Finset.sum_le_sum (fun i _ => hclaim16 i)
    _ = ∑ a ∈ (Finset.univ.image domain),
          Polynomial.rootMultiplicity a (ArkLib.FRS.GK16.foldedWronskian P ω) := by
        rw [Finset.sum_image (fun i _ j _ h => domain.injective h)]
    _ ≤ n * (k - 1) :=
        ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le P ω hP_deg hL_ne _

end ReedSolomon.Folded
