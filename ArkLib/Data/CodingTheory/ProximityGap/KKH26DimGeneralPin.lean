/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimTwoPin
import Mathlib.LinearAlgebra.Lagrange

/-!
# The dimension ladder, all rungs at once: the general-`r` unconditional `δ*` pin (#371)

`KKH26DimOnePin.lean` (`r = 2`, pair ownership) and `KKH26DimTwoPin.lean` (`r = 3`, triple
ownership through the collinearity determinant) climbed the first two rungs of the KKH26
dimension ladder one bespoke determinant at a time.  **This file proves the whole family in
one theorem.**  For every slice `r ≥ 2`, every `m ≥ 1`, and every `ε*` in the band

  `[(C(n, (r−2)m+2)/2)/p , (2^r·C(2^{μ−1},r))/p)`,   `n = 2^μ·m`,

`kkh26_dimGeneral_deltaStar_pin` gives `mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`
— exactly, axiom-clean, with **no open obligation**.  At `m = 1` the band is nonempty
whenever `r(r−1) < 2^{μ−1}` (`dimGeneral_band_nonempty` — the `r ≲ √n` law), and the pinned
radius is beyond Johnson whenever `r² < (r−1)·2^μ`, which the same separation hypothesis
implies (`dimGeneral_sep_beyond_johnson`): **the unconditional in-window pin family extends
to every `r ≲ √n` in one statement**, subsuming both landed rungs as instances.

**The mechanism (the subset-ownership count), determinant-free.**  The `r = 3` proof worked
through the explicit `3`-point collinearity determinant; the generalization replaces the
determinant by the *membership predicate it detects*.  Call `y` *`d`-fit on `T`* if some
polynomial of degree ≤ `d` matches `y` on `T` (`polyFitOn`); on `|T| = d + 2` points
non-fitness is exactly the non-vanishing of the `(d+2)`-point interpolation defect — the
generalized bordered-Vandermonde of the ladder law — but no determinant is ever expanded:

* *Non-fitness of `u₁`* (generalizing "`u₁` not affine"): if `u₁` were `d`-fit on the
  witness `S` by `q₁`, then `u₀ = (u₀ + γu₁) − γu₁` is fit by `qS − γ·q₁`, producing the
  joint pair that `mcaEvent` forbids.
* *Ownership*: pick any `(d+1)`-subset `B₀ ⊆ S` and interpolate `q` through `u₁` on `B₀`
  (Lagrange).  Splitting `S` into the on-fit part `Af ⊇ B₀` (`α ≥ d+1`) and the off-fit
  part `Cf ≠ ∅` (`ξ ≥ 1`, `α + ξ ≥ d+3`), every `(d+1)`-subset of `Af` plus one point of
  `Cf` is a **bad `(d+2)`-subset** (uniqueness of low-degree fits), and there are at least
  `C(α, d+1)·ξ ≥ 2` of them — the worst case `(α, ξ) = (d+1, 2)`.  This is the
  `K(r) = 2·r!` ladder law in unordered form: `n^{(r)}/(2·r!) = C(n,r)/2`.
* *Determination*: a bad subset `R` owned by two scalars gives `u₀ + γᵢu₁` fit on `R` for
  both, so `(γ₁−γ₂)·u₁` is fit on `R`, so `u₁` is fit on `R` — contradiction.  Ownership
  families are disjoint, and only `C(n, d+2)` subsets exist:

  `#bad · 2 ≤ C(n, d+2)`.

**Band separation (the `√n` wall).**  At `m = 1` the good-side count `C(n,r)/2` must sit
below the in-tree ceiling spectrum `2^r·C(h,r)` (`h = 2^{μ−1}`, `n = 2h`), i.e.
`(2h)^{(r)} < 2^{r+1}·h^{(r)}`.  The proof is a product-form induction
(`desc_ratio`: `(2h)^{(r)}·(4h − 2r(r−1)) ≤ 2^r·h^{(r)}·4h`), giving the clean sufficient
criterion `r(r−1) < h` — first-order `r ≲ √n`, exactly where the factor-`2` ownership
stops beating the spectrum; beyond `r ≈ 1.18·√n` the true band closes and the ladder
honestly stalls (boundary instances such as `(r, μ) = (4, 4)`, where `r(r−1) = 12 > 8 = h`
but `910 < 1120` still holds, are checked directly).

**Probe**: `scripts/probes/probe_dim3_interior_ceiling.py` (three independent badness
checkers agree byte-exactly at `r = 4`; below-ceiling hill-climbed max `58 ≤ 910`;
per-scalar unordered ownership min `5 ≥ 2`; ceiling bad count at the instance prime
`= 1233` — **exactly** the `TwoPowerSubsetSumSpectrum` law
`N(4,4) = 2⁴C(8,4) + 2²C(8,2) + C(8,0) = 1120 + 112 + 1`).

**The new rung.**  `deltaStar_dimThree_pin_F4294967377` instantiates the general theorem at
`(r, μ) = (4, 4)`: `δ* = 3/4` exactly for the dimension-three (rate `3/16`) code on the
16-point smooth domain `⟨526957872⟩ ⊆ F_p^×`, `p = 4294967377 = 2³² + 81` (the smallest
prime above the `hp` threshold `16⁸ = 2³²` with `p ≡ 1 mod 16`), `ε* = 910/p` — Johnson
radius `1 − √(3/16) ≈ 0.567 < 3/4 < 13/16` = capacity.  Both landed rungs are re-derived
from the general theorem (`deltaStar_pin_F12289_general_consistency`,
`deltaStar_dimTwo_pin_F12289_general_consistency`) with byte-identical statements.

**Honest scope.**  This pins `δ*` for the low-dimension members of the family (`m = 1`,
`r ≲ √n`; dimension `r − 1 ≲ √n`); the production-dimension conjecture (`k = Θ(ρn)`)
remains open — there the band collapses and the obligation is the genuine 25-year wall.
What is new beyond the landed rungs: one proof for every rung, the determinant-free
encoding (membership + Lagrange uniqueness replaces the bordered Vandermonde, making
linearity and the determination step free at every `r`), the general-`m` interior ceiling,
and the explicit `√n` separation law.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.KKH26DimGeneral

/-! ## Degree-`d` explainability on a subset, and its code-membership face -/

/-- Degree-`d` explainability of the word `y` on the index set `S` over the smooth domain
`x_i = g^i`: some polynomial of degree at most `d` matches `y` at every index of `S`.  At
`|S| = d + 2` its negation is exactly the non-vanishing of the `(d+2)`-point interpolation
defect — the generalized collinearity determinant of the `r = 3` rung, kept in membership
form so that linearity in `y` is free. -/
def polyFitOn {p : ℕ} (g : ZMod p) {n : ℕ} (d : ℕ) (S : Finset (Fin n))
    (y : Fin n → ZMod p) : Prop :=
  ∃ q : Polynomial (ZMod p), q.natDegree ≤ d ∧ ∀ i ∈ S, y i = q.eval (g ^ (i : ℕ))

/-- Evaluations of degree-≤-`d` polynomials belong to the code. -/
theorem polyEval_mem_evalCode {p : ℕ} {g : ZMod p} {n d : ℕ} (q : Polynomial (ZMod p))
    (hq : q.natDegree ≤ d) :
    (fun i : Fin n => q.eval (g ^ (i : ℕ))) ∈ evalCode g n d :=
  ⟨q, hq, fun _ => rfl⟩

/-! ## Lagrange interpolation on the smooth domain: existence and uniqueness of fits -/

/-- **Interpolation existence**: through any `d + 1` indices (distinct domain points) there
is a degree-≤-`d` polynomial matching `y`. -/
theorem exists_interpolant {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {B : Finset (Fin n)} (hB : B.card = d + 1) (y : Fin n → ZMod p) :
    polyFitOn g d B y := by
  have hinj : Set.InjOn (fun i : Fin n => g ^ (i : ℕ)) ↑B := fun a _ b _ h => hginj a b h
  refine ⟨Lagrange.interpolate B (fun i : Fin n => g ^ (i : ℕ)) y, ?_, fun i hi => ?_⟩
  · have hdeg := Lagrange.degree_interpolate_lt y hinj
    rw [hB] at hdeg
    by_cases h0 : Lagrange.interpolate B (fun i : Fin n => g ^ (i : ℕ)) y = 0
    · rw [h0]
      simp
    · have hlt := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg
      omega
  · exact (Lagrange.eval_interpolate_at_node y hinj hi).symm

/-- **Uniqueness of low-degree fits**: two degree-≤-`d` polynomials agreeing on `d + 1`
indices (distinct domain points) coincide. -/
theorem fit_unique {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {B : Finset (Fin n)} (hB : d + 1 ≤ B.card)
    {q q' : Polynomial (ZMod p)} (hq : q.natDegree ≤ d) (hq' : q'.natDegree ≤ d)
    (heq : ∀ i ∈ B, q.eval (g ^ (i : ℕ)) = q'.eval (g ^ (i : ℕ))) : q = q' := by
  have hinj : Set.InjOn (fun i : Fin n => g ^ (i : ℕ)) ↑B := fun a _ b _ h => hginj a b h
  have hq1 : q.natDegree < B.card := by omega
  have hq1' : q'.natDegree < B.card := by omega
  have hdq : q.degree < (B.card : WithBot ℕ) := by
    calc q.degree ≤ (q.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
    _ < (B.card : WithBot ℕ) := by exact_mod_cast hq1
  have hdq' : q'.degree < (B.card : WithBot ℕ) := by
    calc q'.degree ≤ (q'.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
    _ < (B.card : WithBot ℕ) := by exact_mod_cast hq1'
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq B hinj hdq hdq' heq

/-! ## The general subset-ownership count -/

/-- The worst witness split: `(d+1)`-subsets of the on-fit part times off-fit points number
at least two (`α ≥ d+1`, `ξ ≥ 1`, `α + ξ ≥ d+3`); the minimum `2` is attained at
`(α, ξ) = (d+1, 2)` — the unordered form of the `K(r) = 2·r!` ladder law. -/
private lemma two_le_choose_mul {α ξ d : ℕ} (hα : d + 1 ≤ α) (hξ : 1 ≤ ξ)
    (hsum : d + 3 ≤ α + ξ) : 2 ≤ α.choose (d + 1) * ξ := by
  rcases Nat.lt_or_ge ξ 2 with h | h
  · have hξ1 : ξ = 1 := by omega
    subst hξ1
    rw [Nat.mul_one]
    have hα2 : d + 2 ≤ α := by omega
    calc (2 : ℕ) ≤ d + 2 := by omega
    _ = (d + 2).choose (d + 1) := (Nat.choose_succ_self_right (d + 1)).symm
    _ ≤ α.choose (d + 1) := Nat.choose_le_choose _ hα2
  · calc (2 : ℕ) = 1 * 2 := by norm_num
    _ ≤ α.choose (d + 1) * ξ := Nat.mul_le_mul (Nat.choose_pos hα) h

open Classical in
/-- **The general subset-ownership count.**  For the degree-`d` evaluation code at agreement
threshold `> d + 2` (i.e. `(1−δ)·n > d + 2`), every stack `(u₀, u₁)` has at most
`C(n, d+2)/2` bad scalars: each bad scalar owns at least two bad `(d+2)`-subsets of its
witness set (subsets on which `u₁` has no degree-`d` fit), any such subset determines the
scalar through the line constraint, distinct bad scalars own disjoint families, and only
`C(n, d+2)` subsets exist.  Stated multiplicatively to avoid `ℕ`-division.  This subsumes
the `r = 2` pair-ownership (`d = 0`) and `r = 3` triple-ownership (`d = 1`) counts:
`C(n,2)/2 = (n²−n)/4` and `C(n,3)/2 = n(n−1)(n−2)/12`. -/
theorem dimGeneral_badScalars_card_mul_two_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
        Finset.univ).card * 2 ≤ n.choose (d + 2) := by
  classical
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- Step 1: for every bad scalar, a witness set with the three working properties:
  -- size ≥ d + 3, the line point degree-`d`-fit on it, and `u₁` NOT fit on it
  -- (the generalized non-affinity: a fit of `u₁` would produce the forbidden joint pair).
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), d + 3 ≤ S.card ∧
      (∃ qS : Polynomial (ZMod p), qS.natDegree ≤ d ∧
        ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (g ^ (i : ℕ))) ∧
      ¬ polyFitOn g d S u₁ := by
    intro γ hγ
    obtain ⟨S, hScard, ⟨w, hwC, hagree⟩, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨qS, hqSdeg, hw⟩ := hwC
    have hlin : ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (g ^ (i : ℕ)) := by
      intro i hi
      have h := hagree i hi
      rw [hw i, smul_eq_mul] at h
      exact h.symm
    have hS3 : d + 3 ≤ S.card := by
      have h2 : ((d + 2 : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : (d + 2 : ℕ) < S.card := by exact_mod_cast h2
      omega
    refine ⟨S, hS3, ⟨qS, hqSdeg, hlin⟩, ?_⟩
    rintro ⟨q₁, hq₁deg, hq₁⟩
    refine hnojoint ⟨fun i => (qS - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)),
      polyEval_mem_evalCode _ (le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le hqSdeg (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁deg))),
      fun i => q₁.eval (g ^ (i : ℕ)), polyEval_mem_evalCode _ hq₁deg,
      fun i hi => ⟨?_, ?_⟩⟩
    · show (qS - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)) = u₀ i
      have e := hlin i hi
      have e1 := hq₁ i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination γ * e1 - e
    · exact (hq₁ i hi).symm
  choose Sf hSf using hwit
  -- the per-scalar owned family: bad `(d+2)`-subsets inside the witness set
  set Pt : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 2)).filter
      (fun R => R ⊆ Sf γ.1 γ.2 ∧ ¬ polyFitOn g d R u₁)) with hPt
  -- Step 2: each bad scalar owns at least two bad subsets.
  have hP2 : ∀ γ : {x // x ∈ B}, 2 ≤ (Pt γ).card := by
    intro γ
    obtain ⟨hcard, _, hunfit⟩ := hSf γ.1 γ.2
    obtain ⟨B0, hB0sub, hB0card⟩ :=
      Finset.exists_subset_card_eq (le_trans (by omega : d + 1 ≤ d + 3) hcard)
    obtain ⟨q, hqdeg, hqval⟩ := exists_interpolant hginj hB0card u₁
    set Af := (Sf γ.1 γ.2).filter (fun i => u₁ i = q.eval (g ^ (i : ℕ))) with hAdef
    set Cf := (Sf γ.1 γ.2).filter (fun i => ¬ u₁ i = q.eval (g ^ (i : ℕ))) with hCdef
    have hB0Af : B0 ⊆ Af := fun i hi => Finset.mem_filter.mpr ⟨hB0sub hi, hqval i hi⟩
    have hA1 : d + 1 ≤ Af.card := hB0card ▸ Finset.card_le_card hB0Af
    have hC1 : 1 ≤ Cf.card := by
      by_contra hcon
      have hCemp : Cf = ∅ := Finset.card_eq_zero.mp (by omega)
      refine hunfit ⟨q, hqdeg, fun i hi => ?_⟩
      by_contra hne
      have hiC : i ∈ Cf := Finset.mem_filter.mpr ⟨hi, hne⟩
      simp [hCemp] at hiC
    have hsum : Af.card + Cf.card = (Sf γ.1 γ.2).card := by
      rw [hAdef, hCdef]
      exact Finset.card_filter_add_card_filter_not _
    have hAC : ∀ i : Fin n, i ∈ Af → i ∈ Cf → False := fun i h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    -- the key certificate: `(d+1)` on-fit indices plus one off-fit index form a bad subset
    -- (uniqueness of low-degree fits forces any fit on the union to be `q`, contradiction
    -- at the off-fit point)
    have hkey : ∀ A' ∈ Af.powersetCard (d + 1), ∀ j ∈ Cf,
        ¬ polyFitOn g d (insert j A') u₁ := by
      intro A' hA' j hj
      obtain ⟨hA'sub, hA'card⟩ := Finset.mem_powersetCard.mp hA'
      rintro ⟨q', hq'deg, hq'⟩
      have hqq' : q = q' := by
        refine fit_unique hginj (le_of_eq hA'card.symm) hqdeg hq'deg fun i hi => ?_
        have h1 : u₁ i = q.eval (g ^ (i : ℕ)) := (Finset.mem_filter.mp (hA'sub hi)).2
        have h2 : u₁ i = q'.eval (g ^ (i : ℕ)) := hq' i (Finset.mem_insert_of_mem hi)
        rw [← h1, ← h2]
      have hjval : u₁ j = q.eval (g ^ (j : ℕ)) := by
        rw [hqq']
        exact hq' j (Finset.mem_insert_self j A')
      exact (Finset.mem_filter.mp hj).2 hjval
    -- the injection `(A', j) ↦ insert j A'` into the owned family
    have hsub : ((Af.powersetCard (d + 1)) ×ˢ Cf).image
        (fun q : Finset (Fin n) × Fin n => insert q.2 q.1) ⊆ Pt γ := by
      intro R hR
      obtain ⟨⟨A', j⟩, hq', rfl⟩ := Finset.mem_image.mp hR
      obtain ⟨hA', hj⟩ := Finset.mem_product.mp hq'
      obtain ⟨hA'sub, hA'card⟩ := Finset.mem_powersetCard.mp hA'
      have hjA' : j ∉ A' := fun hjin => hAC j (hA'sub hjin) hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, ?_⟩, ?_, hkey A' hA' j hj⟩
      · rw [Finset.card_insert_of_notMem hjA', hA'card]
      · exact Finset.insert_subset (Finset.mem_filter.mp hj).1
          (hA'sub.trans (Finset.filter_subset _ _))
    have hinjOn : Set.InjOn (fun q : Finset (Fin n) × Fin n => insert q.2 q.1)
        ↑((Af.powersetCard (d + 1)) ×ˢ Cf) := by
      rintro ⟨A₁, j₁⟩ h₁ ⟨A₂, j₂⟩ h₂ heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
      obtain ⟨hA₁, hj₁⟩ := h₁
      obtain ⟨hA₂, hj₂⟩ := h₂
      obtain ⟨hA₁sub, _⟩ := Finset.mem_powersetCard.mp hA₁
      obtain ⟨hA₂sub, _⟩ := Finset.mem_powersetCard.mp hA₂
      have hj₁A₁ : j₁ ∉ A₁ := fun h => hAC j₁ (hA₁sub h) hj₁
      have hj₂A₂ : j₂ ∉ A₂ := fun h => hAC j₂ (hA₂sub h) hj₂
      simp only at heq
      have hj12 : j₂ = j₁ := by
        have hmem : j₂ ∈ insert j₁ A₁ := heq ▸ Finset.mem_insert_self j₂ A₂
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact absurd h (fun hh => hAC j₂ (hA₁sub hh) hj₂)
      subst hj12
      have hA12 : A₁ = A₂ := by
        have h1 : (insert j₂ A₁).erase j₂ = A₁ := Finset.erase_insert hj₁A₁
        have h2 : (insert j₂ A₂).erase j₂ = A₂ := Finset.erase_insert hj₂A₂
        rw [← h1, ← h2, heq]
      rw [hA12]
    have hcount : 2 ≤ (((Af.powersetCard (d + 1)) ×ˢ Cf).image
        (fun q : Finset (Fin n) × Fin n => insert q.2 q.1)).card := by
      rw [Finset.card_image_of_injOn hinjOn, Finset.card_product,
        Finset.card_powersetCard]
      exact two_le_choose_mul hA1 hC1 (by omega)
    exact le_trans hcount (Finset.card_le_card hsub)
  -- Step 3: the owned families of distinct bad scalars are disjoint (a common bad subset
  -- would make `(γ₁−γ₂)·u₁`, hence `u₁`, fit on it).
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (Pt γ₁) (Pt γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro R hR1 hR2
    obtain ⟨_, hRsub1, hRunfit⟩ := Finset.mem_filter.mp hR1
    obtain ⟨_, hRsub2, _⟩ := Finset.mem_filter.mp hR2
    obtain ⟨q₁, hq₁deg, hl1⟩ := (hSf γ₁.1 γ₁.2).2.1
    obtain ⟨q₂, hq₂deg, hl2⟩ := (hSf γ₂.1 γ₂.2).2.1
    have hγne : γ₁.1 - γ₂.1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    refine hRunfit ⟨Polynomial.C (γ₁.1 - γ₂.1)⁻¹ * (q₁ - q₂),
      le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_trans (Polynomial.natDegree_sub_le _ _) (max_le hq₁deg hq₂deg)),
      fun i hi => ?_⟩
    have e1 := hl1 i (hRsub1 hi)
    have e2 := hl2 i (hRsub2 hi)
    have hdiff : (γ₁.1 - γ₂.1) * u₁ i = (q₁ - q₂).eval (g ^ (i : ℕ)) := by
      rw [Polynomial.eval_sub]
      linear_combination e1 - e2
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hdiff, ← mul_assoc,
      inv_mul_cancel₀ hγne, one_mul]
  -- Step 4: assemble through the `(d+2)`-subset space.
  have hbig : B.attach.card * 2 ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * 2 = ∑ _γ ∈ B.attach, 2 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP2 γ)
  have hsubE : (B.attach.biUnion Pt) ⊆
      (Finset.univ : Finset (Fin n)).powersetCard (d + 2) := by
    intro R hR
    obtain ⟨γ, _, hRP⟩ := Finset.mem_biUnion.mp hR
    exact (Finset.mem_filter.mp hRP).1
  calc B.card * 2 = B.attach.card * 2 := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ (((Finset.univ : Finset (Fin n))).powersetCard (d + 2)).card :=
      Finset.card_le_card hsubE
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The general `ε_mca` bound:** at agreement threshold `> d + 2`, the MCA error of the
degree-`d` evaluation code is at most `(C(n, d+2)/2)/p` — uniformly in `δ`. -/
theorem dimGeneral_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 2) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h2 := dimGeneral_badScalars_card_mul_two_le (g := g) d hginj hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ n.choose (d + 2) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
  exact_mod_cast hle

/-! ## The `InteriorCeiling` discharge at every slice `(r, m)` -/

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the
`KKH26WitnessSpread` cancellation argument). -/
private lemma pow_inj_below_order {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-- **The interior ceiling holds unconditionally at every slice:** for every `r ≥ 2`,
`m ≥ 1`, and `ε* ≥ (C(n, (r−2)m+2)/2)/p`, every `δ` below the KKH26 ceiling `1 − r/2^μ`
gives agreement threshold `> rm ≥ (r−2)m + 2`, so the subset-ownership bound applies. -/
theorem interiorCeiling_dimGeneral
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (εstar : ℝ≥0∞)
    (hband : ((n.choose ((r - 2) * m + 2) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ m r εstar := by
  intro δ hδ
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 ^ μ * m) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (Nat.mul_ne_zero (by positivity) (by omega))] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    have hi : (i : ℕ) < 2 ^ μ * m := by have := i.isLt; omega
    have hj : (j : ℕ) < 2 ^ μ * m := by have := j.isLt; omega
    exact Fin.ext (pow_inj_below_order hg0 hg _ hi _ hj hij)
  refine le_trans (dimGeneral_epsMCA_le (g := g) ((r - 2) * m) hginj ?_) hband
  -- threshold arithmetic: `δ < 1 − r/2^μ` gives `(1−δ)·n > r·m ≥ (r−2)m + 2`
  have hsum : δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 := lt_tsub_iff_right.mp hδ
  have hlt : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc (r : ℝ≥0) / (2 : ℝ≥0) ^ μ + δ = δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ := by ring
    _ < 1 := hsum
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have hm0 : (0 : ℝ≥0) < (m : ℝ≥0) := by exact_mod_cast (by omega : 0 < m)
  have hkey : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ * ((2 : ℝ≥0) ^ μ * (m : ℝ≥0)) = (r : ℝ≥0) * m := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hpow0)]
  have hrm : (r : ℝ≥0) * m < (1 - δ) * ((2 : ℝ≥0) ^ μ * m) := by
    have h := mul_lt_mul_of_pos_right hlt (mul_pos hpow0 hm0)
    rwa [hkey] at h
  have hnat : (r - 2) * m + 2 ≤ r * m := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have hexp : (s + 2) * m = s * m + 2 * m := by ring
    have hexp2 : (s + 2 - 2) * m = s * m := by norm_num
    omega
  have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ μ * m := by
    rw [Fintype.card_fin, hn]
    push_cast
    ring
  rw [hcard]
  calc (((r - 2) * m + 2 : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0) := by exact_mod_cast hnat
  _ = (r : ℝ≥0) * m := by push_cast; ring
  _ < (1 - δ) * ((2 : ℝ≥0) ^ μ * m) := hrm

/-! ## THE GENERAL PIN -/

/-- **THE DIMENSION LADDER, ALL RUNGS AT ONCE.**  For every slice `r ≥ 2`, every `m ≥ 1`,
and every `ε*` in the band `[(C(n,(r−2)m+2)/2)/p, (2^r·C(2^{μ−1},r))/p)`,

  `mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`

with **no open obligation**: the good side is the general subset-ownership incidence bound,
the bad side is the in-tree KKH26 witness spread.  The two landed rungs are the instances
`(r, m) = (2, 1)` and `(3, 1)`; at `m = 1` the band is nonempty for every `r(r−1) < 2^{μ−1}`
(`dimGeneral_band_nonempty`), extending the unconditional pin family to all `r ≲ √n`. -/
theorem kkh26_dimGeneral_deltaStar_pin
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hlo : ((n.choose ((r - 2) * m + 2) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  subst hn
  exact kkh26_deltaStar_pin_of_interior_ceiling hμ hm rfl hg hp hr2 hr εstar hhi
    (interiorCeiling_dimGeneral hm hr2 rfl hg εstar hlo)

/-! ## Band nonemptiness: the `r ≲ √n` separation law -/

/-- The per-step inequality of the falling-product induction:
`(2h − k)(4h − 2k(k+1)) ≤ (2h − 2k)(4h − 2k(k−1))` over `ℕ` (truncated subtraction;
the genuine content is `0 ≤ 2k(2h + k² − 3k)` once `4h ≥ 2k(k+1)`). -/
private lemma desc_step (h k : ℕ) :
    (2 * h - k) * (4 * h - 2 * (k * (k + 1)))
      ≤ (2 * h - 2 * k) * (4 * h - 2 * (k * (k - 1))) := by
  rcases Nat.lt_or_ge (4 * h) (2 * (k * (k + 1))) with hlt | hge
  · have hz : 4 * h - 2 * (k * (k + 1)) = 0 := by omega
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hkk : k * (k + 1) ≤ 2 * h := by omega
      have hk2 : 2 * k ≤ k * (k + 1) := by
        calc 2 * k = k * 2 := by ring
        _ ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
      have hkh : 2 * k ≤ 2 * h := le_trans hk2 hkk
      have hk1 : k * (k - 1) ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
      have hkk1 : k * (k - 1) + 2 * k = k * (k + 1) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      zify [hkk, le_trans hk1 hkk, hkh, le_trans hkh (by omega : 2 * h ≤ 4 * h),
        (by omega : k ≤ 2 * h), (by omega : 2 * (k * (k - 1)) ≤ 4 * h),
        (by omega : 2 * (k * (k + 1)) ≤ 4 * h), (by omega : 1 ≤ k)]
      nlinarith [sq_nonneg ((k : ℤ) - 1), (by exact_mod_cast hkk : ((k : ℤ)) * (k + 1) ≤ 2 * h),
        (by exact_mod_cast hk : (1 : ℤ) ≤ k)]

/-- **The falling-product ratio bound** (induction core):
`(2h)^{(r)}·(4h − 2r(r−1)) ≤ 2^r·h^{(r)}·4h` — the integral form of
`∏ (2h−a)/(2h−2a) ≤ 1/(1 − r(r−1)/(2h))`. -/
private lemma desc_ratio (h : ℕ) :
    ∀ r : ℕ, (2 * h).descFactorial r * (4 * h - 2 * (r * (r - 1)))
      ≤ 2 ^ r * h.descFactorial r * (4 * h)
  | 0 => by simp
  | (r + 1) => by
    have IH := desc_ratio h r
    have hstep := desc_step h r
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.add_sub_cancel]
    have hcomm : (r + 1) * r = r * (r + 1) := Nat.mul_comm _ _
    rw [hcomm]
    calc (2 * h - r) * (2 * h).descFactorial r * (4 * h - 2 * (r * (r + 1)))
        = (2 * h).descFactorial r * ((2 * h - r) * (4 * h - 2 * (r * (r + 1)))) := by
          ring
      _ ≤ (2 * h).descFactorial r * ((2 * h - 2 * r) * (4 * h - 2 * (r * (r - 1)))) :=
          Nat.mul_le_mul_left _ hstep
      _ = (2 * h - 2 * r) * ((2 * h).descFactorial r * (4 * h - 2 * (r * (r - 1)))) := by
          ring
      _ ≤ (2 * h - 2 * r) * (2 ^ r * h.descFactorial r * (4 * h)) :=
          Nat.mul_le_mul_left _ IH
      _ = 2 ^ (r + 1) * ((h - r) * h.descFactorial r) * (4 * h) := by
          rw [show 2 * h - 2 * r = 2 * (h - r) by omega]
          ring

/-- **Falling-factorial band separation:** `r(r−1) < h` forces
`(2h)^{(r)} < 2^{r+1}·h^{(r)}` — the exact arithmetic of the `√n` wall. -/
private lemma descFactorial_band {h r : ℕ} (hr2 : 2 ≤ r) (hsep : r * (r - 1) < h) :
    (2 * h).descFactorial r < 2 ^ (r + 1) * h.descFactorial r := by
  have hrr : r ≤ r * (r - 1) := by
    calc r = r * 1 := (Nat.mul_one r).symm
    _ ≤ r * (r - 1) := Nat.mul_le_mul_left r (by omega)
  have hrh : r ≤ h := le_trans hrr (le_of_lt hsep)
  have hdpos : 0 < h.descFactorial r := Nat.descFactorial_pos.mpr hrh
  have hA := desc_ratio h r
  have hge : 2 * h + 2 ≤ 4 * h - 2 * (r * (r - 1)) := by omega
  have h1 : (2 * h).descFactorial r * (2 * h + 2) ≤ 2 ^ r * h.descFactorial r * (4 * h) :=
    le_trans (Nat.mul_le_mul_left _ hge) hA
  have h2 : 2 ^ r * h.descFactorial r * (4 * h)
      < 2 ^ (r + 1) * h.descFactorial r * (2 * h + 2) := by
    have hlt : 4 * h < 2 * (2 * h + 2) := by omega
    calc 2 ^ r * h.descFactorial r * (4 * h)
        < 2 ^ r * h.descFactorial r * (2 * (2 * h + 2)) :=
          mul_lt_mul_of_pos_left hlt
            (Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) r) hdpos)
      _ = 2 ^ (r + 1) * h.descFactorial r * (2 * h + 2) := by ring
  have hchain := lt_of_le_of_lt h1 h2
  exact lt_of_mul_lt_mul_right hchain (Nat.zero_le _)

/-- **Band nonemptiness, general `r` (the `r ≲ √n` law):** whenever `r(r−1) < 2^{μ−1}`, the
subset-ownership bound `C(2^μ, r)/2` sits strictly below the KKH26 ceiling count
`2^r·C(2^{μ−1}, r)`.  First-order this is `r(r−1) ≲ n/2`: the unconditional pin family
extends to every `r ≲ √n`, and the factor-`2` ownership stops beating the spectrum at the
`√n` wall (boundary instances just past the criterion are checked directly). -/
theorem dimGeneral_band_nonempty {μ r : ℕ} (hr2 : 2 ≤ r)
    (hsep : r * (r - 1) < 2 ^ (μ - 1)) :
    (2 ^ μ).choose r / 2 < 2 ^ r * (2 ^ (μ - 1)).choose r := by
  have h2 : 2 ≤ r * (r - 1) := by
    calc (2 : ℕ) = 2 * 1 := by norm_num
    _ ≤ r * (r - 1) := Nat.mul_le_mul hr2 (by omega)
  have hμ1 : 1 ≤ μ := by
    by_contra hcon
    have hμ0 : μ = 0 := by omega
    rw [hμ0] at hsep
    simp at hsep
    omega
  have hpow : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hdesc := descFactorial_band hr2 hsep
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    at hdesc
  have hch : (2 * 2 ^ (μ - 1)).choose r < 2 ^ (r + 1) * (2 ^ (μ - 1)).choose r := by
    have hre : 2 ^ (r + 1) * (r.factorial * (2 ^ (μ - 1)).choose r)
        = r.factorial * (2 ^ (r + 1) * (2 ^ (μ - 1)).choose r) := by ring
    rw [hre] at hdesc
    exact lt_of_mul_lt_mul_left hdesc (Nat.zero_le _)
  rw [hpow]
  refine (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)).mpr ?_
  calc (2 * 2 ^ (μ - 1)).choose r < 2 ^ (r + 1) * (2 ^ (μ - 1)).choose r := hch
  _ = 2 ^ r * (2 ^ (μ - 1)).choose r * 2 := by ring

/-! ## The canonical pin at `m = 1`, and the window criteria at general `r` -/

/-- **The canonical general pin** (`m = 1`): at `ε* = (C(n,r)/2)/p` itself the pin fires for
every `r ≥ 2` whose band is nonempty — by `dimGeneral_band_nonempty` whenever
`r(r−1) < 2^{μ−1}`, and by direct evaluation at boundary instances. -/
theorem kkh26_dimGeneral_deltaStar_pin_canonical
    {p : ℕ} [Fact p.Prime] {μ r : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ) [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1))
    (hband : n.choose r / 2 < 2 ^ r * (2 ^ (μ - 1)).choose r) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2))
        (((n.choose r / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hcode : (r - 2) * 1 = r - 2 := Nat.mul_one _
  have hidx : (r - 2) * 1 + 2 = r := by omega
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have h := kkh26_dimGeneral_deltaStar_pin (μ := μ) (m := 1) (r := r) (n := n) hμ le_rfl hr2
    (by rw [hn, mul_one]) (by rw [mul_one]; exact hg) hp hr
    (((n.choose r / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (le_of_eq (by rw [hidx]))
    (ENNReal.div_lt_div_right hp0 hpt (by exact_mod_cast hband))
  rwa [hcode] at h

/-- **The separation criterion implies beyond-Johnson:** `r(r−1) < 2^{μ−1}` forces
`r² < (r−1)·2^μ`, the squared-form criterion for the pinned radius `1 − r/2^μ` to lie
strictly beyond the Johnson radius `1 − √ρ` of the rate-`(r−1)/2^μ` code.  Every rung the
general band law certifies is therefore automatically in-window. -/
theorem dimGeneral_sep_beyond_johnson {μ r : ℕ} (hr2 : 2 ≤ r)
    (hsep : r * (r - 1) < 2 ^ (μ - 1)) : r * r < (r - 1) * 2 ^ μ := by
  have h2 : 2 ≤ r * (r - 1) := by
    calc (2 : ℕ) = 2 * 1 := by norm_num
    _ ≤ r * (r - 1) := Nat.mul_le_mul hr2 (by omega)
  have hμ1 : 1 ≤ μ := by
    by_contra hcon
    have hμ0 : μ = 0 := by omega
    rw [hμ0] at hsep
    simp at hsep
    omega
  have hpow : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpow]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have hs : (s + 2) * (s + 1) < 2 ^ (μ - 1) := by
    have he : (s + 2) * (s + 2 - 1) = (s + 2) * (s + 1) := by norm_num
    rwa [he] at hsep
  have he2 : (s + 2 - 1) = s + 1 := by norm_num
  rw [he2]
  calc (s + 2) * (s + 2) ≤ 2 * ((s + 2) * (s + 1)) := by nlinarith
  _ < 2 * 2 ^ (μ - 1) := by omega
  _ ≤ (s + 1) * (2 * 2 ^ (μ - 1)) := Nat.le_mul_of_pos_left _ (by omega)

/-- **Beyond Johnson (squared form), general `r`:** if `r² < (r−1)·2^μ` then the ceiling's
distance to `1` is strictly below the Johnson distance `√ρ` (`ρ = (r−1)/2^μ` the rate of
the `m = 1` slice code), stated square-free. -/
theorem dimGeneral_beyond_johnson_sq {μ r : ℕ} (hcrit : r * r < (r - 1) * 2 ^ μ) :
    ((r : ℝ≥0) / (2 : ℝ≥0) ^ μ) ^ 2 < ((r - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  rw [div_pow, div_lt_div_iff₀ (by positivity) hpow0]
  have hnat : r * r * 2 ^ μ < (r - 1) * 2 ^ μ * 2 ^ μ :=
    mul_lt_mul_of_pos_right hcrit (by positivity)
  calc (r : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ μ = ((r * r * 2 ^ μ : ℕ) : ℝ≥0) := by
        push_cast
        ring
  _ < (((r - 1) * 2 ^ μ * 2 ^ μ : ℕ) : ℝ≥0) := by exact_mod_cast hnat
  _ = ((r - 1 : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ μ) ^ 2 := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
        push_cast
        ring

/-- **Below capacity, general `r`:** the pinned radius `1 − r/2^μ` is strictly below
capacity `1 − ρ = 1 − (r−1)/2^μ` whenever `2 ≤ r ≤ 2^μ`. -/
theorem dimGeneral_below_capacity {μ r : ℕ} (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ μ) :
    (1 : ℝ≥0) - (r : ℝ≥0) / (2 : ℝ≥0) ^ μ
      < 1 - ((r - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have hrle : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ ≤ 1 := by
    rw [div_le_one hpow0]
    calc (r : ℝ≥0) ≤ ((2 ^ μ : ℕ) : ℝ≥0) := by exact_mod_cast hr
    _ = (2 : ℝ≥0) ^ μ := by push_cast; ring
  have hlt : ((r - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ μ < (r : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
    rw [div_lt_div_iff₀ hpow0 hpow0]
    refine mul_lt_mul_of_pos_right ?_ hpow0
    exact_mod_cast (by omega : r - 1 < r)
  have hr1le : ((r - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ μ ≤ 1 := le_trans hlt.le hrle
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub hr1le, NNReal.coe_sub hrle, NNReal.coe_one]
  have hltR := NNReal.coe_lt_coe.mpr hlt
  linarith

end ArkLib.ProximityGap.KKH26DimGeneral

/-! ## The landed rungs re-derived from the general theorem (consistency instances) -/

namespace ArkLib.ProximityGap.KKH26DimGeneral

section Concrete12289

local instance fact_prime_12289 : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- **Consistency, rung `r = 2`:** the general theorem re-derives the landed
`KKH26DimOnePin.deltaStar_pin_F12289` statement byte-for-byte — `δ* = 3/4` for the
dimension-one code on `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 14/12289` (note
`C(8,2)/2 = 14 = (8²−8)/4`). -/
theorem deltaStar_pin_F12289_general_consistency :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 0) ((14 : ℝ≥0∞) / (12289 : ℝ≥0∞))
      = 3 / 4 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_dimGeneral_deltaStar_pin_canonical (p := 12289) (μ := 3) (r := 2)
    (by norm_num) le_rfl (n := 8) (g := (4043 : ZMod 12289)) (by norm_num)
    ArkLib.ProximityGap.KKH26DimOne.orderOf_4043 (by norm_num) (by norm_num) (by decide)
  have e0 : (2 : ℕ) - 2 = 0 := rfl
  have e1 : ((8 : ℕ).choose 2 / 2 : ℕ) = 14 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 3 / 4 := by
    have hd : ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 1 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e1, e2, e3] at h
  exact_mod_cast h

/-- **Consistency, rung `r = 3`:** the general theorem re-derives the landed
`KKH26DimTwoPin.deltaStar_dimTwo_pin_F12289` statement byte-for-byte — `δ* = 5/8` for the
dimension-two code on `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 28/12289` (note
`C(8,3)/2 = 28 = 8·7·6/12`). -/
theorem deltaStar_dimTwo_pin_F12289_general_consistency :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 1) ((28 : ℝ≥0∞) / (12289 : ℝ≥0∞))
      = 5 / 8 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_dimGeneral_deltaStar_pin_canonical (p := 12289) (μ := 3) (r := 3)
    (by norm_num) (by norm_num) (n := 8) (g := (4043 : ZMod 12289)) (by norm_num)
    ArkLib.ProximityGap.KKH26DimOne.orderOf_4043 (by norm_num) (by norm_num) (by decide)
  have e0 : (3 : ℕ) - 2 = 1 := rfl
  have e1 : ((8 : ℕ).choose 3 / 2 : ℕ) = 28 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 5 / 8 := by
    have hd : ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 3 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e1, e2, e3] at h
  exact_mod_cast h

end Concrete12289

/-! ## The NEW rung: `r = 4` at `p = 4294967377 = 2³² + 81` -/

section Concrete4294967377

local instance fact_prime_4294967377 : Fact (Nat.Prime 4294967377) := ⟨by norm_num⟩

/-- `526957872` has multiplicative order `16` in `F_p`, `p = 4294967377`
(`526957872⁸ = −1`; the element is `15^((p−1)/16)` for the primitive root `15`). -/
theorem orderOf_526957872 : orderOf (526957872 : ZMod 4294967377) = 16 := by
  have h8 : ¬ (526957872 : ZMod 4294967377) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h16 : (526957872 : ZMod 4294967377) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (526957872 : ZMod 4294967377)) h8 h16
  norm_num at h
  exact h

/-- **THE THIRD RUNG (new):** `δ* = 3/4` exactly, for the dimension-three (`r = 4`) code on
the 16-point smooth domain `⟨526957872⟩ ⊆ F_p^×`, `p = 4294967377 = 2³² + 81` — the
smallest prime above the KKH26 size threshold `16⁸ = 2³²` with `p ≡ 1 (mod 16)` — at
`ε* = 910/p = (C(16,4)/2)/p`.  The rate is `ρ = 3/16`, the Johnson radius is
`1 − √(3/16) ≈ 0.567 < 3/4 < 13/16` = capacity: a third exact `δ*` value strictly inside
the open window, at a third rate, produced by the *general* theorem (the boundary instance
`(r, μ) = (4, 4)` sits just past the `r(r−1) < 2^{μ−1}` criterion — `12 > 8` — so the band
`910 < 1120` is checked directly; `r² = 16 < 48 = (r−1)·2^μ` keeps it beyond Johnson). -/
theorem deltaStar_dimThree_pin_F4294967377 :
    mcaDeltaStar (F := ZMod 4294967377) (A := ZMod 4294967377)
        (evalCode (526957872 : ZMod 4294967377) 16 2)
        ((910 : ℝ≥0∞) / (4294967377 : ℝ≥0∞))
      = 3 / 4 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_dimGeneral_deltaStar_pin_canonical (p := 4294967377) (μ := 4) (r := 4)
    (by norm_num) (by norm_num) (n := 16) (g := (526957872 : ZMod 4294967377))
    (by norm_num) orderOf_526957872 (by norm_num) (by norm_num) (by decide)
  have e0 : (4 : ℕ) - 2 = 2 := rfl
  have e1 : ((16 : ℕ).choose 4 / 2 : ℕ) = 910 := rfl
  have e2 : ((4294967377 : ℕ) : ℝ≥0∞) = (4294967377 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((4 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 4) = 3 / 4 := by
    have hd : ((4 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 4) = 1 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e1, e2, e3] at h
  exact_mod_cast h

/-- The new rung is beyond Johnson: `(4/16)² = 1/16 < 3/16 = ρ`. -/
theorem dimThree_pin_beyond_johnson_sq :
    ((4 : ℝ≥0) / (2 : ℝ≥0) ^ 4) ^ 2 < (3 : ℝ≥0) / (2 : ℝ≥0) ^ 4 := by
  have h := dimGeneral_beyond_johnson_sq (μ := 4) (r := 4) (by norm_num)
  have e3 : ((4 - 1 : ℕ) : ℝ≥0) = (3 : ℝ≥0) := by norm_num
  have e4 : ((4 : ℕ) : ℝ≥0) = (4 : ℝ≥0) := by norm_num
  rwa [e3, e4] at h

end Concrete4294967377

end ArkLib.ProximityGap.KKH26DimGeneral

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_badScalars_card_mul_two_le
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_epsMCA_le
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.interiorCeiling_dimGeneral
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.kkh26_dimGeneral_deltaStar_pin
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_band_nonempty
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.kkh26_dimGeneral_deltaStar_pin_canonical
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_sep_beyond_johnson
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_beyond_johnson_sq
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_below_capacity
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.deltaStar_pin_F12289_general_consistency
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.deltaStar_dimTwo_pin_F12289_general_consistency
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
#print axioms ArkLib.ProximityGap.KKH26DimGeneral.deltaStar_dimThree_pin_F4294967377
