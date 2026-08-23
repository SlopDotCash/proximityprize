/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ConstrainedCensusLaw

/-!
# The census lower bound: every census scalar is MCA-bad — the pin's lower half as a theorem

`CensusConditionalPin.lean` reduced "pin δ*" (given census-upper extremality) to census
numerics *plus one `ε_mca` lower-bound hypothesis at the crossing radius*. This file
discharges that hypothesis **as a theorem, at every scale**, by welding the constrained
census law (`badScalar_iff_constrainedSubsetSum`, the O138/O139 law) into the MCA event:

* `census_mem_badScalar` — every scalar of `constrainedCensus H k a` fires `mcaEvent` for
  the adjacent-exponent monomial stack `(X^a, X^{a−1})` evaluated on the domain, at the grid
  radius `1 − a/n`. The agreement half is the census law's reverse direction; the
  no-joint-explanation half is **free**: a degree-`< k` codeword agreeing with `X^{a−1}` on
  `≥ a > a−1` points would make `X^{a−1} − q'` a nonzero polynomial of degree `≤ a−1` with
  `≥ a` distinct roots.
* `census_le_epsMCA` — hence `ε_mca(C, 1 − a/n) ≥ |census|/|F|` for the degree-`< k`
  evaluation code on any injective domain: **the census is an unconditional lower bound on
  the MCA error**, mirroring (and generalizing to all scales) the per-instance bad-stack
  computations of the exact-point files.
* `mcaDeltaStar_eq_of_censusCrossing'` — **the strengthened conditional pin**: census-upper
  extremality + census numerics (clears `ε*` above the crossing, exceeds it at the crossing)
  ⟹ `mcaDeltaStar = 1 − a_c/n` exactly. The lower side now consumes *only* the census
  cardinality — δ* is pinned by counting constrained subset sums, conditional on a single
  named hypothesis (`CensusUpperExtremal`).

Together with the radius-quantization theorem this completes the round-2 architecture's
bracket plumbing: the O139/O140/O141/O142 census tables *are* δ*-statements modulo
extremality, with both numeric sides machine-checkable per scale.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the census arc); `KKH26ConstrainedCensusLaw.lean` (the law),
  `CensusConditionalPin.lean` (the pin and quantization).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.CensusLowerBound

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ArkLib.ProximityGap.KKH26

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The degree-`< k` evaluation code -/

/-- Evaluations of polynomials of degree `< k` (i.e. `natDegree ≤ k − 1`) on a domain. -/
def evalCode (dom : ι → F) (k : ℕ) : Submodule F (ι → F) where
  carrier := {f | ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ ∀ i, f i = q.eval (dom i)}
  zero_mem' := ⟨0, by simp, fun i => by simp⟩
  add_mem' := by
    rintro f g ⟨q, hq, hf⟩ ⟨q', hq', hg⟩
    exact ⟨q + q', le_trans (Polynomial.natDegree_add_le _ _) (max_le hq hq'),
      fun i => by rw [Pi.add_apply, hf i, hg i, Polynomial.eval_add]⟩
  smul_mem' := by
    rintro c f ⟨q, hq, hf⟩
    exact ⟨C c * q, le_trans (Polynomial.natDegree_C_mul_le _ _) hq,
      fun i => by rw [Pi.smul_apply, hf i, Polynomial.eval_mul, Polynomial.eval_C,
        smul_eq_mul]⟩

theorem mem_evalCode {dom : ι → F} {k : ℕ} (f : ι → F) :
    f ∈ (evalCode dom k : Set (ι → F)) ↔
      ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ ∀ i, f i = q.eval (dom i) :=
  Iff.rfl

/-! ## Vieta bridge: vanishing symmetric functions = zero constrained band -/

/-- The first elementary symmetric function of a multiset is its sum. -/
theorem esymm_one_eq_sum (s : Multiset F) : s.esymm 1 = s.sum := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp

/-- The census filter condition (`e_j(T) = 0` on the band) gives the law's
`ConstrainedBandZero` (vanishing coefficients of the vanishing polynomial). -/
theorem bandZero_of_esymm {T : Finset F} {a k : ℕ} (hcard : T.card = a)
    (h : ∀ j ∈ Finset.Icc 2 (a - k), T.val.esymm j = 0) :
    ConstrainedBandZero T a k := by
  intro j hj2 hjak
  have hja : j ≤ a := le_trans hjak (Nat.sub_le _ _)
  have hcard' : Multiset.card T.val = a := hcard
  have hcoeff : (∏ x ∈ T, (X - C x)).coeff (a - j)
      = (-1) ^ j * T.val.esymm j := by
    rw [Finset.prod_eq_multiset_prod]
    have hle : a - j ≤ Multiset.card T.val := by omega
    rw [Multiset.prod_X_sub_C_coeff T.val hle, hcard']
    congr 1
    · congr 1
      omega
    · congr 1
      omega
  rw [hcoeff, h j (Finset.mem_Icc.mpr ⟨hj2, hjak⟩), mul_zero]

/-! ## Every census scalar fires the MCA event -/

/-- A degree-`< k` explanation cannot match `X^{a−1}` on `≥ a` points: the no-joint half. -/
theorem no_explanation_of_pow {dom : ι → F} (hinj : Function.Injective dom)
    {k a : ℕ} (hk : 1 ≤ k) (hka : k + 1 ≤ a) {S : Finset ι} (hS : a ≤ S.card)
    {q' : Polynomial F} (hq' : q'.natDegree ≤ k - 1)
    (hagree : ∀ i ∈ S, q'.eval (dom i) = dom i ^ (a - 1)) : False := by
  classical
  set g : Polynomial F := X ^ (a - 1) - q' with hg
  have hgne : g ≠ 0 := by
    intro h0
    have hq'eq : q' = X ^ (a - 1) := by
      have := sub_eq_zero.mp h0
      exact this.symm
    have hdeg : (X ^ (a - 1) : Polynomial F).natDegree = a - 1 :=
      Polynomial.natDegree_X_pow _
    rw [hq'eq, hdeg] at hq'
    omega
  have hgdeg : g.natDegree ≤ a - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact max_le le_rfl (by omega)
  -- the image of S under dom consists of ≥ a distinct roots of g
  have hsub : S.image dom ⊆ g.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
    show g.IsRoot (dom i)
    rw [Polynomial.IsRoot, hg, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hagree i hi, sub_self]
  have hcount : a ≤ g.natDegree := by
    calc a ≤ S.card := hS
      _ = (S.image dom).card := (Finset.card_image_of_injective S hinj).symm
      _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
  omega

/-- **Every census scalar is MCA-bad** for the adjacent-exponent monomial stack at the
grid radius `1 − a/n`: the agreement half is the constrained census law (reverse
direction), the no-joint half is the root-count impossibility above. -/
theorem census_mem_badScalar (dom : ι → F) (hinj : Function.Injective dom)
    {k a : ℕ} (hk : 1 ≤ k) (hka : k + 1 ≤ a) (han : a ≤ Fintype.card ι)
    {lam : F}
    (hlam : lam ∈ constrainedCensus (Finset.univ.image dom) k a) :
    mcaEvent (F := F) (A := F) (evalCode dom k : Set (ι → F))
      (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0))
      (fun i => dom i ^ a) (fun i => dom i ^ (a - 1)) lam := by
  classical
  -- unpack the census membership into the law's subset data
  obtain ⟨T, hTfilter, hTlam⟩ := Finset.mem_image.mp hlam
  rw [Finset.mem_filter] at hTfilter
  obtain ⟨hTpow, hTband⟩ := hTfilter
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTpow
  have hband : ConstrainedBandZero T a k := bandZero_of_esymm hTcard hTband
  have hlam' : lam = -∑ x ∈ T, x := by
    rw [← hTlam, esymm_one_eq_sum, Finset.sum_val]
    rfl
  -- the law's reverse direction: an explanation with ≥ a agreements
  obtain ⟨q, hq, hagree⟩ :=
    badScalar_of_constrainedSubsetSum hk hka hTsub hTcard hband
  rw [← hlam'] at hagree
  -- transfer the agreement set to the index side
  set S : Finset ι :=
    Finset.univ.filter (fun i => dom i ∈ lineAgreeSet (Finset.univ.image dom) a lam q)
    with hSdef
  have hSimage : S.image dom = lineAgreeSet (Finset.univ.image dom) a lam q := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [hSdef, Finset.mem_filter] at hi
      exact hi.2
    · intro x hx
      have hxH : x ∈ Finset.univ.image dom := Finset.mem_of_mem_filter _ hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
      have hiS : i ∈ S := by
        rw [hSdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hx⟩
      exact Finset.mem_image_of_mem dom hiS
  have hScard : a ≤ S.card := by
    calc a ≤ (lineAgreeSet (Finset.univ.image dom) a lam q).card := hagree
      _ = (S.image dom).card := by rw [hSimage]
      _ = S.card := Finset.card_image_of_injective S hinj
  -- assemble the event through the quantization bridge
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero han]
  refine ⟨S, hScard, ⟨fun i => q.eval (dom i), ⟨q, hq, fun i => rfl⟩, fun i hi => ?_⟩, ?_⟩
  · -- the line agrees with the explanation on S
    rw [hSdef, Finset.mem_filter] at hi
    have hx := hi.2
    rw [lineAgreeSet, Finset.mem_filter] at hx
    rw [smul_eq_mul]
    exact (hx.2).symm
  · -- no joint explanation: row 1 is X^{a−1}, inexplicable on ≥ a points
    rintro ⟨v₀, _, v₁, hv₁, hag⟩
    obtain ⟨q', hq', hv₁'⟩ := (mem_evalCode v₁).mp hv₁
    refine no_explanation_of_pow hinj hk hka hScard hq' fun i hi => ?_
    rw [← hv₁' i]
    exact (hag i hi).2

/-! ## The census lower bound on the MCA error -/

open Classical in
/-- **The census is an unconditional lower bound on the MCA error** at its grid radius:
`|constrainedCensus|/|F| ≤ ε_mca(C, 1 − a/n)` for the degree-`< k` evaluation code on any
injective domain. The lower half of the census-conditional pin, as a theorem at every
scale. -/
theorem census_le_epsMCA (dom : ι → F) (hinj : Function.Injective dom)
    {k a : ℕ} (hk : 1 ≤ k) (hka : k + 1 ≤ a) (han : a ≤ Fintype.card ι) :
    ((constrainedCensus (Finset.univ.image dom) k a).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode dom k : Set (ι → F))
          (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := F) _ _
    ![fun i => dom i ^ a, fun i => dom i ^ (a - 1)])
  have h0 : (![fun i => dom i ^ a, fun i => dom i ^ (a - 1)] :
      WordStack F (Fin 2) ι) 0 = fun i => dom i ^ a := rfl
  have h1 : (![fun i => dom i ^ a, fun i => dom i ^ (a - 1)] :
      WordStack F (Fin 2) ι) 1 = fun i => dom i ^ (a - 1) := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hsub : constrainedCensus (Finset.univ.image dom) k a ⊆
      Finset.filter (fun lam : F => mcaEvent (F := F) (A := F)
        (evalCode dom k : Set (ι → F)) (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0))
        (fun i => dom i ^ a) (fun i => dom i ^ (a - 1)) lam) Finset.univ := by
    intro lam hlam
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, census_mem_badScalar dom hinj hk hka han hlam⟩
  gcongr

/-! ## The strengthened conditional pin -/

/-- **The strengthened census-conditional δ\* pin.** For the degree-`< k` evaluation code
on an injective domain: census-upper extremality above the crossing agreement `a_c`, plus
pure census numerics (the census fraction clears `ε*` above the crossing and exceeds it at
the crossing), pin `mcaDeltaStar = 1 − a_c/n` **exactly**. The only remaining hypothesis
beyond finite counting is the named `CensusUpperExtremal`. -/
theorem mcaDeltaStar_eq_of_censusCrossing' (dom : ι → F)
    (hinj : Function.Injective dom) (k : ℕ) (εstar : ℝ≥0∞) {ac : ℕ}
    (hk : 1 ≤ k) (hkac : k + 1 ≤ ac) (hacn : ac ≤ Fintype.card ι)
    (hupper : CensusUpperExtremal (F := F) (A := F)
      (evalCode dom k : Set (ι → F)) (Finset.univ.image dom) k ac)
    (hcensus : ∀ a : ℕ, ac < a → a ≤ Fintype.card ι →
      ((constrainedCensus (Finset.univ.image dom) k a).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hbad : εstar < ((constrainedCensus (Finset.univ.image dom) k ac).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F) (evalCode dom k : Set (ι → F)) εstar
      = 1 - (ac : ℝ≥0) / (Fintype.card ι : ℝ≥0) :=
  mcaDeltaStar_eq_of_censusCrossing (F := F) (A := F)
    (evalCode dom k : Set (ι → F)) (Finset.univ.image dom) k εstar hupper hcensus
    (lt_of_lt_of_le hbad (census_le_epsMCA dom hinj hk hkac hacn))

/-! ## Source audit -/

#print axioms census_mem_badScalar
#print axioms census_le_epsMCA
#print axioms mcaDeltaStar_eq_of_censusCrossing'

end ProximityGap.CensusLowerBound
