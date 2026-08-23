/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimGeneralPin

/-!
# Sharpening the subset-ownership count past the `√n` wall (#371)

`KKH26DimGeneralPin.lean` pins `δ* = 1 − r/2^μ` for the degree-`d = (r−2)m` evaluation code via a
**subset-ownership count** `#bad · 2 ≤ C(n, d+2)`, nonempty against the KKH26 ceiling only while
`r(r−1) < 2^{μ−1}` (the `r ≲ √n` wall).  That factor-`2` is loose: the count is the *minimum* over
witness splits of the family of bad `(d+2)`-subsets, but the family is in fact much larger.

**The sharp count.**  At a witness `S` with `|S| ≥ d+3` on which `u₁` is *not* degree-`d`-fit, build
a non-fit `(d+3)`-subset `S'` (on-fit base of `d+1` points + one off-fit point + one extra).  Among
the `d+3` `(d+2)`-subsets of `S'`, **at most one is fit** (two fit `(d+2)`-subsets share `d+1`
points, hence the same degree-`d` interpolant, hence all of `S'` is fit — contradiction).  So `S'`
owns at least `d+2` non-fit `(d+2)`-subsets, giving

  `#bad · (d+2) ≤ C(n, d+2)`   (`dimGeneralSharp_badScalars_card_mul_succ_le`),

a factor-`(d+2)/2` improvement.  At `m = 1` this divisor is `r`, sharpening the *general* band
criterion from the factor-`2` `r(r−1) < 2^{μ−1}` (`r ≲ √(n/2)`) to **`r² < 2^μ`** (`r < √n`,
`dimGeneralSharp_band_nonempty`) — a `√2` improvement proven in one statement; per-instance
decidable checks reach further still *past* `√n` (e.g. `r = 6` at `μ = 4`, where `√n = 4`).  The
asymptotic potential of the sharp count is `r ≲ √(n·ln n)`, but that is a heuristic estimate, *not*
a landed general theorem — only `r < √n` and the explicit instances are proven here.  The
disjointness and assembly are reused verbatim from the general count (a non-fit subset still
determines `γ`); only the per-scalar lower bound changes from `2` to `d+2`.

The concrete witness: at `μ = 4`, `r = 5` (`d = 3`, dimension-four code on the 16-point smooth
domain) the prior factor-`2` band is **empty** (`C(16,5)/2 = 2184 > 1792 = 2⁵·C(8,5)`), yet the
sharp band is nonempty (`C(16,5)/5 = 873 < 1792`): `δ* = 11/16`, beyond Johnson (`1/2`) and below
capacity (`3/4`), a rung the factor-`2` count cannot reach.

## References
- [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*, ePrint 2026/782.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26DimGeneral

namespace ArkLib.ProximityGap.KKH26DimGeneralSharp

/-- `polyFitOn` restricts to subsets (the same interpolant works). -/
theorem polyFitOn_mono {p : ℕ} {g : ZMod p} {n d : ℕ} {T T' : Finset (Fin n)}
    {y : Fin n → ZMod p} (h : polyFitOn g d T y) (hsub : T' ⊆ T) : polyFitOn g d T' y := by
  obtain ⟨q, hq, hv⟩ := h
  exact ⟨q, hq, fun i hi => hv i (hsub hi)⟩

open Classical in
/-- **At most one fit `(d+2)`-subset of a non-fit `(d+3)`-set.** Two distinct fit `(d+2)`-subsets of
a `(d+3)`-set share `d+1` points, hence the same degree-`d` interpolant, hence their union (all
`d+3` points) is fit — contradicting non-fitness. -/
theorem fit_subsets_card_le_one {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j) {d : ℕ}
    {S' : Finset (Fin n)} (hS'card : S'.card = d + 3) {u₁ : Fin n → ZMod p}
    (hS'unfit : ¬ polyFitOn g d S' u₁) :
    ((S'.powersetCard (d + 2)).filter (fun R => polyFitOn g d R u₁)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro T1 hT1 T2 hT2
  obtain ⟨hT1mem, hT1fit⟩ := Finset.mem_filter.mp hT1
  obtain ⟨hT2mem, hT2fit⟩ := Finset.mem_filter.mp hT2
  obtain ⟨hT1sub, hT1c⟩ := Finset.mem_powersetCard.mp hT1mem
  obtain ⟨hT2sub, hT2c⟩ := Finset.mem_powersetCard.mp hT2mem
  by_contra hT12
  apply hS'unfit
  -- T1 ⊊ T1 ∪ T2 (some point of T2 outside T1, else T1 = T2)
  have hgt : d + 2 < (T1 ∪ T2).card := by
    rw [← hT1c]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset Finset.subset_union_left]
    obtain ⟨x, hxT2, hxT1⟩ : ∃ x, x ∈ T2 ∧ x ∉ T1 := by
      by_contra hcon
      push_neg at hcon
      exact hT12 (Finset.eq_of_subset_of_card_le hcon (by rw [hT1c, hT2c])).symm
    exact ⟨x, Finset.mem_union_right _ hxT2, hxT1⟩
  have hle : (T1 ∪ T2).card ≤ d + 3 :=
    le_trans (Finset.card_le_card (Finset.union_subset hT1sub hT2sub)) (le_of_eq hS'card)
  have hunion : (T1 ∪ T2).card = d + 3 := by omega
  have hunionEq : T1 ∪ T2 = S' :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hT1sub hT2sub) (by rw [hS'card, hunion])
  have hinter : (T1 ∩ T2).card = d + 1 := by
    have hadd := Finset.card_union_add_card_inter T1 T2
    rw [hunion, hT1c, hT2c] at hadd
    omega
  obtain ⟨q1, hq1d, hq1v⟩ := hT1fit
  obtain ⟨q2, hq2d, hq2v⟩ := hT2fit
  have hq12 : q1 = q2 :=
    fit_unique hginj (by rw [hinter]) hq1d hq2d (fun i hi => by
      rw [← hq1v i (Finset.mem_of_mem_inter_left hi), ← hq2v i (Finset.mem_of_mem_inter_right hi)])
  refine ⟨q1, hq1d, fun i hi => ?_⟩
  rw [← hunionEq] at hi
  rcases Finset.mem_union.mp hi with h | h
  · exact hq1v i h
  · rw [hq12]; exact hq2v i h

open Classical in
/-- **The sharp subset-ownership count.** For the degree-`d` evaluation code at agreement threshold
`> d + 2`, every stack has at most `C(n, d+2)/(d+2)` bad scalars: each bad scalar owns at least
`d+2` non-fit `(d+2)`-subsets of its witness (the sharp count), distinct bad scalars own disjoint
families, and only `C(n, d+2)` subsets exist. This sharpens the factor-`2` general count by
`(d+2)/2`. -/
theorem dimGeneralSharp_badScalars_card_mul_succ_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
        Finset.univ).card * (d + 2) ≤ n.choose (d + 2) := by
  classical
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- witness extraction (verbatim from the general count): a witness with size ≥ d+3, the line
  -- degree-d-fit on it, and `u₁` NOT fit on it.
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
  -- per-scalar owned family
  set Pt : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 2)).filter
      (fun R => R ⊆ Sf γ.1 γ.2 ∧ ¬ polyFitOn g d R u₁)) with hPt
  -- THE SHARP COUNT: each bad scalar owns ≥ d+2 bad subsets.
  have hPr : ∀ γ : {x // x ∈ B}, d + 2 ≤ (Pt γ).card := by
    intro γ
    obtain ⟨hcard, _, hunfit⟩ := hSf γ.1 γ.2
    -- on-fit base B0 (d+1 points) + interpolant q
    obtain ⟨B0, hB0sub, hB0card⟩ :=
      Finset.exists_subset_card_eq (le_trans (by omega : d + 1 ≤ d + 3) hcard)
    obtain ⟨q, hqdeg, hqval⟩ := exists_interpolant hginj hB0card u₁
    -- an off-fit point c ∈ Sf (exists since u₁ is not fit on Sf)
    obtain ⟨c, hcS, hcne⟩ : ∃ c ∈ Sf γ.1 γ.2, u₁ c ≠ q.eval (g ^ (c : ℕ)) := by
      by_contra hcon
      push_neg at hcon
      exact hunfit ⟨q, hqdeg, fun i hi => hcon i hi⟩
    have hcB0 : c ∉ B0 := fun h => hcne (hqval c h)
    have hbc_card : (insert c B0).card = d + 2 := by
      rw [Finset.card_insert_of_notMem hcB0, hB0card]
    have hbcsub : insert c B0 ⊆ Sf γ.1 γ.2 := Finset.insert_subset hcS hB0sub
    -- an extra point e ∈ Sf outside insert c B0 (size d+2 < d+3 ≤ |Sf|)
    obtain ⟨e, heS, hebc⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hbcsub, fun heq => by rw [← heq, hbc_card] at hcard; omega⟩)
    set S' := insert e (insert c B0) with hS'def
    have hS'card : S'.card = d + 3 := by rw [hS'def, Finset.card_insert_of_notMem hebc, hbc_card]
    have hS'sub : S' ⊆ Sf γ.1 γ.2 := Finset.insert_subset heS hbcsub
    -- insert c B0 is non-fit (the fit would equal q on B0, contradicting c off-fit)
    have hcB0_unfit : ¬ polyFitOn g d (insert c B0) u₁ := by
      rintro ⟨q', hq'deg, hq'⟩
      have hqq' : q = q' := fit_unique hginj (le_of_eq hB0card.symm) hqdeg hq'deg
        (fun i hi => by rw [← hqval i hi, hq' i (Finset.mem_insert_of_mem hi)])
      exact hcne (by rw [hqq']; exact hq' c (Finset.mem_insert_self c B0))
    have hS'unfit : ¬ polyFitOn g d S' u₁ :=
      fun h => hcB0_unfit (polyFitOn_mono h (by rw [hS'def]; exact Finset.subset_insert _ _))
    -- count: d+3 subsets of S', ≤ 1 fit ⇒ ≥ d+2 non-fit; they all land in `Pt γ`
    have htotal : (S'.powersetCard (d + 2)).card = d + 3 := by
      rw [Finset.card_powersetCard, hS'card]
      exact Nat.choose_succ_self_right (d + 2)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S'.powersetCard (d + 2)) (p := fun R => polyFitOn g d R u₁)
    have hfit1 := fit_subsets_card_le_one hginj hS'card hS'unfit
    have hnonfit_ge :
        d + 2 ≤ ((S'.powersetCard (d + 2)).filter (fun R => ¬ polyFitOn g d R u₁)).card := by
      rw [htotal] at hsplit
      omega
    have hsubPt : (S'.powersetCard (d + 2)).filter (fun R => ¬ polyFitOn g d R u₁) ⊆ Pt γ := by
      intro R hR
      obtain ⟨hRmem, hRnf⟩ := Finset.mem_filter.mp hR
      obtain ⟨hRsub, hRc⟩ := Finset.mem_powersetCard.mp hRmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hRc⟩, hRsub.trans hS'sub, hRnf⟩
    exact le_trans hnonfit_ge (Finset.card_le_card hsubPt)
  -- disjointness (verbatim from the general count): a common bad subset would fit `u₁`.
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Pt γ₁) (Pt γ₂) := by
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
  -- assemble
  have hbig : B.attach.card * (d + 2) ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * (d + 2) = ∑ _γ ∈ B.attach, (d + 2) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hPr γ)
  have hsubE : (B.attach.biUnion Pt) ⊆ (Finset.univ : Finset (Fin n)).powersetCard (d + 2) := by
    intro R hR
    obtain ⟨γ, _, hRP⟩ := Finset.mem_biUnion.mp hR
    exact (Finset.mem_filter.mp hRP).1
  calc B.card * (d + 2) = B.attach.card * (d + 2) := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ (((Finset.univ : Finset (Fin n))).powersetCard (d + 2)).card := Finset.card_le_card hsubE
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The sharp `ε_mca` bound:** at agreement threshold `> d + 2`, the MCA error of the degree-`d`
code is at most `(C(n, d+2)/(d+2))/p` — a factor `(d+2)/2` below the general bound. -/
theorem dimGeneralSharp_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 2) / (d + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h2 := dimGeneralSharp_badScalars_card_mul_succ_le (g := g) d hginj hδ (u 0) (u 1)
  exact (Nat.le_div_iff_mul_le (by omega)).mpr h2

/-! ## The sharp `InteriorCeiling` discharge and the past-the-wall pin -/

/-- **The interior ceiling at every slice, sharp band.** Identical threshold arithmetic to the
general discharge, but with the sharp ownership divisor `(r−2)m+2` in place of `2`. -/
theorem interiorCeiling_dimGeneralSharp
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (εstar : ℝ≥0∞)
    (hband : ((n.choose ((r - 2) * m + 2) / ((r - 2) * m + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ m r εstar := by
  intro δ hδ
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    have hi : (i : ℕ) ∈ Set.Iio (orderOf g) := by rw [hg, ← hn]; exact i.isLt
    have hj : (j : ℕ) ∈ Set.Iio (orderOf g) := by rw [hg, ← hn]; exact j.isLt
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj hij)
  refine le_trans (dimGeneralSharp_epsMCA_le (g := g) ((r - 2) * m) hginj ?_) hband
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
    rw [Fintype.card_fin, hn]; push_cast; ring
  rw [hcard]
  calc (((r - 2) * m + 2 : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0) := by exact_mod_cast hnat
  _ = (r : ℝ≥0) * m := by push_cast; ring
  _ < (1 - δ) * ((2 : ℝ≥0) ^ μ * m) := hrm

/-- **THE PAST-THE-WALL PIN.** Same statement as the general pin, but with the *sharp* lower band
endpoint `C(n,(r−2)m+2)/((r−2)m+2)` — a factor `((r−2)m+2)/2` smaller — so the band stays nonempty
for `r` beyond the factor-`2` `√n` wall, extending the unconditional `δ*` pin family. -/
theorem kkh26_dimGeneralSharp_deltaStar_pin
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hlo : ((n.choose ((r - 2) * m + 2) / ((r - 2) * m + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  subst hn
  exact kkh26_deltaStar_pin_of_interior_ceiling hμ hm rfl hg hp hr2 hr εstar hhi
    (interiorCeiling_dimGeneralSharp hm hr2 rfl hg εstar hlo)

/-! ## The general sharp band law: `r² < 2^μ` (a `√2` improvement over `r(r−1) < 2^{μ−1}`) -/

/-- Per-step inequality of the falling-product induction (copy of the general count's `desc_step`,
which is `private` upstream). -/
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

/-- Falling-product ratio bound (copy of the general count's `desc_ratio`). -/
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
        = (2 * h).descFactorial r * ((2 * h - r) * (4 * h - 2 * (r * (r + 1)))) := by ring
      _ ≤ (2 * h).descFactorial r * ((2 * h - 2 * r) * (4 * h - 2 * (r * (r - 1)))) :=
          Nat.mul_le_mul_left _ hstep
      _ = (2 * h - 2 * r) * ((2 * h).descFactorial r * (4 * h - 2 * (r * (r - 1)))) := by ring
      _ ≤ (2 * h - 2 * r) * (2 ^ r * h.descFactorial r * (4 * h)) := Nat.mul_le_mul_left _ IH
      _ = 2 ^ (r + 1) * ((h - r) * h.descFactorial r) * (4 * h) := by
          rw [show 2 * h - 2 * r = 2 * (h - r) by omega]
          ring

/-- **Sharp falling-factorial band:** `r² < 2h` forces `(2h)^{(r)} < r·2^r·h^{(r)}` — the sharp wall
arithmetic. The criterion `r² < 2h` is a `√2` relaxation of the factor-`2` count's `r(r−1) < h`,
because the sharp divisor `r` (not `2`) absorbs the ratio `(4h)/(4h−2r(r−1)) < r ⟺ r² < 2h`. -/
private lemma descFactorial_band_sharp {h r : ℕ} (hr2 : 2 ≤ r) (hsep : r * r < 2 * h) :
    (2 * h).descFactorial r < r * (2 ^ r * h.descFactorial r) := by
  have hrr : r * (r - 1) < r * r := mul_lt_mul_of_pos_left (by omega) (by omega)
  have hsep2 : 2 * (r * (r - 1)) < 4 * h := by omega
  have hrh : r ≤ h := by nlinarith [hsep, hr2]
  have hdpos : 0 < h.descFactorial r := Nat.descFactorial_pos.mpr hrh
  have hA := desc_ratio h r
  -- the key ratio fact `4h < r·(4h − 2r(r−1))`, reducing to `2r² < 4h`
  have hexp : 2 * r + 2 * (r * (r - 1)) = 2 * (r * r) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have h2rX : 2 * r < 4 * h - 2 * (r * (r - 1)) := by omega
  have hfac : 4 * h < r * (4 * h - 2 * (r * (r - 1))) := by
    set X := 4 * h - 2 * (r * (r - 1)) with hXdef
    have hXeq : 2 * (r * (r - 1)) + X = 4 * h := by omega
    -- 4h = 2r(r−1) + X < r·X  ⟺  2r(r−1) < (r−1)·X, from X > 2r and r ≥ 2
    have hlt : 2 * (r * (r - 1)) < (r - 1) * X := by
      calc 2 * (r * (r - 1)) = (r - 1) * (2 * r) := by ring
      _ < (r - 1) * X := mul_lt_mul_of_pos_left h2rX (by omega)
    nlinarith [hXeq, hlt, hr2]
  have hp2 : 0 < 2 ^ r * h.descFactorial r := Nat.mul_pos (pow_pos (by norm_num) r) hdpos
  have hmid : 2 ^ r * h.descFactorial r * (4 * h)
      < r * (2 ^ r * h.descFactorial r) * (4 * h - 2 * (r * (r - 1))) := by
    calc 2 ^ r * h.descFactorial r * (4 * h)
        < 2 ^ r * h.descFactorial r * (r * (4 * h - 2 * (r * (r - 1)))) :=
          mul_lt_mul_of_pos_left hfac hp2
      _ = r * (2 ^ r * h.descFactorial r) * (4 * h - 2 * (r * (r - 1))) := by ring
  exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hA hmid) (Nat.zero_le _)

/-- **The sharp band law:** whenever `r² < 2^μ`, the sharp ownership bound `C(2^μ, r)/r` sits
strictly below the KKH26 ceiling count `2^r·C(2^{μ−1}, r)`. The criterion `r² < 2^μ` is a `√2`
improvement on the factor-`2` law `r(r−1) < 2^{μ−1}` — the unconditional pin family now reaches
every `r < √n` in one statement. -/
theorem dimGeneralSharp_band_nonempty {μ r : ℕ} (hr2 : 2 ≤ r) (hsep : r * r < 2 ^ μ) :
    (2 ^ μ).choose r / r < 2 ^ r * (2 ^ (μ - 1)).choose r := by
  have hμ1 : 1 ≤ μ := by
    by_contra hcon
    have : μ = 0 := by omega
    rw [this] at hsep; simp at hsep; omega
  have hpow : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hsep' : r * r < 2 * 2 ^ (μ - 1) := by rw [← hpow]; exact hsep
  have hdesc := descFactorial_band_sharp hr2 hsep'
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hch : (2 * 2 ^ (μ - 1)).choose r < r * (2 ^ r * (2 ^ (μ - 1)).choose r) := by
    have hre : r * (2 ^ r * (r.factorial * (2 ^ (μ - 1)).choose r))
        = r.factorial * (r * (2 ^ r * (2 ^ (μ - 1)).choose r)) := by ring
    rw [hre] at hdesc
    exact lt_of_mul_lt_mul_left hdesc (Nat.zero_le _)
  rw [hpow]
  refine (Nat.div_lt_iff_lt_mul (by omega : (0 : ℕ) < r)).mpr ?_
  calc (2 * 2 ^ (μ - 1)).choose r < r * (2 ^ r * (2 ^ (μ - 1)).choose r) := hch
  _ = 2 ^ r * (2 ^ (μ - 1)).choose r * r := by ring

/-- **The canonical sharp pin** (`m = 1`): at `ε* = (C(n,r)/r)/p` the pin fires for every `r` with
`r² < 2^μ` (and at boundary instances past it, by direct evaluation). -/
theorem kkh26_dimGeneralSharp_deltaStar_pin_canonical
    {p : ℕ} [Fact p.Prime] {μ r : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ) [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1))
    (hband : n.choose r / r < 2 ^ r * (2 ^ (μ - 1)).choose r) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2))
        (((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hcode : (r - 2) * 1 = r - 2 := Nat.mul_one _
  have hidx : (r - 2) * 1 + 2 = r := by omega
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have h := kkh26_dimGeneralSharp_deltaStar_pin (μ := μ) (m := 1) (r := r) (n := n) hμ le_rfl hr2
    (by rw [hn, mul_one]) (by rw [mul_one]; exact hg) hp hr
    (((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (le_of_eq (by rw [hidx]))
    (ENNReal.div_lt_div_right hp0 hpt (by exact_mod_cast hband))
  rwa [hcode] at h

end ArkLib.ProximityGap.KKH26DimGeneralSharp

/-! ## The concrete past-the-wall rung: `r = 5` at `μ = 4` (where factor-2 fails) -/

namespace ArkLib.ProximityGap.KKH26DimGeneralSharp

section ConcretePastWall

local instance fact_prime_4294967377 : Fact (Nat.Prime 4294967377) := ⟨by norm_num⟩

/-- **The factor-`2` count cannot reach `r = 5` at `μ = 4`:** the general band lower endpoint
`C(16,5)/2 = 2184` exceeds the ceiling count `2⁵·C(8,5) = 1792`, so the general (factor-`2`) band is
**empty** here. -/
theorem factor_two_band_empty_mu4_r5 :
    ¬ ((16 : ℕ).choose 5 / 2 < 2 ^ 5 * (8 : ℕ).choose 5) := by decide

/-- **The sharp band IS nonempty at `r = 5`, `μ = 4`:** `C(16,5)/5 = 873 < 1792 = 2⁵·C(8,5)`. The
sharp ownership reaches a rung the factor-`2` count provably cannot. -/
theorem sharp_band_nonempty_mu4_r5 :
    (16 : ℕ).choose 5 / 5 < 2 ^ 5 * (8 : ℕ).choose 5 := by decide

/-- **THE CONCRETE PAST-THE-WALL PIN:** `δ* = 11/16` exactly, for the degree-`3` (dimension-four)
code on the 16-point smooth domain `⟨526957872⟩ ⊆ F_p^×`, `p = 4294967377 = 2³² + 81`, at
`ε* = (C(16,5)/5)/p = 873/p`.  The rate is `ρ = 4/16 = 1/4`, Johnson radius `1 − 1/2 = 1/2 < 11/16`,
capacity `1 − 1/4 = 3/4 > 11/16`: an exact in-window `δ*` of dimension four, **strictly past the
factor-`2` `√n` wall** (`factor_two_band_empty_mu4_r5`), produced by the sharp ownership count. -/
theorem deltaStar_dimFour_pin_F4294967377 :
    mcaDeltaStar (F := ZMod 4294967377) (A := ZMod 4294967377)
        (evalCode (526957872 : ZMod 4294967377) 16 3)
        ((((16 : ℕ).choose 5 / 5 : ℕ) : ℝ≥0∞) / (4294967377 : ℝ≥0∞))
      = 1 - (5 : ℝ≥0) / ((2 : ℝ≥0) ^ 4) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have hcode : ((5 : ℕ) - 2) * 1 = 3 := by norm_num
  have hdivisor : ((5 : ℕ) - 2) * 1 + 2 = 5 := by norm_num
  have h := kkh26_dimGeneralSharp_deltaStar_pin (p := 4294967377) (μ := 4) (m := 1) (r := 5)
    (g := (526957872 : ZMod 4294967377)) (n := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872) (by norm_num) (by norm_num)
    _ le_rfl ?_
  · rw [hcode, hdivisor] at h
    exact h
  · -- band nonemptiness as ℝ≥0∞ quotients
    rw [hdivisor]
    refine ENNReal.div_lt_div_right (Nat.cast_ne_zero.mpr (by norm_num))
      (ENNReal.natCast_ne_top _) ?_
    exact_mod_cast (show (16 : ℕ).choose 5 / 5 < 2 ^ 5 * (2 ^ (4 - 1)).choose 5 by decide)

end ConcretePastWall

end ArkLib.ProximityGap.KKH26DimGeneralSharp

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.interiorCeiling_dimGeneralSharp
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.kkh26_dimGeneralSharp_deltaStar_pin
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.factor_two_band_empty_mu4_r5
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.sharp_band_nonempty_mu4_r5
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.deltaStar_dimFour_pin_F4294967377

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.fit_subsets_card_le_one
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.dimGeneralSharp_badScalars_card_mul_succ_le
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.dimGeneralSharp_epsMCA_le
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.dimGeneralSharp_band_nonempty
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.kkh26_dimGeneralSharp_deltaStar_pin_canonical
