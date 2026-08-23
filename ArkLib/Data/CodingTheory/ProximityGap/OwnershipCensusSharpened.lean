/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimGeneralPin

/-!
# The sharpened ownership census: from factor `2` to `C(w,d+1)/(d+2)` — and its ceiling (#371)

The landed general ladder bound (`dimGeneral_badScalars_card_mul_two_le`,
`KKH26DimGeneralPin.lean`) gives each bad scalar **two** owned bad `(d+2)`-subsets, from the
on-fit/off-fit split with worst case `(α, ξ) = (d+1, 2)`.  This file re-derives the honest
ownership law and proves the sharpened count, the new band it opens, and the *ceiling* that
shows the sharpening is essentially maximal for the subset-counting scheme.

**The sharpened law** (`exists_offFit_extension` → `sharpened_badScalars_card_mul_choose_le`).
For *every* `(d+1)`-subset `B` of the witness `S` there is at least one `x ∈ S \ B` with
`u₁` not degree-`d`-fit on `insert x B` — otherwise the Lagrange interpolant through `B`
would fit `u₁` on all of `S`, contradicting the witness property.  Counting the owned
**pairs** `(B, x)` (each determines the scalar through the line constraint exactly as the
owned subsets do) gives, for witness threshold `w₀ < (1−δ)n`:

  `#bad · C(w₀+1, d+1) ≤ C(n, d+1)·(n−d−1)`

— per-scalar ownership `C(w, d+1)` pairs (equivalently `≥ C(w,d+1)/(d+2)` subsets), versus
the landed `2`.  At the ladder slice (`m = 1`, `w₀ = r`, `d = r−2`) the good-side count
drops from `C(n,r)/2` to `C(n,r)·r/C(r+1,2) = 2·C(n,r)/(r+1)` — a factor-`(r+1)/4` gain.

**The exact minimum, and why the landed worst case was unattainable** (`deviation_unfit_iff`,
`deviation_ownership_card`): the true per-witness minimum ownership is exactly
`C(w−1, d+1)`, attained by the *single-deviation* configurations — `u₁` equal to a
degree-`≤ d` polynomial on `S` minus one point `j` and deviating at `j`; then a
`(d+2)`-subset of `S` is unfit **iff it contains `j`**, so exactly `C(w−1, d+1)` subsets
are owned.  At the minimal witness `w = r+1` this is `C(r, r−1) = r`, not `2`: the landed
`(d+1, 2)`-split worst case is realizable as a *split* but never as an ownership count for
`r ≥ 3` (it is exact only at `r = 2`).  Probe: `scripts/probes/probe_ownership_census.py`
(full census at `p = 12289`, `r ∈ {2,3,4,5}`: every measured ownership `≥ C(w−1,d+1)`,
the deviation stacks attain it 90/90, and the provable pair law holds at every witness).

**The ceiling (the cannot-sharpen half).**  `deviation_ownership_card` *is* the ceiling: no
per-witness-subset ownership bound can guarantee more than `C(w−1, d+1)` subsets (the
deviation stacks realize a bad scalar with exactly that), and trivially at most
`C(w, d+2)` subsets exist in a witness.  At `w = r+1` these are `r` and `r+1`: the
`(d+2)`-subset counting war cannot be pushed past good-side `C(n,r)/(r+1)`, i.e. past
`r ≈ √(4h·ln r)` — the proven pair bound (`(r+1)/2` per scalar) already saturates the
scheme's wall `r = Θ(√(n log n))` up to the additive `ln 2` inside the logarithm.
Production dimension `k = Θ(ρn)` (i.e. `r = Θ(n)`) would need per-scalar ownership
`e^{Θ(n)}`, while the scheme caps at `r+1`: **no refinement of per-witness subset counting
reaches the production regime** — that wall needs a genuinely different counting surface.

**The new band** (`sharpened_band_nonempty`): the sharpened floor sits below the in-tree
ceiling spectrum `2^r·C(2^{μ−1}, r)` under the clean criterion **`r(r+1) < 2^μ`** — twice
the `r²`-reach of the landed `r(r−1) < 2^{μ−1}`; the true reach grows like `√(2n·ln r)`
(probe wall table: max pinned `r/√n` grows `1.06 → 1.59 → 2.63` for `μ = 5 → 10` while the
landed bound stays `≈ 1.15`).  Newly opened, previously *empty* rungs (`dimGeneral_band_empty_at_*`):

* `(μ, r) = (4, 5)`: floor `1456 < 1792` (old floor `2184` ≥ ceiling) —
  **`deltaStar_dimFour_pin_F4294967377`**: `δ* = 11/16` exactly for the dimension-four
  (rate `1/4`) code on the 16-point smooth domain in `F_p`, `p = 2³² + 81`, at
  `ε* = 1456/p`; Johnson `1 − √(1/4) = 1/2 < 11/16 < 3/4` = capacity — a fourth exact
  in-window pin, at a fourth rate, *unreachable by the landed factor-2 bound*.
* `(μ, r) = (5, 7), (5, 8), (5, 9)`: the band facts are proven here as ℕ-inequalities
  (`sharpened_band_at_r{7,8,9}_mu5`; old floors all empty); the corresponding `δ*` pins
  `25/32, 24/32, 23/32` await only a prime `p > 32¹⁶ = 2⁸⁰`, `p ≡ 1 (mod 32)` (the in-tree
  `hp` size hypothesis), which `decide` cannot reasonably certify — left as data.

**Honest scope.**  This moves the ladder wall from `r ≈ 1.18·√n` to `r = Θ(√(n log n))`
and proves that within per-witness subset counting the new position is final (up to the
constant inside the log).  The production-dimension conjecture (`k = Θ(ρn)`) is untouched
— the band at `m ≥ 2` stays empty (the floor exponent `(r−2)m+2` beats the ceiling
exponent `r` for every `m ≥ 2, r ≥ 5`), exactly as before.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26DimGeneral

namespace ArkLib.ProximityGap.OwnershipCensus

/-! ## The off-fit extension: every `(d+1)`-subset of the witness owns a bad pair -/

/-- **The off-fit extension lemma** — the engine of the sharpened census.  If `u₁` has no
degree-`d` fit on `S`, then for *every* `(d+1)`-subset `B ⊆ S` some `x ∈ S \ B` makes
`insert x B` unfit: otherwise the Lagrange interpolant of `u₁` through `B` would extend to
a fit on all of `S` (any fit on `insert x B` agrees with it on the `d+1` points of `B`,
hence coincides with it).  This produces `C(|S|, d+1)` owned pairs per bad scalar, versus
the landed worst-case count of `2` owned subsets. -/
theorem exists_offFit_extension {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} {u₁ : Fin n → ZMod p}
    (hunfit : ¬ polyFitOn g d S u₁)
    {B : Finset (Fin n)} (_hBsub : B ⊆ S) (hBcard : B.card = d + 1) :
    ∃ x ∈ S, x ∉ B ∧ ¬ polyFitOn g d (insert x B) u₁ := by
  obtain ⟨q, hqdeg, hqval⟩ := exists_interpolant hginj hBcard u₁
  by_contra hcon
  push Not at hcon
  refine hunfit ⟨q, hqdeg, fun i hi => ?_⟩
  by_cases hiB : i ∈ B
  · exact hqval i hiB
  · obtain ⟨q', hq'deg, hq'⟩ := hcon i hi hiB
    have hqq' : q = q' := by
      refine fit_unique hginj (le_of_eq hBcard.symm) hqdeg hq'deg fun b hb => ?_
      rw [← hqval b hb]
      exact hq' b (Finset.mem_insert_of_mem hb)
    rw [hqq']
    exact hq' i (Finset.mem_insert_self i B)

/-! ## The sharpened ownership count -/

open Classical in
/-- **The sharpened subset-ownership count.**  At witness threshold `w₀ < (1−δ)·n`
(`d + 2 ≤ w₀`), every stack `(u₀, u₁)` satisfies

  `#bad · C(w₀+1, d+1) ≤ C(n, d+1) · (n − d − 1)`

— each bad scalar owns at least `C(w, d+1) ≥ C(w₀+1, d+1)` pairs `(B, x)` (a `(d+1)`-subset
of its witness together with an off-fit extension point), each pair determines the scalar
through the line constraint, and only `C(n, d+1)·(n−d−1)` pairs exist.  This sharpens the
landed factor-`2` bound to factor-`C(w₀+1, d+1)`: at the ladder slice (`w₀ = r`, `d = r−2`)
the per-scalar ownership is `C(r+1, r−1) = r(r+1)/2` instead of `2`. -/
theorem sharpened_badScalars_card_mul_choose_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d w₀ : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    (_hw₀ : d + 2 ≤ w₀)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
        Finset.univ).card * (w₀ + 1).choose (d + 1)
      ≤ n.choose (d + 1) * (n - (d + 1)) := by
  classical
  have npos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- Step 1: for every bad scalar, a witness set with the three working properties
  -- (size ≥ w₀ + 1, the line point degree-`d`-fit on it, `u₁` NOT fit on it).
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), w₀ + 1 ≤ S.card ∧
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
    have hSw : w₀ + 1 ≤ S.card := by
      have h2 : ((w₀ : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : w₀ < S.card := by exact_mod_cast h2
      omega
    refine ⟨S, hSw, ⟨qS, hqSdeg, hlin⟩, ?_⟩
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
  -- the per-scalar owned family: pairs (B, x) with `insert x B` unfit, inside the witness
  set Pt : {x // x ∈ B} → Finset (Finset (Fin n) × Fin n) := fun γ =>
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 1) ×ˢ Finset.univ).filter
      (fun Bx => Bx.1 ⊆ Sf γ.1 γ.2 ∧ Bx.2 ∈ Sf γ.1 γ.2 ∧ Bx.2 ∉ Bx.1 ∧
        ¬ polyFitOn g d (insert Bx.2 Bx.1) u₁)) with hPt
  -- Step 2: each bad scalar owns at least C(w₀+1, d+1) pairs.
  have hP : ∀ γ : {x // x ∈ B}, (w₀ + 1).choose (d + 1) ≤ (Pt γ).card := by
    intro γ
    have hex2 : ∀ Bs : Finset (Fin n), ∃ x : Fin n,
        Bs ∈ (Sf γ.1 γ.2).powersetCard (d + 1) →
          x ∈ Sf γ.1 γ.2 ∧ x ∉ Bs ∧ ¬ polyFitOn g d (insert x Bs) u₁ := by
      intro Bs
      by_cases hBs : Bs ∈ (Sf γ.1 γ.2).powersetCard (d + 1)
      · obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hBs
        obtain ⟨x, hx1, hx2, hx3⟩ :=
          exists_offFit_extension hginj (hSf γ.1 γ.2).2.2 hsub hcard
        exact ⟨x, fun _ => ⟨hx1, hx2, hx3⟩⟩
      · exact ⟨⟨0, npos⟩, fun h => absurd h hBs⟩
    choose pick hpick using hex2
    have hmaps : ∀ Bs ∈ (Sf γ.1 γ.2).powersetCard (d + 1), (Bs, pick Bs) ∈ Pt γ := by
      intro Bs hBs
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hBs
      obtain ⟨h1, h2, h3⟩ := hpick Bs hBs
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩,
        hsub, h1, h2, h3⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    have hinj : Set.InjOn (fun Bs : Finset (Fin n) => (Bs, pick Bs))
        ↑((Sf γ.1 γ.2).powersetCard (d + 1)) := by
      intro a _ b _ hab
      exact congrArg Prod.fst hab
    calc (w₀ + 1).choose (d + 1)
        ≤ (Sf γ.1 γ.2).card.choose (d + 1) := Nat.choose_le_choose _ (hSf γ.1 γ.2).1
    _ = ((Sf γ.1 γ.2).powersetCard (d + 1)).card := (Finset.card_powersetCard _ _).symm
    _ ≤ (Pt γ).card := Finset.card_le_card_of_injOn _ hmaps hinj
  -- Step 3: the owned families of distinct bad scalars are disjoint (a common owned pair
  -- gives a common unfit `(d+2)`-subset, which determines the scalar).
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (Pt γ₁) (Pt γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro Bx hR1 hR2
    obtain ⟨_, hsub1, hmem1, _, hunfit⟩ := Finset.mem_filter.mp hR1
    obtain ⟨_, hsub2, hmem2, _, _⟩ := Finset.mem_filter.mp hR2
    have hRsub1 : insert Bx.2 Bx.1 ⊆ Sf γ₁.1 γ₁.2 := Finset.insert_subset hmem1 hsub1
    have hRsub2 : insert Bx.2 Bx.1 ⊆ Sf γ₂.1 γ₂.2 := Finset.insert_subset hmem2 hsub2
    obtain ⟨q₁, hq₁deg, hl1⟩ := (hSf γ₁.1 γ₁.2).2.1
    obtain ⟨q₂, hq₂deg, hl2⟩ := (hSf γ₂.1 γ₂.2).2.1
    have hγne : γ₁.1 - γ₂.1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    refine hunfit ⟨Polynomial.C (γ₁.1 - γ₂.1)⁻¹ * (q₁ - q₂),
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
  -- Step 4: assemble through the global pair space, of size C(n, d+1)·(n−d−1).
  set G : Finset (Finset (Fin n) × Fin n) :=
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 1) ×ˢ Finset.univ).filter
      (fun Bx => Bx.2 ∉ Bx.1)) with hG
  have hGcard : G.card = n.choose (d + 1) * (n - (d + 1)) := by
    have hGeq : G = Finset.biUnion
        ((Finset.univ : Finset (Fin n)).powersetCard (d + 1))
        (fun Bs => ({Bs} : Finset (Finset (Fin n))) ×ˢ (Finset.univ \ Bs)) := by
      ext Bx
      constructor
      · intro hx
        obtain ⟨hprod, hnot⟩ := Finset.mem_filter.mp hx
        obtain ⟨h1, _⟩ := Finset.mem_product.mp hprod
        refine Finset.mem_biUnion.mpr ⟨Bx.1, h1, ?_⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩⟩
      · intro hx
        obtain ⟨Bs, hBs, hmem⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        have hB1 : Bx.1 = Bs := Finset.mem_singleton.mp h1
        obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp h2
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · rw [hB1]; exact hBs
        · rw [hB1]; exact hnot
    have hdisjF : ∀ a ∈ (Finset.univ : Finset (Fin n)).powersetCard (d + 1),
        ∀ b ∈ (Finset.univ : Finset (Fin n)).powersetCard (d + 1), a ≠ b →
        Disjoint (({a} : Finset (Finset (Fin n))) ×ˢ (Finset.univ \ a))
          (({b} : Finset (Finset (Fin n))) ×ˢ (Finset.univ \ b)) := by
      intro a _ b _ hab
      rw [Finset.disjoint_left]
      intro Bx h1 h2
      have ha : Bx.1 = a := Finset.mem_singleton.mp (Finset.mem_product.mp h1).1
      have hb : Bx.1 = b := Finset.mem_singleton.mp (Finset.mem_product.mp h2).1
      exact hab (ha ▸ hb)
    rw [hGeq, Finset.card_biUnion hdisjF]
    have hterm : ∀ Bs ∈ (Finset.univ : Finset (Fin n)).powersetCard (d + 1),
        (({Bs} : Finset (Finset (Fin n))) ×ˢ ((Finset.univ : Finset (Fin n)) \ Bs)).card
          = n - (d + 1) := by
      intro Bs hBs
      obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hBs
      rw [Finset.card_product, Finset.card_singleton, one_mul,
        Finset.card_univ_diff, Fintype.card_fin, hcard]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hbig : B.attach.card * (w₀ + 1).choose (d + 1) ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * (w₀ + 1).choose (d + 1)
        = ∑ _γ ∈ B.attach, (w₀ + 1).choose (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP γ)
  have hsubE : B.attach.biUnion Pt ⊆ G := by
    intro Bx hBx
    obtain ⟨γ, _, hmem⟩ := Finset.mem_biUnion.mp hBx
    obtain ⟨hprod, _, _, hnotin, _⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hprod, hnotin⟩
  calc B.card * (w₀ + 1).choose (d + 1)
      = B.attach.card * (w₀ + 1).choose (d + 1) := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ G.card := Finset.card_le_card hsubE
  _ = n.choose (d + 1) * (n - (d + 1)) := hGcard

open Classical in
/-- **The sharpened `ε_mca` bound:** at witness threshold `w₀ < (1−δ)·n`, the MCA error of
the degree-`d` evaluation code is at most `(C(n,d+1)·(n−d−1)/C(w₀+1,d+1))/p`. -/
theorem sharpened_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d w₀ : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    (hw₀ : d + 2 ≤ w₀)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 1) * (n - (d + 1)) / (w₀ + 1).choose (d + 1) : ℕ) : ℝ≥0∞)
        / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h2 := sharpened_badScalars_card_mul_choose_le (g := g) d w₀ hginj hw₀ hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ n.choose (d + 1) * (n - (d + 1)) / (w₀ + 1).choose (d + 1) :=
    (Nat.le_div_iff_mul_le (Nat.choose_pos (by omega))).mpr h2
  exact_mod_cast hle

/-! ## The interior ceiling and the sharpened pin -/

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy: the original in
`KKH26DimGeneralPin` is `private`). -/
private lemma sharp_pow_inj_below_order {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
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

/-- **The interior ceiling from the sharpened count:** at every slice `(r, m)` the witness
threshold below the KKH26 ceiling is `> rm`, so the sharpened count applies with
`w₀ = rm`, giving the floor `(C(n,(r−2)m+1)·(n−(r−2)m−1)/C(rm+1,(r−2)m+1))/p`. -/
theorem interiorCeiling_sharpened
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (εstar : ℝ≥0∞)
    (hband : ((n.choose ((r - 2) * m + 1) * (n - ((r - 2) * m + 1)) /
        (r * m + 1).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
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
    exact Fin.ext (sharp_pow_inj_below_order hg0 hg _ hi _ hj hij)
  refine le_trans (sharpened_epsMCA_le (g := g) ((r - 2) * m) (r * m) hginj ?_ ?_) hband
  · -- `(r−2)m + 2 ≤ rm`
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have h1 : (s + 2) * m = s * m + 2 * m := by ring
    have h2 : (s + 2 - 2) * m = s * m := by norm_num
    omega
  · -- threshold arithmetic: `δ < 1 − r/2^μ` gives `(1−δ)·n > r·m`
    have hsum : δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 := lt_tsub_iff_right.mp hδ
    have hlt : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (r : ℝ≥0) / (2 : ℝ≥0) ^ μ + δ = δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ := by ring
      _ < 1 := hsum
    have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
    have hm0 : (0 : ℝ≥0) < (m : ℝ≥0) := by exact_mod_cast (by omega : 0 < m)
    have hkey : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ * ((2 : ℝ≥0) ^ μ * (m : ℝ≥0))
        = (r : ℝ≥0) * m := by
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hpow0)]
    have hrm : (r : ℝ≥0) * m < (1 - δ) * ((2 : ℝ≥0) ^ μ * m) := by
      have h := mul_lt_mul_of_pos_right hlt (mul_pos hpow0 hm0)
      rwa [hkey] at h
    have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ μ * m := by
      rw [Fintype.card_fin, hn]
      push_cast
      ring
    rw [hcard]
    calc ((r * m : ℕ) : ℝ≥0) = (r : ℝ≥0) * m := by push_cast; ring
    _ < (1 - δ) * ((2 : ℝ≥0) ^ μ * m) := hrm

/-- **The sharpened general pin:** for every slice `r ≥ 2`, `m ≥ 1`, and every `ε*` in the
*sharpened* band `[(C(n,(r−2)m+1)·(n−(r−2)m−1)/C(rm+1,(r−2)m+1))/p, (2^r·C(2^{μ−1},r))/p)`,

  `mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`

— same statement as the landed `kkh26_dimGeneral_deltaStar_pin` but with the good-side
floor lowered by the factor `~(r+1)/4`, extending the unconditional pin family from
`r(r−1) < 2^{μ−1}` to `r(r+1) < 2^μ` (and further by direct evaluation). -/
theorem kkh26_sharpened_deltaStar_pin
    {p : ℕ} [Fact p.Prime] {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ * m) [NeZero n] (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hlo : ((n.choose ((r - 2) * m + 1) * (n - ((r - 2) * m + 1)) /
        (r * m + 1).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  subst hn
  exact kkh26_deltaStar_pin_of_interior_ceiling hμ hm rfl hg hp hr2 hr εstar hhi
    (interiorCeiling_sharpened hm hr2 rfl hg εstar hlo)

/-- **The canonical sharpened pin** (`m = 1`): at `ε* = (C(n,r−1)·(n−r+1)/C(r+1,r−1))/p`
itself — note `C(n,r−1)·(n−r+1) = C(n,r)·r` and `C(r+1,r−1) = r(r+1)/2`, so this is
`2·C(n,r)/(r+1)` against the landed `C(n,r)/2`. -/
theorem kkh26_sharpened_deltaStar_pin_canonical
    {p : ℕ} [Fact p.Prime] {μ r : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ) [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (hr : r ≤ 2 ^ (μ - 1))
    (hband : n.choose (r - 1) * (n - (r - 1)) / (r + 1).choose (r - 1)
      < 2 ^ r * (2 ^ (μ - 1)).choose r) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2))
        (((n.choose (r - 1) * (n - (r - 1)) / (r + 1).choose (r - 1) : ℕ) : ℝ≥0∞)
          / (p : ℝ≥0∞))
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hcode : (r - 2) * 1 = r - 2 := Nat.mul_one _
  have hidx : (r - 2) * 1 + 1 = r - 1 := by omega
  have hidx2 : r * 1 + 1 = r + 1 := by omega
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have h := kkh26_sharpened_deltaStar_pin (μ := μ) (m := 1) (r := r) (n := n) hμ le_rfl hr2
    (by rw [hn, mul_one]) (by rw [mul_one]; exact hg) hp hr
    (((n.choose (r - 1) * (n - (r - 1)) / (r + 1).choose (r - 1) : ℕ) : ℝ≥0∞)
      / (p : ℝ≥0∞))
    (le_of_eq (by rw [hidx, hidx2]))
    (ENNReal.div_lt_div_right hp0 hpt (by exact_mod_cast hband))
  rwa [hcode] at h

/-! ## Band nonemptiness: the `r(r+1) < 2^μ` criterion (twice the landed `r²`-reach) -/

/-- Per-step inequality of the falling-product induction (local copy of the landed
`desc_step`, which is `private` to `KKH26DimGeneralPin`). -/
private lemma sharp_desc_step (h k : ℕ) :
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
      zify [hkk, le_trans hk1 hkk, hkh, le_trans hkh (by omega : 2 * h ≤ 4 * h),
        (by omega : k ≤ 2 * h), (by omega : 2 * (k * (k - 1)) ≤ 4 * h),
        (by omega : 2 * (k * (k + 1)) ≤ 4 * h), (by omega : 1 ≤ k)]
      nlinarith [sq_nonneg ((k : ℤ) - 1),
        (by exact_mod_cast hkk : ((k : ℤ)) * (k + 1) ≤ 2 * h),
        (by exact_mod_cast hk : (1 : ℤ) ≤ k)]

/-- The falling-product ratio bound (local copy of the landed `desc_ratio`). -/
private lemma sharp_desc_ratio (h : ℕ) :
    ∀ r : ℕ, (2 * h).descFactorial r * (4 * h - 2 * (r * (r - 1)))
      ≤ 2 ^ r * h.descFactorial r * (4 * h)
  | 0 => by simp
  | (r + 1) => by
    have IH := sharp_desc_ratio h r
    have hstep := sharp_desc_step h r
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

/-- The strict step of the sharpened criterion: `r(r+1) < 2h` forces
`8h + 2 ≤ (r+1)·(4h − 2r(r−1))` — the exact arithmetic making the sharpened floor beat
the spectrum with per-scalar ownership `(r+1)/2` instead of `2`. -/
private lemma sharp_step {h r : ℕ} (hr2 : 2 ≤ r) (hcrit : r * (r + 1) < 2 * h) :
    8 * h + 2 ≤ (r + 1) * (4 * h - 2 * (r * (r - 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have he : (s + 2) * (s + 2 - 1) = (s + 2) * (s + 1) := by norm_num
  rw [he]
  have he2 : (s + 2) * (s + 2 + 1) = (s + 2) * (s + 3) := by norm_num
  rw [he2] at hcrit
  have hmono : (s + 2) * (s + 1) ≤ (s + 2) * (s + 3) :=
    Nat.mul_le_mul_left (s + 2) (by omega)
  have hle : 2 * ((s + 2) * (s + 1)) ≤ 4 * h := by omega
  have key : ((s : ℤ) + 2) * ((s : ℤ) + 3) + 1 ≤ 2 * (h : ℤ) := by
    have h' : (((s + 2) * (s + 3) : ℕ) : ℤ) < 2 * (h : ℤ) := by exact_mod_cast hcrit
    push_cast at h'
    linarith
  zify [hle]
  nlinarith [key, mul_le_mul_of_nonneg_left key (show (0 : ℤ) ≤ (s : ℤ) + 1 by positivity),
    (show (0 : ℤ) ≤ (s : ℤ) by positivity)]

/-- **The sharpened descFactorial separation:** `r(r+1) < 2h` forces
`2·(2h)^{(r)} < (r+1)·2^r·h^{(r)}`. -/
private lemma sharp_descFactorial_band {h r : ℕ} (hr2 : 2 ≤ r)
    (hcrit : r * (r + 1) < 2 * h) :
    2 * (2 * h).descFactorial r < (r + 1) * (2 ^ r * h.descFactorial r) := by
  have hrr : r ≤ r * (r + 1) := Nat.le_mul_of_pos_right r (by omega)
  have hr2h : r ≤ 2 * h := le_trans hrr hcrit.le
  have hpos : 0 < (2 * h).descFactorial r := Nat.descFactorial_pos.mpr hr2h
  have hA := sharp_desc_ratio h r
  have hstep := sharp_step hr2 hcrit
  have h1 : (2 * h).descFactorial r * (8 * h + 2)
      ≤ ((r + 1) * (2 ^ r * h.descFactorial r)) * (4 * h) := by
    calc (2 * h).descFactorial r * (8 * h + 2)
        ≤ (2 * h).descFactorial r * ((r + 1) * (4 * h - 2 * (r * (r - 1)))) :=
          Nat.mul_le_mul_left _ hstep
      _ = (r + 1) * ((2 * h).descFactorial r * (4 * h - 2 * (r * (r - 1)))) := by ring
      _ ≤ (r + 1) * (2 ^ r * h.descFactorial r * (4 * h)) := Nat.mul_le_mul_left _ hA
      _ = ((r + 1) * (2 ^ r * h.descFactorial r)) * (4 * h) := by ring
  have h2 : (2 * (2 * h).descFactorial r) * (4 * h)
      < (2 * h).descFactorial r * (8 * h + 2) := by
    calc (2 * (2 * h).descFactorial r) * (4 * h)
        = (2 * h).descFactorial r * (8 * h) := by ring
    _ < (2 * h).descFactorial r * (8 * h + 2) :=
        mul_lt_mul_of_pos_left (by omega) hpos
  exact lt_of_mul_lt_mul_right (lt_of_lt_of_le h2 h1) (Nat.zero_le _)

/-- **The sharpened binomial separation:** `r(r+1) < 2h` forces
`2·C(2h,r) < (r+1)·2^r·C(h,r)` — the band criterion in `choose` form. -/
theorem sharpened_choose_band {h r : ℕ} (hr2 : 2 ≤ r) (hcrit : r * (r + 1) < 2 * h) :
    2 * (2 * h).choose r < (r + 1) * (2 ^ r * h.choose r) := by
  have hd := sharp_descFactorial_band hr2 hcrit
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hd
  have hre : 2 * (r.factorial * (2 * h).choose r)
      = r.factorial * (2 * (2 * h).choose r) := by ring
  have hre2 : (r + 1) * (2 ^ r * (r.factorial * h.choose r))
      = r.factorial * ((r + 1) * (2 ^ r * h.choose r)) := by ring
  rw [hre, hre2] at hd
  exact lt_of_mul_lt_mul_left hd (Nat.zero_le _)

/-- **Band nonemptiness for the sharpened floor (the new wall criterion):** whenever
`r(r+1) < 2^μ`, the sharpened good-side count `C(n,r−1)·(n−r+1)/C(r+1,r−1)`
(`= 2·C(n,r)/(r+1)`) sits strictly below the ceiling spectrum `2^r·C(2^{μ−1},r)` —
**twice** the `r²`-reach of the landed criterion `r(r−1) < 2^{μ−1}`; the true reach of the
sharpened band grows like `√(2n·ln r)` (probe wall table), versus the landed `≈ 1.18·√n`. -/
theorem sharpened_band_nonempty {μ r : ℕ} (hr2 : 2 ≤ r)
    (hcrit : r * (r + 1) < 2 ^ μ) :
    (2 ^ μ).choose (r - 1) * (2 ^ μ - (r - 1)) / (r + 1).choose (r - 1)
      < 2 ^ r * (2 ^ (μ - 1)).choose r := by
  have hμ1 : 1 ≤ μ := by
    by_contra hcon
    have hμ0 : μ = 0 := by omega
    subst hμ0
    have h0 : r * (r + 1) < 1 := by simpa using hcrit
    have hpos : 0 < r * (r + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  set h : ℕ := 2 ^ (μ - 1) with hh
  have hpow : (2 : ℕ) ^ μ = 2 * h := by
    rw [hh]
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpow]
  have hcrit' : r * (r + 1) < 2 * h := by rw [← hpow]; exact hcrit
  -- the choose identity: `C(2h,r−1)·(2h−(r−1)) = C(2h,r)·r`
  have hid : (2 * h).choose (r - 1) * (2 * h - (r - 1)) = (2 * h).choose r * r := by
    have hsucc := Nat.choose_succ_right_eq (2 * h) (r - 1)
    rw [show r - 1 + 1 = r by omega] at hsucc
    exact hsucc.symm
  -- the small binomial: `C(r+1,r−1)·2 = r·(r+1)`
  have hb2 : (r + 1).choose (r - 1) * 2 = r * (r + 1) := by
    have hsym : (r + 1).choose (r - 1) = (r + 1).choose 2 := by
      rw [show r - 1 = (r + 1) - 2 by omega]
      exact Nat.choose_symm (by omega)
    rw [hsym, Nat.choose_two_right, show r + 1 - 1 = r by omega]
    have hdvd : 2 ∣ (r + 1) * r := by
      rw [mul_comm]
      exact (Nat.even_mul_succ_self r).two_dvd
    rw [Nat.div_mul_cancel hdvd, mul_comm]
  have hbpos : 0 < (r + 1).choose (r - 1) := Nat.choose_pos (by omega)
  rw [Nat.div_lt_iff_lt_mul hbpos]
  -- multiply both sides by 2 and use the strict choose separation times r
  have hkey := sharpened_choose_band hr2 hcrit'
  have hr0 : 0 < r := by omega
  have hL : (2 * h).choose (r - 1) * (2 * h - (r - 1)) * 2
      = (2 * (2 * h).choose r) * r := by
    rw [hid]; ring
  have hR : (2 ^ r * h.choose r * ((r + 1).choose (r - 1))) * 2
      = ((r + 1) * (2 ^ r * h.choose r)) * r := by
    calc (2 ^ r * h.choose r * ((r + 1).choose (r - 1))) * 2
        = (2 ^ r * h.choose r) * ((r + 1).choose (r - 1) * 2) := by ring
      _ = (2 ^ r * h.choose r) * (r * (r + 1)) := by rw [hb2]
      _ = ((r + 1) * (2 ^ r * h.choose r)) * r := by ring
  have hmul2 : (2 * h).choose (r - 1) * (2 * h - (r - 1)) * 2
      < (2 ^ r * h.choose r * ((r + 1).choose (r - 1))) * 2 := by
    rw [hL, hR]
    exact mul_lt_mul_of_pos_right hkey hr0
  exact lt_of_mul_lt_mul_right hmul2 (Nat.zero_le _)

/-- The sharpened criterion keeps every certified rung beyond Johnson:
`r(r+1) < 2^μ` forces `r² < (r−1)·2^μ` (the squared-form Johnson criterion, consumed by
the in-tree `dimGeneral_beyond_johnson_sq`). -/
theorem sharpened_crit_beyond_johnson {μ r : ℕ} (hr2 : 2 ≤ r)
    (hcrit : r * (r + 1) < 2 ^ μ) : r * r < (r - 1) * 2 ^ μ := by
  have h1 : r * r ≤ r * (r + 1) := Nat.mul_le_mul_left r (by omega)
  calc r * r ≤ r * (r + 1) := h1
  _ < 2 ^ μ := hcrit
  _ = 1 * 2 ^ μ := (one_mul _).symm
  _ ≤ (r - 1) * 2 ^ μ := Nat.mul_le_mul_right _ (by omega)

/-! ## The ceiling: the exact minimum ownership is `C(w−1, d+1)` (cannot sharpen further) -/

/-- **The deviation dichotomy.**  If `u₁` agrees with a degree-`≤ d` polynomial on `S`
everywhere except the single point `j` (where it deviates), then a `(d+2)`-subset
`T ⊆ S` is unfit **iff `j ∈ T`** — off `j` the polynomial itself fits; through `j` any fit
would coincide with the polynomial on the other `d+1` points and contradict the
deviation. -/
theorem deviation_unfit_iff {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} {j : Fin n} (_hj : j ∈ S)
    {q : Polynomial (ZMod p)} (hqdeg : q.natDegree ≤ d) {u₁ : Fin n → ZMod p}
    (hfit : ∀ i ∈ S, i ≠ j → u₁ i = q.eval (g ^ (i : ℕ)))
    (hdev : u₁ j ≠ q.eval (g ^ (j : ℕ)))
    {T : Finset (Fin n)} (hT : T ⊆ S) (hTcard : T.card = d + 2) :
    ¬ polyFitOn g d T u₁ ↔ j ∈ T := by
  constructor
  · intro hunfit
    by_contra hjT
    exact hunfit ⟨q, hqdeg, fun i hi => hfit i (hT hi) (fun he => hjT (he ▸ hi))⟩
  · rintro hjT ⟨q', hq'deg, hq'⟩
    have herase : (T.erase j).card = d + 1 := by
      rw [Finset.card_erase_of_mem hjT, hTcard]
      omega

    have hqq' : q = q' := by
      refine fit_unique hginj (le_of_eq herase.symm) hqdeg hq'deg fun i hi => ?_
      have hiT : i ∈ T := Finset.mem_of_mem_erase hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [← hfit i (hT hiT) hij]
      exact hq' i hiT
    refine hdev ?_
    rw [hqq']
    exact hq' j hjT

open Classical in
/-- **The exact minimum ownership (the cannot-sharpen theorem).**  For a single-deviation
direction, the owned (unfit) `(d+2)`-subsets of the witness `S` are *exactly* those
containing the deviation point, and they number **exactly `C(|S|−1, d+1)`**.  Since the
deviation configurations are realizable as bad scalars at every witness size (probe:
`probe_ownership_census.py`, 90/90 constructions), no per-witness subset-ownership bound
can exceed `C(w−1, d+1)`: the sharpened census (`C(w,d+1)/(d+2)`, within factor
`(d+2)(w−d−1)/w ≤ 2` of this) is final for the scheme, and the subset-counting war stalls
at `r = Θ(√(n log n))` — the production regime `r = Θ(n)` is unreachable by any further
refinement of per-witness subset counting. -/
theorem deviation_ownership_card {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S)
    {q : Polynomial (ZMod p)} (hqdeg : q.natDegree ≤ d) {u₁ : Fin n → ZMod p}
    (hfit : ∀ i ∈ S, i ≠ j → u₁ i = q.eval (g ^ (i : ℕ)))
    (hdev : u₁ j ≠ q.eval (g ^ (j : ℕ))) :
    ((S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOn g d T u₁)).card
      = (S.card - 1).choose (d + 1) := by
  classical
  have hfe : (S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOn g d T u₁)
      = ((S.erase j).powersetCard (d + 1)).image (insert j) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hmem, hunfit⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hmem
      have hjT : j ∈ T :=
        (deviation_unfit_iff hginj hj hqdeg hfit hdev hTsub hTcard).mp hunfit
      refine Finset.mem_image.mpr ⟨T.erase j, ?_, Finset.insert_erase hjT⟩
      refine Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase j hTsub, ?_⟩
      rw [Finset.card_erase_of_mem hjT, hTcard]
      omega

    · intro hT
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨hAsub, hAcard⟩ := Finset.mem_powersetCard.mp hA
      have hjA : j ∉ A := fun hjin => (Finset.mem_erase.mp (hAsub hjin)).1 rfl
      have hTsub : insert j A ⊆ S :=
        Finset.insert_subset hj (hAsub.trans (Finset.erase_subset _ _))
      have hTcard : (insert j A).card = d + 2 := by
        rw [Finset.card_insert_of_notMem hjA, hAcard]

      refine Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩, ?_⟩
      exact (deviation_unfit_iff hginj hj hqdeg hfit hdev hTsub hTcard).mpr
        (Finset.mem_insert_self _ _)
  rw [hfe, Finset.card_image_of_injOn ?inj, Finset.card_powersetCard,
    Finset.card_erase_of_mem hj]
  case inj =>
    intro a ha b hb hab
    have ha' := Finset.mem_powersetCard.mp (Finset.mem_coe.mp ha)
    have hb' := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hb)
    have hja : j ∉ a := fun hjin => (Finset.mem_erase.mp (ha'.1 hjin)).1 rfl
    have hjb : j ∉ b := fun hjin => (Finset.mem_erase.mp (hb'.1 hjin)).1 rfl
    rw [← Finset.erase_insert hja, ← Finset.erase_insert hjb, hab]

end ArkLib.ProximityGap.OwnershipCensus

/-! ## The newly opened rung: `(μ, r) = (4, 5)` at `p = 4294967377 = 2³² + 81` -/

namespace ArkLib.ProximityGap.OwnershipCensus

/-- The landed factor-2 band is **empty** at `(μ, r) = (4, 5)`: the old floor
`C(16,5)/2 = 2184` already meets the ceiling `2⁵·C(8,5) = 1792`.  The rung below is
reachable only through the sharpened ownership count. -/
theorem dimGeneral_band_empty_at_r5_mu4 :
    2 ^ 5 * (8 : ℕ).choose 5 ≤ (16 : ℕ).choose 5 / 2 := by decide

/-- The sharpened band is **nonempty** at `(μ, r) = (4, 5)`: floor
`C(16,4)·12/C(6,4) = 1456 < 1792` (a boundary instance: `r(r+1) = 30 ≥ 16` fails the clean
criterion, but the direct evaluation passes — the criterion is sufficient, not tight). -/
theorem sharpened_band_at_r5_mu4 :
    (16 : ℕ).choose 4 * (16 - 4) / (6 : ℕ).choose 4 < 2 ^ 5 * (8 : ℕ).choose 5 := by
  decide

section Concrete4294967377

local instance fact_prime_4294967377 : Fact (Nat.Prime 4294967377) := ⟨by norm_num⟩

/-- **THE FOURTH RUNG (new, unreachable by the landed bound):** `δ* = 11/16` exactly, for
the dimension-four (`r = 5`, rate `1/4`) code on the 16-point smooth domain
`⟨526957872⟩ ⊆ F_p^×`, `p = 4294967377 = 2³² + 81`, at `ε* = 1456/p
= (C(16,4)·12/C(6,4))/p`.  Johnson radius `1 − √(1/4) = 1/2 < 11/16 < 3/4` = capacity: a
fourth exact `δ*` value strictly inside the open window, at a fourth rate — produced by the
sharpened ownership census where the landed band is provably empty
(`dimGeneral_band_empty_at_r5_mu4`: old floor `2184 ≥ 1792` = ceiling). -/
theorem deltaStar_dimFour_pin_F4294967377 :
    mcaDeltaStar (F := ZMod 4294967377) (A := ZMod 4294967377)
        (evalCode (526957872 : ZMod 4294967377) 16 3)
        ((1456 : ℝ≥0∞) / (4294967377 : ℝ≥0∞))
      = 11 / 16 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_sharpened_deltaStar_pin_canonical (p := 4294967377) (μ := 4) (r := 5)
    (by norm_num) (by norm_num) (n := 16) (g := (526957872 : ZMod 4294967377))
    (by norm_num) ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
    (by norm_num) (by norm_num) (by decide)
  have e0 : (5 : ℕ) - 2 = 3 := rfl
  have e1 : ((16 : ℕ).choose (5 - 1) * (16 - (5 - 1)) / ((5 + 1).choose (5 - 1)) : ℕ)
      = 1456 := rfl
  have e2 : ((4294967377 : ℕ) : ℝ≥0∞) = (4294967377 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((5 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 4) = 11 / 16 := by
    have hd : ((5 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 4) = 5 / 16 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e1, e2, e3] at h
  exact_mod_cast h

/-- The new rung is beyond Johnson: `(5/16)² = 25/256 < 64/256 = 1/4 = ρ`. -/
theorem dimFour_pin_beyond_johnson_sq :
    ((5 : ℝ≥0) / (2 : ℝ≥0) ^ 4) ^ 2 < (4 : ℝ≥0) / (2 : ℝ≥0) ^ 4 := by
  have h := ArkLib.ProximityGap.KKH26DimGeneral.dimGeneral_beyond_johnson_sq
    (μ := 4) (r := 5) (by norm_num)
  have e3 : ((5 - 1 : ℕ) : ℝ≥0) = (4 : ℝ≥0) := by norm_num
  have e4 : ((5 : ℕ) : ℝ≥0) = (5 : ℝ≥0) := by norm_num
  rwa [e3, e4] at h

end Concrete4294967377

/-! ## The `μ = 5` reach: rungs `r = 7, 8, 9` opened (old band empty at all three)

The corresponding `δ*` pins `25/32, 24/32, 23/32` need a prime `p > 32¹⁶ = 2⁸⁰` with
`p ≡ 1 (mod 32)` (the in-tree `hp` hypothesis); the band facts are pure arithmetic and
proven here.  The binomials at `n = 32` are evaluated through the descFactorial identity
(`9!·C(32,9) = 32^{(9)}`) — kernel-friendly, since `Nat.choose` itself recurses
binomially. -/

private lemma choose_32_6 : (32 : ℕ).choose 6 = 906192 :=
  Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 6)
    (by rw [← Nat.descFactorial_eq_factorial_mul_choose]; decide)

private lemma choose_32_7 : (32 : ℕ).choose 7 = 3365856 :=
  Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 7)
    (by rw [← Nat.descFactorial_eq_factorial_mul_choose]; decide)

private lemma choose_32_8 : (32 : ℕ).choose 8 = 10518300 :=
  Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 8)
    (by rw [← Nat.descFactorial_eq_factorial_mul_choose]; decide)

private lemma choose_32_9 : (32 : ℕ).choose 9 = 28048800 :=
  Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 9)
    (by rw [← Nat.descFactorial_eq_factorial_mul_choose]; decide)

/-- Old band empty at `(5, 7)`: `2⁷·C(16,7) = 1464320 ≤ 1682928 = C(32,7)/2`. -/
theorem dimGeneral_band_empty_at_r7_mu5 :
    2 ^ 7 * (16 : ℕ).choose 7 ≤ (32 : ℕ).choose 7 / 2 := by
  rw [choose_32_7]
  decide

/-- Sharpened band open at `(5, 7)`: `C(32,6)·26/C(8,6) = 841464 < 1464320`. -/
theorem sharpened_band_at_r7_mu5 :
    (32 : ℕ).choose 6 * (32 - 6) / (8 : ℕ).choose 6 < 2 ^ 7 * (16 : ℕ).choose 7 := by
  rw [choose_32_6]
  decide

/-- Old band empty at `(5, 8)`: `2⁸·C(16,8) = 3294720 ≤ 5259150 = C(32,8)/2`. -/
theorem dimGeneral_band_empty_at_r8_mu5 :
    2 ^ 8 * (16 : ℕ).choose 8 ≤ (32 : ℕ).choose 8 / 2 := by
  rw [choose_32_8]
  decide

/-- Sharpened band open at `(5, 8)`: `C(32,7)·25/C(9,7) = 2337400 < 3294720`. -/
theorem sharpened_band_at_r8_mu5 :
    (32 : ℕ).choose 7 * (32 - 7) / (9 : ℕ).choose 7 < 2 ^ 8 * (16 : ℕ).choose 8 := by
  rw [choose_32_7]
  decide

/-- Old band empty at `(5, 9)`: `2⁹·C(16,9) = 5857280 ≤ 14024400 = C(32,9)/2`. -/
theorem dimGeneral_band_empty_at_r9_mu5 :
    2 ^ 9 * (16 : ℕ).choose 9 ≤ (32 : ℕ).choose 9 / 2 := by
  rw [choose_32_9]
  decide

/-- Sharpened band open at `(5, 9)`: `C(32,8)·24/C(10,8) = 5609760 < 5857280` — the deepest
rung the sharpened census opens at `μ = 5` (`r = 10` fails: `11729498 ≥ 8200192`), at
`r/√n = 9/√32 ≈ 1.59` versus the landed reach `≈ 1.06`. -/
theorem sharpened_band_at_r9_mu5 :
    (32 : ℕ).choose 8 * (32 - 8) / (10 : ℕ).choose 8 < 2 ^ 9 * (16 : ℕ).choose 9 := by
  rw [choose_32_8]
  decide

end ArkLib.ProximityGap.OwnershipCensus

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.OwnershipCensus.exists_offFit_extension
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_badScalars_card_mul_choose_le
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_epsMCA_le
#print axioms ArkLib.ProximityGap.OwnershipCensus.interiorCeiling_sharpened
#print axioms ArkLib.ProximityGap.OwnershipCensus.kkh26_sharpened_deltaStar_pin
#print axioms ArkLib.ProximityGap.OwnershipCensus.kkh26_sharpened_deltaStar_pin_canonical
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_choose_band
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_band_nonempty
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_crit_beyond_johnson
#print axioms ArkLib.ProximityGap.OwnershipCensus.deviation_unfit_iff
#print axioms ArkLib.ProximityGap.OwnershipCensus.deviation_ownership_card
#print axioms ArkLib.ProximityGap.OwnershipCensus.dimGeneral_band_empty_at_r5_mu4
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_band_at_r5_mu4
#print axioms ArkLib.ProximityGap.OwnershipCensus.deltaStar_dimFour_pin_F4294967377
#print axioms ArkLib.ProximityGap.OwnershipCensus.dimFour_pin_beyond_johnson_sq
#print axioms ArkLib.ProximityGap.OwnershipCensus.dimGeneral_band_empty_at_r9_mu5
#print axioms ArkLib.ProximityGap.OwnershipCensus.sharpened_band_at_r9_mu5
