/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList
import ArkLib.Data.CodingTheory.ProximityGap.DeepQuotientTransfer
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# S2 (#357): the LD⇔MCA dictionary as one bracket — the interpolation sandwich

The two prize quantities of #357 §1 — the MCA threshold `mcaDeltaStar C ε*` and the
interleaved list-decoding profile `δ ↦ |Λ(C^{≡2}, δ)|` — are connected by two transfer
engines that grew in different lanes and were never stated as a single object:

* **upper half** (`epsMCA_le_of_interleavedList_card_le_doubledRadius`, the GCXK25-style
  conversion): a uniform interleaved list bound at radius `2δ` gives
  `ε_mca(C, δ) ≤ (1 + 2δn·L)/q`;
* **lower half** (`deep_quotient_epsMCA_lower_bound`, the [KKH26] App-A DEEP-quotient
  engine): a separated list-decoding configuration of size `L` at radius `δ` gives
  `ε_mca(C', δ) ≥ L/p` for the explicit quotient evaluation code `C'`.

This file welds the two halves onto the bracket engine (`MCAThresholdLedger`) and states the
**bracket-interpolation sandwich**: a list-profile budget at `δgood` and a DEEP configuration
at `δbad` pinch

  `δgood ≤ mcaDeltaStar(evalCode, ε*) ≤ δbad`,

with **every dictionary loss factor explicit in the hypotheses** (the `1 + 2δn·L` numerator
on the good side; the bare `L/p` on the bad side; no other loss). When the two list-side
thresholds meet (`δbad ≤ δgood`), the MCA threshold is *pinned exactly*
(`mcaDeltaStar_eq_of_dictionary_meet`) — i.e. **the `mcaDeltaStar` brackets meet whenever
the list-profile brackets meet**. This is the precise in-tree form of the [ABF26] §5
"collapse" question: the open direction (a good MCA bound *implies* a good interleaved list
bound) is exactly what is *not* provided here, and the sandwich measures what its absence
costs — nothing, for codes whose list profile is pinned; everything, otherwise.

## New objects

* `interleavedListProfile C a` — the worst-case `C^{≡2}` list size over all received stacks
  at agreement floor `a` (`Finset.sup` over the finite stack space): the profile object
  [ABF26] §5 quantifies over, now a single `ℕ`-valued function.
* `evalCodeFin g n d` + `coe_evalCodeFin` + `pairClosed_evalCodeFin` — the KKH26 evaluation
  code as a `Finset` with the `PairClosed` structure the upper half consumes (closure under
  the pair-extraction combinations, from polynomial algebra).
* `DeepListConfig` — the DEEP-quotient list configuration bundled as a structure (word,
  polynomial family, witness sets, degree/size/separation hypotheses), so a future
  beyond-Johnson list lower bound lands here as a single term.
* `le_mcaDeltaStar_of_profile` / `mcaDeltaStar_le_of_deepConfig` — the two ledger-composed
  transfer theorems.
* `mcaDeltaStar_dictionary_sandwich` / `mcaDeltaStar_eq_of_dictionary_meet` — the headline.

## Honest scope

The sandwich is *conditional on its inputs*: the profile budget on the good side (open
beyond Johnson for explicit RS — the 25-year coupling wall), and the configuration supply on
the bad side (open below the KKH26 strip). Both inputs are exactly the named open surfaces
of #357; this file contributes the *lossless welding*, so that any future movement on either
list-side input moves `mcaDeltaStar` mechanically. Nothing here closes the open core.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement.*
  ePrint 2026/680, §5. Issue #357 (hypothesis S2).
* [GCXK25] *List-decodability implies proximity gaps.* ePrint 2025/870.
* [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity.*
  ePrint 2026/782, Appendix A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code InterleavedMCACollapse Round17CAPair
open ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap

namespace ProximityGap.MCADictionaryBracket

/-! ## The interleaved list profile -/

section Profile

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The interleaved list profile**: the worst-case `C^{≡2}` list size over all received
stacks at joint-agreement floor `a`. This is the profile function `δ ↦ |Λ(C^{≡2}, δ)|`
of [ABF26] §5, as a single `ℕ`-valued object (`a = ⌈(1−δ)n⌉` converts radius to floor). -/
def interleavedListProfile (C : Finset (ι → F)) (a : ℕ) : ℕ :=
  Finset.univ.sup (fun uv : (ι → F) × (ι → F) => (interleavedList C uv.1 uv.2 a).card)

/-- Every stack's interleaved list is bounded by the profile. -/
theorem interleavedList_card_le_profile (C : Finset (ι → F)) (u₀ u₁ : ι → F) (a : ℕ) :
    (interleavedList C u₀ u₁ a).card ≤ interleavedListProfile C a :=
  Finset.le_sup (f := fun uv : (ι → F) × (ι → F) => (interleavedList C uv.1 uv.2 a).card)
    (Finset.mem_univ (u₀, u₁))

/-- The profile is antitone in the agreement floor. -/
theorem interleavedListProfile_anti (C : Finset (ι → F)) {a a' : ℕ} (h : a ≤ a') :
    interleavedListProfile C a' ≤ interleavedListProfile C a := by
  refine Finset.sup_le fun uv _ => ?_
  exact le_trans (interleavedList_card_anti C uv.1 uv.2 h)
    (interleavedList_card_le_profile C uv.1 uv.2 a)

/-- Unconditional ceiling: the profile never exceeds `|C|²`. -/
theorem interleavedListProfile_le_sq (C : Finset (ι → F)) (a : ℕ) :
    interleavedListProfile C a ≤ C.card * C.card :=
  Finset.sup_le fun uv _ => interleavedList_card_le_sq C uv.1 uv.2 a

/-- **The unconditional profile pin (half-distance regime).** If distinct codewords pairwise
agree on at most `J` positions and the floor clears the RVW13 half-threshold
(`J + n < 2a`), the interleaved list profile is at most `1`: two list pairs overlap on
`≥ 2a − n > J` positions row-wise, forcing equality. This supplies the good-side input of
the dictionary sandwich *unconditionally*, so the sandwich is non-vacuously instantiable
end-to-end in the unique-decoding regime. -/
theorem interleavedListProfile_le_one (C : Finset (ι → F)) {a J : ℕ}
    (hpair : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun i => g₁ i = g₂ i)).card ≤ J)
    (hhalf : J + Fintype.card ι < 2 * a) :
    interleavedListProfile C a ≤ 1 := by
  refine Finset.sup_le fun uv _ => ?_
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [interleavedList, Finset.mem_filter, Finset.mem_product] at hx hy
  obtain ⟨⟨hx1, hx2⟩, hxa⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hya⟩ := hy
  -- Row-wise rigidity: two codewords matching `uv` on `≥ a` joint positions each must agree
  -- on `≥ 2a − n > J` positions, hence be equal.
  have row : ∀ (w : ι → F) (g g' : ι → F), g ∈ C → g' ∈ C →
      ∀ (A B : Finset ι), (∀ i ∈ A, g i = w i) → (∀ i ∈ B, g' i = w i) →
      a ≤ A.card → a ≤ B.card → g = g' := by
    intro w g g' hg hg' A B hA hB hAa hBa
    by_contra hne
    have hsub : A ∩ B ⊆ Finset.univ.filter (fun i => g i = g' i) := by
      intro i hi
      rw [Finset.mem_inter] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hA i hi.1, hB i hi.2]
    have hcard : A.card + B.card - Finset.card (Finset.univ : Finset ι) ≤ (A ∩ B).card := by
      have := Finset.card_inter_add_card_union A B
      have hun : (A ∪ B).card ≤ Finset.card (Finset.univ : Finset ι) :=
        Finset.card_le_card (Finset.subset_univ _)
      omega
    have hJ : (A ∩ B).card ≤ J := le_trans (Finset.card_le_card hsub) (hpair g hg g' hg' hne)
    have hn : Finset.card (Finset.univ : Finset ι) = Fintype.card ι := rfl
    omega
  -- Apply to both rows; the joint agreement set witnesses both row agreements
  -- (note `jointAgreeSet` stores `received = codeword`, so we flip).
  have hx1' : ∀ i ∈ jointAgreeSet uv.1 uv.2 x.1 x.2, x.1 i = uv.1 i := by
    intro i hi
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.1.symm
  have hx2' : ∀ i ∈ jointAgreeSet uv.1 uv.2 x.1 x.2, x.2 i = uv.2 i := by
    intro i hi
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2.symm
  have hy1' : ∀ i ∈ jointAgreeSet uv.1 uv.2 y.1 y.2, y.1 i = uv.1 i := by
    intro i hi
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.1.symm
  have hy2' : ∀ i ∈ jointAgreeSet uv.1 uv.2 y.1 y.2, y.2 i = uv.2 i := by
    intro i hi
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2.symm
  have e1 : x.1 = y.1 := row uv.1 x.1 y.1 hx1 hy1 _ _ hx1' hy1' hxa hya
  have e2 : x.2 = y.2 := row uv.2 x.2 y.2 hx2 hy2 _ _ hx2' hy2' hxa hya
  exact Prod.ext e1 e2

open Classical in
/-- **Good-side transfer through the profile.** A profile value at the doubled-radius floor
bounds `ε_mca` with the explicit dictionary numerator `1 + 2δn·profile`. -/
theorem epsMCA_le_of_profile (C : Finset (ι → F)) (hC : PairClosed C) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) *
          interleavedListProfile C ⌈(1 - 2 * δ) * (Fintype.card ι : ℝ≥0)⌉₊ : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_interleavedList_card_le_doubledRadius C hC δ _
    (fun u₀ u₁ => interleavedList_card_le_profile C u₀ u₁ _)

open Classical in
/-- **Good-side ledger composition.** If the dictionary numerator at `δ` clears the target
budget `ε*`, then `δ` is below the MCA threshold: `δ ≤ mcaDeltaStar C ε*`. The loss of the
LD⇒MCA dictionary direction is exactly the visible numerator `1 + 2δn·profile`. -/
theorem le_mcaDeltaStar_of_profile (C : Finset (ι → F)) (hC : PairClosed C)
    (εstar : ℝ≥0∞) {δ : ℝ≥0} (hδ : δ ≤ 1)
    (hbudget : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) *
        interleavedListProfile C ⌈(1 - 2 * δ) * (Fintype.card ι : ℝ≥0)⌉₊ : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ (le_trans (epsMCA_le_of_profile C hC δ) hbudget)

end Profile

/-! ## The evaluation code as a `PairClosed` finset -/

section EvalCode

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- The KKH26 evaluation code `{eval q on ⟨g⟩ : deg q ≤ d}` as a `Finset`. -/
noncomputable def evalCodeFin (g : ZMod p) (n d : ℕ) : Finset (Fin n → ZMod p) :=
  Finset.univ.filter (fun w => w ∈ KKH26.evalCode g n d)

open Classical in
@[simp] theorem coe_evalCodeFin (g : ZMod p) (n d : ℕ) :
    (↑(evalCodeFin g n d) : Set (Fin n → ZMod p)) = KKH26.evalCode g n d := by
  ext w
  simp [evalCodeFin]

open Classical in
/-- The evaluation code is `PairClosed`: the two pair-extraction combinations
`(γ−γ')⁻¹•(c−c')` and `c − γ•((γ−γ')⁻¹•(c−c'))` are again low-degree evaluations. -/
theorem pairClosed_evalCodeFin (g : ZMod p) (n d : ℕ) :
    PairClosed (evalCodeFin g n d) := by
  intro c hc c' hc' γ γ' hne
  simp only [evalCodeFin, Finset.mem_filter, Finset.mem_univ, true_and] at hc hc' ⊢
  obtain ⟨q, hqd, hq⟩ := hc
  obtain ⟨q', hqd', hq'⟩ := hc'
  have hmem₁ : (γ - γ')⁻¹ • (c - c') ∈ KKH26.evalCode g n d := by
    refine ⟨(γ - γ')⁻¹ • (q - q'), ?_, ?_⟩
    · exact le_trans (natDegree_smul_le _ _)
        (le_trans (natDegree_sub_le _ _) (max_le hqd hqd'))
    · intro i
      simp [Pi.smul_apply, Pi.sub_apply, hq i, hq' i, smul_eq_mul,
        Polynomial.eval_smul, Polynomial.eval_sub]
  refine ⟨hmem₁, ?_⟩
  obtain ⟨q₁, hq₁d, hq₁⟩ := hmem₁
  refine ⟨q - γ • q₁, ?_, ?_⟩
  · exact le_trans (natDegree_sub_le _ _)
      (max_le hqd (le_trans (natDegree_smul_le _ _) hq₁d))
  · intro i
    simp [Pi.sub_apply, Pi.smul_apply, hq i, hq₁ i, smul_eq_mul,
      Polynomial.eval_smul, Polynomial.eval_sub]

end EvalCode

/-! ## The DEEP-quotient configuration, bundled -/

section DeepConfig

variable {p : ℕ} [Fact p.Prime]

/-- **A DEEP-quotient list configuration**: the bundled hypothesis package of the
[KKH26] App-A transfer engine. A future beyond-Johnson list-decoding lower bound for the
`m`-power subfamily lands in the ledger as a single term of this structure. Fields:

* `u` — the received word on the smooth domain `⟨g⟩` of size `n`;
* `qhat c` — the `L` list polynomials (degree ≤ `D`), agreeing with `u` on `S c`;
* size clauses — each `S c` has relative size ≥ `1 − δ` and clears the quotient degree
  budget `D·m + 1`;
* `hw` — the shift `w` is fiber-disjoint from the domain;
* `hsep` — the shift separates the list (`ĉ(w)` pairwise distinct). -/
structure DeepListConfig (n : ℕ) [NeZero n] (g w : ZMod p) (m D : ℕ) (δ : ℝ≥0)
    (L : ℕ) : Type where
  u : Fin n → ZMod p
  qhat : Fin L → Polynomial (ZMod p)
  S : Fin L → Finset (Fin n)
  hg : orderOf g = n
  hm : 1 ≤ m
  hD : 1 ≤ D
  hq : ∀ c, (qhat c).natDegree ≤ D
  hSsize : ∀ c, (((S c).card : ℝ≥0)) ≥ (1 - δ) * Fintype.card (Fin n)
  hScard : ∀ c, D * m + 1 ≤ (S c).card
  hagree : ∀ c, ∀ j ∈ S c, u j = (qhat c).eval ((g ^ (j : ℕ)) ^ m)
  hw : ∀ j : Fin n, (g ^ (j : ℕ)) ^ m ≠ w
  hsep : Function.Injective fun c => (qhat c).eval w

/-- **Bad-side transfer.** A DEEP configuration of size `L` forces `ε_mca ≥ L/p` on the
quotient evaluation code — the dictionary's MCA-failure-from-list-failure direction, with
no loss in the count and no radius loss. -/
theorem epsMCA_ge_of_deepConfig {n : ℕ} [NeZero n] {g w : ZMod p} {m D L : ℕ} {δ : ℝ≥0}
    (cfg : DeepListConfig n g w m D δ L) :
    (L : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (KKH26.evalCode g n ((D - 1) * m)) δ := by
  have h := ArkLib.ProximityGap.DeepQuotientTransfer.deep_quotient_epsMCA_lower_bound
    cfg.hg cfg.hm cfg.hD δ cfg.u cfg.qhat cfg.S cfg.hq cfg.hSsize cfg.hScard
    cfg.hagree cfg.hw cfg.hsep
  simpa [Fintype.card_fin] using h

/-- **Bad-side ledger composition.** A DEEP configuration whose size beats the budget
(`ε* < L/p`) caps the MCA threshold of the quotient code at its radius. -/
theorem mcaDeltaStar_le_of_deepConfig {n : ℕ} [NeZero n] {g w : ZMod p} {m D L : ℕ}
    (εstar : ℝ≥0∞) {δbad : ℝ≥0} (cfg : DeepListConfig n g w m D δbad L)
    (hbig : εstar < (L : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (KKH26.evalCode g n ((D - 1) * m)) εstar ≤ δbad :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hbig (epsMCA_ge_of_deepConfig cfg))

end DeepConfig

/-! ## The headline: the bracket-interpolation sandwich -/

section Sandwich

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- **THE BRACKET-INTERPOLATION SANDWICH (S2 of #357).** For the explicit quotient
evaluation code `C' = evalCode g n ((D−1)m)`: a list-profile budget at `δgood` (good side,
dictionary numerator `1 + 2δn·profile` explicit) and a DEEP configuration at `δbad` (bad
side, bare `L/p`) pinch the MCA threshold

  `δgood ≤ mcaDeltaStar(C', ε*) ≤ δbad`.

Every loss factor of the LD⇔MCA dictionary is a visible hypothesis; the open [ABF26] §5
collapse question is precisely whether the good-side input can be supplied past Johnson. -/
theorem mcaDeltaStar_dictionary_sandwich {n : ℕ} [NeZero n] {g w : ZMod p}
    {m D L : ℕ} (εstar : ℝ≥0∞) {δgood δbad : ℝ≥0} (hδg : δgood ≤ 1)
    (hbudget : ((1 + (Fintype.card (Fin n) -
        (2 * ⌈(1 - δgood) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
        interleavedListProfile (evalCodeFin g n ((D - 1) * m))
          ⌈(1 - 2 * δgood) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ : ℕ) : ℝ≥0∞)
      / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar)
    (cfg : DeepListConfig n g w m D δbad L)
    (hbig : εstar < (L : ℝ≥0∞) / (p : ℝ≥0∞)) :
    δgood ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (KKH26.evalCode g n ((D - 1) * m)) εstar ∧
      mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (KKH26.evalCode g n ((D - 1) * m)) εstar ≤ δbad := by
  constructor
  · have h := le_mcaDeltaStar_of_profile (evalCodeFin g n ((D - 1) * m))
      (pairClosed_evalCodeFin g n ((D - 1) * m)) εstar hδg hbudget
    rwa [coe_evalCodeFin] at h
  · exact mcaDeltaStar_le_of_deepConfig εstar cfg hbig

open Classical in
/-- **The meet corollary: the MCA brackets meet whenever the list-profile brackets meet.**
If the configuration radius is at most the budget radius (`δbad ≤ δgood`), the dictionary
sandwich collapses to an exact pin: `mcaDeltaStar(C', ε*) = δgood = δbad`. This is the
"if" direction of the [ABF26] §5 collapse, formal; the converse direction (an MCA pin
forces a list-profile pin) is the named open seam. -/
theorem mcaDeltaStar_eq_of_dictionary_meet {n : ℕ} [NeZero n] {g w : ZMod p}
    {m D L : ℕ} (εstar : ℝ≥0∞) {δgood δbad : ℝ≥0} (hδg : δgood ≤ 1)
    (hbudget : ((1 + (Fintype.card (Fin n) -
        (2 * ⌈(1 - δgood) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
        interleavedListProfile (evalCodeFin g n ((D - 1) * m))
          ⌈(1 - 2 * δgood) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ : ℕ) : ℝ≥0∞)
      / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar)
    (cfg : DeepListConfig n g w m D δbad L)
    (hbig : εstar < (L : ℝ≥0∞) / (p : ℝ≥0∞))
    (hmeet : δbad ≤ δgood) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (KKH26.evalCode g n ((D - 1) * m)) εstar = δgood := by
  obtain ⟨hlo, hhi⟩ := mcaDeltaStar_dictionary_sandwich εstar hδg hbudget cfg hbig
  exact le_antisymm (le_trans hhi hmeet) hlo

end Sandwich

/-! ## Source audit -/

#print axioms interleavedListProfile_le_sq
#print axioms le_mcaDeltaStar_of_profile
#print axioms pairClosed_evalCodeFin
#print axioms mcaDeltaStar_le_of_deepConfig
#print axioms mcaDeltaStar_dictionary_sandwich
#print axioms mcaDeltaStar_eq_of_dictionary_meet

end ProximityGap.MCADictionaryBracket
