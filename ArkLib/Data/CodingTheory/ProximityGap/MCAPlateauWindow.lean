/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RadiusOne
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointUpper
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumRadiusOne
import ArkLib.ToMathlib.RestrictedSumsetGeneral

/-!
# The MCA plateau at capacity and the canonical-witness window bound

Two new unconditional results about the mutual-correlated-agreement error
`ε_mca` (ABF26 Definition 4.3) of Reed–Solomon codes, both feeding the
value question of the §1 **Grand MCA Challenge** (where, on the `1/n`-radius
lattice, does `ε_mca` cross the threshold `ε*`?).

## 1. The plateau (`epsMCA_eq_epsMCA_one_of_le_succ`)

`mcaEvent` requires a witness set `S` with `|S| ≥ (1-δ)·n` on which the folded
line matches a codeword while no joint pair of codewords matches `(u₀,u₁)`.
Over an RS code, the `¬ pairJointAgreesOn` clause forces `u₁` to be
*non-extendable* on `S` (`nonExtendable_of_mcaEvent`), and interpolation makes
every set of size `≤ k` extendable (`card_ge_of_nonExtendable`): witness sets
always have `|S| ≥ k + 1`. Hence the size clause is **inert** whenever
`(1-δ)·n ≤ k+1`, and

  `ε_mca(RS, δ) = ε_mca(RS, 1)`  for every `δ ≥ 1 - (k+1)/n`.

In particular the **capacity radius `δ = 1 - ρ` lies on the radius-one
plateau**, so every radius-one lower bound transfers verbatim to capacity:

* `epsMCA_capacityPred_ge_card_subsetSums` — the unconditional subset-sum
  floor `|Σ_{k+1}(L)|/q ≤ ε_mca(RS, 1 - (k+1)/n)`;
* `epsMCA_capacityPred_ge_erdos_heilbronn_general` — the Dias da
  Silva–Hamidoune floor `((k+1)(n-k-1)+1)/q` over prime-characteristic
  domains;
* `MCAUpperWitness.ofSubsetSumsCapacityPred` /
  `GrandMCAResolution.δStar_le_capacityPred_of_subsetSums` — **for
  `q < 2¹²⁸·|Σ_{k+1}(L)|` the maximal MCA threshold of any resolution of the
  Grand Challenge is strictly below capacity**: `δ* ≤ 1 - (k+1)/n < 1 - ρ`.
  The naive-capacity answer to the Grand MCA Challenge is dead in this whole
  field regime, unconditionally.

## 2. The canonical-witness window bound (`epsMCA_le_choose_div`)

Sharpening the `2^n/q` witness-set-pinning bound (`MCAEndpointUpper.lean`):
every bad scalar admits a witness of size **exactly** `m := max(⌈(1-δ)n⌉, k+1)`
(shrink the non-extendable row to a `(k+1)`-core by gluing
(`exists_card_eq_subset_nonExtendable`), then pad back inside the original
witness), and two bad scalars sharing a witness set would manufacture the
forbidden joint pair (`pairJointAgreesOn_of_two_lines`). The bad set therefore
injects into the size-`m` subsets:

  `ε_mca(RS, δ) ≤ C(n, max(⌈(1-δ)n⌉, k+1)) / q`,  unconditionally, at every δ.

At `δ = 1` this recovers the radius-one bound `C(n,k+1)/q`
(`epsMCA_one_le_choose_div`); combined with monotonicity it yields the
two-sided window form `min(C(n,k+1), C(n, max(⌈(1-δ)n⌉, k+1)))/q` and the
**first unconditional beyond-Johnson lower witnesses**
(`MCALowerWitness.ofChooseLe`): `δ* ≥ δ` whenever
`C(n, max(⌈(1-δ)n⌉, k+1)) ≤ ε*·q`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. 2026. §1 (Grand MCA Challenge), §4.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section Plateau

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Non-extendability is monotone under enlarging the set: a codeword agreeing with `g`
on `S'` agrees with `g` on any subset `T ⊆ S'`. -/
theorem NonExtendableOn.mono {C : Set (ι → F)} {T S' : Finset ι} {g : ι → F}
    (hTS : T ⊆ S') (hne : NonExtendableOn C T g) :
    NonExtendableOn C S' g := by
  rintro ⟨v, hv, hvagree⟩
  exact hne ⟨v, hv, fun i hi => hvagree i (hTS hi)⟩

/-- If `u₁` is non-extendable on `S`, then no joint pair of codewords agrees with
`(u₀, u₁)` on `S` (the second component of a joint pair would extend `u₁`). -/
theorem not_pairJointAgreesOn_of_nonExtendable_right
    {C : Set (ι → F)} {S : Finset ι} {u₀ u₁ : ι → F}
    (hne : NonExtendableOn C S u₁) :
    ¬ pairJointAgreesOn C S u₀ u₁ := by
  rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
  exact hne ⟨v₁, hv₁, fun i hi => (hagree i hi).2⟩

/-- **The plateau, event form.** Over an RS code, whenever `(1-δ)·n ≤ k+1` the
`mcaEvent` at radius `δ` coincides with the radius-one event: witness sets always have
`≥ k+1` points (interpolation extends any smaller restriction, and `¬ pairJointAgreesOn`
forces `u₁` non-extendable), so the size clause is inert. -/
theorem mcaEvent_iff_one_of_le_succ (domain : ι ↪ F) (k : ℕ) {δ : ℝ≥0}
    (hδ : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ ((k : ℝ≥0) + 1))
    (u₀ u₁ : ι → F) (γ : F) :
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ γ ↔
      mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ := by
  constructor
  · rintro ⟨S, _hScard, hline, hpair⟩
    refine ⟨S, ?_, hline, hpair⟩
    simp
  · rintro ⟨S, _hScard, hline, hpair⟩
    obtain ⟨w, hw, hwline⟩ := hline
    have hneS : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁ :=
      nonExtendable_of_mcaEvent (ReedSolomon.code domain k) hw hwline hpair
    have hcard : k + 1 ≤ S.card := card_ge_of_nonExtendable domain hneS
    refine ⟨S, ?_, ⟨w, hw, hwline⟩, hpair⟩
    calc ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)
        ≤ ((k : ℝ≥0) + 1) := hδ
      _ ≤ (S.card : ℝ≥0) := by exact_mod_cast hcard

/-- **The plateau.** `ε_mca(RS[F, domain, k], δ) = ε_mca(RS[F, domain, k], 1)` whenever
`(1-δ)·n ≤ k+1`, i.e. on the whole band `δ ∈ [1 - (k+1)/n, 1]` — which includes the
capacity radius `1 - ρ`. -/
theorem epsMCA_eq_epsMCA_one_of_le_succ (domain : ι ↪ F) (k : ℕ) {δ : ℝ≥0}
    (hδ : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ ((k : ℝ≥0) + 1)) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ =
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  unfold epsMCA
  refine iSup_congr fun u => ?_
  exact Pr_congr fun γ => mcaEvent_iff_one_of_le_succ domain k hδ (u 0) (u 1) γ

/-- The capacity-adjacent radius `δ := 1 - (k+1)/n` satisfies the plateau hypothesis. -/
theorem capacityPred_le_succ_hyp (k : ℕ) :
    ((1 : ℝ≥0) - (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0))) *
        (Fintype.card ι : ℝ≥0) ≤ ((k : ℝ≥0) + 1) := by
  have hn_pos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  by_cases hle : ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0) ≤ 1
  · have h1 : (1 : ℝ≥0) - (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) ≤
        ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0) :=
      tsub_tsub_le_tsub_add.trans (by simp)
    calc ((1 : ℝ≥0) - (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0))) *
            (Fintype.card ι : ℝ≥0)
        ≤ (((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) := by
          exact mul_le_mul_left h1 _
      _ = ((k : ℝ≥0) + 1) := by
          rw [div_mul_cancel₀]
          exact hn_pos.ne'
  · -- `(k+1)/n > 1`, i.e. `n < k+1`: then `(1 - (1 - x)) * n ≤ 1 * n = n ≤ k+1`.
    push Not at hle
    have hn_le : (Fintype.card ι : ℝ≥0) ≤ ((k : ℝ≥0) + 1) := by
      have h1n := (lt_div_iff₀ hn_pos).mp hle
      rw [one_mul] at h1n
      exact h1n.le
    calc ((1 : ℝ≥0) - (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0))) *
            (Fintype.card ι : ℝ≥0)
        ≤ 1 * (Fintype.card ι : ℝ≥0) := by
          exact mul_le_mul_left (tsub_le_self.trans le_rfl) _
      _ = (Fintype.card ι : ℝ≥0) := one_mul _
      _ ≤ ((k : ℝ≥0) + 1) := hn_le

/-- **Capacity transfer of the subset-sum floor.** The unconditional radius-one floor
`|Σ_{k+1}(L)|/q ≤ ε_mca(RS, 1)` (`epsMCA_one_ge_card_subsetSums`) holds verbatim at the
capacity-adjacent radius `δ = 1 - (k+1)/n` (and on the whole plateau band): -/
theorem epsMCA_capacityPred_ge_card_subsetSums (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι) :
    ((subsetSumsKplus1 domain k).card : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) := by
  rw [epsMCA_eq_epsMCA_one_of_le_succ domain k (capacityPred_le_succ_hyp k)]
  exact epsMCA_one_ge_card_subsetSums domain hk

/-- **Capacity transfer of the Dias da Silva–Hamidoune floor.** Over prime-characteristic
domains, `((k+1)(n-k-1)+1)/q ≤ ε_mca(RS, 1 - (k+1)/n)`. -/
theorem epsMCA_capacityPred_ge_erdos_heilbronn_general (domain : ι ↪ F) {p : ℕ}
    (hp : p.Prime) (hchar : ringChar F = p) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hnp : Fintype.card ι ≤ p)
    (hsmall : (k + 1) * (Fintype.card ι - (k + 1)) < p) :
    (((k + 1) * (Fintype.card ι - (k + 1)) + 1 : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) := by
  rw [epsMCA_eq_epsMCA_one_of_le_succ domain k (capacityPred_le_succ_hyp k)]
  exact epsMCA_one_ge_erdos_heilbronn_general domain hp hchar hk hnp hsmall

/-- **Strict-below-capacity refutation band.** For `q < 2¹²⁸ · |Σ_{k+1}(L)|`, the prize
threshold `ε* = 2⁻¹²⁸` is already exceeded at the capacity-adjacent radius
`δ = 1 - (k+1)/n`. -/
theorem epsStar_lt_epsMCA_capacityPred_of_subsetSums (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) := by
  rw [epsMCA_eq_epsMCA_one_of_le_succ domain k (capacityPred_le_succ_hyp k)]
  exact epsStar_lt_epsMCA_one_of_subsetSums domain hk hsmall

/-- **Witness form**: in the band `q < 2¹²⁸·|Σ_{k+1}(L)|`, the capacity-adjacent radius is
an `MCAUpperWitness` for the prize threshold. -/
noncomputable def MCAUpperWitness.ofSubsetSumsCapacityPred (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar :=
  ⟨1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0),
    epsStar_lt_epsMCA_capacityPred_of_subsetSums domain hk hsmall⟩

/-- **The Grand-MCA-Challenge consequence: the threshold is strictly below capacity.**
Any resolution of the Grand MCA Challenge (for the RS code at prize threshold
`ε* = 2⁻¹²⁸`) has `δ* ≤ 1 - (k+1)/n` whenever `q < 2¹²⁸·|Σ_{k+1}(L)|` — one full lattice
step below the capacity radius `1 - ρ = 1 - k/n`. The naive-capacity answer to the
challenge is unconditionally dead in this entire field regime. -/
theorem GrandMCAResolution.δStar_le_capacityPred_of_subsetSums (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card)
    (R : GrandChallenges.GrandMCAResolution
      (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar) :
    R.δStar ≤ 1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0) :=
  (MCAUpperWitness.ofSubsetSumsCapacityPred domain hk hsmall).δStar_le R

end Plateau

section WindowBound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Canonical-witness counting, per stack.** For a fixed stack `(u₀, u₁)` and any radius
`δ`, the `mcaEvent` probability is at most `C(n, max(⌈(1-δ)n⌉, k+1)) / q`: every bad
scalar has a witness of size exactly `m := max(⌈(1-δ)n⌉, k+1)` (shrink the
non-extendable row `u₁` to a `(k+1)`-core, then pad inside the original witness), and a
shared witness set would manufacture the forbidden joint pair. -/
theorem mcaEvent_prob_le_choose_div (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ γ ] ≤
      ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  classical
  set MC := ReedSolomon.code domain k with hMC
  set m := max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1) with hm
  rw [prob_uniform_eq_card_filter_div_card]
  set Bad := Finset.univ.filter
    (fun γ : F => mcaEvent (MC : Set (ι → F)) δ u₀ u₁ γ) with hBad
  -- Every bad scalar has a canonical witness of size exactly `m`, on which the line
  -- carries a codeword and `u₁` is non-extendable.
  have hwit : ∀ γ ∈ Bad,
      ∃ S' : Finset ι, S'.card = m ∧
        (∃ w ∈ (MC : Set (ι → F)), ∀ i ∈ S', w i = u₀ i + γ • u₁ i) ∧
        NonExtendableOn (MC : Set (ι → F)) S' u₁ := by
    intro γ hγ
    rw [hBad, Finset.mem_filter] at hγ
    obtain ⟨S, hScard, ⟨w, hw, hwline⟩, hpair⟩ := hγ.2
    have hneS : NonExtendableOn (MC : Set (ι → F)) S u₁ :=
      nonExtendable_of_mcaEvent MC hw hwline hpair
    obtain ⟨T, hTS, hTcard, hneT⟩ := exists_card_eq_subset_nonExtendable domain hneS
    -- `m ≤ S.card`: the ceiling is below `S.card` by the event's size clause, and
    -- `k+1 ≤ S.card` by non-extendability.
    have hceil_le : ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ ≤ S.card :=
      Nat.ceil_le.mpr (by exact_mod_cast hScard)
    have hk1_le : k + 1 ≤ S.card := card_ge_of_nonExtendable domain hneS
    have hm_le : m ≤ S.card := max_le hceil_le hk1_le
    have hT_le : T.card ≤ m := by
      rw [hTcard]
      exact le_max_right _ _
    obtain ⟨S', hTS', hS'S, hS'card⟩ :=
      Finset.exists_subsuperset_card_eq hTS hT_le hm_le
    refine ⟨S', hS'card, ⟨w, hw, fun i hi => hwline i (hS'S hi)⟩, ?_⟩
    exact NonExtendableOn.mono hTS' hneT
  choose! Sf hSfcard hSfline hSfne using hwit
  -- Injectivity: a shared canonical witness would manufacture the forbidden joint pair.
  have hinj : (↑Bad : Set F).InjOn Sf := by
    intro γ₁ hγ₁ γ₂ hγ₂ hSeq
    by_contra hne
    have hγ₁' : γ₁ ∈ Bad := hγ₁
    have hγ₂' : γ₂ ∈ Bad := hγ₂
    obtain ⟨w₁, hw₁, hw₁line⟩ := hSfline γ₁ hγ₁'
    obtain ⟨w₂, hw₂, hw₂line⟩ := hSfline γ₂ hγ₂'
    have hjoint : pairJointAgreesOn (MC : Set (ι → F)) (Sf γ₂) u₀ u₁ := by
      refine pairJointAgreesOn_of_two_lines MC (S := Sf γ₂) (γ := γ₁) (γ' := γ₂) hne
        hw₁ ?_ hw₂ hw₂line
      rw [← hSeq]
      exact hw₁line
    exact not_pairJointAgreesOn_of_nonExtendable_right (hSfne γ₂ hγ₂') hjoint
  -- The canonical witnesses live among the size-`m` subsets.
  have hmaps : Set.MapsTo Sf (↑Bad) (↑(Finset.univ.powersetCard m : Finset (Finset ι))) := by
    intro γ hγ
    have hγ' : γ ∈ Bad := hγ
    exact Finset.mem_coe.mpr
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSfcard γ hγ'⟩)
  have hcard_le : Bad.card ≤ (Finset.univ.powersetCard m : Finset (Finset ι)).card :=
    Finset.card_le_card_of_injOn Sf hmaps hinj
  rw [Finset.card_powersetCard, Finset.card_univ] at hcard_le
  -- Push to `ENNReal` division (align the two `ℕ → ENNReal` cast routes first).
  have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
    push_cast; rfl
  rw [hden]
  gcongr
  exact_mod_cast hcard_le

/-- **The canonical-witness window bound.** For every RS code and every radius `δ`:

  `ε_mca(RS[F, domain, k], δ) ≤ C(n, max(⌈(1-δ)·n⌉, k+1)) / q`, unconditionally.

At `δ = 1` this is the radius-one bound `C(n, k+1)/q`; for `⌈(1-δ)n⌉ > n - k - 1` it
strictly sharpens the radius-one + monotonicity bound, and it always sharpens the
`2^n/q` pinning bound (`epsMCA_le_two_pow_card_div`). -/
theorem epsMCA_le_choose_div (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤
      ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  exact mcaEvent_prob_le_choose_div domain k δ (u 0) (u 1)

/-- **Unconditional lower witness from the window bound.** Whenever the binomial count
clears the threshold — `C(n, max(⌈(1-δ)n⌉, k+1)) ≤ ε*·q` — the radius `δ` is a verified
`MCALowerWitness`: `δ* ≥ δ` for every resolution. This needs no Johnson-range analysis,
no list-decoding input, and no field-structure hypothesis. -/
noncomputable def MCALowerWitness.ofChooseLe (domain : ι ↪ F) (k : ℕ) {δ ε_star : ℝ≥0}
    (hδ : δ ≤ 1)
    (hle : ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ
    (le_trans (epsMCA_le_choose_div domain k δ) hle)

end WindowBound

section LatticeBracket

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open GrandChallenges GrandChallengesLattice

/-! ## Unconditional brackets on the faithful MCA lattice threshold

The existing lattice brackets (`Hab25Core`, `GrandChallengesLattice`) all consume
external admits ([BCHKS25]/[CS25]/[DG25]-shaped hypotheses). The two witnesses built in
this file are **unconditional**, so feeding them through the step-function bridge gives
the first hypothesis-free two-sided pinning of `mcaThreshold` — the faithful "largest
lattice radius" object of the Grand MCA Challenge. -/

/-- **Unconditional staircase floor + existence.** If the canonical-witness count clears
the threshold at radius `δ`, the faithful MCA lattice threshold exists. -/
theorem mcaThresholdExists_ofChooseLe (domain : ι ↪ F) (k : ℕ) {δ ε_star : ℝ≥0}
    (hδ : δ ≤ 1)
    (hle : ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _ (MCALowerWitness.ofChooseLe domain k hδ hle)

/-- **Unconditional staircase floor.** `⌊δ·n⌋ ≤ mcaThreshold` whenever
`C(n, max(⌈(1-δ)n⌉, k+1)) ≤ ε*·q`. -/
theorem le_mcaThreshold_ofChooseLe (domain : ι ↪ F) (k : ℕ) {δ ε_star : ℝ≥0}
    (hδ : δ ≤ 1)
    (hle : ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal))
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    latticeIndexOf (ι := ι) δ hδ ≤
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne (MCALowerWitness.ofChooseLe domain k hδ hle)

/-- **Unconditional capacity-side lattice ceiling.** For `q < 2¹²⁸·|Σ_{k+1}(L)|` the
faithful MCA lattice threshold sits strictly below the lattice index of the
capacity-adjacent radius `1 - (k+1)/n`. -/
theorem mcaThreshold_lt_capacityPred_of_subsetSums (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F))
      ProximityGap.epsStar) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar hne <
      latticeIndexOf (ι := ι)
        (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) tsub_le_self :=
  mcaThreshold_lt_MCAUpperWitness _ _ hne
    (MCAUpperWitness.ofSubsetSumsCapacityPred domain hk hsmall) tsub_le_self

/-- **The first unconditional two-sided bracket of the faithful Grand-MCA lattice
threshold.** Under the two numeric window conditions — the canonical-witness count clears
`ε* = 2⁻¹²⁸` at radius `δ` (floor) while the field is below the subset-sum refutation
band (ceiling) — the threshold exists and satisfies

  `⌊δ·n⌋ ≤ mcaThreshold < ⌊(1 - (k+1)/n)·n⌋` (lattice indices),

i.e. the answer to the (faithful, lattice-form) Grand MCA Challenge for this code lies
in `[δ, 1 - (k+1)/n)` — strictly below capacity. Both hypotheses are simultaneously
satisfiable (e.g. small `δ` with `C(n, max(⌈(1-δ)n⌉, k+1)) ≤ q/2¹²⁸ < |Σ_{k+1}(L)|`,
available over prime-characteristic domains where `|Σ_{k+1}(L)|` is quadratic in `n`),
and **no external-paper hypothesis is consumed**. -/
theorem mcaThreshold_bracketed_unconditional (domain : ι ↪ F) {k : ℕ} {δ : ℝ≥0}
    (hk : k + 1 ≤ Fintype.card ι) (hδ : δ ≤ 1)
    (hlo : ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (ProximityGap.epsStar : ENNReal))
    (hhi : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F))
        ProximityGap.epsStar,
      latticeIndexOf (ι := ι) δ hδ ≤
          mcaThreshold (ReedSolomon.code domain k : Set (ι → F))
            ProximityGap.epsStar hne ∧
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F))
            ProximityGap.epsStar hne <
          latticeIndexOf (ι := ι)
            (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) tsub_le_self := by
  refine ⟨mcaThresholdExists_ofChooseLe domain k hδ hlo, ?_, ?_⟩
  · exact le_mcaThreshold_ofChooseLe domain k hδ hlo _
  · exact mcaThreshold_lt_capacityPred_of_subsetSums domain hk hhi _

/-- Per-rate canonical-window lower bounds and adjacent middle-radius spike certificates resolve
the faithful MCA lattice prize directly.

This is the arithmetic-facing form of
`mcaPrizeLatticeResolved_of_lowerWitnesses_and_spike_adjacent`: the lower witnesses are
instantiated from the unconditional canonical-witness window bound, so an ABF26 certificate file
only has to provide, at each of the four prize rates, the lower binomial/count inequality, the
spike admissibility inequalities, and the one-step lattice adjacency check. -/
theorem mcaPrizeLatticeResolved_of_chooseBounds_and_spike_adjacent
    (domain : ι ↪ F)
    (δ_lo δ_hi : Fin 4 → ℝ≥0) (t : Fin 4 → ℕ)
    (hδlo : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hlo : ∀ j : Fin 4,
      ((Fintype.card ι).choose
          (max
            (⌈((1 : ℝ≥0) - δ_lo j) * (Fintype.card ι : ℝ≥0)⌉₊)
            (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (ht_n : ∀ j : Fin 4,
      t j + ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (ht_q : ∀ j : Fin 4, t j ≤ Fintype.card F)
    (hspike_radius : ∀ j : Fin 4,
      ((1 - δ_hi j) * Fintype.card ι : ℝ≥0) ≤
        (Fintype.card ι - t j + 1 : ℕ))
    (hspike_gt : ∀ j : Fin 4,
      (epsStar : ENNReal) < (t j : ENNReal) / (Fintype.card F : ENNReal))
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ_lo j) (hδlo j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ_lo j) (hδlo j)) := by
  let wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := fun j =>
    MCALowerWitness.ofChooseLe domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (hδlo j) (hlo j)
  have hadj' : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1 := by
    intro j
    simpa [wlo] using hadj j
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  refine ⟨mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j), ?_⟩
  simpa [wlo, C] using
    (mcaThreshold_eq_of_lowerWitnesses_and_spike_adjacent
      domain wlo t δ_hi hδhi ht_n ht_q hspike_radius hspike_gt hadj' j)

/-- Packaged four-rate plateau-window frontier for #70.

The fields are exactly the arithmetic-facing inputs consumed by
`mcaPrizeLatticeResolved_of_chooseBounds_and_spike_adjacent`: per-rate lower radii with the
canonical-window binomial/count upper bound, per-rate spike radii and spike sizes, and the one-step
lattice adjacency check.  The hard work remains proving these fields for the prize rates; this
structure only makes the route reusable and prevents downstream files from repeating the long
hypothesis list. -/
structure MCAPrizeChooseSpikeFrontier (domain : ι ↪ F) where
  δ_lo : Fin 4 → ℝ≥0
  δ_hi : Fin 4 → ℝ≥0
  t : Fin 4 → ℕ
  δ_lo_le_one : ∀ j : Fin 4, δ_lo j ≤ 1
  choose_bound : ∀ j : Fin 4,
    ((Fintype.card ι).choose
        (max
          (⌈((1 : ℝ≥0) - δ_lo j) * (Fintype.card ι : ℝ≥0)⌉₊)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)) : ENNReal) /
      (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)
  δ_hi_le_one : ∀ j : Fin 4, δ_hi j ≤ 1
  t_le_n : ∀ j : Fin 4,
    t j + ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι
  t_le_q : ∀ j : Fin 4, t j ≤ Fintype.card F
  spike_radius : ∀ j : Fin 4,
    ((1 - δ_hi j) * Fintype.card ι : ℝ≥0) ≤
      (Fintype.card ι - t j + 1 : ℕ)
  spike_gt : ∀ j : Fin 4,
    (epsStar : ENNReal) < (t j : ENNReal) / (Fintype.card F : ENNReal)
  adjacent : ∀ j : Fin 4,
    (latticeIndexOf (ι := ι) (δ_hi j) (δ_hi_le_one j)).val =
      (latticeIndexOf (ι := ι) (δ_lo j) (δ_lo_le_one j)).val + 1

/-- Reassemble a faithful MCA lattice-prize resolution from the packaged plateau-window
frontier. -/
theorem mcaPrizeLatticeResolved_of_chooseSpikeFrontier
    (domain : ι ↪ F)
    (frontier : MCAPrizeChooseSpikeFrontier (F := F) domain) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (frontier.δ_lo j) (frontier.δ_lo_le_one j)) :=
  mcaPrizeLatticeResolved_of_chooseBounds_and_spike_adjacent
    domain frontier.δ_lo frontier.δ_hi frontier.t frontier.δ_lo_le_one
    frontier.choose_bound frontier.δ_hi_le_one frontier.t_le_n frontier.t_le_q
    frontier.spike_radius frontier.spike_gt frontier.adjacent

#print axioms ProximityGap.MCAPrizeChooseSpikeFrontier
#print axioms ProximityGap.mcaPrizeLatticeResolved_of_chooseSpikeFrontier

end LatticeBracket

end ProximityGap
