/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RadiusOneExact
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumRadiusOne

/-!
# The radius-one bad-scalar count as a ratio-image cardinality (Issue #39)

`GRAND-CHALLENGE-RESOLUTION.md` §6 identifies the residual open content of the
formalized Grand MCA Challenge as one finite extremal quantity: the maximal number of
distinct "bad ratios" of a line word. This file **names that target exactly** and
sharpens the lower-bound technology:

* `badRatios` — the finite set `{ -c_T(u₀)/c_T(u₁) : T ∈ ([n] choose k+1), c_T(u₁) ≠ 0 }`.
* `mcaEvent_one_iff_mem_badRatios` — the radius-one MCA event for `(u₀, u₁)` holds at `γ`
  **iff** `γ` is one of these ratios. (Forward: the good-subset extraction; backward:
  every ratio is realised, generalising `mcaEvent_at_gammaT` from the deep-hole second
  word to arbitrary `u₁`.)
* `mcaBadCount_one_eq_card_badRatios` — **the exact extremal target as an identity**:
  `mcaBadCount (RS) 1 u₀ u₁ = |badRatios u₀ u₁|`. The Grand-MCA middle band asks for
  `max_{u₀,u₁} |badRatios|`.
* `ratioSupport_card_le_mul_badCount` — **pigeonhole sharpening of the lower side**:
  if every realised line word `u₀ + γ·u₁` has `c_T`-vanishing multiplicity `≤ m`, then
  `|ratioSupport| ≤ m · mcaBadCount`. This separates the extremal problem into a
  *generic counting numerator* (`|ratioSupport u₁|`, which is `C(n, k+1)` for any `u₁`
  that is nowhere locally a codeword, e.g. the deep hole) and a *domain-dependent
  coincidence denominator* (`max_γ cTVanishCount(u₀ + γ·u₁)` — how many `(k+1)`-subsets
  of the domain can interpolate one line word, a line-decoding-flavoured quantity).
* `mcaBadCount_one_le_choose` — the `C(n, k+1)` cap, recovered in one line.

## Reconciliation (issue ask 4)

* `GrandChallengeRadiusOneExact.epsMCA_one_eq_choose_div` is the regime where the
  pigeonhole denominator can be forced to `1` on a generic stack: for
  `q > C(C(n,k+1), 2)` all `C(n,k+1)` ratios can be made pairwise distinct.
* `MCASecondMoment` lower-bounds the *same* image cardinality via the second moment of
  the ratio multiplicity; the pigeonhole form here replaces the variance argument with a
  max-multiplicity hypothesis, which is sharper whenever a uniform vanishing bound is
  available (e.g. from distance/list arguments about the line words).
* In the remaining middle band `q ∈ [2¹²⁸·Θ(ρ(1−ρ)n²), C(C(n,k+1),2)]` the exact value
  of `max |badRatios|` is the domain-dependent open core; see
  `research/proximity-prize/GRAND-MCA-CHALLENGE-RESOLUTION-2026-06-06.md` (the rogue /
  coincidence analysis) for its current measured structure.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. 2026. §1, §4.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- If `u₁` is non-extendable on `S`, no joint pair of codewords agrees with `(u₀, u₁)`
on `S` (the second component of a joint pair would extend `u₁`). Local copy of the
`MCAPlateauWindow` helper, kept here to keep this file's import cone small. -/
private theorem not_pairJoint_of_nonExtendable_right'
    {C : Set (ι → F)} {S : Finset ι} {u₀ u₁ : ι → F}
    (hne : NonExtendableOn C S u₁) :
    ¬ pairJointAgreesOn C S u₀ u₁ := by
  rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
  exact hne ⟨v₁, hv₁, fun i hi => (hagree i hi).2⟩

open Classical in
/-- The `(k+1)`-subsets on which `u₁` is non-extendable, i.e. `c_T(u₁) ≠ 0` — the
"support" of the ratio map for the stack direction `u₁`. -/
noncomputable def ratioSupport (domain : ι ↪ F) (k : ℕ) (u₁ : ι → F) : Finset (Finset ι) :=
  (Finset.univ.powersetCard (k + 1)).filter (fun T => cT domain k T u₁ ≠ 0)

open Classical in
/-- The bad-ratio image: the finite set of scalars `-c_T(u₀)/c_T(u₁)` over the ratio
support. By `mcaBadCount_one_eq_card_badRatios` its cardinality **is** the radius-one
bad-scalar count of the stack `(u₀, u₁)`. -/
noncomputable def badRatios (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) : Finset F :=
  (ratioSupport domain k u₁).image (fun T => -(cT domain k T u₀) / cT domain k T u₁)

/-- **The radius-one MCA event is exactly ratio membership.** Generalises
`mcaEvent_at_gammaT` (deep-hole second word) to arbitrary stacks. -/
theorem mcaEvent_one_iff_mem_badRatios (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) (γ : F) :
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ ↔
      γ ∈ badRatios domain k u₀ u₁ := by
  classical
  constructor
  · -- event ⟹ a good (k+1)-subset ⟹ the ratio identity
    intro h
    obtain ⟨T, hTcard, ⟨w, hw, hwline⟩, hneT⟩ := exists_goodSubset_of_mcaEvent domain h
    -- `c_T(u₁) ≠ 0` from non-extendability
    have hne0 : cT domain k T u₁ ≠ 0 := fun h0 =>
      hneT ((extendable_iff_cT_eq_zero domain hTcard u₁).mpr h0)
    -- the line is extendable on `T`, so its functional vanishes
    have hline0 : cT domain k T (u₀ + γ • u₁) = 0 := by
      refine (extendable_iff_cT_eq_zero domain hTcard (u₀ + γ • u₁)).mp ?_
      exact ⟨w, hw, fun i hi => hwline i hi⟩
    -- linearity turns the vanishing into the ratio identity
    have hlin : cT domain k T u₀ + γ * cT domain k T u₁ = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← map_add]
      exact hline0
    have hγ : γ = -(cT domain k T u₀) / cT domain k T u₁ := by
      field_simp
      linear_combination hlin
    rw [badRatios, Finset.mem_image]
    refine ⟨T, ?_, hγ.symm⟩
    rw [ratioSupport, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, hTcard⟩, hne0⟩
  · -- every ratio is realised: witness set `T` itself
    intro h
    rw [badRatios, Finset.mem_image] at h
    obtain ⟨T, hT, hγ⟩ := h
    rw [ratioSupport, Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨-, hTcard⟩, hne0⟩ := hT
    have hneT : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T u₁ := fun hext =>
      hne0 ((extendable_iff_cT_eq_zero domain hTcard u₁).mp hext)
    refine ⟨T, by simp, ?_, not_pairJoint_of_nonExtendable_right' hneT⟩
    -- the line functional vanishes at the ratio, so the line is extendable on `T`
    have hline0 : cT domain k T (u₀ + γ • u₁) = 0 := by
      rw [map_add, map_smul, smul_eq_mul, ← hγ, div_mul_cancel₀ _ hne0]
      ring
    obtain ⟨w, hw, hwagree⟩ :=
      (extendable_iff_cT_eq_zero domain hTcard (u₀ + γ • u₁)).mpr hline0
    exact ⟨w, hw, fun i hi => hwagree i hi⟩

/-- **The exact extremal target, named (Issue #39 ask 1).** The radius-one bad-scalar
count of a stack is the cardinality of its bad-ratio image; the Grand-MCA middle band is
the determination of `max_{u₀,u₁} |badRatios|`. -/
theorem mcaBadCount_one_eq_card_badRatios (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F) (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ =
      (badRatios domain k u₀ u₁).card := by
  classical
  unfold mcaBadCount
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mcaEvent_one_iff_mem_badRatios domain k u₀ u₁ γ

open Classical in
/-- The `c_T`-vanishing multiplicity of a word: how many `(k+1)`-subsets interpolate it.
This is the domain-dependent coincidence quantity of the pigeonhole bound. -/
noncomputable def cTVanishCount (domain : ι ↪ F) (k : ℕ) (v : ι → F) : ℕ :=
  ((Finset.univ.powersetCard (k + 1)).filter (fun T => cT domain k T v = 0)).card

/-- **Pigeonhole sharpening of the lower side (Issue #39 asks 2–3).** If every realised
line word `u₀ + γ·u₁` (γ a bad ratio) has vanishing multiplicity at most `m`, then

  `|ratioSupport u₁| ≤ m · mcaBadCount(RS, 1, u₀, u₁)`.

The numerator `|ratioSupport u₁|` is generic counting (it equals `C(n, k+1)` whenever
`u₁` is locally non-extendable everywhere, e.g. the deep hole, by `cT_deepHole`); the
multiplicity bound `m` isolates the domain-dependent additive/coincidence input. Any
upper bound on line-word interpolation coincidences immediately becomes a lower bound on
the extremal count, strengthening the second-moment route of `MCASecondMoment`. -/
theorem ratioSupport_card_le_mul_badCount (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F)
    (m : ℕ)
    (hm : ∀ γ ∈ badRatios domain k u₀ u₁,
      cTVanishCount domain k (u₀ + γ • u₁) ≤ m) :
    (ratioSupport domain k u₁).card ≤
      m * mcaBadCount (F := F) (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ := by
  classical
  rw [mcaBadCount_one_eq_card_badRatios]
  rw [badRatios]
  refine Finset.card_le_mul_card_image (s := ratioSupport domain k u₁) m ?_
  intro γ hγ
  refine le_trans (Finset.card_le_card ?_) (hm γ (by rwa [badRatios]))
  intro T hT
  rw [Finset.mem_filter] at hT
  obtain ⟨hTsupp, hTratio⟩ := hT
  have hTsupp' := hTsupp
  rw [ratioSupport, Finset.mem_filter] at hTsupp'
  rw [Finset.mem_filter]
  refine ⟨hTsupp'.1, ?_⟩
  -- the ratio equation makes the line functional vanish
  rw [map_add, map_smul, smul_eq_mul, ← hTratio, div_mul_cancel₀ _ hTsupp'.2]
  ring

/-- The `C(n, k+1)` cap on the bad-scalar count, recovered from the ratio-image identity
in one line (reconciles with `epsMCA_one_le_choose_div`). -/
theorem mcaBadCount_one_le_choose (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F) (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ ≤
      (Fintype.card ι).choose (k + 1) := by
  classical
  rw [mcaBadCount_one_eq_card_badRatios]
  calc (badRatios domain k u₀ u₁).card
      ≤ (ratioSupport domain k u₁).card := Finset.card_image_le
    _ ≤ (Finset.univ.powersetCard (k + 1) : Finset (Finset ι)).card :=
        Finset.card_filter_le _ _
    _ = (Fintype.card ι).choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ]

/-- For the deep-hole direction the ratio support is **everything**: the generic-counting
numerator of the pigeonhole bound equals `C(n, k+1)` exactly. -/
theorem ratioSupport_deepHole_eq (domain : ι ↪ F) (k : ℕ) :
    ratioSupport domain k (deepHole domain k) =
      Finset.univ.powersetCard (k + 1) := by
  classical
  rw [ratioSupport]
  refine Finset.filter_true_of_mem ?_
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  rw [cT_deepHole domain hT.2]
  exact one_ne_zero

/-! ## Sharp exact-value criterion: ratio-injectivity replaces the field-size hypothesis

`GrandChallengeRadiusOneExact.epsMCA_one_eq_choose_div` proves the exact radius-one value
`ε_mca(RS, 1) = C(n, k+1)/q` under the *crude field-size* sufficient condition
`q > C(C(n, k+1), 2)` (enough room for `C(n,k+1)` distinct subset functionals to be pairwise
separated generically). The genuine attainment criterion is sharper: the `C(n,k+1)` cap is hit
exactly as soon as **some** stack direction `u₀` has the `(k+1)`-subset functionals `c_T(u₀)`
pairwise distinct — equivalently its bad-ratio image is injective. This holds on far smaller
fields for structured domains, directly **narrowing the undecided middle band** (Issue #39). -/

/-- **Sharp radius-one lower bound.** If some `u₀` has injective `c_T` functionals over the
`(k+1)`-subsets, then `C(n, k+1)/q ≤ ε_mca(RS, 1)` — *no* field-size hypothesis. The deep-hole
second word turns each subset `T` into the distinct bad scalar `-c_T(u₀)`. -/
theorem epsMCA_one_ge_choose_div_of_cT_injOn (domain : ι ↪ F) (k : ℕ) (u₀ : ι → F)
    (hu₀ : ∀ T ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
        cT domain k T u₀ = cT domain k T' u₀ → T = T') :
    (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  refine le_trans (mcaEvent_prob_ge domain hu₀) ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 (u 0) (u 1) γ ])
    (Code.finMapTwoWords u₀ (deepHole domain k))

/-- **Sharp EXACT radius-one value.** `ε_mca(RS, 1) = C(n, k+1)/q` whenever some `u₀` has
injective `c_T` functionals over the `(k+1)`-subsets. Strictly weaker hypothesis than
`epsMCA_one_eq_choose_div`'s `q > C(C(n,k+1), 2)` (which produces such a `u₀` via
`exists_u0_injOn_cT`); needs no `k + 1 ≤ n` either. -/
theorem epsMCA_one_eq_choose_div_of_cT_injOn (domain : ι ↪ F) (k : ℕ) (u₀ : ι → F)
    (hu₀ : ∀ T ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
        cT domain k T u₀ = cT domain k T' u₀ → T = T') :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 =
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) :=
  le_antisymm (epsMCA_one_le_choose_div domain k)
    (epsMCA_one_ge_choose_div_of_cT_injOn domain k u₀ hu₀)

/-- **Sharp decision of the formal Grand MCA Challenge.** Under ratio-injectivity for some
`u₀`, the Challenge holds for `RS[F, domain, k]` at threshold `ε*` iff `C(n, k+1)/q ≤ ε*` —
the same clean dichotomy as `grandMCAChallenge_iff_choose_le` but on the sharper criterion,
deciding the predicate on smaller fields than the `q > C(C(n,k+1),2)` regime. -/
theorem grandMCAChallenge_iff_choose_le_of_cT_injOn (domain : ι ↪ F) (k : ℕ) (u₀ : ι → F)
    (hu₀ : ∀ T ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
        cT domain k T u₀ = cT domain k T' u₀ → T = T') (ε_star : ℝ≥0) :
    grandMCAChallenge (ReedSolomon.code domain k) ε_star ↔
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal)
        ≤ (ε_star : ENNReal) := by
  rw [grandMCAChallenge_iff_epsMCA_one, epsMCA_one_eq_choose_div_of_cT_injOn domain k u₀ hu₀]

open GrandChallenges in
/-- **Sharp four-rate MCA prize decision.** Under ratio-injectivity at each prize rate (some
`u₀ j` with injective `c_T` over the `(k_j+1)`-subsets, `k_j := ⌊ρ_j·n⌋`), the ABF26 §1 MCA
prize holds iff `C(n, k_j+1)/q ≤ ε*` at all four prize rates — the sharp analogue of
`mcaPrize_iff_of_quadratic_field`, deciding the prize on smaller fields than the
`q > C(C(n,k+1),2)` quadratic-field regime. -/
theorem mcaPrize_iff_of_cT_injOn (domain : ι ↪ F)
    (u₀ : Fin 4 → (ι → F))
    (hu₀ : ∀ j : Fin 4,
      ∀ T ∈ (Finset.univ : Finset ι).powersetCard
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1),
        cT domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ T (u₀ j) =
          cT domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ T' (u₀ j) → T = T') :
    mcaPrize domain ↔
      ∀ j : Fin 4,
        ((Fintype.card ι).choose (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal) /
            (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal) := by
  unfold mcaPrize grandMCAChallengeRSrate grandMCAChallengeRS
  exact forall_congr' fun j =>
    grandMCAChallenge_iff_choose_le_of_cT_injOn domain _ (u₀ j) (hu₀ j) epsStar

/-! ## Unification with the subset-sum floor

For the canonical deep-hole stack `(u₀, u₁) = (deepHole_{k+1}, deepHole_k)`, the bad-ratio image
is exactly the negated `(k+1)`-subset-sum set, so the radius-one bad count equals
`|Σ_{k+1}(L)|`. This recovers the unconditional subset-sum floor
(`SubsetSumRadiusOne.epsMCA_one_ge_card_subsetSums`) as an *exact* bad-scalar count, unifying the
`badRatios` exact-value thread with the additive-combinatorics floor. -/

/-- **badRatios of the deep-hole stack = negated `(k+1)`-subset-sums.** Every `(k+1)`-subset `T`
contributes the bad ratio `-c_T(deepHole_{k+1})/c_T(deepHole_k) = -(∑_{i∈T} domain i)`
(`cT_deepHole_succ` + `cT_deepHole`); the ratio support is all of `([n] choose k+1)`. -/
theorem badRatios_deepHole_eq (domain : ι ↪ F) (k : ℕ) :
    badRatios domain k (deepHole domain (k + 1)) (deepHole domain k) =
      (subsetSumsKplus1 domain k).image (fun s => -s) := by
  classical
  rw [badRatios, ratioSupport_deepHole_eq, subsetSumsKplus1, Finset.image_image]
  refine Finset.image_congr ?_
  intro T hT
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hT
  simp only [Function.comp]
  rw [cT_deepHole_succ domain hT.2, cT_deepHole domain hT.2, div_one]

/-- **The radius-one bad count for the deep-hole stack is exactly `|Σ_{k+1}(L)|`.** Recovers the
unconditional subset-sum floor as an *exact* bad-scalar count via the bad-ratio image
(negation is injective). -/
theorem mcaBadCount_one_deepHole_eq_card_subsetSums (domain : ι ↪ F) (k : ℕ) :
    mcaBadCount (F := F) (ReedSolomon.code domain k : Set (ι → F)) 1
        (deepHole domain (k + 1)) (deepHole domain k) =
      (subsetSumsKplus1 domain k).card := by
  rw [mcaBadCount_one_eq_card_badRatios, badRatios_deepHole_eq,
    Finset.card_image_of_injective _ neg_injective]

end ProximityGap
