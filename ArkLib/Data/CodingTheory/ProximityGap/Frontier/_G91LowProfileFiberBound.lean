/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiberMixedProfileFit
import ArkLib.Data.CodingTheory.ProximityGap.LineListIncidenceMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# G91 (#466): a q-FREE low-profile fiber bound — `D(t) ≤ C(s, a−t)` under a
# direction-only nonzero-codeword census, with the exact dichotomy on failure

The weld's `hlow` production obligation (dossier v3 §6 Tier-1 item 2) asks for a
better-than-field-power bound on the exact-appearance fibers
`D(t) = #exactAppearingZeroAgreementFiber(S)`, `|S| = t < k`, on large-zero-safe lines.
Known bounds: the field-power envelope `q^(k−t)` (useless — formally refuted as a fit), and
the per-scalar circular bound `D(t) ≤ Λ_b` (`_LowProfileFiberBound.lean`, vicious).

**This file proves the first non-circular, `q`-free fiber bound**, by a *support-localized
incidence-ownership* argument (the localization of the `_SecondWitnessFloor` incidence cap
to a single exact profile — note `AgreementFarDirection` itself is FALSE on every large-zero
direction, because the zero codeword agrees with `u₁` on its whole zero set, so the
`_SecondWitnessFloor` cap is not applicable here; excluding the zero codeword and localizing
to the fiber is exactly what makes the argument go through):

* **Headline** (`exactAppearingZeroAgreementFiber_card_le_choose_of_sVanishingFar`): if no
  NONZERO codeword vanishing on `S` agrees with the direction `u₁` on ≥ `a` coordinates
  (`SVanishingFarDirection` — a DIRECTION-only census, no `u₀`), then

  `D(S) ≤ C(s, a − t)`,   `s = #support(u₁)`, `t = #S`  —  **no `q` anywhere.**

  Mechanism: every heavy incidence `(γ, c)` with exact zero-profile `S` owns a private
  `(a−t)`-subset of the moving support: its agreement set meets `Z` only inside `S`
  (exactness), so it has ≥ `a−t` support agreements; sharing an `(a−t)`-subset `T` across
  scalars would make `d = (γ−γ')⁻¹(c−c')` a codeword that vanishes on `S` (both witnesses
  equal `u₀` there) and agrees with `u₁` on `S ∪ T` (`a` coordinates, `d = u₁ ≠ 0` on
  `T ⊆ supp`, so `d ≠ 0`) — refuting the census; sharing within one scalar forces the two
  witnesses to agree on `S ∪ T` (`a ≥ k` points of the same line word), hence coincide.

* **The dichotomy** (`exactFiber_card_le_choose_or_exists_nonzero_vanishing_agreeing`):
  unconditionally, every exact fiber either obeys the `C(s, a−t)` cap or its line's
  direction admits a NONZERO codeword vanishing on `S` with ≥ `a` agreements — i.e. the
  direction's coset contains a second large-zero representative.  The failure branch is a
  structured direction-census event, not an unknown.

* **Satisfiability, both ways** (skeptic guards):
  - `nonzeroAgreementFarDirection_of_largeZero_of_unique_decoding`: above unique decoding
    (`n + k ≤ 2a`) the census is a THEOREM on every large-zero direction, so
    `uniformLargeZeroSafeLowExactFiberBudgeted_of_unique_decoding` is unconditional there.
  - `not_nonzeroAgreementFar_census_of_two_mul_le`: at `2a ≤ n` (all prize shapes) the
    uniform census over ALL large-zero directions is FALSE (step direction + constant
    codeword) — so in-window the census is a genuine named hypothesis on the direction
    class, and this file's uniform consumer must not be silently upgraded.

* **Consumer** (named, in-tree): the uniform form
  `uniformLargeZeroSafeLowExactFiberBudgeted_of_census` produces exactly
  `UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a
  (fun t => (n−a).choose (a−t))` — the `hExactLow` slot of
  `uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit`
  (`LineListAppearanceFiberMixedProfileFit.lean`); the composition
  `uniformLineBadScalarsBudgeted_of_census_mixedChooseProfileSumsFit` fires that consumer
  with the `hExactLow` slot DISCHARGED.

**Probe** (`scripts/probes/probe_466_g91_lowprofile_fiber.py`, output
`_out_466_g91_lowprofile_fiber.txt`; n = 8, k = 2, a = 4, q = 17,
978 lines, 35 708 far `(S,t)` instances): 0 violations; 1 818 NONEMPTY far fibers, with
`D = 2 > 1` realized at `t = 1 < k` (so no `≤ 1` uniqueness bound covers the low profiles;
there the cap is `C(4,3) = 4` against field-power `17`); on the failure branch `D` up to
`14 > C(s,a−t)` is realized, so the census hypothesis is load-bearing, not decorative.

**Honest scope.** This does NOT discharge `hlow` at prize budgets: the choose-profile
arithmetic downstream of the fiber budget explodes independently of `D(t)`
(`_LowProfileFiberCoupled.lean` — occupancy), and in-window the census itself is open on the
adversarial direction class (refuter above).  What is new: the field-power envelope on the
open `t < k` fibers is replaced, on the census class, by a `q`-free binomial in the moving
support only — the first fiber bound that survives `q → ∞` at fixed `(n, k, a)` — plus the
exact structure of the complement (second large-zero coset representative).

All theorems axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.G91LowProfileFiberBound

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 0. The direction-only census Props -/

/-- **The per-profile census** (the minimal hypothesis of the headline): no NONZERO codeword
vanishing on `S` agrees with the direction `u₁` on `a` or more coordinates.  Unlike
`AgreementFarDirection` (`_SecondWitnessFloor`), the zero codeword is excluded — essential on
the large-zero branch, where `0` agrees with `u₁` on the whole zero set (`≥ a` points). -/
def SVanishingFarDirection
    (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) (S : Finset (Fin n)) : Prop :=
  ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ 0 → (∀ i ∈ S, c i = 0) →
    (agreeSet c u₁).card < a

/-- **The direction census**: no NONZERO codeword agrees with `u₁` on `a` or more
coordinates.  Implies the per-profile census for every `S`. -/
def NonzeroAgreementFarDirection
    (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) : Prop :=
  ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ 0 →
    (agreeSet c u₁).card < a

theorem sVanishingFarDirection_of_nonzeroAgreementFar
    (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F)
    (hfar : NonzeroAgreementFarDirection dom k a u₁) (S : Finset (Fin n)) :
    SVanishingFarDirection dom k a u₁ S :=
  fun c hc hne _ => hfar c hc hne

/-! ### 1. Exact-profile incidences and their support-subset fibers -/

open Classical in
/-- Heavy incidences `(γ, c)` whose codeword has zero-direction agreement set exactly `S`. -/
noncomputable def exactProfileIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (F × (Fin n → F)) :=
  (lineHeavyIncidences dom k a u₀ u₁).filter
    (fun e => directionZeroAgreementSet e.2 u₀ u₁ = S)

open Classical in
theorem mem_exactProfileIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n))
    (e : F × (Fin n → F)) :
    e ∈ exactProfileIncidences dom k a u₀ u₁ S ↔
      e.2 ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i)).card ∧
        directionZeroAgreementSet e.2 u₀ u₁ = S := by
  rw [exactProfileIncidences, Finset.mem_filter, mem_lineHeavyIncidences]
  tauto

open Classical in
/-- Exact-profile incidences whose agreement set contains the fixed support subset `T`. -/
noncomputable def supportSubsetIncidenceFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S T : Finset (Fin n)) :
    Finset (F × (Fin n → F)) :=
  (exactProfileIncidences dom k a u₀ u₁ S).filter
    (fun e => T ⊆ agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i))

open Classical in
theorem mem_supportSubsetIncidenceFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S T : Finset (Fin n))
    (e : F × (Fin n → F)) :
    e ∈ supportSubsetIncidenceFiber dom k a u₀ u₁ S T ↔
      e ∈ exactProfileIncidences dom k a u₀ u₁ S ∧
        T ⊆ agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i) := by
  rw [supportSubsetIncidenceFiber, Finset.mem_filter]

/-! ### 2. The rigidity core: each support `(a−t)`-subset is owned by ≤ 1 incidence -/

open Classical in
/-- **Support-localized incidence rigidity.**  On a line whose direction passes the
per-profile census over `S`, a support subset `T` with `#T = a − #S` (and `#S < a`,
`k ≤ a`) is contained in the agreement set of AT MOST ONE exact-profile-`S` incidence:
sharing across scalars produces a nonzero codeword vanishing on `S` and agreeing with `u₁`
on `S ∪ T` (`a` points) against the census; sharing within one scalar makes the two
witnesses agree on `S ∪ T` (`a ≥ k` points of the same line word), forcing them equal. -/
theorem supportSubsetIncidenceFiber_card_le_one
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S T : Finset (Fin n)}
    (hSa : S.card < a)
    (hfar : SVanishingFarDirection dom k a u₁ S)
    (hT : T ⊆ directionSupportSet u₁) (hTcard : T.card = a - S.card) :
    (supportSubsetIncidenceFiber dom k a u₀ u₁ S T).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨γ, c⟩ he ⟨γ', c'⟩ he'
  rw [mem_supportSubsetIncidenceFiber, mem_exactProfileIncidences] at he he'
  obtain ⟨⟨hcCode, -, hzS⟩, hTagr⟩ := he
  obtain ⟨⟨hc'Code, -, hzS'⟩, hTagr'⟩ := he'
  -- pointwise consequences of exactness: both witnesses equal `u₀` on `S`, and `S ⊆ Z`
  have hcS : ∀ i ∈ S, c i = u₀ i := by
    intro i hi
    have hmem : i ∈ directionZeroAgreementSet c u₀ u₁ := by rw [hzS]; exact hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hmem
    exact hmem.2
  have hc'S : ∀ i ∈ S, c' i = u₀ i := by
    intro i hi
    have hmem : i ∈ directionZeroAgreementSet c' u₀ u₁ := by rw [hzS']; exact hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hmem
    exact hmem.2
  have hSzero : ∀ i ∈ S, u₁ i = 0 := by
    intro i hi
    have hmem : i ∈ directionZeroAgreementSet c u₀ u₁ := by rw [hzS]; exact hi
    rw [directionZeroAgreementSet, Finset.mem_filter, directionZeroSet,
      Finset.mem_filter] at hmem
    exact hmem.1.2
  have hTsupp : ∀ i ∈ T, u₁ i ≠ 0 := by
    intro i hi
    have := hT hi
    rw [directionSupportSet, Finset.mem_filter] at this
    exact this.2
  -- line equations on T
  have hcT : ∀ i ∈ T, c i = u₀ i + γ • u₁ i := by
    intro i hi
    have := hTagr hi
    rw [agreeSet, Finset.mem_filter] at this
    exact this.2
  have hc'T : ∀ i ∈ T, c' i = u₀ i + γ' • u₁ i := by
    intro i hi
    have := hTagr' hi
    rw [agreeSet, Finset.mem_filter] at this
    exact this.2
  -- S and T are disjoint, and their union has exactly a elements
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact hTsupp i hiT (hSzero i hiS)
  have hcardST : (S ∪ T).card = a := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard]
    omega
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    omega
  -- scalars agree
  have hγ : γ = γ' := by
    by_contra hγne
    have hδ : γ - γ' ≠ 0 := sub_ne_zero.mpr hγne
    set d : Fin n → F := (γ - γ')⁻¹ • (c - c') with hd
    have hdCode : d ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hcCode hc'Code)
    have hdT : ∀ i ∈ T, d i = u₁ i := by
      intro i hi
      have h1 := hcT i hi
      have h2 := hc'T i hi
      show (γ - γ')⁻¹ • (c i - c' i) = u₁ i
      rw [h1, h2]
      simp only [smul_eq_mul]
      field_simp
      ring
    have hdS : ∀ i ∈ S, d i = 0 := by
      intro i hi
      show (γ - γ')⁻¹ • (c i - c' i) = 0
      rw [hcS i hi, hc'S i hi, sub_self, smul_zero]
    have hdne : d ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := hTne
      intro h0
      have hz : d i₀ = 0 := by rw [h0]; rfl
      rw [hdT i₀ hi₀] at hz
      exact hTsupp i₀ hi₀ hz
    have hsub : S ∪ T ⊆ agreeSet d u₁ := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hi with hiS | hiT
      · rw [hdS i hiS, hSzero i hiS]
      · exact hdT i hiT
    have hge : a ≤ (agreeSet d u₁).card := by
      calc a = (S ∪ T).card := hcardST.symm
        _ ≤ (agreeSet d u₁).card := Finset.card_le_card hsub
    exact absurd hge (not_le.mpr (hfar d hdCode hdne hdS))
  subst hγ
  -- witnesses agree (both interpolate the same line word on S ∪ T, a ≥ k points)
  have hc : c = c' := by
    by_contra hne
    have hsub : S ∪ T ⊆ agreeSet c c' := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hi with hiS | hiT
      · rw [hcS i hiS, hc'S i hiS]
      · rw [hcT i hiT, hc'T i hiT]
    have hlarge : a ≤ (agreeSet c c').card := by
      calc a = (S ∪ T).card := hcardST.symm
        _ ≤ (agreeSet c c').card := Finset.card_le_card hsub
    have hsmall : (agreeSet c c').card ≤ k - 1 :=
      rsCode_pairwise_agreeSet_card_le dom hk1 hcCode hc'Code hne
    omega
  subst hc
  rfl

/-! ### 3. The cover: every exact-profile incidence owns an `(a−t)`-support-subset -/

open Classical in
/-- Every exact-profile-`S` incidence has at least `a − #S` support agreements (its agreement
set meets the zero set only inside `S`), hence lies in some support-subset fiber. -/
theorem exactProfileIncidences_subset_biUnion
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    exactProfileIncidences dom k a u₀ u₁ S ⊆
      ((directionSupportSet u₁).powersetCard (a - S.card)).biUnion
        (fun T => supportSubsetIncidenceFiber dom k a u₀ u₁ S T) := by
  intro e he
  obtain ⟨hcCode, hheavy, hzS⟩ := (mem_exactProfileIncidences dom k a u₀ u₁ S e).mp he
  set Ag : Finset (Fin n) := agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i) with hAg
  -- the zero-direction part of the agreement set sits inside S
  have hAgZ : Ag.filter (fun i => u₁ i = 0) ⊆ S := by
    intro i hi
    rw [Finset.mem_filter, hAg, agreeSet, Finset.mem_filter] at hi
    obtain ⟨⟨-, hagr⟩, hz⟩ := hi
    rw [← hzS, directionZeroAgreementSet, Finset.mem_filter, directionZeroSet,
      Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hz⟩, ?_⟩
    rw [hagr, hz, smul_zero, add_zero]
  -- so the support part has at least a − #S elements
  have hsplit : (Ag.filter (fun i => u₁ i = 0)).card
      + (Ag.filter (fun i => ¬ u₁ i = 0)).card = Ag.card :=
    Finset.card_filter_add_card_filter_not (fun i => u₁ i = 0)
  have hzcard : (Ag.filter (fun i => u₁ i = 0)).card ≤ S.card :=
    Finset.card_le_card hAgZ
  have hsuppcard : a - S.card ≤ (Ag.filter (fun i => ¬ u₁ i = 0)).card := by
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hsuppcard
  refine Finset.mem_biUnion.mpr ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, hTcard⟩
    intro i hi
    have := hTsub hi
    rw [Finset.mem_filter] at this
    rw [directionSupportSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, this.2⟩
  · rw [mem_supportSubsetIncidenceFiber]
    refine ⟨he, ?_⟩
    intro i hi
    have := hTsub hi
    rw [Finset.mem_filter, hAg] at this
    exact this.1

open Classical in
/-- **The exact-profile incidence cap**: under the per-profile census, the TOTAL number of
heavy incidences with exact zero-profile `S` is at most `C(s, a − #S)` — `q`-free. -/
theorem exactProfileIncidences_card_le_choose
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hSa : S.card < a)
    (hfar : SVanishingFarDirection dom k a u₁ S) :
    (exactProfileIncidences dom k a u₀ u₁ S).card
      ≤ (directionSupportSet u₁).card.choose (a - S.card) := by
  calc (exactProfileIncidences dom k a u₀ u₁ S).card
      ≤ (((directionSupportSet u₁).powersetCard (a - S.card)).biUnion
          (fun T => supportSubsetIncidenceFiber dom k a u₀ u₁ S T)).card :=
        Finset.card_le_card (exactProfileIncidences_subset_biUnion dom k a u₀ u₁ S)
    _ ≤ ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
          (supportSubsetIncidenceFiber dom k a u₀ u₁ S T).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ (directionSupportSet u₁).powersetCard (a - S.card), 1 := by
        refine Finset.sum_le_sum (fun T hT => ?_)
        obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
        exact supportSubsetIncidenceFiber_card_le_one dom k a hk1 hka u₀ u₁ hSa hfar
          hTsub hTcard
    _ = (directionSupportSet u₁).card.choose (a - S.card) := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powersetCard]

/-! ### 4. The headline: `D(t) ≤ C(s, a−t)` -/

open Classical in
/-- The exact appearance fiber injects into the exact-profile incidences (project any
appearing scalar back onto the codeword). -/
theorem exactAppearingZeroAgreementFiber_card_le_exactProfileIncidences_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
      ≤ (exactProfileIncidences dom k a u₀ u₁ S).card := by
  have hsub : exactAppearingZeroAgreementFiber dom k a u₀ u₁ S ⊆
      (exactProfileIncidences dom k a u₀ u₁ S).image Prod.snd := by
    intro c hc
    obtain ⟨happ, hzS⟩ := (mem_exactAppearingZeroAgreementFiber dom k a u₀ u₁ c S).mp hc
    rw [lineAppearingCodewords, Finset.mem_filter] at happ
    obtain ⟨-, hcCode, γ, hγ⟩ := happ
    refine Finset.mem_image.mpr ⟨(γ, c), ?_, rfl⟩
    rw [mem_exactProfileIncidences]
    exact ⟨hcCode, hγ, hzS⟩
  calc (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
      ≤ ((exactProfileIncidences dom k a u₀ u₁ S).image Prod.snd).card :=
        Finset.card_le_card hsub
    _ ≤ (exactProfileIncidences dom k a u₀ u₁ S).card := Finset.card_image_le

open Classical in
/-- **HEADLINE — the `q`-free low-profile fiber bound.**  Under the per-profile census (no
nonzero codeword vanishing on `S` agrees with the direction on ≥ `a` points), the exact
appearance fiber obeys

  `D(S) ≤ C(#support(u₁), a − #S)`.

No field size appears; the bound survives `q → ∞` at fixed `(n, k, a)`.  Compare: the
field-power envelope is `q^(k−#S)` (refuted as a fit), and the per-scalar route only gives
the circular `D ≤ Λ_b` (`_LowProfileFiberBound.lean` §6-7).  When `a − #S > s` the binomial
is `0` — the bound degenerates exactly to the R2B stratum-emptiness fact. -/
theorem exactAppearingZeroAgreementFiber_card_le_choose_of_sVanishingFar
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hSa : S.card < a)
    (hfar : SVanishingFarDirection dom k a u₁ S) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
      ≤ (directionSupportSet u₁).card.choose (a - S.card) :=
  le_trans
    (exactAppearingZeroAgreementFiber_card_le_exactProfileIncidences_card
      dom k a u₀ u₁ S)
    (exactProfileIncidences_card_le_choose dom k a hk1 hka u₀ u₁ hSa hfar)

/-! ### 5. The unconditional dichotomy -/

open Classical in
/-- **The dichotomy.**  With no hypothesis on the direction: every exact fiber either obeys
the `q`-free cap `C(s, a − t)`, or the direction admits a NONZERO codeword vanishing on `S`
that agrees with it on ≥ `a` coordinates — i.e. `u₁ − c` is a SECOND large-zero
representative of the direction's coset (it vanishes on the ≥ `a` agreement points).  The
failure branch is a structured coset-census event, exactly the object the weld's
direction-coset invariance (`mcaEvent_direction_sub_codeword_iff`) manipulates. -/
theorem exactFiber_card_le_choose_or_exists_nonzero_vanishing_agreeing
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hSa : S.card < a) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card
        ≤ (directionSupportSet u₁).card.choose (a - S.card)
      ∨ ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ 0 ∧
          (∀ i ∈ S, c i = 0) ∧ a ≤ (agreeSet c u₁).card := by
  by_cases hfar : SVanishingFarDirection dom k a u₁ S
  · exact Or.inl
      (exactAppearingZeroAgreementFiber_card_le_choose_of_sVanishingFar
        dom k a hk1 hka u₀ u₁ hSa hfar)
  · rw [SVanishingFarDirection] at hfar
    push Not at hfar
    obtain ⟨c, hcCode, hcne, hcvan, hcagr⟩ := hfar
    exact Or.inr ⟨c, hcCode, hcne, hcvan, hcagr⟩

/-! ### 6. Consumers: the named in-tree `hExactLow` slot -/

open Classical in
/-- Per-line consumer: the direction census delivers the in-tree low exact-fiber budget
shape with `M t = C(s, a − t)`. -/
theorem zeroLowExactFiberBudgeted_of_nonzeroAgreementFar
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (u₀ u₁ : Fin n → F)
    (hfar : NonzeroAgreementFarDirection dom k a u₁) :
    ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁
      (fun t => (directionSupportSet u₁).card.choose (a - t)) := by
  intro t ht _htk S hS
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  have hb := exactAppearingZeroAgreementFiber_card_le_choose_of_sVanishingFar
    dom k a hk1 hka u₀ u₁ (S := S) (by omega)
    (sVanishingFarDirection_of_nonzeroAgreementFar dom k a u₁ hfar S)
  rw [hScard] at hb
  exact hb

open Classical in
/-- **The uniform consumer.**  If the direction census holds on the large-zero class, the
named production obligation `UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted`
holds with the `q`-FREE budget `M t = C(n − a, a − t)` (on large-zero directions
`s ≤ n − a`).  This is verbatim the `hExactLow` hypothesis of
`uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit`
(`LineListAppearanceFiberMixedProfileFit.lean`) — the in-tree consumer that fires below. -/
theorem uniformLargeZeroSafeLowExactFiberBudgeted_of_census
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (hcensus : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      NonzeroAgreementFarDirection dom k a u₁) :
    UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a
      (fun t => (n - a).choose (a - t)) := by
  intro u₀ u₁ hne _hsafe t ht htk S hS
  have hb := zeroLowExactFiberBudgeted_of_nonzeroAgreementFar dom k a hk1 hka u₀ u₁
    (hcensus u₁ hne) t ht htk S hS
  -- on large-zero directions the support has at most n − a elements
  have hz : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hne
    omega
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.card_filter_add_card_filter_not]
    simp
  have hs : (directionSupportSet u₁).card ≤ n - a := by omega
  exact le_trans hb (Nat.choose_le_choose (a - t) hs)

open Classical in
/-- **The consumer FIRES.**  The composition of the census result with the in-tree consumer
`uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit`: the `hExactLow` slot
is DISCHARGED at the `q`-free exact budget `Mexact t = C(n − a, a − t)`; the remaining named
hypotheses (support list budget, arithmetic fits, zero safety, high ceilings) are the
residual exactly as before.  This retires the exact-fiber slot of the mixed route on the
census class. -/
theorem uniformLineBadScalarsBudgeted_of_census_mixedChooseProfileSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (hka : k ≤ a)
    (Mcoarse : ℕ → ℕ)
    (hcensus : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      NonzeroAgreementFarDirection dom k a u₁)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfileFit : UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a
      (fun t => (n - a).choose (a - t)) Mcoarse)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
    dom hk a L B (fun t => (n - a).choose (a - t)) Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactFiberBudgeted_of_census dom k a hk hka hcensus)
    hProfileFit hHigh hFiberFits

/-! ### 7. Satisfiability guard: the census is a THEOREM above unique decoding -/

open Classical in
/-- **The census is unconditional above unique decoding.**  On any large-zero direction
(`z ≥ a`), if `n + k ≤ 2a`, no nonzero codeword agrees with `u₁` on ≥ `a` points: its
agreements on the zero set are among its own ≤ `k − 1` zeros, and its agreements on the
support are among ≤ `n − a` coordinates.  So the census class is nonempty — indeed full —
in the unique-decoding band, and the uniform consumers below are unconditional there. -/
theorem nonzeroAgreementFarDirection_of_largeZero_of_unique_decoding
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k)
    {u₁ : Fin n → F} (hz : a ≤ (directionZeroSet u₁).card)
    (hud : n + k ≤ 2 * a) :
    NonzeroAgreementFarDirection dom k a u₁ := by
  intro c hcCode hcne
  -- agreements on the zero set are zeros of c
  have hzero : (agreeSet c u₁).filter (fun i => u₁ i = 0) ⊆ agreeSet c (0 : Fin n → F) := by
    intro i hi
    rw [Finset.mem_filter, agreeSet, Finset.mem_filter] at hi
    obtain ⟨⟨-, hagr⟩, hzi⟩ := hi
    rw [agreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hagr, hzi]
    rfl
  have hzeros : ((agreeSet c u₁).filter (fun i => u₁ i = 0)).card ≤ k - 1 :=
    le_trans (Finset.card_le_card hzero)
      (rsCode_pairwise_agreeSet_card_le dom hk1 hcCode (Submodule.zero_mem _) hcne)
  -- agreements on the support are at most s ≤ n − a
  have hsupp : (agreeSet c u₁).filter (fun i => ¬ u₁ i = 0) ⊆ directionSupportSet u₁ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [directionSupportSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2⟩
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.card_filter_add_card_filter_not]
    simp
  have hsuppcard : ((agreeSet c u₁).filter (fun i => ¬ u₁ i = 0)).card ≤ n - a :=
    le_trans (Finset.card_le_card hsupp) (by omega)
  have hsplit : ((agreeSet c u₁).filter (fun i => u₁ i = 0)).card
      + ((agreeSet c u₁).filter (fun i => ¬ u₁ i = 0)).card = (agreeSet c u₁).card :=
    Finset.card_filter_add_card_filter_not (fun i => u₁ i = 0)
  -- a ≤ z ≤ n, so all the nat subtractions are honest
  have han : a ≤ n := le_trans hz (by
    calc (directionZeroSet u₁).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin])
  omega

open Classical in
/-- Unconditional instantiation in the unique-decoding band: the named `hExactLow`
production obligation holds outright (no census hypothesis) once `n + k ≤ 2a`.  In-window
(sub-Johnson, `2a < n + k`) the census remains a genuine named hypothesis — see the refuter
below for why it cannot be granted wholesale there. -/
theorem uniformLargeZeroSafeLowExactFiberBudgeted_of_unique_decoding
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (hud : n + k ≤ 2 * a) :
    UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a
      (fun t => (n - a).choose (a - t)) := by
  refine uniformLargeZeroSafeLowExactFiberBudgeted_of_census dom k a hk1 hka ?_
  intro u₁ hne
  have hz : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hne
    omega
  exact nonzeroAgreementFarDirection_of_largeZero_of_unique_decoding dom k a hk1 hz hud

/-! ### 8. The refuter: the uniform census is FALSE at every prize shape (`2a ≤ n`) -/

open Classical in
/-- **The over-consumption guard.**  At `2a ≤ n` (every prize shape: in-window
`a < √ρ·n ≤ n/2`), the census does NOT hold on the whole large-zero class: the step
direction `u₁ = 1_{[0,a)}` has `n − a ≥ a` zeros, yet the constant codeword `1` agrees with
it on the `a` support coordinates.  So the uniform-census consumers of §6 must keep the
census as a named per-direction hypothesis in-window; only the unique-decoding band (§7)
grants it for free.  (Machine analogue of the weld's own
`not_forall_nonvanishing_lineListBudgeted_of_lt_field` vacuity guard.) -/
theorem not_nonzeroAgreementFar_census_of_two_mul_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha1 : 1 ≤ a) (h2a : 2 * a ≤ n) :
    ¬ ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        NonzeroAgreementFarDirection dom k a u₁ := by
  intro hall
  set u₁ : Fin n → F := fun i => if (i : ℕ) < a then 1 else 0 with hu₁
  -- the low a coordinates, as a Finset of Fin n
  have han : a ≤ n := by omega
  set lowA : Finset (Fin n) :=
    (Finset.range a).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) han)
    with hlowA
  have hlowAcard : lowA.card = a := by
    rw [hlowA, Finset.card_attachFin, Finset.card_range]
  -- the direction is large-zero: its zero set is the complement of lowA
  have hzset : directionZeroSet u₁ = lowAᶜ := by
    ext i
    rw [directionZeroSet, Finset.mem_filter, Finset.mem_compl, hlowA,
      Finset.mem_attachFin, Finset.mem_range]
    by_cases h : (i : ℕ) < a
    · simp [hu₁, h, one_ne_zero]
    · simp [hu₁, h]
  have hne : ¬ SupportEligibleLineDirection a u₁ := by
    rw [SupportEligibleLineDirection, hzset, Finset.card_compl, Fintype.card_fin,
      hlowAcard]
    omega
  -- the constant codeword 1 refutes the census on u₁
  have hcCode : (fun _ : Fin n => (1 : F)) ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    refine ⟨Polynomial.C 1, lt_of_le_of_lt Polynomial.degree_C_le ?_, ?_⟩
    · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    · funext i; simp
  have hcne : (fun _ : Fin n => (1 : F)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
  have hagr : a ≤ (agreeSet (fun _ : Fin n => (1 : F)) u₁).card := by
    have hsub : lowA ⊆ agreeSet (fun _ : Fin n => (1 : F)) u₁ := by
      intro i hi
      rw [hlowA, Finset.mem_attachFin, Finset.mem_range] at hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [hu₁, hi]⟩
    calc a = lowA.card := hlowAcard.symm
      _ ≤ (agreeSet (fun _ : Fin n => (1 : F)) u₁).card := Finset.card_le_card hsub
  exact absurd hagr
    (not_le.mpr (hall u₁ hne (fun _ : Fin n => (1 : F)) hcCode hcne))

end ProximityGap.G91LowProfileFiberBound

/-! ## Axiom audit -/

-- expected: [propext, Classical.choice, Quot.sound] for every theorem
#print axioms ProximityGap.G91LowProfileFiberBound.sVanishingFarDirection_of_nonzeroAgreementFar
#print axioms ProximityGap.G91LowProfileFiberBound.mem_exactProfileIncidences
#print axioms ProximityGap.G91LowProfileFiberBound.mem_supportSubsetIncidenceFiber
#print axioms ProximityGap.G91LowProfileFiberBound.supportSubsetIncidenceFiber_card_le_one
#print axioms ProximityGap.G91LowProfileFiberBound.exactProfileIncidences_subset_biUnion
#print axioms ProximityGap.G91LowProfileFiberBound.exactProfileIncidences_card_le_choose
#print axioms ProximityGap.G91LowProfileFiberBound.exactAppearingZeroAgreementFiber_card_le_exactProfileIncidences_card
#print axioms ProximityGap.G91LowProfileFiberBound.exactAppearingZeroAgreementFiber_card_le_choose_of_sVanishingFar
#print axioms ProximityGap.G91LowProfileFiberBound.exactFiber_card_le_choose_or_exists_nonzero_vanishing_agreeing
#print axioms ProximityGap.G91LowProfileFiberBound.zeroLowExactFiberBudgeted_of_nonzeroAgreementFar
#print axioms ProximityGap.G91LowProfileFiberBound.uniformLargeZeroSafeLowExactFiberBudgeted_of_census
#print axioms ProximityGap.G91LowProfileFiberBound.uniformLineBadScalarsBudgeted_of_census_mixedChooseProfileSumsFit
#print axioms ProximityGap.G91LowProfileFiberBound.nonzeroAgreementFarDirection_of_largeZero_of_unique_decoding
#print axioms ProximityGap.G91LowProfileFiberBound.uniformLargeZeroSafeLowExactFiberBudgeted_of_unique_decoding
#print axioms ProximityGap.G91LowProfileFiberBound.not_nonzeroAgreementFar_census_of_two_mul_le
