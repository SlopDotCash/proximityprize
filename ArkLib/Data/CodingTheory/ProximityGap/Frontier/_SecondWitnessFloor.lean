/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListIncidenceMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The second-witness / multiplicity floor dies on extremal far lines (#466, lane L2)

Dossier v3 §6 Tier-1 item 2, third bullet asked: prove `NoUniqueBadScalarWitness` on hard
lines (every bad scalar has ≥ 2 witnessing codewords, buying the factor-two discount
`#bad ≤ puncturedWeight/2`), or exhibit a unique-witness bad scalar.

**Verdict: the floor is structurally impossible exactly on the lines that matter.**  The probe
(`scripts/probes/probe_466_second_witness.py`, outputs `_out_466_second_witness*.txt`) found
that on every extremal far line at the first window-interior level (`n = 8, k = 2, a = 3`,
`q ∈ {4129, 8273}`, worst count `56 = C(8,3)` — the direction-blind ceiling SATURATED) **every
single bad scalar has exactly one witness** (multiplicity histogram `{1w:56}`), and lines one
below saturation (`#bad = 55`) carry exactly one doubleton (`{1w:54, 2w:1}` — incidence count
`56` again).  This file proves the law that forces this — the numbers above are its exact
extremal cases, not a coincidence:

* **The incidence cap** (`lineHeavyIncidences_card_le_choose`): on any line whose direction is
  `a`-far from the code (`AgreementFarDirection`: no codeword agrees with `u₁` on `a` points —
  the probe's `agreemax < a` guard), the TOTAL witness count `Σ_γ #fiber(γ)` is at most
  `C(n, a)`.  Charging: each incidence `(γ, c)` owns the `a`-subsets of its agreement set;
  across distinct `γ` a shared `a`-subset would transport `u₁` itself into the code
  (`(γ−γ')⁻¹·(c−c')` agrees with `u₁` there), and within one `γ` two distinct codewords
  sharing an `a ≥ k`-subset of the SAME line word are equal.  This strengthens the
  scalar-count ceiling (`FirstInteriorLevelDirectionBlind.levelBadScalars_card_le_choose`,
  stated for `a = k+1` in the KKH26 vocabulary) to the full incidence multiset, at every
  level `a ≥ k`, in the production (`Ownership`) vocabulary.

* **The defect-forcing law** (`two_mul_lineBadScalars_card_le_choose_add_singletonDefect`):
  `2·#bad ≤ C(n,a) + defect` — the singleton defect grows at least linearly once `#bad`
  exceeds `C(n,a)/2`.  Hence:

* **The trade-off** (`lineBadScalars_card_mul_two_le_choose_of_noUniqueBadScalarWitness`):
  `NoUniqueBadScalarWitness ⟹ #bad ≤ C(n,a)/2` — the multiplicity floor and near-extremality
  are MUTUALLY EXCLUSIVE.  A line within a factor 2 of the direction-blind ceiling cannot
  satisfy the floor; the worst lines (which determine the far-line budget the weld consumes)
  provably violate it.

* **Saturation forces all-singleton** (`singletonBadScalars_eq_lineBadScalars_of_choose_le`,
  `not_noUniqueBadScalarWitness_of_saturated`): `#bad = C(n,a)` makes EVERY bad scalar a
  singleton (`defect = #bad`) — the measured `{1w:56}` histograms, as a theorem.  At
  saturation the in-tree discount chain `2·#bad ≤ weight + defect` degenerates to the
  undiscounted `#bad ≤ weight`: the multiplicity route buys exactly nothing there.

* **The unguarded Prop was never viable** (`not_noUniqueBadScalarWitness_of_line_through_code`):
  any line passing through the code at a scalar `γ` (`u₀ + γ·u₁ ∈ RS_k`, `k ≤ a ≤ n`) has the
  exact singleton fiber `{u₀ + γ·u₁}` there — so `NoUniqueBadScalarWitness` as a universal
  statement fails for EVERY code, field, and window level, with zero computation.  (This is
  the probe's encoded theory check.)

**Honest scope.**  What survives of the second-witness idea is only the contrapositive
budget: any line class on which the floor CAN be proven automatically satisfies
`#bad ≤ C(n,a)/2` — but at prize depth `C(n,a)` is astronomically above the needed budget,
and on the extremal lines the floor is false.  The pairwise-interpolation intuition ("two
singleton scalars force a second witness") is refuted in the strongest sense: the extremal
object is a PERFECT MATCHING between bad scalars and `a`-subsets, with no multiplicity
anywhere.  Deeper levels (`a ≥ k+2`, where `C(n,a)` is slack) still show singleton domination
empirically (`n = 8, a = 4`: worst line `{1w:8, 2w:1}`), so the failure is not an artifact of
the `a = k+1` cap; the route is dead as a production discount.

Numerics: `scripts/probes/probe_466_second_witness.py` (3-way verified counts; independent
full-`q²` codeword-enumeration fiber checks at `k = 2`).  Axiom-clean; no `sorry`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The `a`-far direction guard -/

/-- A direction is `a`-far from the code when no codeword agrees with it on `a` or more
coordinates (the probe's `agreemax < a` eligibility guard; same shape as the in-flight
`_SpreadExcessLaw.FarDirection`, restated so this file depends only on landed substrate).
Note this is about the DIRECTION `u₁`, not the offset: it is the exact hypothesis making the
per-`a`-subset scalar unique. -/
def AgreementFarDirection (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) : Prop :=
  ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)), (agreeSet c u₁).card < a

/-! ## The per-`a`-subset incidence fiber and its rigidity -/

open Classical in
/-- Incidences whose agreement set contains the fixed coordinate subset `T`. -/
noncomputable def subsetIncidenceFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (T : Finset (Fin n)) :
    Finset (F × (Fin n → F)) :=
  (lineHeavyIncidences dom k a u₀ u₁).filter
    (fun e => T ⊆ agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i))

open Classical in
theorem mem_subsetIncidenceFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (T : Finset (Fin n))
    (e : F × (Fin n → F)) :
    e ∈ subsetIncidenceFiber dom k a u₀ u₁ T ↔
      e ∈ lineHeavyIncidences dom k a u₀ u₁ ∧
        T ⊆ agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i) := by
  rw [subsetIncidenceFiber, Finset.mem_filter]

open Classical in
/-- **Per-subset incidence rigidity.**  On an `a`-far-direction line, a coordinate subset of
size at least `k` (in particular any `a`-subset once `k ≤ a`) is contained in the agreement
set of AT MOST ONE incidence: sharing it across scalars would put `(γ−γ')⁻¹·(c−c')` — which
agrees with `u₁` on `T` — into the code against the guard, and sharing it within a scalar
forces the two witnessing codewords (both agreeing with the same line word on `≥ k` points)
to coincide. -/
theorem subsetIncidenceFiber_card_le_one
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    {T : Finset (Fin n)} (hTk : k ≤ T.card) (hTa : T.card = a) :
    (subsetIncidenceFiber dom k a u₀ u₁ T).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨γ, c⟩ he ⟨γ', c'⟩ he'
  rw [mem_subsetIncidenceFiber] at he he'
  obtain ⟨heI, heT⟩ := he
  obtain ⟨heI', heT'⟩ := he'
  rw [mem_lineHeavyIncidences] at heI heI'
  obtain ⟨hcCode, -⟩ := heI
  obtain ⟨hc'Code, -⟩ := heI'
  -- pointwise line equations on T
  have hcT : ∀ i ∈ T, c i = u₀ i + γ • u₁ i := by
    intro i hi
    have := heT hi
    rw [agreeSet, Finset.mem_filter] at this
    exact this.2
  have hc'T : ∀ i ∈ T, c' i = u₀ i + γ' • u₁ i := by
    intro i hi
    have := heT' hi
    rw [agreeSet, Finset.mem_filter] at this
    exact this.2
  -- first: the scalars agree
  have hγ : γ = γ' := by
    by_contra hγne
    have hδ : γ - γ' ≠ 0 := sub_ne_zero.mpr hγne
    set d : Fin n → F := (γ - γ')⁻¹ • (c - c') with hd
    have hdCode : d ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hcCode hc'Code)
    have hdT : T ⊆ agreeSet d u₁ := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 := hcT i hi
      have h2 := hc'T i hi
      rw [hd]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [h1, h2]
      field_simp
      ring
    have hlt := hfar d hdCode
    have hge : a ≤ (agreeSet d u₁).card := by
      calc a = T.card := hTa.symm
        _ ≤ (agreeSet d u₁).card := Finset.card_le_card hdT
    omega
  subst hγ
  -- then: the codewords agree (both interpolate the same line word on ≥ k points)
  have hc : c = c' := by
    by_contra hne
    have hsub : T ⊆ agreeSet c c' := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hcT i hi).trans (hc'T i hi).symm⟩
    have hlarge : k ≤ (agreeSet c c').card :=
      le_trans hTk (Finset.card_le_card hsub)
    have hsmall : (agreeSet c c').card ≤ k - 1 :=
      rsCode_pairwise_agreeSet_card_le dom hk1 hcCode hc'Code hne
    omega
  subst hc
  rfl

/-! ## The incidence cap `Σ_γ #witnesses(γ) ≤ C(n, a)` -/

open Classical in
/-- **The incidence cap.**  On an `a`-far-direction line with `1 ≤ k ≤ a`, the full witness
incidence count — the SUM of the per-bad-scalar witness multiplicities — is at most `C(n, a)`.
This is the incidence strengthening of the direction-blind scalar ceiling: every incidence
owns a private `a`-subset of coordinates. -/
theorem lineHeavyIncidences_card_le_choose
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁) :
    (lineHeavyIncidences dom k a u₀ u₁).card ≤ n.choose a := by
  have hcover : lineHeavyIncidences dom k a u₀ u₁ ⊆
      (Finset.powersetCard a (Finset.univ : Finset (Fin n))).biUnion
        (fun T => subsetIncidenceFiber dom k a u₀ u₁ T) := by
    intro e he
    have hheavy : a ≤ (agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i)).card :=
      ((mem_lineHeavyIncidences dom k a u₀ u₁ e).mp he).2
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hheavy
    refine Finset.mem_biUnion.mpr ⟨T, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
    · rw [mem_subsetIncidenceFiber]
      exact ⟨he, hTsub⟩
  calc (lineHeavyIncidences dom k a u₀ u₁).card
      ≤ ((Finset.powersetCard a (Finset.univ : Finset (Fin n))).biUnion
          (fun T => subsetIncidenceFiber dom k a u₀ u₁ T)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ T ∈ Finset.powersetCard a (Finset.univ : Finset (Fin n)),
          (subsetIncidenceFiber dom k a u₀ u₁ T).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ Finset.powersetCard a (Finset.univ : Finset (Fin n)), 1 := by
        refine Finset.sum_le_sum (fun T hT => ?_)
        have hTcard : T.card = a := (Finset.mem_powersetCard.mp hT).2
        exact subsetIncidenceFiber_card_le_one dom k a hk1 u₀ u₁ hfar
          (hTcard ▸ hka) hTcard
    _ = n.choose a := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]

open Classical in
/-- The direction-blind scalar ceiling in the production vocabulary: at every level `a ≥ k`,
an `a`-far-direction line has at most `C(n, a)` bad scalars (any embedding domain).  Companion
to `FirstInteriorLevelDirectionBlind.levelBadScalars_card_le_choose` (`a = k+1`, smooth
domain). -/
theorem lineBadScalars_card_le_choose
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁) :
    (lineBadScalars dom k a u₀ u₁).card ≤ n.choose a :=
  le_trans (lineBadScalars_card_le_lineHeavyIncidences_card dom k a u₀ u₁)
    (lineHeavyIncidences_card_le_choose dom k a hk1 hka u₀ u₁ hfar)

/-! ## The multiplicity trade-off: floors and extremality are mutually exclusive -/

open Classical in
/-- An `R`-fold multiplicity floor caps the bad-scalar count at `C(n, a)/R`: multiplicity is
paid for out of the same `C(n, a)` incidence budget that the bad scalars themselves consume. -/
theorem lineBadScalars_card_mul_le_choose_of_multiplicityFloor
    (dom : Fin n ↪ F) (k a R : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    (hmult : LineBadScalarMultiplicityFloor dom k a u₀ u₁ R) :
    (lineBadScalars dom k a u₀ u₁).card * R ≤ n.choose a :=
  le_trans
    (lineBadScalars_card_mul_le_lineHeavyIncidences_card_of_multiplicityFloor
      dom k a R u₀ u₁ hmult)
    (lineHeavyIncidences_card_le_choose dom k a hk1 hka u₀ u₁ hfar)

open Classical in
/-- **The mutual-exclusivity law.**  `NoUniqueBadScalarWitness` (the `R = 2` floor) forces
`2·#bad ≤ C(n, a)`: the multiplicity floor CANNOT hold on any line within a factor two of the
direction-blind ceiling — in particular not on the extremal far lines whose worst-case count
the weld's budget must dominate.  The probe measures those lines AT the ceiling. -/
theorem lineBadScalars_card_mul_two_le_choose_of_noUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    (hno : NoUniqueBadScalarWitness dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card * 2 ≤ n.choose a :=
  lineBadScalars_card_mul_le_choose_of_multiplicityFloor dom k a 2 hk1 hka u₀ u₁ hfar
    ((lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness dom k a u₀ u₁).mpr hno)

/-! ## The defect-forcing law and saturation -/

open Classical in
/-- **The defect-forcing law**: `2·#bad ≤ C(n, a) + defect`.  Once a line's bad-scalar count
exceeds half the ceiling, unique-witness scalars are forced in at least the excess
`2·#bad − C(n, a)`.  (Composes the in-tree defect identity with the incidence cap.) -/
theorem two_mul_lineBadScalars_card_le_choose_add_singletonDefect
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁) :
    (lineBadScalars dom k a u₀ u₁).card * 2
      ≤ n.choose a + singletonBadScalarDefect dom k a u₀ u₁ :=
  le_trans
    (lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
      dom k a u₀ u₁)
    (Nat.add_le_add_right
      (lineHeavyIncidences_card_le_choose dom k a hk1 hka u₀ u₁ hfar) _)

open Classical in
/-- At (or above) ceiling saturation the defect swallows everything:
`#bad ≤ defect` (with `defect ≤ #bad` always, this pins `defect = #bad`). -/
theorem lineBadScalars_card_le_singletonDefect_of_choose_le
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    (hsat : n.choose a ≤ (lineBadScalars dom k a u₀ u₁).card) :
    (lineBadScalars dom k a u₀ u₁).card ≤ singletonBadScalarDefect dom k a u₀ u₁ := by
  have h := two_mul_lineBadScalars_card_le_choose_add_singletonDefect
    dom k a hk1 hka u₀ u₁ hfar
  omega

open Classical in
/-- **Saturation forces all-singleton**: a line attaining the direction-blind ceiling has
EVERY bad scalar unique-witness.  This is the probe's measured `{1w:56}` histogram
(`#bad = 56 = C(8,3)` at `n = 8, k = 2, a = 3`, both primes, all four hard directions), as a
theorem. -/
theorem singletonBadScalars_eq_lineBadScalars_of_choose_le
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    (hsat : n.choose a ≤ (lineBadScalars dom k a u₀ u₁).card) :
    singletonBadScalars dom k a u₀ u₁ = lineBadScalars dom k a u₀ u₁ := by
  refine Finset.eq_of_subset_of_card_le
    (singletonBadScalars_subset_lineBadScalars dom k a u₀ u₁) ?_
  have h := lineBadScalars_card_le_singletonDefect_of_choose_le
    dom k a hk1 hka u₀ u₁ hfar hsat
  rw [singletonBadScalarDefect] at h
  exact h

open Classical in
/-- A nonempty saturated line refutes the no-unique-witness condition outright. -/
theorem not_noUniqueBadScalarWitness_of_saturated
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a) (u₀ u₁ : Fin n → F)
    (hfar : AgreementFarDirection dom k a u₁)
    (hne : (lineBadScalars dom k a u₀ u₁).Nonempty)
    (hsat : n.choose a ≤ (lineBadScalars dom k a u₀ u₁).card) :
    ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  intro hno
  have hzero :=
    (singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness dom k a u₀ u₁).mpr hno
  have hle := lineBadScalars_card_le_singletonDefect_of_choose_le
    dom k a hk1 hka u₀ u₁ hfar hsat
  have hpos : 0 < (lineBadScalars dom k a u₀ u₁).card := Finset.card_pos.mpr hne
  omega

/-! ## The unguarded universal Prop was never viable: lines through the code -/

open Classical in
/-- A line passing through the code at `γ` (`u₀ + γ·u₁ ∈ RS_k`) has the EXACT singleton
witness fiber `{u₀ + γ·u₁}` there, at every level `k ≤ a ≤ n`: the line word witnesses
itself (agreement `n`), and any other codeword witness would agree with it on `a ≥ k`
points.  (The probe's encoded theory check.) -/
theorem badScalarWitnessCodewords_eq_singleton_of_line_through_code
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (han : a ≤ n) (u₀ u₁ : Fin n → F) (γ : F)
    (hline : (fun i => u₀ i + γ • u₁ i) ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    badScalarWitnessCodewords dom k a u₀ u₁ γ = {fun i => u₀ i + γ • u₁ i} := by
  ext c
  rw [mem_badScalarWitnessCodewords, Finset.mem_singleton]
  constructor
  · rintro ⟨hcCode, hheavy⟩
    by_contra hne
    have hsmall : (agreeSet c (fun i => u₀ i + γ • u₁ i)).card ≤ k - 1 :=
      rsCode_pairwise_agreeSet_card_le dom hk1 hcCode hline hne
    omega
  · rintro rfl
    refine ⟨hline, ?_⟩
    have hself : agreeSet (fun i => u₀ i + γ • u₁ i) (fun i => u₀ i + γ • u₁ i) =
        (Finset.univ : Finset (Fin n)) := by
      ext i
      simp [agreeSet]
    rw [hself, Finset.card_univ, Fintype.card_fin]
    exact han

open Classical in
/-- The through-the-code scalar is bad (its own line word is a full-agreement witness). -/
theorem mem_lineBadScalars_of_line_through_code
    (dom : Fin n ↪ F) (k a : ℕ) (han : a ≤ n) (u₀ u₁ : Fin n → F) (γ : F)
    (hline : (fun i => u₀ i + γ • u₁ i) ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    γ ∈ lineBadScalars dom k a u₀ u₁ := by
  rw [lineBadScalars, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, (fun i => u₀ i + γ • u₁ i), hline, ?_⟩
  have hself : agreeSet (fun i => u₀ i + γ • u₁ i) (fun i => u₀ i + γ • u₁ i) =
      (Finset.univ : Finset (Fin n)) := by
    ext i
    simp [agreeSet]
  rw [hself, Finset.card_univ, Fintype.card_fin]
  exact han

open Classical in
/-- **The universal `NoUniqueBadScalarWitness` is false for every code and every window
level**: any line through the code (e.g. any offset `u₀ ∈ RS_k` at `γ = 0`, for ANY
direction) carries a unique-witness bad scalar.  Any usable multiplicity-floor Prop must at
minimum guard away lines meeting the code — and the probe shows the floor fails on genuinely
far lines too. -/
theorem not_noUniqueBadScalarWitness_of_line_through_code
    (dom : Fin n ↪ F) (k a : ℕ) (hk1 : 1 ≤ k) (hka : k ≤ a)
    (han : a ≤ n) (u₀ u₁ : Fin n → F) (γ : F)
    (hline : (fun i => u₀ i + γ • u₁ i) ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  intro hno
  refine hno γ (mem_lineBadScalars_of_line_through_code dom k a han u₀ u₁ γ hline) ?_
  rw [badScalarWitnessCodewords_eq_singleton_of_line_through_code
    dom k a hk1 hka han u₀ u₁ γ hline]
  exact Finset.card_singleton _

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.subsetIncidenceFiber_card_le_one
#print axioms ProximityGap.Ownership.lineHeavyIncidences_card_le_choose
#print axioms ProximityGap.Ownership.lineBadScalars_card_le_choose
#print axioms ProximityGap.Ownership.lineBadScalars_card_mul_le_choose_of_multiplicityFloor
#print axioms ProximityGap.Ownership.lineBadScalars_card_mul_two_le_choose_of_noUniqueBadScalarWitness
#print axioms ProximityGap.Ownership.two_mul_lineBadScalars_card_le_choose_add_singletonDefect
#print axioms ProximityGap.Ownership.lineBadScalars_card_le_singletonDefect_of_choose_le
#print axioms ProximityGap.Ownership.singletonBadScalars_eq_lineBadScalars_of_choose_le
#print axioms ProximityGap.Ownership.not_noUniqueBadScalarWitness_of_saturated
#print axioms ProximityGap.Ownership.badScalarWitnessCodewords_eq_singleton_of_line_through_code
#print axioms ProximityGap.Ownership.not_noUniqueBadScalarWitness_of_line_through_code
