/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessCountEngine

/-!
# The antichain refinement (#357): witnesses of distinct bad scalars cannot nest

The witness-counting engine (`MCAWitnessCountEngine.lean`) bounds the bad-scalar count by
the witness-family size. This file proves the structural refinement that makes the bound
**tight at the granularity radius**:

* `bad_scalar_eq_of_witness_subset` — if `γ` is bad with witness `S` and `γ'` merely has a
  *close* point whose witness contains `S`, then `γ = γ'`: closeness restricts downward to
  `S`, where `γ`'s `¬pairJointAgreesOn` clause and `unique_bad_gamma_common_witness` force
  the scalars equal. **The chosen witnesses of distinct bad scalars therefore form an
  antichain** in the witness family.

* `badScalar_card_le_card_at_granularity` — at the granularity radius the witness family
  is `{n erasures} ∪ {univ}` and `univ` contains every erasure, so an antichain either
  avoids `univ` (≤ n members) or is `{univ}` alone: **every linear code has at most `n`
  bad scalars per stack at `δ = 1/n`**, improving the engine's `n + 1`.

* `epsMCA_le_card_div_at_granularity` — `ε_mca(C, 1/n) ≤ n/q` for every linear code; and
  `epsMCA_rs_jump_bracket_tight` — the distance-`≥ 3` RS jump bracket sharpens to

    `2/q ≤ ε_mca(RS[F, D, k], 1/n) ≤ n/q`.

The upper end now **matches the probes' flat-`n` law exactly** (max bad count measured
`= n` at `(4,2)` over F₅, `(5,3)` over F₇, `(12,6)` over F₁₃/F₃₇/F₆₁): the universal cap
is `n`, attained by the `k = n−2` instances. What remains open for the exact jump value
`ε_mca(RS[F,D,n−2], 1/n) = n/q` is only the lower side's per-excluded-point
nondegeneracy (the `n−2` interpolation scalars).

The general-`δ` antichain consequence (largest antichain in `{S : |S| ≥ t}` is `C(n,t)`
for `t ≥ n/2`, via LYM — giving `ε_mca ≤ C(n, ⌈(1−δ)n⌉)/q` for *every linear code* at
`δ ≤ 1/2`) is registered as the next engine extension; this file delivers the granularity
case, where the antichain count is elementary.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (campaign round 2); `MCAWitnessCountEngine.lean`, `MCAWitnessSpread.lean`,
  `MCADeltaStarHighRateFamily.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCAWitnessCountEngine

namespace ProximityGap.MCAAntichainEngine

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- A proper subset misses a point. -/
theorem exists_notMem_of_ne_univ {S : Finset ι} (hS : S ≠ Finset.univ) :
    ∃ j, j ∉ S := by
  by_contra h
  push Not at h
  exact hS (Finset.eq_univ_of_forall h)

/-- **The nesting collapse.** If `γ` is bad with witness `S` (closeness + no joint
explanation on `S`) and `γ'` has a codeword matching its line point on any superset
`S' ⊇ S`, then `γ = γ'`: the `S'`-closeness restricts to `S`, where `γ`'s
`¬pairJointAgreesOn` clause forces the scalars equal. -/
theorem bad_scalar_eq_of_witness_subset (C : Submodule F (ι → A))
    {u₀ u₁ : ι → A} {γ γ' : F} {S S' : Finset ι} (hSS : S ⊆ S')
    (hline : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (hline' : ∃ w ∈ C, ∀ i ∈ S', w i = u₀ i + γ' • u₁ i) :
    γ = γ' := by
  obtain ⟨w', hw', hag'⟩ := hline'
  exact unique_bad_gamma_common_witness C S u₀ u₁ hno hline
    ⟨w', hw', fun i hi => hag' i (hSS hi)⟩

open Classical in
/-- **The granularity antichain count.** At `δ = 1/n` every stack of every linear code has
at most `n` bad scalars: chosen witnesses are distinct (`unique_bad_gamma`), and if any
bad scalar's witness is `univ`, the nesting collapse identifies it with every other bad
scalar — so the witnesses live among the `n` erasures, or the bad set is a singleton. -/
theorem badScalar_card_le_card_at_granularity (C : Submodule F (ι → A))
    (u : WordStack A (Fin 2) ι) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) (1 / (Fintype.card ι : ℝ≥0))
          (u 0) (u 1) γ)).card
      ≤ Fintype.card ι := by
  classical
  set δ : ℝ≥0 := 1 / (Fintype.card ι : ℝ≥0) with hδdef
  set G := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) with hG
  -- two cases: some bad scalar has closeness on `univ`, or none does
  by_cases hu : ∃ γ ∈ G, ∃ w ∈ C, ∀ i, w i = u 0 i + γ • u 1 i
  · -- nesting collapse: G is a singleton
    obtain ⟨γu, hγu, hwu⟩ := hu
    have hsub : G ⊆ {γu} := by
      intro γ hγ
      rw [Finset.mem_singleton]
      rw [hG, Finset.mem_filter] at hγ
      obtain ⟨-, S, hcard, hline, hno⟩ := hγ
      obtain ⟨w', hw', hag'⟩ := hwu
      exact bad_scalar_eq_of_witness_subset C (Finset.subset_univ S) hline hno
        ⟨w', hw', fun i _ => hag' i⟩
    calc G.card ≤ ({γu} : Finset F).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton γu
      _ ≤ Fintype.card ι := Fintype.card_pos
  · -- no univ-closeness: each bad scalar's witness omits a point; inject into ι
    push Not at hu
    -- inject each bad scalar to the point its chosen witness misses
    apply Finset.card_le_card_of_injOn (fun γ =>
      if h : mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ
      then (if hfull : h.choose = Finset.univ then Classical.arbitrary ι
        else (exists_notMem_of_ne_univ hfull).choose)
      else Classical.arbitrary ι)
    · intro γ _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro γ hγ γ' hγ' heq
      rw [Finset.mem_coe, hG, Finset.mem_filter] at hγ hγ'
      obtain ⟨-, hev⟩ := hγ
      obtain ⟨-, hev'⟩ := hγ'
      -- neither chosen witness is univ (else univ-closeness, contradicting `hu`)
      have hnu : hev.choose ≠ Finset.univ := by
        intro hfull
        obtain ⟨-, hline, -⟩ := hev.choose_spec
        rw [hfull] at hline
        obtain ⟨w, hw, hag⟩ := hline
        obtain ⟨i, hi⟩ := hu γ
          (by rw [hG, Finset.mem_filter]; exact ⟨Finset.mem_univ γ, hev⟩) w hw
        exact hi (hag i (Finset.mem_univ i))
      have hnu' : hev'.choose ≠ Finset.univ := by
        intro hfull
        obtain ⟨-, hline', -⟩ := hev'.choose_spec
        rw [hfull] at hline'
        obtain ⟨w, hw, hag⟩ := hline'
        obtain ⟨i, hi⟩ := hu γ'
          (by rw [hG, Finset.mem_filter]; exact ⟨Finset.mem_univ γ', hev'⟩) w hw
        exact hi (hag i (Finset.mem_univ i))
      simp only [dif_pos hev, dif_pos hev', dif_neg hnu, dif_neg hnu'] at heq
      -- the two witnesses each miss the same point `j`, and have size ≥ n−1 ⟹ equal
      set j := (exists_notMem_of_ne_univ hnu).choose with hjdef
      have hj : j ∉ hev.choose := (exists_notMem_of_ne_univ hnu).choose_spec
      have hj' : (exists_notMem_of_ne_univ hnu').choose ∉ hev'.choose :=
        (exists_notMem_of_ne_univ hnu').choose_spec
      rw [← heq] at hj'
      -- both witnesses ⊆ univ.erase j with card ≥ n−1 = |univ.erase j| ⟹ both = erase j
      have hsize : ∀ (S : Finset ι), j ∉ S →
          ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) →
          S = Finset.univ.erase j := by
        intro S hjS hcard
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact Finset.mem_erase.mpr ⟨fun hxj => hjS (hxj ▸ hx), Finset.mem_univ x⟩
        · rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
          have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
            rw [← ProximityGap.MCADeltaStarHighRateFamily.card_clause_arith
              Fintype.card_pos]
            exact hcard
          exact_mod_cast hcast
      have hS : hev.choose = Finset.univ.erase j :=
        hsize hev.choose hj hev.choose_spec.1
      have hS' : hev'.choose = Finset.univ.erase j :=
        hsize hev'.choose hj' hev'.choose_spec.1
      -- same witness set ⟹ same scalar
      obtain ⟨-, hline, hno⟩ := hev.choose_spec
      obtain ⟨-, hline', -⟩ := hev'.choose_spec
      rw [hS] at hline hno
      rw [hS'] at hline'
      exact unique_bad_gamma_common_witness C (Finset.univ.erase j) (u 0) (u 1)
        hno hline hline'

open Classical in
/-- **The tight granularity cap:** `ε_mca(C, 1/n) ≤ n/q` for every linear code. -/
theorem epsMCA_le_card_div_at_granularity (C : Submodule F (ι → A)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) (1 / (Fintype.card ι : ℝ≥0))
      ≤ ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_card_at_granularity C u

open Classical in
/-- **The tight jump bracket for distance-`≥ 3` RS codes:**

  `2/q ≤ ε_mca(RS[F, D, k], 1/n) ≤ n/q`.

The upper end matches the probes' flat-`n` law; only the lower side's per-excluded-point
nondegeneracy separates the bracket from the exact value `n/q` at `k = n−2`. -/
theorem epsMCA_rs_jump_bracket_tight (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2) {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
      ∧ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
          ≤ ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ⟨ProximityGap.MCADeltaStarHighRateFamily.epsMCA_highRate_ge domain hk hb,
    epsMCA_le_card_div_at_granularity (ReedSolomon.code domain k)⟩

/-! ## Source audit -/

#print axioms bad_scalar_eq_of_witness_subset
#print axioms badScalar_card_le_card_at_granularity
#print axioms epsMCA_le_card_div_at_granularity
#print axioms epsMCA_rs_jump_bracket_tight

end ProximityGap.MCAAntichainEngine
