/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Commitments.Functional.KZG.HardnessAssumptions
public import ArkLib.Commitments.Functional.KZG.FunctionBinding.TauInQueries

/-!
# Adversary model of the KZG hardness assumptions

The canonical `Groups.tSdhAssumption` and `Groups.arsdhAssumption` take an explicit adversary
class. This file exhibits concrete-group adversaries showing why `Set.univ` cannot model hardness
below error one under the stated group and field hypotheses.

Given public `g₂ ^ τ` with `g₂ ≠ 1`, `exhaustiveDlog` recovers `τ`. The t-SDH adversary uses
offset zero and the sampler's nonzero trapdoor. The ARSDH adversary chooses a size-`D + 1` set
avoiding `τ` when `p ≥ D + 2` and `g₁ ≠ 1`. A separate t-SDH witness uses `(0, 1)` when
`g₁ = 1`.

An adversary class witnessing t-SDH hardness below error one must exclude this exhaustive
adversary. The computational interpretation still requires a resource-bounded class and the
relevant reduction-membership conditions.
-/

@[expose] public section

open OracleSpec OracleComp
open scoped NNReal ENNReal

namespace Groups

section PrimeOrder

variable {p : outParam ℕ} [Fact (Nat.Prime p)]

/-- Every output of `sampleNonzeroZMod` is nonzero. -/
lemma ne_zero_of_mem_support_sampleNonzeroZMod {τ : ZMod p}
    (hτ : τ ∈ support (sampleNonzeroZMod (p := p))) : τ ≠ 0 := by
  unfold sampleNonzeroZMod at hτ
  rw [support_map] at hτ
  obtain ⟨i, -, rfl⟩ := hτ
  have hi : (i : ℕ) + 1 < p := by have := i.isLt; omega
  intro h
  have h' : (((i : ℕ) + 1 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) h') (not_le.mpr hi)

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p]
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p]

/-- A t-SDH adversary that ignores its query cache and deterministically outputs `out srs`. -/
def tSdhConstAdversary (D : ℕ) (out : Vector G₁ (D + 1) × Vector G₂ 2 → ZMod p × G₁) :
    tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs => pure (some (out srs))

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] in
/-- A constant-output t-SDH adversary that wins for every nonzero trapdoor wins with
probability one. -/
lemma tSdhExperiment_constAdversary_eq_one
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (out : Vector G₁ (D + 1) × Vector G₂ 2 → ZMod p × G₁)
    (hwin : ∀ τ : ZMod p, τ ≠ 0 →
      tSdhCondition (g₁ := g₁)
        (τ, (out (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).1,
          (out (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).2)) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (tSdhConstAdversary D out) = 1 := by
  unfold tSdhExperiment tSdhGame
  refine OptionT.prEvent_mk_bind_eq_one_of_support _ (prEvent_true_eq_one _) _ _ ?_
  intro τ hτ
  have hτ0 := ne_zero_of_mem_support_sampleNonzeroZMod hτ
  simp only [tSdhConstAdversary, StateT.run'_pure', pure_bind, Option.map_some]
  classical
  rw [OptionT.prEvent_mk, prEvent_pure]
  split_ifs with hc
  · rfl
  · exact absurd (by simpa using hwin τ hτ0) hc

/-- Exhaustive discrete logarithm base `g`: some exponent `t` with `g ^ t.val = x` if one
exists, otherwise `0`. This is an (unbounded) function, not an efficient algorithm. -/
noncomputable def exhaustiveDlog {G : Type} [Group G] (g x : G) : ZMod p :=
  open Classical in
  if h : ∃ t : ZMod p, g ^ t.val = x then Classical.choose h else 0

/-- Exhaustive discrete logarithm is correct for a nontrivial base of prime order. -/
lemma exhaustiveDlog_pow {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1)
    (τ : ZMod p) : exhaustiveDlog (p := p) g (g ^ τ.val) = τ := by
  have hord : orderOf g = p := orderOf_eq_prime_of_ne_one g hg
  have hex : ∃ t : ZMod p, g ^ t.val = g ^ τ.val := ⟨τ, rfl⟩
  have hspec := Classical.choose_spec hex
  unfold exhaustiveDlog
  simp only [hex, ↓reduceDIte]
  have hdiv : g ^ (Classical.choose hex - τ).val = 1 := by
    rw [← gpow_div_eq hord, hspec, div_self']
  exact sub_eq_zero.1 (zmod_eq_zero_of_gpow_eq_one hord hdiv)

/-- The exhaustive-search t-SDH adversary: recover `τ` from the public `g₂ ^ τ` by exhaustive
discrete logarithm and answer with `c = 0`, `h = g₁ ^ (1 / τ)`. It lies in the unrestricted
adversary class quantified by `tSdhAssumption`. -/
noncomputable def tSdhExhaustiveAdversary (g₁ : G₁) (g₂ : G₂) (D : ℕ) :
    tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  tSdhConstAdversary D fun srs =>
    (0, g₁ ^ (1 / exhaustiveDlog (p := p) g₂ srs.2[1]).val)

omit [PrimeOrderWith G₁ p] in
/-- For a nontrivial `g₂`, the exhaustive-search adversary wins the t-SDH game with
probability one. -/
theorem tSdhExperiment_exhaustiveAdversary_eq_one
    {g₁ : G₁} {g₂ : G₂} (hg₂ : g₂ ≠ 1) (D : ℕ) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (tSdhExhaustiveAdversary (p := p) g₁ g₂ D) = 1 := by
  refine tSdhExperiment_constAdversary_eq_one D _ fun τ hτ => ?_
  have hsrs : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).2[1] = g₂ ^ τ.val := by
    simp [PowerSrs.generate, PowerSrs.tower]
  simp only [hsrs, exhaustiveDlog_pow hg₂]
  exact ⟨by simpa using hτ, by simp⟩

omit [PrimeOrderWith G₂ p] in
/-- For a degenerate `g₁ = 1`, the t-SDH winning condition is met by the constant answer
`(c, h) = (0, 1)` with probability one, whatever `g₂` is. -/
theorem tSdhExperiment_trivialGenerator_eq_one
    {g₂ : G₂} (D : ℕ) :
    tSdhExperiment (g₁ := (1 : G₁)) (g₂ := g₂) D
      (tSdhConstAdversary (p := p) D fun _ => (0, 1)) = 1 :=
  tSdhExperiment_constAdversary_eq_one D _ fun τ hτ => ⟨by simpa using hτ, by simp⟩

omit [PrimeOrderWith G₁ p] in
/-- **The unrestricted t-SDH assumption is unsatisfiable below error one.** Since
`tSdhAssumption` at `Set.univ` quantifies over every function-valued adversary, including exhaustive
discrete-logarithm search, it fails for every `error < 1` as soon as `g₂ ≠ 1` (or `g₁ = 1`, by
`tSdhExperiment_trivialGenerator_eq_one`). Hypotheses of the form `tSdhAssumption D Set.univ ε` with
`ε < 1` are therefore contradictory, and theorems conditioned on them carry no computational
content; see the module docstring. -/
theorem not_tSdhAssumption_of_lt_one
    {g₁ : G₁} {g₂ : G₂} (hg₂ : g₂ ≠ 1) (D : ℕ) {error : ℝ≥0} (herror : error < 1) :
    ¬ tSdhAssumption (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error := by
  intro h
  have h1 := h (tSdhExhaustiveAdversary (p := p) g₁ g₂ D) (Set.mem_univ _)
  rw [tSdhExperiment_exhaustiveAdversary_eq_one hg₂] at h1
  have h2 : (error : ℝ≥0∞) < 1 := by exact_mod_cast herror
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- An ARSDH adversary that ignores its query cache and deterministically outputs `out srs`. -/
def arsdhConstAdversary (D : ℕ)
    (out : Vector G₁ (D + 1) × Vector G₂ 2 → Finset (ZMod p) × G₁ × G₁) :
    arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs => pure (some (out srs))

omit [PrimeOrderWith G₂ p] in
/-- A constant-output ARSDH adversary that wins for every nonzero trapdoor wins with
probability one. -/
lemma arsdhExperiment_constAdversary_eq_one
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (out : Vector G₁ (D + 1) × Vector G₂ 2 → Finset (ZMod p) × G₁ × G₁)
    (hwin : ∀ τ : ZMod p, τ ≠ 0 →
      arsdhCondition (G₁ := G₁) D
        (τ, (out (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).1,
          (out (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).2.1,
          (out (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).2.2)) :
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D (arsdhConstAdversary D out) = 1 := by
  unfold arsdhExperiment arsdhGame
  refine OptionT.prEvent_mk_bind_eq_one_of_support _ (prEvent_true_eq_one _) _ _ ?_
  intro τ hτ
  have hτ0 := ne_zero_of_mem_support_sampleNonzeroZMod hτ
  simp only [arsdhConstAdversary, StateT.run'_pure', pure_bind, Option.map_some]
  classical
  rw [OptionT.prEvent_mk, prEvent_pure]
  split_ifs with hc
  · rfl
  · exact absurd (by simpa using hwin τ hτ0) hc

/-- The exhaustive-search ARSDH adversary: recover `τ` from the public `g₂ ^ τ` by exhaustive
discrete logarithm, pick a size-`D + 1` set `S` avoiding `τ`, and answer with
`(S, g₁, g₁ ^ (1 / Z_S(τ)))`. -/
noncomputable def arsdhExhaustiveAdversary (g₁ : G₁) (g₂ : G₂) (D : ℕ) :
    arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  arsdhConstAdversary D fun srs =>
    let τ' := exhaustiveDlog (p := p) g₂ srs.2[1]
    let S := KZG.CommitmentScheme.chooseSMiddle D τ'
    (S, g₁, g₁ ^ (1 / (∏ s ∈ S,
      (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s :
        CompPoly.CPolynomial (ZMod p))).eval τ').val)

/-- For nontrivial `g₁, g₂` and `p ≥ D + 2`, the exhaustive-search adversary wins the ARSDH game
with probability one. -/
theorem arsdhExperiment_exhaustiveAdversary_eq_one
    {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1) {D : ℕ} (hp : p ≥ D + 2) :
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D (arsdhExhaustiveAdversary (p := p) g₁ g₂ D) = 1 := by
  refine arsdhExperiment_constAdversary_eq_one D _ fun τ _ => ?_
  have hsrs : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).2[1] = g₂ ^ τ.val := by
    simp [PowerSrs.generate, PowerSrs.tower]
  simp only [hsrs, exhaustiveDlog_pow hg₂]
  exact ⟨KZG.CommitmentScheme.choose_s_middle_card (p := p) hp τ,
    KZG.CommitmentScheme.choose_s_middle_eval_ne_zero τ, hg₁, rfl⟩

/-- **The unrestricted ARSDH assumption is unsatisfiable below error one** whenever
`g₁ ≠ 1`, `g₂ ≠ 1`, and `p ≥ D + 2`, for the same reason as `not_tSdhAssumption_of_lt_one`. -/
theorem not_arsdhAssumption_of_lt_one
    {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1) {D : ℕ} (hp : p ≥ D + 2)
    {error : ℝ≥0} (herror : error < 1) :
    ¬ arsdhAssumption (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error := by
  intro h
  have h1 := h (arsdhExhaustiveAdversary (p := p) g₁ g₂ D) (Set.mem_univ _)
  rw [arsdhExperiment_exhaustiveAdversary_eq_one hg₁ hg₂ hp] at h1
  have h2 : (error : ℝ≥0∞) < 1 := by exact_mod_cast herror
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-! ### Adversary-class-indexed assumptions

A meaningful computational assumption must restrict the adversary class (for example to a
resource-bounded family closed under the reductions in use). The former downstream names below alias the canonical class-indexed assumptions. -/

/-- t-SDH hardness against the adversary class `Adv`. -/
abbrev tSdhAssumptionFor
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (Adv : Set (tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)))
    (error : ℝ≥0) : Prop :=
  tSdhAssumption (g₁ := g₁) (g₂ := g₂) D Adv error

/-- ARSDH hardness against the adversary class `Adv`. -/
abbrev arsdhAssumptionFor
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (Adv : Set (arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)))
    (error : ℝ≥0) : Prop :=
  arsdhAssumption (g₁ := g₁) (g₂ := g₂) D Adv error

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] in
/-- The unrestricted t-SDH assumption is the class-indexed one at the full class. -/
theorem tSdhAssumption_iff_univ
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) :
    tSdhAssumption (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error ↔
      tSdhAssumptionFor (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error :=
  Iff.rfl

omit [PrimeOrderWith G₂ p] in
/-- The unrestricted ARSDH assumption is the class-indexed one at the full class. -/
theorem arsdhAssumption_iff_univ
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) :
    arsdhAssumption (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error ↔
      arsdhAssumptionFor (g₁ := g₁) (g₂ := g₂) (p := p) D Set.univ error :=
  Iff.rfl

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] in
/-- Class-indexed t-SDH hardness is antitone in the adversary class. -/
theorem tSdhAssumptionFor.mono
    {g₁ : G₁} {g₂ : G₂} {D : ℕ} {Adv Adv' : Set (tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))}
    {error : ℝ≥0} (h : tSdhAssumptionFor (g₁ := g₁) (g₂ := g₂) D Adv error) (hsub : Adv' ⊆ Adv) :
    tSdhAssumptionFor (g₁ := g₁) (g₂ := g₂) D Adv' error :=
  fun A hA => h A (hsub hA)

omit [PrimeOrderWith G₂ p] in
/-- Class-indexed ARSDH hardness is antitone in the adversary class. -/
theorem arsdhAssumptionFor.mono
    {g₁ : G₁} {g₂ : G₂} {D : ℕ}
    {Adv Adv' : Set (arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))}
    {error : ℝ≥0} (h : arsdhAssumptionFor (g₁ := g₁) (g₂ := g₂) D Adv error)
    (hsub : Adv' ⊆ Adv) :
    arsdhAssumptionFor (g₁ := g₁) (g₂ := g₂) D Adv' error :=
  fun A hA => h A (hsub hA)

omit [PrimeOrderWith G₁ p] in
/-- Any class-indexed t-SDH assumption below error one must exclude the exhaustive-search
adversary. -/
theorem tSdhExhaustiveAdversary_not_mem_of_assumptionFor
    {g₁ : G₁} {g₂ : G₂} (hg₂ : g₂ ≠ 1) {D : ℕ}
    {Adv : Set (tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))} {error : ℝ≥0}
    (herror : error < 1) (h : tSdhAssumptionFor (g₁ := g₁) (g₂ := g₂) D Adv error) :
    tSdhExhaustiveAdversary (p := p) g₁ g₂ D ∉ Adv := by
  intro hmem
  have h1 := h _ hmem
  rw [tSdhExperiment_exhaustiveAdversary_eq_one hg₂] at h1
  have h2 : (error : ℝ≥0∞) < 1 := by exact_mod_cast herror
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

end PrimeOrder
end Groups
