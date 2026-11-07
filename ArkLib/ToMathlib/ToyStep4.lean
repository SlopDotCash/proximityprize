/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ProximityPrize.Extensions.ProofSystem.ToyProblem.Definitions
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ProximityPrize.Extensions.Data.CodingTheory.InterleavedCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance

/-!
# Toy IOR — a distinct-challenge → winning-set cardinality bridge

This file proves a **cardinality bridge**, not the ABF26 Lemma 6.12 attack. An
injective family of `N` challenges all lying in a winning set
`Ω^{f₁,f₂}_{v,μ₁,μ₂}` (Definition 6.11) forces `|Ω| ≥ N ≥ N·|F| / (|F| + N − 1)`.
It is used by the honest-instance lemma
`ToyProblem.winningSet_zeroInstance_ncard_ge_listDecoding_expr`
(`ProximityPrize/Extensions/ProofSystem/ToyProblem/SoundnessBounds.lean`).

## What it does not prove

* No hypothesis says the instance `(f₁, f₂)` **violates** the relaxed relation, so the
  bridge applies equally to valid (honest) instances; e.g. the all-zero instance, where
  every challenge wins. Its conclusions are therefore not soundness lower bounds.
* The codeword family `c : Fin N → ι → F` is **not** required to be distinct, nor to
  come from the list `Λ(C^{≡2}, δ)`; only the challenges are injective.
* The genuine Lemma 6.12 (violating instance, fixed-encoding relation, final bound
  `N·|F| / (|F| + 2N)`) is the canonical
  `ToyProblem.exists_winningSetFor_ncard_ge_of_lambda_lt_card`
  (`ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean`). There
  `N·|F| / (|F| + N − 1)` is only the intermediate first-B.1 image bound.

## Contents

* `listDecoding_lb_le_listSize` — `N·|F| / (|F| + N − 1) ≤ N`.
* `winningSet_card_ge_of_inj` / `winningSet_ncard_ge_of_inj` — an injective family of
  winning challenges lower-bounds `|winningSet|` by `N`, hence by the expression above.
* `winningChal_mem_winningSet` — under the linear-encoder hypothesis `hEnc`, if
  `f₁ + γ·f₂` is `δ`-close to some `c ∈ C`, then `γ ∈ winningSet C δ 0 0 0 f₁ f₂`
  (the `v = μ₁ = μ₂ = 0` instance, where the linear constraint is vacuous).
* `simplified_iop_listDecoding_lb_of_winningChallenges` — the two combined.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-! ## Arithmetic: the expression never exceeds the list size -/

/-- **Arithmetic core.** The expression
`N·|F| / (|F| + N − 1)` never exceeds `N`: clearing the positive denominator,
`N·|F| ≤ N·(|F| + N − 1)` is `0 ≤ N·(N − 1)`. Hence a winning set with `≥ N`
distinct challenges already exceeds it. PROVEN, axiom-clean. -/
lemma listDecoding_lb_le_listSize (N : ℕ) (M : ℝ) (hM : (1 : ℝ) ≤ M) :
    ((N : ℝ) * M) / (M + (N : ℝ) - 1) ≤ (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hden_pos : 0 < M + (N : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)]

/-! ## Cardinality bridge: distinct winning challenges lower-bound the winning set -/

/-- **Cardinality bridge.** If `chal : Fin N → F` is injective and every value
`chal j` lies in `winningSet C δ v μ₁ μ₂ f₁ f₂`, then the winning set has at least `N`
elements. PROVEN, axiom-clean (pure `Set.ncard_le_ncard_of_injOn`). -/
lemma winningSet_card_ge_of_inj {k N : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → F}
    (chal : Fin N → F) (hchal_inj : Function.Injective chal)
    (hchal_win : ∀ j, chal j ∈ winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂) :
    (N : ℕ) ≤ (winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard := by
  classical
  have hmaps : ∀ a ∈ (Set.univ : Set (Fin N)), chal a ∈
      winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂ := fun a _ => hchal_win a
  have hinjOn : Set.InjOn chal (Set.univ : Set (Fin N)) :=
    fun a _ b _ h => hchal_inj h
  have h := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set (Fin N)))
    (t := winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂) chal hmaps hinjOn (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-- **Cardinality bridge (real-valued).** An injective
family of `N` winning challenges forces the winning set's cardinality to be at least
`N·|F| / (|F| + N − 1)`. Combines `winningSet_card_ge_of_inj`
(distinct challenges ⟹ `|Ω| ≥ N`) with `listDecoding_lb_le_listSize` (`N·|F|/(|F|+N−1) ≤ N`).
PROVEN, axiom-clean. -/
lemma winningSet_ncard_ge_of_inj {k N : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → F}
    (chal : Fin N → F) (hchal_inj : Function.Injective chal)
    (hchal_win : ∀ j, chal j ∈ winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂) :
    (((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ)) ≥
      ((N : ℝ) * Fintype.card F) / (Fintype.card F + (N : ℝ) - 1) := by
  have hcard : (N : ℕ) ≤ (winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard :=
    winningSet_card_ge_of_inj chal hchal_inj hchal_win
  have hM : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    have : 1 ≤ Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  calc ((N : ℝ) * Fintype.card F) / (Fintype.card F + (N : ℝ) - 1)
      ≤ (N : ℝ) := listDecoding_lb_le_listSize N (Fintype.card F : ℝ) hM
    _ ≤ ((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) := by exact_mod_cast hcard

/-! ## Per-challenge winning-set membership (the `v = μ₁ = μ₂ = 0` instance) -/

/-- **Per-challenge winning-set membership.** Under the linear-encoder
hypothesis `hEnc` (the code's standing assumption, cf. `simplified_iop_soundness_ca_lb`),
a challenge `γ` is *winning* for the attack instance `(0, 0, 0, f₁, f₂)` whenever the line
`f₁ + γ·f₂` is `δ`-close to *some* codeword `c ∈ C`.

This is the `v = μ₁ = μ₂ = 0` instance of Definition 6.11: the linear constraint
`∑ⱼ M·0 = 0 = μ₁ + γ·μ₂` is vacuous, so any close codeword `c` is a valid relation witness
(via `hEnc`), and the closeness supplies the agreement set. PROVEN, axiom-clean. -/
theorem winningChal_mem_winningSet [Nonempty ι] {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (δlt : δ ≤ 1)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    {f₁ f₂ : ι → F} {γ : F} {c : ι → F}
    (hc_mem : c ∈ C) (hc_dist : δᵣ((fun j => f₁ j + γ * f₂ j), c) ≤ δ) :
    γ ∈ winningSet (k := k) C δ (0 : Fin k → F) 0 0 f₁ f₂ := by
  classical
  obtain ⟨encode, hEnc_mem, hEnc_surj⟩ := hEnc
  -- `relation`-from-membership bridge under the encoder hypothesis.
  have hrel_of_mem : relation (k := k) (ℓ := 1) C (0 : Fin k → F) (fun _ ↦ (0 : F))
      (fun _ ↦ c) := by
    obtain ⟨m, hm⟩ := hEnc_surj c hc_mem
    exact ⟨fun _ ↦ m, ⟨encode, hEnc_mem, fun _ ↦ hm.symm⟩, by intro i; simp⟩
  -- Unfold winning-set membership: build the `relaxedRelation` witness.
  refine ⟨fun _ => c, ?_, ?_⟩
  · -- The relation holds with constraint value `μ₁ + γ·μ₂ = 0 + γ·0 = 0`.
    simpa using hrel_of_mem
  · -- Agreement set from `δᵣ(f₁ + γ·f₂, c) ≤ δ`.
    rw [relCloseToWord_iff_exists_agreementCols] at hc_dist
    obtain ⟨T, hT_card, hT_agree⟩ := hc_dist
    refine ⟨T, ?_, ?_⟩
    · -- `(1 - δ)·|ι| ≤ |T|`.
      have hcomp := (relDist_floor_bound_iff_complement_bound (Fintype.card ι) T.card δ).mp
        hT_card
      have hcompR : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) := by
        have := (NNReal.coe_le_coe.mpr hcomp)
        rwa [NNReal.coe_mul, NNReal.coe_natCast] at this
      rwa [NNReal.coe_sub δlt, NNReal.coe_one] at hcompR
    · -- On `T`, `(f₁ + γ·f₂) j = c j`.
      intro i j hj
      have := (hT_agree j).1 hj
      simpa using this

/-! ## The assembled cardinality bridge -/

/-- **Distinct-challenge cardinality bridge (zero-constraint instance).**

Given the linear-encoder hypothesis `hEnc`, an injective `chal : Fin N → F`, and for each
`j` some codeword `c j ∈ C` to which the line `f₁ + (chal j)·f₂` is `δ`-close, the winning
set of `(0, 0, 0, f₁, f₂)` has at least `N ≥ N·|F| / (|F| + N − 1)` elements.

Only the challenges must be distinct; the `c j` need not be distinct or list elements, and
no violation condition on `(f₁, f₂)` is assumed, so honest instances satisfy the
hypotheses. This is not the ABF26 L6.12 attack (see the module docstring). -/
theorem simplified_iop_listDecoding_lb_of_winningChallenges [Nonempty ι] {k N : ℕ}
    {C : Set (ι → F)} {δ : ℝ≥0} (δlt : δ ≤ 1)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    {f₁ f₂ : ι → F}
    (chal : Fin N → F) (hchal_inj : Function.Injective chal)
    (c : Fin N → (ι → F)) (hc_mem : ∀ j, c j ∈ C)
    (hc_dist : ∀ j, δᵣ((fun i => f₁ i + (chal j) * f₂ i), c j) ≤ δ) :
    (((winningSet (k := k) C δ (0 : Fin k → F) 0 0 f₁ f₂).ncard : ℝ)) ≥
      ((N : ℝ) * Fintype.card F) / (Fintype.card F + (N : ℝ) - 1) := by
  have hwin : ∀ j, chal j ∈ winningSet (k := k) C δ (0 : Fin k → F) 0 0 f₁ f₂ := by
    intro j
    exact winningChal_mem_winningSet δlt hEnc (hc_mem j) (hc_dist j)
  exact winningSet_ncard_ge_of_inj chal hchal_inj hwin

end ToyProblem

/-! ## Kernel-dependency audit

Each `#print axioms` below must report only Lean's standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) — i.e. **no** `sorryAx` and **no** project-level
assumed constant. -/

-- Arithmetic core (pure real analysis):
#print axioms ToyProblem.listDecoding_lb_le_listSize

-- Cardinality bridge (Set.ncard_le_ncard_of_injOn):
#print axioms ToyProblem.winningSet_card_ge_of_inj

-- Cardinality bridge + list-decoding bound:
#print axioms ToyProblem.winningSet_ncard_ge_of_inj

-- Per-challenge winning-set membership (the v = μ₁ = μ₂ = 0 instance):
#print axioms ToyProblem.winningChal_mem_winningSet

-- The assembled cardinality bridge (not the L6.12 attack; see module docstring):
#print axioms ToyProblem.simplified_iop_listDecoding_lb_of_winningChallenges
