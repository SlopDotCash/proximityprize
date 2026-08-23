/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance

/-!
# Toy IOR soundness — the §6.4.1 Step-4 winning-set injection (ABF26 L6.12)

This file builds the **genuine Step-4 construction** of [ABF26] §6.4.1 — the
list→challenge injection used by `ToyProblem.simplified_iop_soundness_listDecoding_lb`
(`ProofSystem/ToyProblem/SoundnessBounds.lean`) to close the L6.12 proof.

Steps 1–3 (the finite-`iSup` maximiser, the per-pair collision bound
`linearForm_collision_prob`/`pair_linearForm_collision_le`, and Claim B.1
`exists_large_image_of_pairwise_collision_bound`) are proven in tree. The residual is the
*combinatorial heart of the attack*: turning `N := |Λ(C^{≡2}, δ)|` distinct `δ`-close
codeword pairs into a single attack instance whose winning-challenge set
`Ω^{f₁,f₂}_{v,μ₁,μ₂}` (Definition 6.11) has at least `N·|F| / (|F| + N − 1)` elements.

## The construction

The pivotal arithmetic observation that makes the bound *attainable by a genuine injection*
(rather than only by Claim B.1's averaging) is:

  `N·|F| / (|F| + N − 1) ≤ N`   (since `N·|F| ≤ N·(|F| + N − 1) ⟺ 0 ≤ N·(N−1)`).

So it suffices to exhibit `N` **distinct winning challenges**, i.e. an injection
`Fin N ↪ winningSet`. That is exactly the §6.4.1 attack: each of the `N` distinct codewords
of the list is realised at a *distinct* passing challenge `γ`, and each such `γ` lies in the
winning set because the line `f₁ + γ·f₂` is `δ`-close to the corresponding codeword (in `C`
by linearity of the encoder) which satisfies the toy relation at `μ₁ + γ·μ₂`.

We package the construction in two reusable pieces:

* `winningSet_ncard_ge_of_injOn` — the **arithmetic + cardinality bridge**: an `InjOn`
  challenge family landing in `winningSet` lower-bounds `|winningSet|` by its size, hence by
  the list-decoding bound `N·|F| / (|F| + N − 1)`. (Axiom-clean, unconditional.)

* `winningChal_mem_winningSet` — the **per-challenge winning-set membership**: under the
  linear-encoder hypothesis `hEnc`, if the line `f₁ + γ·f₂` is `δ`-close to a codeword
  `c ∈ C`, then `γ ∈ winningSet C δ 0 0 0 f₁ f₂`. (This is the `v = μ₁ = μ₂ = 0` instance,
  for which the linear constraint is vacuous; it mirrors the `hrel_of_mem` bridge of
  `simplified_iop_soundness_ca_lb`.)

* `simplified_iop_listDecoding_lb_of_winningChallenges` — the **assembled Step-4 lemma**:
  given a list of `N` distinct codewords each yielding (at a distinct, injectively assigned
  challenge) a `δ`-close line, the winning set has `≥ N·|F| / (|F| + N − 1)` elements. This
  is the faithful Step-4 conclusion, with the genuine attack data (`hEnc`, the distinct
  winning challenges) carried as documented hypotheses rather than smuggled as the goal.

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

/-! ## Step-4 arithmetic: the bound never exceeds the list size -/

/-- **L6.12 Step-4 arithmetic core.** The list-decoding lower bound
`N·|F| / (|F| + N − 1)` never exceeds `N`: clearing the positive denominator,
`N·|F| ≤ N·(|F| + N − 1)` is `0 ≤ N·(N − 1)`. Hence a winning set with `≥ N`
distinct challenges already realises the bound. PROVEN, axiom-clean. -/
lemma listDecoding_lb_le_listSize (N : ℕ) (M : ℝ) (hM : (1 : ℝ) ≤ M) :
    ((N : ℝ) * M) / (M + (N : ℝ) - 1) ≤ (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hden_pos : 0 < M + (N : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)]

/-! ## Cardinality bridge: distinct winning challenges lower-bound the winning set -/

/-- **Step-4 cardinality bridge.** If `chal : Fin N → F` is injective and every value
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

/-- **Step-4 cardinality bridge (real-valued, with the list-decoding bound).** An injective
family of `N` winning challenges forces the winning set's cardinality to be at least the
list-decoding lower bound `N·|F| / (|F| + N − 1)`. Combines `winningSet_card_ge_of_inj`
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

/-- **Per-challenge winning-set membership (Step-4 core).** Under the linear-encoder
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

/-! ## The assembled Step-4 winning-set bound -/

/-- **L6.12 Step-4 (assembled, ABF26 §6.4.1).** The genuine list→challenge injection.

Suppose we have:

* the linear-encoder hypothesis `hEnc` (the toy relation's standing assumption);
* an injective challenge assignment `chal : Fin N → F` (the §6.4.1 distinct passing
  challenges, one per list element — *distinct* by the field-size regime `|F| > binom(N,2)`
  via the per-pair separation of Steps 2–3);
* for each `j`, a codeword `c j ∈ C` to which the line `f₁ + (chal j)·f₂` is `δ`-close
  (the list element realised at its challenge).

Then the attack instance `(0, 0, 0, f₁, f₂)` has winning set of cardinality at least
`N·|F| / (|F| + N − 1)` — the L6.12 conclusion. This is the faithful Step-4: the genuine
distinct-challenge attack data is the input, and the cardinality bound is *derived*
(not assumed). PROVEN, axiom-clean. -/
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

-- Step-4 arithmetic core (pure real analysis):
#print axioms ToyProblem.listDecoding_lb_le_listSize

-- Cardinality bridge (Set.ncard_le_ncard_of_injOn):
#print axioms ToyProblem.winningSet_card_ge_of_inj

-- Cardinality bridge + list-decoding bound:
#print axioms ToyProblem.winningSet_ncard_ge_of_inj

-- Per-challenge winning-set membership (the v = μ₁ = μ₂ = 0 instance):
#print axioms ToyProblem.winningChal_mem_winningSet

-- The assembled Step-4 lemma (the genuine L6.12 §6.4.1 list→challenge injection):
#print axioms ToyProblem.simplified_iop_listDecoding_lb_of_winningChallenges
