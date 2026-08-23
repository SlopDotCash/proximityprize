/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gao-Cai-Xu-Kan (GCXK25) Union Bound Bridge

This module formalizes the union-bound-over-the-list reduction step used in the proof of
the proximity gap theorem for Reed-Solomon codes. Specifically, it relates the list-decodability
parameters of a code to its correlated agreement (CA) / multi-correlated agreement (MCA) error,
as detailed in Theorem 3 of [GCXK25] (corresponding to Theorem 5.1 of [ABF26]).

In the proximity gap reduction, we bound the MCA error:
$$\varepsilon_{\mathrm{mca}}(C, 1 - \sqrt{1 - \delta + \eta}) \le \frac{L^2 \delta n +
1/\eta}{|F|}$$
by analyzing the set of "bad" combining scalars $\gamma \in F$ for a given stack $u = (u_0, u_1)$.
A combining scalar $\gamma$ is bad if there exists a large agreement witness set $S \subset \iota$
on which the line $u_0 + \gamma u_1$ agrees with some codeword $w \in C$, but $u$ is not jointly
close to $C$ on $S$.

Rather than treating this bad scalar count monolithically, this file implements the union bound
decomposition:
1. We define the set of bad combining scalars associated with a *fixed* codeword $w \in C$
(`mcaBadWitness`).
2. We prove that any bad combining scalar in `mcaBad` must be associated with at least one codeword
$w$
   in the list of close codewords, establishing the containment `mcaBad ⊆ ⋃_{w ∈ C} mcaBadWitness
   w`.
3. We deduce the corresponding union bound and the card-based scaling bounds.

## References
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026.
* [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*, eprint 2025/870.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- For a fixed stack $u = (u_0, u_1)$, agreement parameter $\delta$, and a specific codeword $w \in
C$,
`mcaBadWitness` is the set of combining scalars $\gamma \in F$ for which the multi-correlated
agreement (MCA)
event is witnessed by $w$. That is, there exists a subset $S \subset \iota$ of size at least $(1 -
\delta)n$
on which $w$ agrees with the line $u_0 + \gamma u_1$, yet no joint codeword pair of $C$ agrees with
$u$ on $S$. -/
noncomputable def mcaBadWitness (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (w : ι → A) :
    Finset F :=
  Finset.univ.filter (fun γ : F =>
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn C S u₀ u₁)

open Classical in
/-- Union bound containment for bad combining scalars.
Every bad scalar $\gamma \in \mathrm{mcaBad}$ is witnessed by at least one codeword $w \in C$.
Consequently, the set of all bad scalars is contained in the union of the per-codeword witness sets
`mcaBadWitness w` as $w$ ranges over a finite set of codewords $T$ containing $C$. -/
theorem mcaBad_subset_biUnion_mcaBadWitness
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T) :
    mcaBad (F := F) C δ u₀ u₁ ⊆ T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w) := by
  classical
  intro γ hγ
  rw [mcaBad, Finset.mem_filter] at hγ
  obtain ⟨S, hScard, ⟨w, hwC, hwagree⟩, hpair⟩ := hγ.2
  rw [Finset.mem_biUnion]
  refine ⟨w, hT w hwC, ?_⟩
  rw [mcaBadWitness, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨S, hScard, hwagree, hpair⟩⟩

open Classical in
/-- Cardinality union bound for bad combining scalars.
The size of `mcaBad` is bounded by the sum of the cardinalities of the per-codeword witness sets
`mcaBadWitness w`
for all $w$ in the finite set of codewords $T$. -/
theorem mcaBad_card_le_sum_mcaBadWitness_card
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T) :
    (mcaBad (F := F) C δ u₀ u₁).card ≤
      ∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card := by
  classical
  calc (mcaBad (F := F) C δ u₀ u₁).card
      ≤ (T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w)).card :=
        Finset.card_le_card (mcaBad_subset_biUnion_mcaBadWitness C δ u₀ u₁ T hT)
    _ ≤ ∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card := Finset.card_biUnion_le

open Classical in
/-- Reduction of the bad combining scalar count to a per-codeword bound.
Assuming the set of candidate witness codewords is bounded by a list size factor $|T|$, and each
individual
codeword $w \in T$ yields at most $b$ bad combining scalars, the total number of bad combining
scalars
is at most $|T| \cdot b$. -/
theorem mcaBad_card_le_of_per_codeword
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T)
    {b : ℝ} (_hb0 : 0 ≤ b)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ (T.card : ℝ) * b := by
  classical
  have hsum : ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤
      ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by
    have := mcaBad_card_le_sum_mcaBadWitness_card (F := F) C δ u₀ u₁ T hT
    calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
        ≤ ((∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by push_cast; ring
  calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := hsum
    _ ≤ ∑ _w ∈ T, b := Finset.sum_le_sum (fun w hw => hper w hw)
    _ = (T.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

end

end ProximityGap
