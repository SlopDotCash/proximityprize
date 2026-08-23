/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice
import ArkLib.Data.CodingTheory.InterleavedListSize
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# Value bounds for the genuine list-decoding threshold (ABF26 §1, faithful form)

`GrandChallengeLDAttainment` shows the `∃ δ*`-with-maximality formalization of the Grand
List Decoding Challenge is degenerate; `GrandChallengeLattice` provides the faithful
object instead: `listLatticeThreshold C m ε*` — the largest grid index `j` (radius `j/n`)
with `Λ(C^⋈m, j/n) ≤ ε*·|F|`.  The paper's actual challenge is to *determine the value*
of this threshold.  This file proves the two value bounds within reach of current
mathematics:

* **Capacity-side upper bound** (`GrandChallenges.listLatticeThreshold_le_capacity`, unconditional):
  for every Reed–Solomon instance with `1 ≤ deg ≤ n`, `m ≥ 1`, `ε* < 1`,
  `GrandChallenges.listLatticeThreshold ≤ n - deg`.  Reason: at any radius `j/n` with `j > n - deg`,
  the `|F|`-sized family `{c · ∏_{t ∈ T}(X - x_t) : c ∈ F}` (with `|T| = n - j < deg`)
  consists of distinct codewords vanishing on `T`, hence lying within distance `j/n`
  of the zero word; already the base-code list at the zero word exceeds `ε*·|F|`.
  In δ-units: the genuine threshold never exceeds the capacity radius `1 - ρ`.

* **Johnson-side lower bound** (`le_listLatticeThreshold_of_johnson`, parameterized by
  the radical-free Johnson condition): if the in-tree Johnson cap
  `closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition` applies at radius
  `j/n` with list cap `ℓ`, and `ℓ^m ≤ ε*·|F|`, then `j ≤ GrandChallenges.listLatticeThreshold`.  The
  per-centre cap lifts to `Λ` (`Lambda_le_of_johnson_condition`) and to the interleaved
  code through `Lambda_interleaved_le_pow` (ABF26 Lemma 2.10, elementary form).

What remains open — the actual content of the prize — is the gap between these bounds:
whether the threshold for smooth-domain RS codes sits near the Johnson radius or near
capacity.  Neither bound here decides that question; this file pins the provable
interval and leaves the open core explicit.

**Dead route (do not revive): smooth-domain RIM derandomization.**  The natural attack on
the capacity side — derandomizing the BGM23/AGL24/GZ23 capacity machinery from random
evaluation points to the smooth domain `μ_{2^t}` via the reduced-intersection-matrix
full-rank property at the geometric point `Xᵢ = ωⁱ` — is *refuted*, not merely unproven:
`MuTwoPowDerandRefutation.not_kwpc_rigidity` exhibits a 3-weakly-partition-connected
agreement hypergraph with a nonzero agreement certificate over every field containing
`ω` with `ω⁴ = -1` (every prize-legal field; concretely `ZMod 17`, `ω = 9`, in
`not_kwpc_rigidity_zmod17`), and `MuTwoPowDerandRefutation.rimMatrix_rank_drop` packages the
matrix-level determinant/rank drop.  See
`ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRefutation`,
`ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRIMRank`, and the dead-route index
`ArkLib.Data.CodingTheory.ProximityGap.PermanentlyBlocked`.  Any closure of the gap must
route around the `±`-pair obstruction (e.g. odd-order subdomains or non-RIM arguments).
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable

section JohnsonSide

variable {F ι : Type} [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The per-centre radical-free Johnson cap lifts to the maximised list size `Λ`. -/
theorem Lambda_le_of_johnson_condition
    (C : Code ι F) (δ : ℝ) {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card F) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) < 0) :
    Lambda C δ ≤ (ℓ : ℕ∞) := by
  classical
  refine Lambda_le_of_forall_ncard_le fun f => ?_
  have hpt := JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    (C := C) (f := f) (δ := δ) (ℓ := ℓ) (β := β) hδ hq hβ hcond
  rw [card_closeCodewordsRelFinset_eq_ncard] at hpt
  exact_mod_cast hpt

/-- Johnson-side membership in the lattice set: a radical-free Johnson cap `ℓ` at radius
`j/n` whose `m`-th power clears the budget puts `j` in the list-decoding lattice set. -/
theorem mem_listLatticeSet_of_johnson
    (C : Set (ι → F)) {m j : ℕ} (hjn : j ≤ Fintype.card ι)
    {ℓ : ℕ} {β : ℝ} (hq : 0 < Fintype.card F) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) < 0)
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    j ∈ GrandChallenges.listLatticeSet C m ε_star := by
  classical
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.lt_succ_of_le hjn, ?_⟩
  -- base-code Johnson cap at radius j/n
  have hbase : Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞) :=
    Lambda_le_of_johnson_condition C _ (by positivity) hq hβ hcond
  -- interleaved cap via the m-th-power bound
  have hint : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) ^ m := by
    show Lambda (Code.interleavedCodeSet (κ := Fin m) C)
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    exact InterleavedCode.ListSize.Lambda_interleaved_le_pow (m := m) C _
  have hpowENat : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      ((ℓ : ℕ∞)) ^ m :=
    le_trans hint (pow_le_pow_left' hbase m)
  -- cast `ℕ∞ → ℝ≥0∞` and conclude
  calc (Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
      ≤ (((ℓ : ℕ∞) ^ m : ℕ∞) : ENNReal) := by exact_mod_cast hpowENat
    _ = ((ℓ : ENNReal)) ^ m := by
        push_cast
        rfl
    _ ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) := hpow

/-- **Generic lower certificate for the list-decoding lattice set.**  Any base-code
`Λ(C, j/n) ≤ ℓ` cap whose `m`-th power clears the prize budget puts the lattice index `j`
in the faithful list-decoding lattice set.  This is the Johnson-side wrapper with the hard
list-size theorem factored out as the hypothesis `hLambda`; capacity-style RS residuals can
target exactly that hypothesis. -/
theorem mem_listLatticeSet_of_Lambda_le
    (C : Set (ι → F)) {m j ℓ : ℕ} (hjn : j ≤ Fintype.card ι)
    (hLambda :
      Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    j ∈ GrandChallenges.listLatticeSet C m ε_star := by
  classical
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.lt_succ_of_le hjn, ?_⟩
  have hint : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) ^ m := by
    show Lambda (Code.interleavedCodeSet (κ := Fin m) C)
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    exact InterleavedCode.ListSize.Lambda_interleaved_le_pow (m := m) C _
  have hpowENat : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      ((ℓ : ℕ∞)) ^ m :=
    le_trans hint (pow_le_pow_left' hLambda m)
  calc (Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
      ≤ (((ℓ : ℕ∞) ^ m : ℕ∞) : ENNReal) := by exact_mod_cast hpowENat
    _ = ((ℓ : ENNReal)) ^ m := by
        push_cast
        rfl
    _ ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) := hpow

/-- **Johnson-side lower witness for the list-decoding challenge.**  A lattice
radius `j/n` with a budget-clearing Johnson cap is immediately a
`ListLowerWitness`, not only a member of the faithful lattice set. -/
noncomputable def listLowerWitness_of_johnson
    (C : Set (ι → F)) {m j : ℕ} (hjn : j ≤ Fintype.card ι)
    {ℓ : ℕ} {β : ℝ} (hq : 0 < Fintype.card F) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) < 0)
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    GrandChallenges.ListLowerWitness C m ε_star := by
  classical
  let δ : ℝ≥0 := (j : ℝ≥0) / (Fintype.card ι : ℝ≥0)
  have hδ_le : δ ≤ 1 := by
    have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := ι))
    calc
      δ = (j : ℝ≥0) / (Fintype.card ι : ℝ≥0) := rfl
      _ ≤ (Fintype.card ι : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hjn) (by positivity)
      _ = 1 := div_self hn0
  have hmem := mem_listLatticeSet_of_johnson
    (C := C) (m := m) (j := j) hjn (ℓ := ℓ) (β := β) hq hβ hcond hpow
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at hmem
  exact GrandChallenges.ListLowerWitness.ofLe (C := C) (m := m)
    (ε_star := ε_star) (δ := δ) hδ_le hmem.2

/-- **Johnson-side lower bound on the genuine threshold.**  Any lattice radius `j/n`
with a budget-clearing Johnson cap lower-bounds `GrandChallenges.listLatticeThreshold`. -/
theorem le_listLatticeThreshold_of_johnson
    (C : Set (ι → F)) {m j : ℕ} (hjn : j ≤ Fintype.card ι)
    {ℓ : ℕ} {β : ℝ} (hq : 0 < Fintype.card F) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        - 2 * β * (((Fintype.card ι -
              ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) < 0)
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    j ≤ GrandChallenges.listLatticeThreshold C m ε_star hne :=
  Finset.le_max' _ _ (mem_listLatticeSet_of_johnson C hjn hq hβ hcond hpow)

/-- **Generic lower bound on the genuine list threshold from a base `Λ` cap.**
This is the conditional residual wrapper needed by capacity-style ordinary-RS routes: once
one proves `Λ(C, j/n) ≤ ℓ`, the existing interleaving product bound and budget inequality
give `j ≤ listLatticeThreshold C m ε*`. -/
theorem le_listLatticeThreshold_of_Lambda_le
    (C : Set (ι → F)) {m j ℓ : ℕ} (hjn : j ≤ Fintype.card ι)
    (hLambda :
      Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    j ≤ GrandChallenges.listLatticeThreshold C m ε_star hne :=
  Finset.le_max' _ _ (mem_listLatticeSet_of_Lambda_le C hjn hLambda hpow)

/-- **Generic lower witness from a base `Λ` cap.**  This is the witness-valued version of
`mem_listLatticeSet_of_Lambda_le`: once a base-code list-size bound
`Λ(C, j/n) ≤ ℓ` clears the interleaved prize budget, it produces the public
`ListLowerWitness` consumed by the faithful list-prize lattice API. -/
noncomputable def listLowerWitness_of_Lambda_le
    (C : Set (ι → F)) {m j ℓ : ℕ} (hjn : j ≤ Fintype.card ι)
    (hLambda :
      Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    GrandChallenges.ListLowerWitness C m ε_star := by
  classical
  let δ : ℝ≥0 := (j : ℝ≥0) / (Fintype.card ι : ℝ≥0)
  have hδ_le : δ ≤ 1 := by
    have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := ι))
    calc
      δ = (j : ℝ≥0) / (Fintype.card ι : ℝ≥0) := rfl
      _ ≤ (Fintype.card ι : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hjn) (by positivity)
      _ = 1 := div_self hn0
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := C) (m := m) (j := j) (ℓ := ℓ) hjn hLambda hpow
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at hmem
  exact GrandChallenges.ListLowerWitness.ofLe (C := C) (m := m)
    (ε_star := ε_star) (δ := δ) hδ_le hmem.2

#print axioms ProximityGap.listLowerWitness_of_Lambda_le

end JohnsonSide

section CapacitySide

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

open Polynomial

/-- If two words agree on `T`, their relative Hamming distance is at most
`(n - |T|)/n` (as reals).  Stated instance-generically in the alphabet so it applies
under the classical instances baked into `relHammingBall`. -/
lemma relHammingDist_coe_le_of_agree_on [Nonempty ι]
    {A : Type*} [DecidableEq A] (y x : ι → A)
    (T : Finset ι) (hagree : ∀ i ∈ T, y i = x i) :
    ((Code.relHammingDist y x : ℚ≥0) : ℝ) ≤
      ((Fintype.card ι - T.card : ℕ) : ℝ) / (Fintype.card ι : ℝ) := by
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hham : hammingDist y x ≤ Fintype.card ι - T.card := by
    rw [Code.hammingDist_eq_disagreementCols_card]
    refine le_trans (Finset.card_le_card (t := Finset.univ \ T) ?_) ?_
    · intro i hi
      rw [Code.mem_disagreementCols] at hi
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ i, fun hiT => hi (hagree i hiT)⟩
    · rw [Finset.card_univ_diff]
  have hrel : (Code.relHammingDist y x : ℚ≥0) =
      (hammingDist y x : ℚ≥0) / (Fintype.card ι : ℚ≥0) := rfl
  rw [hrel, show (((hammingDist y x : ℚ≥0) / (Fintype.card ι : ℚ≥0) : ℚ≥0) : ℝ)
      = (hammingDist y x : ℝ) / (Fintype.card ι : ℝ) by push_cast; ring]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast hham

/-- The scaled vanishing family: for `|T| < deg ≤ n`, the evaluations of
`c · ∏_{t ∈ T}(X - x_t)` over `c : F` are `|F|` distinct codewords of
`RS[F, domain, deg]`, all vanishing on `T`. -/
lemma exists_family_vanishing_on (domain : ι ↪ F) {deg : ℕ} (T : Finset ι)
    (hT : T.card < deg) (hTn : T.card < Fintype.card ι) :
    ∃ φ : F → (ι → F), Function.Injective φ ∧
      (∀ c, φ c ∈ (ReedSolomon.code domain deg : Set (ι → F))) ∧
      (∀ c, ∀ i ∈ T, φ c i = 0) := by
  classical
  set P : F[X] := ∏ t ∈ T, (X - Polynomial.C (domain t)) with hP
  have hPdeg : P.natDegree = T.card := by
    rw [hP, natDegree_prod _ _ fun t _ => X_sub_C_ne_zero (domain t)]
    simp
  -- a point outside `T`
  have hex : ∃ i₀, i₀ ∉ T := by
    by_contra hall
    push Not at hall
    have huniv : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ] at hTn
    exact lt_irrefl _ hTn
  obtain ⟨i₀, hi₀⟩ := hex
  have hP0 : P.eval (domain i₀) ≠ 0 := by
    rw [hP, eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    intro h
    exact hi₀ (by rw [domain.injective h]; exact ht)
  have hvanish : ∀ i ∈ T, P.eval (domain i) = 0 := by
    intro i hi
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  refine ⟨fun c => fun i => c * P.eval (domain i), ?_, ?_, ?_⟩
  · intro a b hab
    exact mul_right_cancel₀ hP0 (congrFun hab i₀)
  · intro c
    refine ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      (Polynomial.C c * P) ?_ ?_
    · calc (Polynomial.C c * P).natDegree ≤ P.natDegree := natDegree_C_mul_le c P
        _ = T.card := hPdeg
        _ < deg := hT
    · intro i
      simp [eval_mul]
  · intro c i hi
    simp [hvanish i hi]

/-- **Beyond capacity the interleaved list blows up**: at any grid radius `j/n` with
`j > n - deg`, the radius-`j/n` interleaved list at the zero word already has `|F|`
elements. -/
lemma card_le_Lambda_of_gt_capacity [Fintype F] [Nonempty ι]
    (domain : ι ↪ F) {deg j m : ℕ}
    (hdegn : deg ≤ Fintype.card ι) (hm : m ≠ 0)
    (hj : Fintype.card ι - deg < j) (hjn : j ≤ Fintype.card ι) :
    (Fintype.card F : ℕ∞) ≤
      Lambda ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
  classical
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  -- choose the vanishing set
  obtain ⟨T, -, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
      (n := Fintype.card ι - j) (by rw [Finset.card_univ]; omega)
  have hTdeg : T.card < deg := by omega
  have hTn : T.card < Fintype.card ι := by omega
  obtain ⟨φ, hinj, hmem, hvan⟩ := exists_family_vanishing_on domain T hTdeg hTn
  -- diagonal interleaved stacks
  set ψ : F → (ι → (Fin m → F)) := fun c => fun i _ => φ c i with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply hinj
    funext i
    exact congrFun (congrFun hab i) (Classical.arbitrary (Fin m))
  have hψsub : Set.range ψ ⊆
      closeCodewordsRel
        ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
        (fun _ _ => (0 : F))
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    rintro _ ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · -- interleaved-code membership: every row is `φ c`
      show ∀ k : Fin m, (Matrix.transpose (ψ c)) k ∈
        (ReedSolomon.code domain deg : Set (ι → F))
      intro k
      have hrow : Matrix.transpose (ψ c) k = φ c := rfl
      rw [hrow]
      exact hmem c
    · -- distance bound: differing columns avoid `T`
      simp only [relHammingBall, Set.mem_setOf_eq]
      have hdist := @relHammingDist_coe_le_of_agree_on ι _ _ _ (Fin m → F)
        (fun a b => Classical.propDecidable (a = b))
        (fun _ _ => (0 : F)) (ψ c) T (fun i hi => by
          funext k
          simp [hψ, hvan c i hi])
      refine le_trans hdist ?_
      -- (n - |T|)/n ≤ j/n
      rw [show ((((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0)) : ℝ) =
          ((j : ℝ)) / ((Fintype.card ι : ℝ)) by push_cast; ring]
      apply div_le_div_of_nonneg_right ?_ (by exact_mod_cast Nat.zero_le (Fintype.card ι))
      have : Fintype.card ι - T.card ≤ j := by omega
      exact_mod_cast this
  -- count the family
  have hcard : (Set.range ψ).ncard = Fintype.card F := by
    rw [Set.ncard_range_of_injective hψinj, Nat.card_eq_fintype_card]
  calc (Fintype.card F : ℕ∞)
      = ((Set.range ψ).ncard : ℕ∞) := by rw [hcard]
    _ ≤ ((closeCodewordsRel
          ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
          (fun _ _ => (0 : F))
          (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_le_ncard hψsub (Set.toFinite _)
    _ ≤ _ :=
        le_iSup (fun f => ((closeCodewordsRel _ f _).ncard : ℕ∞)) (fun _ _ => (0 : F))

/-- **Capacity-side upper bound on the genuine threshold** (unconditional): for every
Reed–Solomon instance with `deg ≤ n`, `m ≥ 1`, `ε* < 1`, the genuine lattice threshold
is at most `n - deg`; in δ-units, the capacity radius `1 - ρ` is a hard ceiling. -/
theorem listLatticeThreshold_le_capacity [Fintype F] [Nonempty ι]
    (domain : ι ↪ F) {deg m : ℕ}
    (hdegn : deg ≤ Fintype.card ι) (hm : m ≠ 0)
    {ε_star : ℝ≥0} (hε : ε_star < 1)
    (hne : (GrandChallenges.listLatticeSet (ReedSolomon.code domain deg : Set (ι → F)) m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold (ReedSolomon.code domain deg : Set (ι → F)) m ε_star hne ≤
      Fintype.card ι - deg := by
  classical
  apply Finset.max'_le
  intro j hj
  by_contra hgt
  push Not at hgt
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjr, hjle⟩ := hj
  have hjn : j ≤ Fintype.card ι := Nat.lt_succ_iff.mp hjr
  have hΛ := card_le_Lambda_of_gt_capacity (m := m) domain hdegn hm hgt hjn
  -- `ε*·|F| < |F| ≤ Λ`, contradiction
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Fintype.card F : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < 1 * (Fintype.card F : ENNReal) := by
          rw [mul_comm (ε_star : ENNReal), mul_comm (1 : ENNReal)]
          exact ENNReal.mul_lt_mul_right hq0 hqt (by exact_mod_cast hε)
      _ = (Fintype.card F : ENNReal) := one_mul _
  have h1' : (Fintype.card F : ENNReal) ≤
      (Lambda ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
    calc (Fintype.card F : ENNReal)
        = ((Fintype.card F : ℕ∞) : ENNReal) := by simp
      _ ≤ _ := by exact_mod_cast hΛ
  exact absurd hjle (not_le.mpr (lt_of_lt_of_le h2 h1'))

end CapacitySide

end ProximityGap
