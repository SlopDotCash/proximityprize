/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.Basic.Distance

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ProximityPrize.Extensions.Data.Fin.Basic
import ProximityPrize.Extensions.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.Real.ENatENNReal
import CompPoly.Data.Nat.Bitwise

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Naming conventions
  1. suffix `'`: **computable/instantiation** of the corresponding
  mathematical generic definitions without such suffix (e.g. `Δ₀'(u, C)` vs `Δ₀(u, C)`,
  `δᵣ'(u, C)` vs `δᵣ(u, C)`, ...)
    - **NOTE**: The generic (non-suffixed) definitions (`Δ₀`, `δᵣ`, ...) are recommended
      to be used in generic security statements, and the suffixed definitions
      (`Δ₀'`, `δᵣ'`, ...) are used for proofs or in statements of lemmas that need
      smaller value range.
    - We usually prove the equality as a bridge from the suffixed definitions into the
      non-suffixed definitions (e.g. `distFromCode'_eq_distFromCode`, ...)

  ## Type conventions

  Distance quantities span several numeric types depending on the use case:

  - Hamming distance (absolute, pairwise): `ℕ` — `hammingDist`, `Δ₀(u, v)`.
  - Min distance of a code (absolute): `ℕ` — `Code.minDist`, `‖C‖₀`.
  - Distance to a code (absolute, may be `⊤`): `ℕ∞` — `distFromCode`, `Δ₀(u, C)`.
  - Relative Hamming distance (pairwise): `ℚ≥0` — `relHammingDist`, `δᵣ(u, v)`.
  - Relative distance to a code: `ENNReal` — `relDistFromCode`, `δᵣ(u, C)`.
  - Restricted relative Hamming distance: `ℝ≥0` — `restrictedRelHammingDist`
    (ABF26 `Δ_T(f, g)`).
  - Code rate: `ℚ≥0` — `LinearCode.rate`, `ρ C`.
  - Computable variants: `ℚ≥0` — `δᵣ'`, `Δ₀'`, …

  See `docs/wiki/coding-theory-conventions.md` for the broader set of
  conventions (theorem naming, notation, ε-error types).

  Bridges between these realms are spelled out in the "Switching between different
  distance realms" subsection below (`relDistFromCode_eq_distFromCode_div`,
  `distFromCode_le_iff_relDistFromCode_le`, etc.). Downstream consumers should
  prefer the generic forms (`Δ₀`, `δᵣ`) and only switch to computable forms when
  the proof actually needs evaluation.

  ## Main Definitions
  1. Distance between two words:
    - `hammingDist u v (Δ₀(u, v))`: The Hamming distance between two words `u` and `v`
    - `relHammingDist u v (δᵣ(u, v))`: The relative Hamming distance between two words `u` and `v`
  2. Distance of code:
    - `dist C (‖"C‖₀)`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
      Hamming distances between any two distinct elements of `C`. This is noncomputable.
      + `minDist C`: another statement of `dist C` using equality, we have `dist_eq_minDist`
    - `dist' C (‖C‖₀')`: A computable version of `dist C`, assuming `C` is a `Fintype`.
  3. Distance from a word to a code:
    - `distFromCode u C (Δ₀(u, C))`: The hamming distance from a word `u` to a code `C`
      + `distFromCode_of_empty`: `Δ₀(u, ∅) = ⊤`
      + `distFromCode_eq_top_iff_empty`: `Δ₀(u, C) = ⊤ ↔ C = ∅`
    - `distFromCode' u C (Δ₀'(u, C))`: A computable version of `distFromCode u C`,
      assuming `C` is a `Fintype`.
      + `distFromCode'_eq_distFromCode`: `Δ₀'(u, C) = Δ₀(u, C)`
    - `relDistFromCode u C (δᵣ(u, C))`: The relative Hamming distance from a word `u` to a code `C`
      + `relDistFromCode' u C (δᵣ'(u, C))`: A computable version of `relDistFromCode u C`,
      assuming `C` is a `Fintype` and `C` is **non-empty**.
      + `relDistFromCode'_eq_relDistFromCode`: `δᵣ'(u, C) = δᵣ(u, C)`
  4. Switching between different distance realms:
    - `relDistFromCode_eq_distFromCode_div`: `δᵣ(u, C) = Δ₀(u, C) / |ι|`
    - `pairDist_eq_distFromCode_iff_eq_relDistFromCode_div`:
      `Δ₀(u, v) = Δ₀(u, C) ↔ δᵣ(u, v) = δᵣ(u, C)`
    - `relDistFromCode_le_relDist_to_mem`: `δᵣ(u, C) ≤ δᵣ(u, v)`
    - `relCloseToCode_iff_relCloseToCodeword_of_minDist`: `δᵣ(u, C) ≤ δ ↔ ∃ v ∈ C, δᵣ(u, v) ≤ δ`
    - `pairRelDist_le_iff_pairDist_le`:
      `(δᵣ(u, v) ≤ δ) ↔ (Δ₀(u, v) ≤ Nat.floor (δ * Fintype.card ι))`
    - `distFromCode_le_iff_relDistFromCode_le`:
      `Δ₀(u, C) ≤ e ↔ δᵣ(u, C) ≤ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0)`
    - `relDistFromCode_le_iff_distFromCode_le`:
      `δᵣ(u, C) ≤ δ ↔ Δ₀(u, C) ≤ Nat.floor (δ * Fintype.card ι)`
    - `relCloseToWord_iff_exists_possibleDisagreeCols`
    - `relCloseToWord_iff_exists_agreementCols`
    - `relDist_floor_bound_iff_complement_bound`
    - `distFromCode_le_dist_to_mem`: `Δ₀(u, C) ≤ Δ₀(u, v), given v ∈ C`
    - `distFromCode_le_card_index_of_Nonempty`: `Δ₀(u, C) ≤ |ι|, given C is non-empty`
  5. Unique decoding radius:
    - `uniqueDecodingRadius C (UDR(C))`: The unique decoding radius of a code `C`
    - `relativeUniqueDecodingRadius C (relUDR(C))`:
      The relative unique decoding radius of a code `C`
    - `UDR_close_iff_exists_unique_close_codeword`:
      `Δ₀(u, C) ≤ UDR(C) ↔ ∃! v ∈ C, Δ₀(u, v) ≤ UDR(C)`
    - `UDRClose_iff_two_mul_proximity_lt_d_UDR`: `e ≤ UDR(C) ↔ 2 * e < ‖C‖₀`
    - `eq_of_le_uniqueDecodingRadius`
    - `UDR_close_iff_relURD_close`: `Δ₀(u, C) ≤ UDR(C) ↔ δᵣ(u, C) ≤ relUDR(C)`
    - `dist_le_UDR_iff_relDist_le_relUDR`:
      `e ≤ UDR(C) ↔ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ relUDR(C)`

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.

## Notes
- Implement `ENNRat (ℚ≥0∞)`, for usage in `relDistFromCode` and `relDistFromCode'`,
  as counterpart of `ENat (ℕ∞)` in `distFromCode` and `distFromCode'`.
-/


variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code
open NNReal

-- Notation for Hamming distance
/-- The **agreement set** of two `(ι → R)`-words: the coordinates where they agree.

This is the pointwise dual of `disagreementCols`. Its cardinality is the usual agreement
count, and it partitions the coordinate set with `hammingDist`; see
`agreementCols_card_add_hammingDist` and its two inequality corollaries below. -/
def agreementCols (u v : n → R) : Finset n :=
  Finset.filter (fun i => u i = v i) Finset.univ

@[simp]
lemma mem_agreementCols {u v : n → R} {i : n} :
    i ∈ agreementCols u v ↔ u i = v i := by
  simp [agreementCols]

/-- Agreement count plus Hamming distance partitions the coordinate set. -/
lemma agreementCols_card_add_hammingDist (u v : n → R) :
    (agreementCols u v).card + hammingDist u v = Fintype.card n := by
  classical
  simpa [agreementCols, hammingDist] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset n)) (p := fun i : n => u i = v i))

/-- The agreement count is the complement of the Hamming distance. -/
lemma agreementCols_card_eq_card_sub_hammingDist (u v : n → R) :
    (agreementCols u v).card = Fintype.card n - hammingDist u v := by
  have hpartition := agreementCols_card_add_hammingDist u v
  omega

/-- The Hamming distance is the complement of the agreement count. -/
lemma hammingDist_eq_card_sub_agreementCols_card (u v : n → R) :
    hammingDist u v = Fintype.card n - (agreementCols u v).card := by
  have hpartition := agreementCols_card_add_hammingDist u v
  omega

/-- A lower bound on agreement gives the complementary upper bound on Hamming distance. -/
lemma hammingDist_le_card_sub_of_agreementCols_card_ge {u v : n → R} {a : ℕ}
    (ha : a ≤ (agreementCols u v).card) :
    hammingDist u v ≤ Fintype.card n - a := by
  have hpartition := agreementCols_card_add_hammingDist u v
  omega

/-- A lower bound on Hamming distance gives the complementary upper bound on agreement. -/
lemma agreementCols_card_le_card_sub_of_hammingDist_ge {u v : n → R} {d : ℕ}
    (hd : d ≤ hammingDist u v) :
    (agreementCols u v).card ≤ Fintype.card n - d := by
  have hpartition := agreementCols_card_add_hammingDist u v
  omega

section Computable

variable {C : Set (n → R)} [Fintype C]

section

/-
- Note: We currently do not use `(E)Dist` as it forces the distance(s) into `ℝ`.
        Instead, we take some explicit notion of distance `δf`.
        Let us give this some thought.
-/

variable {α : Type*}
         {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

end

end Computable

end Code
