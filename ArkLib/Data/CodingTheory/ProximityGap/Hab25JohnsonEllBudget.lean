/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonNumericBridge

/-!
# Hab25 §3 — numeric legs at the Johnson list size (#301/#302)

The S11 producers (`JohnsonNumericBound.of_card_le_nat`,
`JohnsonNumericBound.of_algebraic_cover_nat`, `johnsonNumericBound_of_affine_capture_of_list_le`)
all consume one remaining *numeric* side condition: the per-stack factor budget `L` (resp. the
algebraic datum's `ℓ`) must satisfy the closed-form `ℓ`-budget
`L ≤ 2(m+½)⁵ / (3ρ₊^{3/2})`. The natural value the GS analysis produces is the **Johnson list
size** `ℓJ := (m+½)/√ρ₊` (paper S3, `D_Y < ℓ`). This file discharges the numeric leg at that
value by elementary real arithmetic:

* `hab25JohnsonEll` — the Johnson list-size value `(m+½)/√ρ₊` as a named definition;
* `hab25RhoPlus_le_one` / `one_le_hab25JohnsonEll` — basic range facts for `k + 1 ≤ n`;
* `mul_hab25JohnsonEll_le_budget` — **the numeric leg**: `c·ℓJ` is within the `ℓ`-budget for
  any `c ≤ 100` (the key comparison is `3·c·ρ₊ ≤ 2(m+½)⁴`, true since `m ≥ 3`, `ρ₊ ≤ 1`);
* `hab25JohnsonEll_le_budget` / `hab25JohnsonEll_ceil_le_budget` — the `c = 1` and ceiling
  (`⌈ℓJ⌉₊ ≤ ℓJ + 1 ≤ 2·ℓJ`) instances;
* `nat_mul_card_div_le_johnsonBoundReal_of_le_johnsonEll` — the S11 scaled comparison
  `(L·n)/|F| ≤ johnsonBoundReal` for every `L ≤ ⌈ℓJ⌉₊`, with **no numeric side condition**;
* `johnsonNumericBound_of_card_le_johnsonEll` /
  `johnsonNumericBound_of_algebraic_cover_johnsonEll` — `JohnsonNumericBound` producers whose
  only remaining inputs are the *combinatorial* counts (`≤ L·n` bad scalars per stack, resp.
  the algebraic cover with `ℓ ≤ ⌈ℓJ⌉₊`): the numeric edge is gone.

Also the S9 numeric leg of `Hab25Johnson.lean` (`hClaim1Num`, the docstring's
`claim1_bound` step `n ≤ (ℓ⁶/3)·(ρ₊n)²` once `ℓ⁶·ρ₊²·n ≥ 3`):

* `claim1_relax` — the generic relaxation `3 ≤ ℓ⁶ρ²n → n ≤ (ℓ⁶/3)(ρn)²`;
* `hab25_claim1Num` — `3 ≤ ℓJ⁶·ρ₊²·n` holds outright (since `ℓJ⁶ρ₊² = (m+½)⁶/ρ₊ ≥ 3.5⁶`);
* `hab25_claim1_bound` — hence S9's `n ≤ (ℓJ⁶/3)·(ρ₊n)²` with no hypothesis beyond
  `0 < n`, `k + 1 ≤ n`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal Polynomial

attribute [local instance] Classical.propDecidable

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- The **Johnson list-size value** `ℓJ = (m+½)/√ρ₊` — the `ℓ` the Hab25/BCHKS25 GS analysis
actually produces in S3 (`D_Y < ℓ`). -/
noncomputable def hab25JohnsonEll (n k : ℕ) (η : ℝ≥0) : ℝ :=
  (hab25M n k η + 1 / 2) / hab25RhoPlus n k ^ ((1 : ℝ) / 2)

/-- For a genuine RS code (`k + 1 ≤ n`), the rate-plus parameter is at most `1`. -/
theorem hab25RhoPlus_le_one {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) :
    hab25RhoPlus n k ≤ 1 := by
  rw [hab25RhoPlus, ← add_div, div_le_one (by exact_mod_cast hn)]
  exact_mod_cast hkn

/-- The Johnson list size is at least `1` (indeed at least `m + ½ ≥ 3.5`). -/
theorem one_le_hab25JohnsonEll {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    (1 : ℝ) ≤ hab25JohnsonEll n k η := by
  have hρpos := hab25RhoPlus_pos hn k
  have hρ1 := hab25RhoPlus_le_one hn hkn
  have h12pos : (0 : ℝ) < hab25RhoPlus n k ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hρpos _
  have h12le : hab25RhoPlus n k ^ ((1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one hρpos.le hρ1 (by norm_num)
  have hm3 := hab25M_ge_three n k η
  rw [hab25JohnsonEll, le_div_iff₀ h12pos, one_mul]
  linarith

/-- **The S11 numeric leg at the Johnson list size**: any constant multiple `c·ℓJ` with
`c ≤ 100` is within the closed-form `ℓ`-budget `2(m+½)⁵/(3ρ₊^{3/2})`. The core comparison is
`3·c·ρ₊·(m+½) ≤ 2(m+½)⁵`, which holds since `ρ₊ ≤ 1` and `2(m+½)⁴ ≥ 2·3.5⁴ > 300`. -/
theorem mul_hab25JohnsonEll_le_budget {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 100) :
    c * hab25JohnsonEll n k η ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 / (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  have hρpos := hab25RhoPlus_pos hn k
  have hρ1 := hab25RhoPlus_le_one hn hkn
  have hm3 := hab25M_ge_three n k η
  have hmpos : (0 : ℝ) < hab25M n k η + 1 / 2 := by linarith
  have h12pos : (0 : ℝ) < hab25RhoPlus n k ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hρpos _
  have hden : (0 : ℝ) < 3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2) := by
    have := Real.rpow_pos_of_pos hρpos ((3 : ℝ) / 2)
    linarith
  have hsplit : hab25RhoPlus n k ^ ((3 : ℝ) / 2)
      = hab25RhoPlus n k * hab25RhoPlus n k ^ ((1 : ℝ) / 2) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hρpos, Real.rpow_one]
  have h4 : ((7 : ℝ) / 2) ^ 4 ≤ (hab25M n k η + 1 / 2) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hkey : 3 * hab25RhoPlus n k * (c * (hab25M n k η + 1 / 2)) ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 := by
    have h1 : 3 * hab25RhoPlus n k * (c * (hab25M n k η + 1 / 2)) ≤
        3 * c * (hab25M n k η + 1 / 2) := by
      nlinarith [mul_nonneg hc0 hmpos.le, hρ1, hρpos.le]
    have h2 : 3 * c * (hab25M n k η + 1 / 2) ≤ 2 * (hab25M n k η + 1 / 2) ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_right h4 hmpos.le, hc, hc0, hmpos.le]
    linarith
  rw [hab25JohnsonEll, ← mul_div_assoc, div_le_div_iff₀ h12pos hden, hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hkey h12pos.le]

/-- The `c = 1` instance: the Johnson list size itself is within the `ℓ`-budget. -/
theorem hab25JohnsonEll_le_budget {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    hab25JohnsonEll n k η ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 / (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  simpa using mul_hab25JohnsonEll_le_budget hn hkn η
    (c := 1) (by norm_num) (by norm_num)

/-- The ceiling instance: `⌈ℓJ⌉₊` is within the `ℓ`-budget (`⌈ℓJ⌉₊ < ℓJ + 1 ≤ 2·ℓJ`,
using `ℓJ ≥ 1`). This is the natural-number form the S11 cardinality bridge consumes. -/
theorem hab25JohnsonEll_ceil_le_budget {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    ((⌈hab25JohnsonEll n k η⌉₊ : ℕ) : ℝ) ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 / (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  have hx1 := one_le_hab25JohnsonEll hn hkn η
  have h2 := mul_hab25JohnsonEll_le_budget hn hkn η (c := 2) (by norm_num) (by norm_num)
  have hceil : ((⌈hab25JohnsonEll n k η⌉₊ : ℕ) : ℝ) < hab25JohnsonEll n k η + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  linarith

/-- **The S11 scaled comparison with NO numeric side condition**: for any per-stack factor
budget `L ≤ ⌈ℓJ⌉₊`, the scaled count satisfies `(L·n)/|F| ≤ johnsonBoundReal`. -/
theorem nat_mul_card_div_le_johnsonBoundReal_of_le_johnsonEll
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hkn : k + 1 ≤ Fintype.card ι₀)
    (hL : L ≤ ⌈hab25JohnsonEll (Fintype.card ι₀) k η⌉₊) :
    ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ :=
  nat_mul_card_div_le_johnsonBoundReal domain k η δ L
    (le_trans (by exact_mod_cast hL)
      (hab25JohnsonEll_ceil_le_budget Fintype.card_pos hkn η))

/-- **`JohnsonNumericBound` from a per-stack count at the Johnson list size**: a uniform
bad-scalar count `≤ L·n` with `L ≤ ⌈ℓJ⌉₊` discharges the Hab25 numeric residual outright —
the numeric edge `hNdiv` of `JohnsonNumericBound.of_card_le_nat` is supplied by elementary
arithmetic. Only the combinatorial count remains. -/
theorem johnsonNumericBound_of_card_le_johnsonEll
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hkn : k + 1 ≤ Fintype.card ι₀)
    (hL : L ≤ ⌈hab25JohnsonEll (Fintype.card ι₀) k η⌉₊)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ L * Fintype.card ι₀) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_card_le_nat domain k η δ (L * Fintype.card ι₀)
    (nat_mul_card_div_le_johnsonBoundReal_of_le_johnsonEll domain k η δ L hkn hL) hN

/-- **`JohnsonNumericBound` from algebraic covers at the Johnson list size**: per-stack
GS-over-`F(Z)` covers whose factor count satisfies the paper's S3 budget `ℓ ≤ ⌈ℓJ⌉₊`
discharge the numeric residual — the `hNdiv` side condition of
`JohnsonNumericBound.of_algebraic_cover_nat` is supplied by elementary arithmetic. -/
theorem johnsonNumericBound_of_algebraic_cover_johnsonEll
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η)
    (hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ)
    (hkn : k + 1 ≤ Fintype.card ι₀)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ ≤ ⌈hab25JohnsonEll (Fintype.card ι₀) k η⌉₊) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_algebraic_cover_nat domain k η δ
    (⌈hab25JohnsonEll (Fintype.card ι₀) k η⌉₊ * Fintype.card ι₀) hη hδ
    (nat_mul_card_div_le_johnsonBoundReal_of_le_johnsonEll domain k η δ _ hkn le_rfl)
    (fun u => by
      obtain ⟨A, hsub, hAℓ⟩ := hAlg u
      exact ⟨A, hsub, Nat.mul_le_mul_right _ hAℓ⟩)

/-! ## The S9 numeric leg (`hClaim1Num` / `claim1_bound` of `Hab25Johnson.lean`) -/

/-- **The generic S9 relaxation**: once the regime inequality `ℓ⁶·ρ²·n ≥ 3` holds, the
per-factor count `n` relaxes into the paper's closed form `(ℓ⁶/3)·(ρn)²`. Pure real
arithmetic. -/
theorem claim1_relax {l ρ n : ℝ} (hn : 0 ≤ n) (h : 3 ≤ l ^ 6 * ρ ^ 2 * n) :
    n ≤ l ^ 6 / 3 * (ρ * n) ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_right h hn]

/-- **The S9 regime inequality `hClaim1Num` holds outright at the Johnson list size**:
`ℓJ⁶·ρ₊²·n ≥ 3`, since `ℓJ⁶·ρ₊² = (m+½)⁶/ρ₊ ≥ (m+½)⁶ ≥ 3.5⁶ > 3` and `n ≥ 1`. -/
theorem hab25_claim1Num {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    (3 : ℝ) ≤ hab25JohnsonEll n k η ^ 6 * hab25RhoPlus n k ^ 2 * n := by
  have hρpos := hab25RhoPlus_pos hn k
  have hρ1 := hab25RhoPlus_le_one hn hkn
  have hm3 := hab25M_ge_three n k η
  have hmpos : (0 : ℝ) < hab25M n k η + 1 / 2 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h6 : (hab25RhoPlus n k ^ ((1 : ℝ) / 2)) ^ (6 : ℕ) = hab25RhoPlus n k ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (hab25RhoPlus n k ^ ((1 : ℝ) / 2)) 6,
      ← Real.rpow_mul hρpos.le, ← Real.rpow_natCast (hab25RhoPlus n k) 3]
    norm_num
  rw [hab25JohnsonEll, div_pow, h6]
  have hρ3pos : (0 : ℝ) < hab25RhoPlus n k ^ (3 : ℕ) := by positivity
  have hfrac : (1 : ℝ) ≤ hab25RhoPlus n k ^ 2 / hab25RhoPlus n k ^ (3 : ℕ) := by
    rw [le_div_iff₀ hρ3pos, one_mul]
    nlinarith [hρ1, hρpos.le, sq_nonneg (hab25RhoPlus n k)]
  have hm6 : ((7 : ℝ) / 2) ^ 6 ≤ (hab25M n k η + 1 / 2) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 6
  have e1 : (3 : ℝ) ≤ (hab25M n k η + 1 / 2) ^ 6 := by nlinarith [hm6]
  have e2 : (hab25M n k η + 1 / 2) ^ 6 ≤
      (hab25M n k η + 1 / 2) ^ 6 * (hab25RhoPlus n k ^ 2 / hab25RhoPlus n k ^ (3 : ℕ)) :=
    le_mul_of_one_le_right (by positivity) hfrac
  have e3 : (hab25M n k η + 1 / 2) ^ 6 * (hab25RhoPlus n k ^ 2 / hab25RhoPlus n k ^ (3 : ℕ)) ≤
      (hab25M n k η + 1 / 2) ^ 6 * (hab25RhoPlus n k ^ 2 / hab25RhoPlus n k ^ (3 : ℕ)) *
        (n : ℝ) :=
    le_mul_of_one_le_right (by positivity) hn1
  calc (3 : ℝ) ≤ (hab25M n k η + 1 / 2) ^ 6 *
        (hab25RhoPlus n k ^ 2 / hab25RhoPlus n k ^ (3 : ℕ)) * (n : ℝ) := by linarith
    _ = (hab25M n k η + 1 / 2) ^ 6 / hab25RhoPlus n k ^ (3 : ℕ) *
        hab25RhoPlus n k ^ 2 * (n : ℝ) := by ring

/-- **S9 (`claim1_bound`) with the numeric leg discharged**: the per-factor count `n` is
within the paper's closed form `(ℓJ⁶/3)·(ρ₊n)²`, with no hypothesis beyond `0 < n` and
`k + 1 ≤ n`. This realizes the `claim1_bound`-modulo-`hClaim1Num` step documented in
`Hab25Johnson.lean` (S9) at the Johnson list size. -/
theorem hab25_claim1_bound {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    (n : ℝ) ≤ hab25JohnsonEll n k η ^ 6 / 3 * (hab25RhoPlus n k * n) ^ 2 :=
  claim1_relax (Nat.cast_nonneg n) (hab25_claim1Num hn hkn η)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25RhoPlus_le_one
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.one_le_hab25JohnsonEll
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mul_hab25JohnsonEll_le_budget
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25JohnsonEll_le_budget
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25JohnsonEll_ceil_le_budget
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.nat_mul_card_div_le_johnsonBoundReal_of_le_johnsonEll
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_card_le_johnsonEll
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_algebraic_cover_johnsonEll
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.claim1_relax
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25_claim1Num
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25_claim1_bound
