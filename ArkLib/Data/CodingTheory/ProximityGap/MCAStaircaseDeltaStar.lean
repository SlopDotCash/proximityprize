/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.UniversalSpikeFloor
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-!
# The closed-form `δ*` on the granularity ladder (#357)

The two sides of the exact staircase — the master collapse
(`MCAStaircaseMaster.epsMCA_le_div_card_of_dist`: `ε_mca ≤ b/|F|` below `δ·n < b` at
support budget `3(b−1)`) and the universal spike floor
(`SpikeFloor.epsMCA_ge_j_div_card`: `ε_mca ≥ j/|F|` from `δ·n ≥ j−1` at budget `j`) —
invert into the threshold function itself.  For every linear code with the two distance
hypotheses and every target `ε*` in the band `[b/|F|, (b+1)/|F|)`:

  `mcaDeltaStar_eq_band_edge` :  `δ*(C, ε*) = b/n`  **exactly**.

Reading: `δ*(C, ε*) = ⌊ε*·|F|⌋/n` — the threshold function of the granularity ladder in
closed form.  The good-radius set is the half-open interval `[0, b/n)` (every radius
strictly below the band edge is good by the collapse; the band edge itself is bad by the
`(b+1)`-spike), so `δ*` sits at the edge and the supremum is not attained — the jump
phenomenon of the F₅ exact pin (`DeltaStarExactPinF5`), now at every band of every
sufficient-distance code.  Below the first band (`ε* < 1/|F|`) the good set is empty and
`δ* = 0` (`mcaDeltaStar_eq_zero_of_subfloor`).

`mcaDeltaStar_rs_eq_band_edge` / `mcaDeltaStar_rs_eq_zero_of_subfloor` instantiate at
Reed–Solomon via `rs_noWeightLE`: for every RS code with `k + 3(b−1) ≤ n`,
`k + b + 1 ≤ n`, `b + 1 ≤ |F|`,

  `δ*(RS[F, domain, k], ε*) = b/n` on `ε* ∈ [b/|F|, (b+1)/|F|)`.

**Honest scope.** This pins `δ*` exactly on the regime where the staircase is linear —
`ε*·|F|` up to roughly a third of the distance, i.e. radii below `(1−ρ)/3` for RS.  At the
production parameterization (`ε* = 2^-128`, `|F| ≈ 2^192⁺`) the band index `⌊ε*·|F|⌋` far
exceeds `n − k`, so the prize-window value of `δ*` is **not** decided by this theorem; the
open window `(1−√ρ, 1−ρ−Θ(1/log n))` of #357 §1 is untouched.  What this provides is the
first closed-form `δ*` over a code-and-`ε*` family: every `(C, ε*)` with
`⌊ε*·|F|⌋` inside the staircase regime now has its threshold as a single equality, with
both brackets meeting through the ledger combinator
(`mcaDeltaStar_eq_of_good_below_of_bad_above`).

## References
* Issue #357 (the δ* tracker); `MCAStaircaseMaster.lean`, `MCAStaircaseExact.lean`,
  `MCAStaircaseRS.lean` (the staircase sandwich), `UniversalSpikeFloor.lean` (the bad
  side), `MCAExactPin.lean` (the brackets-meet combinator).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAStaircaseDeltaStar

open ProximityGap.MCAStaircaseMaster
open ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The two `NoWeightLE` predicates (master / spike-floor namespaces) are the same
statement. -/
theorem spikeFloor_noWeightLE {C : Submodule F (ι → A)} {m : ℕ}
    (h : NoWeightLE C m) : ProximityGap.SpikeFloor.NoWeightLE C m :=
  fun w hw hsupp => h w hw hsupp

open Classical in
/-- **The closed-form `δ*` on the granularity ladder.** For every linear code with no
nonzero codeword on `≤ 3(b−1)` points (the collapse budget) nor on `≤ b+1` points (the
spike budget), and every target `ε*` in the band `[b/|F|, (b+1)/|F|)`:

  `δ*(C, ε*) = b/n`.

Good below the edge by the master collapse, bad at and above it by the `(b+1)`-spike; the
brackets meet through `mcaDeltaStar_eq_of_good_below_of_bad_above`.  Reading:
`δ* = ⌊ε*·|F|⌋/n` wherever the staircase is linear. -/
theorem mcaDeltaStar_eq_band_edge (C : Submodule F (ι → A)) {b : ℕ} (hb : 1 ≤ b)
    (hC3 : NoWeightLE C (3 * (b - 1))) (hCs : NoWeightLE C (b + 1))
    (hnb : b + 1 ≤ Fintype.card ι) (hbF : b + 1 ≤ Fintype.card F)
    [Nontrivial A] {εstar : ℝ≥0∞}
    (hεlo : (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hεhi : εstar < ((b + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar
      = (b : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  have hn0 : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  refine mcaDeltaStar_eq_of_good_below_of_bad_above (C : Set (ι → A)) εstar ?_ ?_ ?_
  · -- the band edge lies in [0, 1]
    rw [div_le_one hn0]
    exact_mod_cast (by omega : b ≤ Fintype.card ι)
  · -- good strictly below the edge: the master collapse
    intro δ hδ
    have hδn : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0) := (lt_div_iff₀ hn0).mp hδ
    exact le_trans (epsMCA_le_div_card_of_dist C b hb hC3 (by omega) hδn) hεlo
  · -- bad at and above the edge: the (b+1)-spike floor
    intro δ hδ
    have hδn : (b : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := (div_le_iff₀ hn0).mp hδ
    obtain ⟨p⟩ : Nonempty (Fin (b + 1) ↪ ι) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hnb)
    obtain ⟨a⟩ : Nonempty (Fin (b + 1) ↪ F) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hbF)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    refine lt_of_lt_of_le hεhi ?_
    refine ProximityGap.SpikeFloor.epsMCA_ge_j_div_card (j := b + 1) C
      (spikeFloor_noWeightLE hCs) ?_ (by omega) hnb p a hv
    have hcast : ((b + 1 - 1 : ℕ) : ℝ≥0) = (b : ℝ≥0) := by norm_num
    rw [hcast]
    exact hδn

open Classical in
/-- **The degenerate row:** below the universal floor (`ε* < 1/|F|`) every radius is bad
(the `1`-spike fires at every `δ`), so the good set is empty and `δ*(C, ε*) = 0` — for
every linear code with no nonzero weight-1 codeword (distance `≥ 2`). -/
theorem mcaDeltaStar_eq_zero_of_subfloor (C : Submodule F (ι → A))
    (hC1 : NoWeightLE C 1) [Nontrivial A] {εstar : ℝ≥0∞}
    (hε : εstar < 1 / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar = 0 := by
  refine mcaDeltaStar_eq_zero_of_all_bad (C : Set (ι → A)) εstar fun δ => ?_
  obtain ⟨p⟩ : Nonempty (Fin 1 ↪ ι) :=
    Function.Embedding.nonempty_of_card_le
      (by simp only [Fintype.card_fin]; exact Fintype.card_pos)
  obtain ⟨a⟩ : Nonempty (Fin 1 ↪ F) :=
    Function.Embedding.nonempty_of_card_le
      (by simp only [Fintype.card_fin]; exact Fintype.card_pos)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  refine lt_of_lt_of_le ?_
    (ProximityGap.SpikeFloor.epsMCA_ge_j_div_card (j := 1) C
      (spikeFloor_noWeightLE hC1) (by simp) le_rfl
      (Fintype.card_pos (α := ι)) p a hv)
  simpa using hε

open ProximityGap.MCAStaircaseRS

open Classical in
/-- **The closed-form `δ*` for Reed–Solomon.** For every RS code with
`k + 3(b−1) ≤ n`, `k + b + 1 ≤ n`, `b + 1 ≤ |F|`, and every
`ε* ∈ [b/|F|, (b+1)/|F|)`:

  `δ*(RS[F, domain, k], ε*) = b/n`.

The threshold function of the prize code family is `⌊ε*·|F|⌋/n` in closed form throughout
the staircase regime (radii below roughly `(1−ρ)/3`). -/
theorem mcaDeltaStar_rs_eq_band_edge (domain : ι ↪ F) {k b : ℕ} (hb : 1 ≤ b)
    (hk : 1 ≤ k) (hkb3 : k + 3 * (b - 1) ≤ Fintype.card ι)
    (hkb1 : k + b + 1 ≤ Fintype.card ι) (hbF : b + 1 ≤ Fintype.card F)
    {εstar : ℝ≥0∞}
    (hεlo : (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hεhi : εstar < ((b + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) εstar
      = (b : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  refine mcaDeltaStar_eq_band_edge (ReedSolomon.code domain k) hb
    (rs_noWeightLE domain hkb3) (rs_noWeightLE domain (by omega)) (by omega) hbF hεlo hεhi

open Classical in
/-- **The degenerate RS row:** `ε* < 1/|F|` forces `δ*(RS[F, domain, k], ε*) = 0`
whenever `k + 1 ≤ n`. -/
theorem mcaDeltaStar_rs_eq_zero_of_subfloor (domain : ι ↪ F) {k : ℕ}
    (hk1 : k + 1 ≤ Fintype.card ι) {εstar : ℝ≥0∞}
    (hε : εstar < 1 / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) εstar = 0 :=
  mcaDeltaStar_eq_zero_of_subfloor (ReedSolomon.code domain k)
    (rs_noWeightLE domain hk1) hε

/-! ## Source audit -/

#print axioms mcaDeltaStar_eq_band_edge
#print axioms mcaDeltaStar_eq_zero_of_subfloor
#print axioms mcaDeltaStar_rs_eq_band_edge
#print axioms mcaDeltaStar_rs_eq_zero_of_subfloor

end ProximityGap.MCAStaircaseDeltaStar
