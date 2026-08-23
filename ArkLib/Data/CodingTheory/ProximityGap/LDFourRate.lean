/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.LDThresholdHalfDist
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2

/-!
# Four-rate Johnson/Elias bracket certificates for the faithful list-decoding threshold

`GrandChallengesLattice.lean` already provides the **exact** four-rate resolver
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`, which pins each per-rate faithful
list-decoding lattice threshold to a single index *when* the squared-Johnson certificate and
the Elias-volume certificate land on **adjacent** lattice indices `τ` and `τ + 1`.

At the actual ABF26 prize parameters the Johnson floor (`≈ 1 − √ρ`) and the
Elias/capacity ceiling (`≈ 1 − H_q(ρ) < 1 − ρ`) are separated by a constant fraction of
`n`, so the certified indices are *not* adjacent and the exact resolver does not apply.  The
honest, generally-applicable deliverable — requested as the fallback in issue #56 — is the
**bracket** form: from a squared-Johnson lower certificate at `τ_lo r` and an Elias-volume
upper certificate at `τ_hi r` (no adjacency required), conclude per rate

  `τ_lo r ≤ listLatticeThreshold (RS rate r) m ε* < τ_hi r`.

This file adds that LD-side bracket assembler, the exact list-decoding mirror of the
MCA-side `mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25`.  The remaining
content is exactly the per-rate numeric Johnson/Elias inequalities, isolated as hypotheses
indexed by the prize rate `r : Fin 4`.

## Main results

* `listPrizeLattice_bracketed_of_johnson_sq_and_elias` — the four-rate faithful list-decoding
  lattice bracket from a squared-Johnson lower certificate ⊕ an Elias-volume upper
  certificate, with the numeric inequalities isolated per rate.
* `listLatticeThreshold_bracketed_of_johnson_sq_and_elias` — the single-code bracket it is
  built from (Johnson lower ⊕ Elias upper on one Reed–Solomon code), useful on its own.

The nonemptiness hypotheses are dischargeable uniformly by
`listLatticeSet_nonempty_rs` (radius `0` always qualifies once `1 ≤ ε*·|F|`).
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Single-code Johnson/Elias bracket on the faithful list threshold.**
A squared-Johnson lower certificate at index `j_lo` and an Elias-volume upper certificate at
index `j_hi` bracket the genuine lattice threshold: `j_lo ≤ threshold < j_hi`.  No adjacency
is required, so this applies in the general (Johnson floor ≪ Elias ceiling) regime. -/
theorem listLatticeThreshold_bracketed_of_johnson_sq_and_elias
    (C : Submodule F (ι → F)) {m j_lo j_hi ℓ : ℕ}
    (hm : m ≠ 0)
    (hlo_le : j_lo ≤ Fintype.card ι)
    (hhi_pos : 0 < j_hi) (hhi_lt : j_hi < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j_lo : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j_lo : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist (C : Set (ι → F)) : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hvol : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            (((j_hi : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C)))
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    j_lo ≤ GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne ∧
      GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j_hi :=
  ⟨le_listLatticeThreshold_of_johnson_sq (C := (C : Set (ι → F))) (m := m)
      (j := j_lo) (ℓ := ℓ) hlo_le hq1 hP hsq hpow hne,
   listLatticeThreshold_lt_of_elias_volume (C := C) (m := m) (j := j_hi)
      hm hhi_pos hhi_lt hvol hne⟩

/-- **Four-rate faithful list-decoding lattice bracket from squared-Johnson ⊕ Elias-volume.**
For every ABF26 prize rate `r : Fin 4` (degree `k_r := ⌊prizeRates r · n⌋`), a squared-Johnson
lower certificate at lattice index `τ_lo r` and an Elias-volume upper certificate at index
`τ_hi r` bracket the faithful list-decoding lattice threshold of the rate-`r` Reed–Solomon code
between `τ_lo r` and `τ_hi r`.

This is the list-decoding mirror of `mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25`
and the non-adjacent generalisation of `listPrizeLatticeResolved_of_johnson_sq_and_elias_next`:
the remaining content is exactly the per-rate numeric Johnson/Elias inequalities, and no
adjacency between `τ_lo` and `τ_hi` is assumed (so it applies in the genuine prize regime where
the Johnson floor and the Elias ceiling are a constant fraction of `n` apart). -/
theorem listPrizeLattice_bracketed_of_johnson_sq_and_elias
    (domain : ι ↪ F) (m : ℕ)
    (τ_lo τ_hi : Fin 4 → ℕ)
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hlo_le : ∀ r : Fin 4, τ_lo r ≤ Fintype.card ι)
    (hhi_pos : ∀ r : Fin 4, 0 < τ_hi r)
    (hhi_lt : ∀ r : Fin 4, τ_hi r < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - τ_lo r : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - τ_lo r : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((τ_hi r : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    ∀ r : Fin 4,
      τ_lo r ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (hne r) ∧
        GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (hne r) < τ_hi r := fun r =>
  listLatticeThreshold_bracketed_of_johnson_sq_and_elias
    (C := ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j_lo := τ_lo r) (j_hi := τ_hi r) (ℓ := ℓ r)
    hm (hlo_le r) (hhi_pos r) (hhi_lt r) hq1 (hP r) (hsq r) (hpow r) (hvol r) (hne r)

/-! ## Fully unconditional four-rate sandwich

The Johnson/Elias bracket above is the sharpest current route but still needs
per-rate numeric certificates.  The half-distance floor and capacity ceiling from
`GrandChallengeLDThresholdHalfDist.lean` are weaker but unconditional once the
degree side conditions and the prize budget are in force.  The next theorem exposes
that completely discharged sandwich directly on the four ABF26 prize rates.
-/

/-- **Four-rate faithful LD sandwich from half distance and capacity.**

For every ABF26 prize rate `r`, with degree
`k_r = ⌊prizeRates r · |ι|⌋₊`, the canonical faithful list-decoding lattice threshold of
`RS(k_r)` lies between half the RS minimum-distance radius and the capacity radius:

`(|ι| - k_r) / 2 ≤ listLatticeThreshold RS(k_r) m ε* ≤ |ι| - k_r`.

This is weaker than the Johnson/Elias post-RIM frontier, but unlike that frontier it is
fully unconditional after the standard degree, interleaving, and budget side conditions. -/
theorem listPrizeLattice_bracketed_between_halfDist_and_capacity
    (domain : ι ↪ F) (m : ℕ)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hm : m ≠ 0)
    (hbudget : 1 ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hε : epsStar < 1) :
    ∀ r : Fin 4,
      let k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := listLatticeSet_nonempty_rs domain (hdeg_pos r).ne' (hdeg_le r) hbudget
      (Fintype.card ι - k) / 2 ≤
          GrandChallenges.listLatticeThreshold
            (ReedSolomon.code domain k : Set (ι → F)) m epsStar hne ∧
        GrandChallenges.listLatticeThreshold
            (ReedSolomon.code domain k : Set (ι → F)) m epsStar hne ≤
          Fintype.card ι - k := by
  intro r
  exact listLatticeThreshold_rs_between_halfDist_and_capacity
    (domain := domain)
    (deg := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (hdeg_pos r).ne' (hdeg_le r) hm hbudget hε

/-- Every ABF26 prize rate is at least `1/16`. -/
lemma one_sixteenth_le_prizeRates (r : Fin 4) : (1 / 16 : ℝ≥0) ≤ prizeRates r := by
  unfold prizeRates
  rw [show (16 : ℝ≥0) = 2 ^ (4 : ℕ) by norm_num]
  have hpow : (2 : ℝ≥0) ^ (r.val + 1) ≤ 2 ^ (4 : ℕ) :=
    pow_le_pow_right₀ one_le_two (by omega)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow

/-- Every ABF26 prize rate is at most `1/2`. -/
lemma prizeRates_le_half (r : Fin 4) : prizeRates r ≤ 1 / 2 := by
  unfold prizeRates
  have hpow : (2 : ℝ≥0) ^ (1 : ℕ) ≤ 2 ^ (r.val + 1) :=
    pow_le_pow_right₀ one_le_two (by omega)
  rw [pow_one] at hpow
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow

omit [Nonempty ι] [DecidableEq ι] in
/-- If the evaluation domain has at least two points, each prize degree is strictly
below the block length in the form `k_r + 1 ≤ n`. -/
lemma prizeRate_floor_add_one_le (r : Fin 4) (hn : 2 ≤ Fintype.card ι) :
    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι := by
  set k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have hkr : (k : ℝ≥0) ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
    rw [hk_def]
    refine le_trans (Nat.floor_le (zero_le _)) ?_
    gcongr
    exact prizeRates_le_half r
  have hcast : ((k + 1 : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (k : ℝ≥0) + 1
        ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) + 1 := by gcongr
      _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) +
            (1 / 2) * (Fintype.card ι : ℝ≥0) := by
          gcongr
          calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
            _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
                gcongr
                exact_mod_cast hn
      _ = (Fintype.card ι : ℝ≥0) := by
          rw [← add_mul]
          norm_num
  exact_mod_cast hcast

omit [Nonempty ι] [DecidableEq ι] in
/-- If the evaluation domain has at least sixteen points, every ABF26 prize degree is
positive. -/
lemma prizeRate_floor_pos_of_card_ge_sixteen (r : Fin 4) (hn : 16 ≤ Fintype.card ι) :
    0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ := by
  have hprod : ((1 : ℕ) : ℝ≥0) ≤ prizeRates r * (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (1 : ℝ≥0) = (1 / 16) * 16 := by norm_num
      _ ≤ prizeRates r * (Fintype.card ι : ℝ≥0) := by
          gcongr
          · exact one_sixteenth_le_prizeRates r
          · exact_mod_cast hn
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor hprod)

omit [Nonempty ι] [DecidableEq ι] in
/-- If the evaluation domain has at least two points, every ABF26 prize degree is at most
the block length. -/
lemma prizeRate_floor_le_card_of_two_le (r : Fin 4) (hn : 2 ≤ Fintype.card ι) :
    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι :=
  Nat.le_of_succ_le (prizeRate_floor_add_one_le r hn)

/-- **Four-rate faithful LD sandwich with prize-degree side conditions discharged.**

When `16 ≤ |ι|`, all four prize degrees are positive and at most the block length.  Thus the
unconditional half-distance/capacity sandwich needs only the interleaving, budget, and
`ε* < 1` hypotheses. -/
theorem exists_listPrizeLattice_bracketed_between_halfDist_and_capacity_of_card_ge_sixteen
    (domain : ι ↪ F) (m : ℕ) (hn : 16 ≤ Fintype.card ι)
    (hm : m ≠ 0)
    (hbudget : 1 ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hε : epsStar < 1) :
    ∀ r : Fin 4,
      let k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : (GrandChallenges.listLatticeSet
          (ReedSolomon.code domain k : Set (ι → F)) m epsStar).Nonempty,
        (Fintype.card ι - k) / 2 ≤
            GrandChallenges.listLatticeThreshold
              (ReedSolomon.code domain k : Set (ι → F)) m epsStar hne ∧
          GrandChallenges.listLatticeThreshold
              (ReedSolomon.code domain k : Set (ι → F)) m epsStar hne ≤
            Fintype.card ι - k := by
  intro r
  let k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  have hpos : 0 < k := by
    dsimp [k]
    exact prizeRate_floor_pos_of_card_ge_sixteen r hn
  have hle : k ≤ Fintype.card ι := by
    dsimp [k]
    exact prizeRate_floor_le_card_of_two_le r (by omega)
  let hne := listLatticeSet_nonempty_rs (m := m) domain hpos.ne' hle hbudget
  refine ⟨hne, ?_⟩
  exact listLatticeThreshold_rs_between_halfDist_and_capacity
    (domain := domain) (deg := k) (m := m) hpos.ne' hle hm hbudget hε

/-- **Johnson/Elias exact four-rate resolver with prize-degree side conditions discharged.**

The numerics-facing exact resolver in `GrandChallengesLattice` needs only the standard
Reed-Solomon degree side conditions.  For the four ABF26 prize rates, `16 ≤ |ι|` proves those
side conditions automatically, so the remaining hypotheses are the genuine Johnson/Elias
arithmetic certificates and the usual interleaving/budget witnesses. -/
theorem listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hn : 16 ≤ Fintype.card ι)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    GrandChallengesLattice.listPrizeLatticeResolved domain m τ := by
  refine
    GrandChallengesLattice.listPrizeLatticeResolved_of_johnson_sq_rsDegreeLe_and_elias_next
      domain m τ ℓ hm ?_ ?_ hnext hq1 hP hsq hpow hvol_next hne
  · intro r
    exact prizeRate_floor_pos_of_card_ge_sixteen r hn
  · intro r
    exact prizeRate_floor_le_card_of_two_le r (by omega)

/-- **Johnson/Elias exact resolver with all routine prize-side witnesses discharged.**

Compared with `listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next`, this also
constructs the canonical nonempty `listLatticeSet` witnesses from the budget hypothesis and uses
the automatic finite-field fact `1 < |F|`.  The remaining assumptions are precisely the real
Johnson/Elias arithmetic certificates and their interleaving budget. -/
theorem listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next_of_budget
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hn : 16 ≤ Fintype.card ι)
    (hm : m ≠ 0)
    (hbudget : 1 ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))) :
    GrandChallengesLattice.listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next
    domain m τ ℓ hn hm hnext Fintype.one_lt_card hP hsq hpow hvol_next ?_
  intro r
  exact listLatticeSet_nonempty_rs (m := m) domain
    (prizeRate_floor_pos_of_card_ge_sixteen r hn).ne'
    (prizeRate_floor_le_card_of_two_le r (by omega))
    hbudget

/-! ## Post-RIM frontier surface

The theorem above is the current faithful-LD value interface after the smooth-domain
RIM/AGL24 route has been refuted: future work should provide stronger lower and upper
certificates for the same lattice threshold, not a resurrection of the false universal
RIM full-rank premise.  The following small wrappers give that post-refutation target a
stable name and split the numeric cores out from the assembler theorem.
-/

/-- Numeric core of the squared-Johnson lower certificate at lattice index `j`.

This is the exact hypothesis consumed by
`listLatticeThreshold_bracketed_of_johnson_sq_and_elias`, named so post-RIM threshold
frontiers can target it without duplicating the full assembler statement. -/
def ListJohnsonSqLowerCore (C : Set (ι → F)) (j ℓ : ℕ) : Prop :=
  ((ℓ : ℝ) + 1)
      * ((((Fintype.card ι - j : ℕ) : ℝ)) -
          (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
    > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
      * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
          + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist C : ℕ) : ℝ) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))

/-- Numeric core of the Elias-volume upper certificate at lattice index `j`. -/
def ListEliasVolumeUpperCore (C : Submodule F (ι → F)) (j : ℕ)
    (ε_star : ℝ≥0) : Prop :=
  (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
    ENNReal.ofReal
      ((CodingTheory.hammingBallVolume (Fintype.card F)
          (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
          (Fintype.card ι) : ℝ)
        / (Fintype.card F : ℝ) ^
            ((Fintype.card ι : ℝ) - Module.finrank F C))

/-- Single-code bracket using the named post-RIM numeric cores. -/
theorem listLatticeThreshold_bracketed_of_johnson_sq_and_elias_core
    (C : Submodule F (ι → F)) {m j_lo j_hi ℓ : ℕ}
    (hm : m ≠ 0)
    (hlo_le : j_lo ≤ Fintype.card ι)
    (hhi_pos : 0 < j_hi) (hhi_lt : j_hi < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j_lo : ℕ) : ℝ))
    (hsq : ListJohnsonSqLowerCore (C : Set (ι → F)) j_lo ℓ)
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hvol : ListEliasVolumeUpperCore C j_hi ε_star)
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    j_lo ≤ GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne ∧
      GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j_hi :=
  listLatticeThreshold_bracketed_of_johnson_sq_and_elias
    (C := C) (m := m) (j_lo := j_lo) (j_hi := j_hi) (ℓ := ℓ)
    hm hlo_le hhi_pos hhi_lt hq1 hP hsq hpow hvol hne

/-- **Post-refutation four-rate LD threshold frontier.**

This packages the current honest route around the refuted smooth-domain RIM full-rank
program: a per-rate Johnson-side lower core, a per-rate Elias-side upper core, and the
budget/range hypotheses needed to bracket the faithful `listLatticeThreshold`.  It is a
frontier, not a resolution; proving sharper lower/upper fields here is the remaining
post-RIM Grand LD value work. -/
structure PostRIMListThresholdFrontier (domain : ι ↪ F) (m : ℕ) where
  τ_lo : Fin 4 → ℕ
  τ_hi : Fin 4 → ℕ
  ℓ : Fin 4 → ℕ
  hm : m ≠ 0
  hlo_le : ∀ r : Fin 4, τ_lo r ≤ Fintype.card ι
  hhi_pos : ∀ r : Fin 4, 0 < τ_hi r
  hhi_lt : ∀ r : Fin 4, τ_hi r < Fintype.card ι
  hq1 : 1 < Fintype.card F
  hP : ∀ r : Fin 4,
    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - τ_lo r : ℕ) : ℝ)
  hsq : ∀ r : Fin 4,
    ListJohnsonSqLowerCore
      (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (τ_lo r) (ℓ r)
  hpow : ∀ r : Fin 4,
    ((ℓ r : ENNReal)) ^ m ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal)
  hvol : ∀ r : Fin 4,
    ListEliasVolumeUpperCore
      (ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
      (τ_hi r) epsStar
  hne : ∀ r : Fin 4,
    (GrandChallenges.listLatticeSet
      (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar).Nonempty

/-- A post-RIM frontier gives the current certified four-rate faithful LD bracket. -/
theorem listPrizeLattice_bracketed_of_postRIM_frontier
    (domain : ι ↪ F) (m : ℕ)
    (frontier : PostRIMListThresholdFrontier domain m) :
    ∀ r : Fin 4,
      frontier.τ_lo r ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (frontier.hne r) ∧
        GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (frontier.hne r) < frontier.τ_hi r :=
  listPrizeLattice_bracketed_of_johnson_sq_and_elias
    (domain := domain) (m := m) (τ_lo := frontier.τ_lo)
    (τ_hi := frontier.τ_hi) (ℓ := frontier.ℓ) frontier.hm frontier.hlo_le
    frontier.hhi_pos frontier.hhi_lt frontier.hq1 frontier.hP frontier.hsq
    frontier.hpow frontier.hvol frontier.hne

/-! ## Non-vacuity: the certificate inequalities are concretely dischargeable

The per-rate hypotheses above are not vacuous: for a `[4, 2, 3]` code over `𝔽₃`
(`n = 4`, `q = 3`, `minDist = 3`, hence `n − minDist = k − 1 = 1`, `finrank = 2`), the
squared-Johnson inequality holds at lattice index `1` and the Elias-volume inequality holds
at index `2` (with `ℓ = 2`, `m = 1`, budget `ε* = 2/3`, so `ε*·q = 2 = ℓ^m`).  These are
*adjacent*, so on this instance the exact resolver
`listLatticeThreshold_eq_of_johnson_sq_and_elias_next` would pin the threshold to `1`.
The two witnesses below discharge the numeric cores by `norm_num` — including evaluating
the genuine `hammingBallVolume` definition — confirming the machinery fires.

At the *prize* rates `ρ ∈ {1/2, 1/4, 1/8, 1/16}` with `ε* = 2^{-128}` the Johnson floor
(`≈ 1 − √ρ`) and the Elias ceiling (`≈ 1 − H_q(ρ) < 1 − ρ`) are a constant fraction of `n`
apart, so the certified indices are *not* adjacent — there the bracket above is the
applicable form, and it is non-empty because `1 − √ρ < 1 − ρ` strictly for `ρ ∈ (0,1)`. -/

/-- **Squared-Johnson core is dischargeable.**  The optimal-β Johnson inequality at lattice
index `1` for a `[4,2,3]₃` code (`n=4`, `q=3`, `n−minDist = 1`, `ℓ=2`) holds — `25/3 > 16/3`. -/
theorem demo_johnson_sq_n4_q3 :
    ((2 : ℝ) + 1)
        * ((((4 - 1 : ℕ) : ℝ)) - (4 : ℝ) / 3) ^ 2
      > ((4 : ℝ) * (1 - 1 / 3))
        * ((4 : ℝ) * (1 - 1 / 3) + (2 : ℝ) * (((4 - 3 : ℕ) : ℝ) - (4 : ℝ) / 3)) := by
  norm_num

/-- **Elias-volume core is dischargeable**, evaluating the genuine `hammingBallVolume`
definition: at index `2` the Elias volume `Vol₃(2/4, 4) = 33` over `q^{n−k} = 3² = 9` gives
`11/3`, strictly above the budget `ε*·q = 2`. -/
theorem demo_elias_volume_n4_q3 :
    (2 : ℝ) <
      (CodingTheory.hammingBallVolume 3 ((2 : ℝ) / 4) 4 : ℝ) / (3 : ℝ) ^ (2 : ℕ) := by
  have hfloor : ⌊((2 : ℝ) / 4) * (4 : ℕ)⌋₊ = 2 := by
    norm_num
  rw [CodingTheory.hammingBallVolume, hfloor]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-! ## Axiom audit -/

set_option linter.style.longLine false

#print axioms ProximityGap.ListJohnsonSqLowerCore
#print axioms ProximityGap.ListEliasVolumeUpperCore
#print axioms ProximityGap.PostRIMListThresholdFrontier
#print axioms ProximityGap.listPrizeLattice_bracketed_between_halfDist_and_capacity
#print axioms ProximityGap.exists_listPrizeLattice_bracketed_between_halfDist_and_capacity_of_card_ge_sixteen
#print axioms ProximityGap.listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next
#print axioms ProximityGap.listPrizeLatticeResolved_of_card_ge_sixteen_johnson_sq_elias_next_of_budget
#print axioms ProximityGap.listLatticeThreshold_bracketed_of_johnson_sq_and_elias_core
#print axioms ProximityGap.listPrizeLattice_bracketed_of_postRIM_frontier

end ProximityGap
