/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding

/-!
# The Johnson-regime discharge of the sub-Johnson list COUNT (#389)

`SubJohnsonListSupply.lean` names the open core of #389 as `SubJohnsonListBound dom k m L A`:
for every word `w`, the RS codewords agreeing with `w` on `≥ k+m+1` points number `≤ L`, each
agreeing on `≤ A` points.  The downstream wiring
(`explainableCoreSupply_of_listBound`) is proven; only the list bound is open.

That open obligation has TWO independent parameters: the agreement CAP `A` (each codeword's
agreement size) and the list COUNT `L` (how many codewords reach the band).  The agreement cap is
trivially `A = n` (no codeword agrees on more than `n` points).  This file discharges the COUNT `L`
**in the Johnson regime** — the regime where the classical Johnson list-decoding bound applies — by
wiring the in-tree Finset-form Johnson bound (`ArkLib.CS25.rs_list_size_le`,
`CodeGeometry.card_le_of_johnson_sq_dist`) to the named residual.

## The bridge (the new brick)

The named residual is stated in AGREEMENT form (`agree ≥ k+m+1`) over the `rsCode` **submodule**;
the in-tree Johnson bound is stated in DISTANCE form (`hammingDist ≤ e`) over the `rsCodeFinset`.
The translation `agree c w + hammingDist c w = n` (`CodeGeometry.agree_add_hammingDist`) turns
`agree c w ≥ k+m+1` into `hammingDist c w ≤ n − (k+m+1)`, and `mem_rsCode_iff_mem_code` identifies
the two carriers.  Hence

> **`bigAgreeCodewords dom k m w  ⊆  (rsCodeFinset dom k).filter (hammingDist · w ≤ n−(k+m+1))`**
> (`bigAgreeCodewords_subset_rs_ball`),

and the Johnson bound on the RHS (`rs_list_size_le` at `e = n−(k+m+1)`) transfers to the LHS:

> **`johnsonRegime_count`** : under the Johnson squared condition at `e = n−(k+m+1)`,
> `(bigAgreeCodewords dom k m w).card ≤ ℓ`.

Packaged as the named residual with the trivial agreement cap `A = n`:

> **`subJohnsonListBound_johnsonRegime`** : the Johnson squared condition (uniform in `w`) ⟹
> `SubJohnsonListBound dom k m ℓ n`.

## Scope (rule 3 / rule 6, honesty contract)

This is **NOT a CORE closure** and **NOT thinness-essential**: it is the *classical* Johnson
list-decoding bound, valid for EVERY linear MDS code, transported to this file's named residual.
It discharges the list COUNT **only inside the Johnson radius** — exactly the regime where
list-decoding is already known.  The prize regime is **strictly beyond** Johnson
(`DeepBandProductionSubJohnson`: the production band is strictly sub-Johnson, so the Johnson
squared condition `hsq` FAILS there for the relevant `ℓ` — this brick's hypothesis is unmet in the
prize band).  The genuinely-open content — a list bound at the *beyond*-Johnson radius over the thin
subgroup `μ_n` — is untouched: `SubJohnsonListBound` at the prize `m` stays OPEN.  No capacity /
beyond-Johnson / growth-law claim; ASYMPTOTIC GUARD untouched.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Carrier bridge.** The `rsCode` submodule of `GranularityLadderRS` and `ReedSolomon.code`
have the SAME carrier (both are `{P.eval ∘ dom : P.degree < k}`). -/
theorem mem_rsCode_iff_mem_code (dom : Fin n ↪ F) (k : ℕ) (w : Fin n → F) :
    w ∈ (rsCode dom k : Submodule F (Fin n → F)) ↔ w ∈ ReedSolomon.code dom k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  constructor
  · rintro ⟨P, hPdeg, rfl⟩
    exact ⟨P, hPdeg, by funext i; rfl⟩
  · rintro ⟨P, hPdeg, rfl⟩
    exact ⟨P, hPdeg, by funext i; rfl⟩

open Classical in
/-- **The agreement→distance ball inclusion.** A codeword agreeing with `w` on `≥ k+m+1` points is
an RS codeword within Hamming distance `n−(k+m+1)` of `w`. -/
theorem bigAgreeCodewords_subset_rs_ball (dom : Fin n ↪ F) (k m : ℕ) (w : Fin n → F) :
    bigAgreeCodewords dom k m w
      ⊆ (ArkLib.CS25.rsCodeFinset dom k).filter
          (fun c => hammingDist c w ≤ n - (k + m + 1)) := by
  intro c hc
  rw [bigAgreeCodewords, Finset.mem_filter] at hc
  obtain ⟨-, hcmem, hcagree⟩ := hc
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [ArkLib.CS25.mem_rsCodeFinset]
    exact (mem_rsCode_iff_mem_code dom k c).mp hcmem
  · -- agree c w = (listAgreeSet c w).card ≥ k+m+1 and agree + dist = n ⟹ dist ≤ n−(k+m+1)
    have hbridge : CodeGeometry.agree c w + hammingDist c w = Fintype.card (Fin n) :=
      CodeGeometry.agree_add_hammingDist c w
    have hcard_eq : CodeGeometry.agree c w = (listAgreeSet c w).card := by
      rw [CodeGeometry.agree, listAgreeSet]
    rw [Fintype.card_fin] at hbridge
    have hge : k + m + 1 ≤ (listAgreeSet c w).card := hcagree
    omega

open Classical in
/-- **THE JOHNSON-REGIME COUNT.** Under the Johnson squared condition at agreement radius
`e = n − (k+m+1)`, the number of codewords agreeing with `w` on `≥ k+m+1` points is `≤ ℓ`.
(The classical Johnson list-decoding bound, transported to `bigAgreeCodewords`.) -/
theorem johnsonRegime_count (dom : Fin n ↪ F) (k m ℓ : ℕ) [NeZero k] (w : Fin n → F)
    (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)
        ≤ ((Fintype.card (Fin n) - (n - (k + m + 1)) : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card (Fin n) - (n - (k + m + 1)) : ℕ) : ℝ)
          - (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card (Fin n) : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card (Fin n) : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ)
              * (((Fintype.card (Fin n)
                    - (Fintype.card (Fin n) - (k - 1)) : ℕ) : ℝ)
                - (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)))) :
    (bigAgreeCodewords dom k m w).card ≤ ℓ := by
  have hn : 0 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hball :=
    ArkLib.CS25.rs_list_size_le (ι := Fin n) dom k hq1 hn w (n - (k + m + 1)) ℓ hP hsq
  exact le_trans (Finset.card_le_card (bigAgreeCodewords_subset_rs_ball dom k m w)) hball

open Classical in
/-- **THE NAMED RESIDUAL, Johnson regime.** If the Johnson squared condition holds uniformly over
all words `w` (at agreement radius `n−(k+m+1)`), the named residual `SubJohnsonListBound` holds with
list count `L = ℓ` and the trivial agreement cap `A = n`. This discharges the COUNT of the open core
inside the Johnson radius; the prize regime is strictly beyond Johnson (where `hsq` fails). -/
theorem subJohnsonListBound_johnsonRegime (dom : Fin n ↪ F) (k m ℓ : ℕ) [NeZero k]
    (hq1 : 1 < Fintype.card F)
    (hJohnson : ∀ w : Fin n → F,
      (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)
          ≤ ((Fintype.card (Fin n) - (n - (k + m + 1)) : ℕ) : ℝ)
      ∧ ((ℓ : ℝ) + 1)
          * (((Fintype.card (Fin n) - (n - (k + m + 1)) : ℕ) : ℝ)
            - (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card (Fin n) : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card (Fin n) : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ : ℝ)
                * (((Fintype.card (Fin n)
                      - (Fintype.card (Fin n) - (k - 1)) : ℕ) : ℝ)
                  - (Fintype.card (Fin n) : ℝ) / (Fintype.card F : ℝ)))) :
    SubJohnsonListBound dom k m ℓ n := by
  intro w
  refine ⟨johnsonRegime_count dom k m ℓ w hq1 (hJohnson w).1 (hJohnson w).2, ?_⟩
  intro c _hc
  -- the agreement cap A = n is trivial: any agreement set is a subset of univ (card n)
  calc (listAgreeSet c w).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mem_rsCode_iff_mem_code
#print axioms ProximityGap.Ownership.bigAgreeCodewords_subset_rs_ball
#print axioms ProximityGap.Ownership.johnsonRegime_count
#print axioms ProximityGap.Ownership.subJohnsonListBound_johnsonRegime
