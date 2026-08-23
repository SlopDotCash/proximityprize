/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.AgreementCount

/-!
# Good-set aggregation: `|G| ≤ L · k · |ι|` ([BCIKS20] §6 fibre double-count)

Aggregates the per-codeword agreement-count bound `card_curveAgreement_le` over the fibres of a
close-codeword selector `cw`. If no selected codeword has permanent agreement with the curve on
`≥ |ι| - e` coordinates, then `|G| ≤ L · (k·|ι|)` where `L = |G.image cw|` is the curve list size.
Its contrapositive (`exists_heavy_codeword_of_goodSet_card_gt`) is the counting core of
`jointAgreement_of_close_codeword_pigeonhole`. This makes the §6 aggregation step explicit; it is an
*upper* bound on `|G|` — the open `RSCurveListSizeResidual` (the *small-`L`* trivariate-GS content)
is not supplied by this.
-/


open Finset BigOperators

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Good-set ≤ list-size × per-codeword budget** ([BCIKS20] §6 aggregation step).

Aggregating the per-codeword agreement-count bound `card_curveAgreement_le` over the fibres of a
close-codeword selector `cw : F → ι → F`: if no selected codeword has *permanent* agreement with
the curve on `≥ |ι| - e` coordinates (the "no heavy codeword" condition, i.e. `¬ jointAgreement`'s
shadow), then the good set is bounded by the number of distinct selected codewords times `k·|ι|`:

  `|G| ≤ L · (k · |ι|)`,  where `L = |G.image cw|`.

This is the forward (double-count) direction underlying the pigeonhole
`jointAgreement_of_close_codeword_pigeonhole`: its contrapositive is exactly "`|G| > L·k·|ι| ⟹
some selected codeword is heavy ⟹ joint agreement". The bound makes the §6 fibre aggregation
explicit. (It is an *upper* bound on `|G|`; the open residual `RSCurveListSizeResidual` is the
*small-`L`* trivariate-GS content, which this does not supply.) -/
theorem curve_goodSet_card_le_listSize_mul {k : ℕ} (u : Fin (k + 1) → ι → F) (e : ℕ)
    (G : Finset F) (cw : F → ι → F)
    (hcw_agree : ∀ z ∈ G, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = cw z i)).card)
    (hnoperm : ∀ c ∈ G.image cw,
      (Finset.univ.filter (fun i => ∀ z : F,
        ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card < Fintype.card ι - e) :
    G.card ≤ (G.image cw).card * (k * Fintype.card ι) := by
  classical
  -- partition G into fibres of cw
  rw [Finset.card_eq_sum_card_fiberwise (f := cw) (t := G.image cw)
      (fun z hz => Finset.mem_image_of_mem cw hz)]
  -- bound the sum by L copies of k·|ι|
  calc (∑ c ∈ G.image cw, (G.filter (fun z => cw z = c)).card)
      ≤ ∑ _c ∈ G.image cw, k * Fintype.card ι := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        -- fibre ⊆ the agreement filter for c
        have hsub : G.filter (fun z => cw z = c) ⊆ Finset.univ.filter (fun z : F =>
            Fintype.card ι - e ≤
              (Finset.univ.filter
                (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          obtain ⟨hzG, hzc⟩ := hz
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hag := hcw_agree z hzG
          rw [hzc] at hag
          exact hag
        -- per-codeword count: agreement-filter · ((n-e) - perm) ≤ k·n, with (n-e)-perm ≥ 1
        have hbound := card_curveAgreement_le u c e
        have hperm : (Finset.univ.filter (fun i => ∀ z : F,
            ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card < Fintype.card ι - e := hnoperm c hc
        have hpos : 1 ≤ (Fintype.card ι - e)
            - (Finset.univ.filter (fun i => ∀ z : F,
                ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card := by omega
        calc (G.filter (fun z => cw z = c)).card
            ≤ (Finset.univ.filter (fun z : F =>
                Fintype.card ι - e ≤
                  (Finset.univ.filter
                    (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter (fun z : F =>
                Fintype.card ι - e ≤
                  (Finset.univ.filter
                    (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card
                * ((Fintype.card ι - e)
                  - (Finset.univ.filter (fun i => ∀ z : F,
                      ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card) :=
              Nat.le_mul_of_pos_right _ hpos
          _ ≤ k * Fintype.card ι := hbound
    _ = (G.image cw).card * (k * Fintype.card ι) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Heavy-codeword existence from a large good set** (the counting core of
`jointAgreement_of_close_codeword_pigeonhole`, derived by fibre aggregation). If the good set
exceeds `L · k · |ι|` (`L = |G.image cw|`), then *some* selected codeword has permanent agreement
with the curve on `≥ |ι| - e` coordinates — a heavy codeword. This is the contrapositive of
`curve_goodSet_card_le_listSize_mul`, and is exactly the threshold the pigeonhole consumes. -/
theorem exists_heavy_codeword_of_goodSet_card_gt {k : ℕ} (u : Fin (k + 1) → ι → F) (e : ℕ)
    (G : Finset F) (cw : F → ι → F)
    (hcw_agree : ∀ z ∈ G, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = cw z i)).card)
    (hbig : (G.image cw).card * (k * Fintype.card ι) < G.card) :
    ∃ c ∈ G.image cw, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => ∀ z : F,
        ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card := by
  classical
  by_contra hcon
  push Not at hcon
  exact absurd (curve_goodSet_card_le_listSize_mul u e G cw hcw_agree hcon) (by omega)

end ProximityGap
