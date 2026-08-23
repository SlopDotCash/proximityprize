/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The class-structure supply floor (#389, the open core's corrected target)

The supply-anchor probes (same-day arc, 2026-06-12) found the agreement-capped
per-word supply's measured extremizers are the **class-structured words**: the
quadratic-character word `x^{(q−1)/2}` is agreement-capped (its best codeword
agreement is `≈ n/2 = 2k+m+1`, exactly the cap) yet carries supply `258 / 215`
versus random mean `4 / 8` at `(31,16,{3,4},1)` — refuting the naive
polylog-above-mean target the anchor had proposed.  This file formalizes the
mechanism as the reusable floor:

> **`class_supply_floor`** — a word constant on a class `S` has at least
> `C(|S|, k+m+1)` explainable `(k+m+1)`-cores (every core inside the class is
> explained by the constant codeword), and consequently
> (**`explainableCoreSupply_class_floor`**) every `B` satisfying
> `ExplainableCoreSupply dom k m B` obeys `C(s, k+m+1) ≤ B` for every class
> size `s ≤ n` realizable by a word in the quantified family.

For the **capped** residual (`SubJohnsonSupplyResidual`) the relevant class size
is `s = 2k+m+1` and above, up to the cap: the ±1-valued character words realize
`s ≈ n/2` while staying capped (probe-verified; the cap certification of a
concrete instance is the registered next decide-brick).  The corrected shape of
the open supply statement is therefore: **bound the capped supply by the
largest agreement-class structure** — a class-covering question; any positive
route must reproduce `C(class, t)` on the character/coset families, not
`polylog × mean`.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The class-structure floor**: a word constant on `S` has at least
`C(|S|, k+m+1)` explainable `(k+m+1)`-cores — every core inside the class is
explained by the constant codeword. -/
theorem class_supply_floor (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    {w : Fin n → F} {S : Finset (Fin n)} {v : F} (hconst : ∀ i ∈ S, w i = v) :
    S.card.choose (k + m + 1)
      ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => ExplainableOn dom k w T)).card := by
  classical
  have hcw : (fun _ : Fin n => v) ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    refine ⟨Polynomial.C v, ?_, ?_⟩
    · calc (Polynomial.C v).degree ≤ 0 := Polynomial.degree_C_le
      _ < (k : WithBot ℕ) := by exact_mod_cast hk
    · funext i
      simp
  have hsub : S.powersetCard (k + m + 1)
      ⊆ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => ExplainableOn dom k w T) := by
    intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩, ?_⟩
    exact ⟨fun _ => v, hcw, fun i hi => (hconst i (hTsub hi)).symm⟩
  calc S.card.choose (k + m + 1)
      = (S.powersetCard (k + m + 1)).card := (Finset.card_powersetCard _ _).symm
  _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **The supply floor from class structure**: any `B` for the (uncapped)
`ExplainableCoreSupply` dominates `C(s, k+m+1)` at every class size `s ≤ n` —
witnessed by the indicator-style word constant on an `s`-subset.  (For the
*capped* residual the same floor applies through any capped class word — the
character family realizes `s ≈ n/2` capped, per the probes.) -/
theorem explainableCoreSupply_class_floor (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (m : ℕ) {B : ℕ} (hB : ExplainableCoreSupply dom k m B) {s : ℕ} (hs : s ≤ n) :
    s.choose (k + m + 1) ≤ B := by
  classical
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hs :
      s ≤ (Finset.univ : Finset (Fin n)).card)
  refine le_trans ?_ (hB (fun i => if i ∈ S then 1 else 0))
  have := class_supply_floor dom hk m
    (w := fun i => if i ∈ S then (1 : F) else 0) (S := S) (v := 1)
    (fun i hi => by simp [hi])
  rwa [hScard] at this

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.class_supply_floor
#print axioms ProximityGap.PairRank.explainableCoreSupply_class_floor
