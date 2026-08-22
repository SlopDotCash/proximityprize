/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G123TriangularMomentLadder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87MaximalCancellationAssemblyRepresentation

/-!
# G124: the moment LP — linear descent constraints on the depth fibers

G123's ladder identities are exact but not linear in the depth fibers (matching counts vary
within a depth class).  This file extracts the LINEAR content:

1. **Visibility floor** (`descFactorial_le_matchCountM`): every pair at cancellation depth `s`
   admits at least `(r−s)_m` ordered `m`-matchings.  Construction: the landed G87
   maximal-cancellation representation writes `y.1 = assemble e₁ core₁ pad`,
   `y.2 = assemble e₂ core₂ (pad ∘ σ)`; the two padding complements carry the common part with
   explicit relative permutation `σ`, so composing with every `g : Fin m ↪ Fin (r−s)` yields
   `(r−s)_m` distinct matchings.
2. **The moment LP** (`moment_LP_row`): summing the floor against the G123 identity,

   ```text
   Σ_{s=0}^{r} (r−s)_m · depthFiber A r s ≤ (r)_m² · #A^m · E_{r−m}(A)
   ```

   for every `m ≤ r` — a triangular system of LINEAR upper bounds on the depth fibers whose
   data are the lower-rung energies.  Deep rows vanish automatically (`(r−s)_m = 0` for
   `s > r−m`), so each row constrains exactly the depths visible to it.  Row `m = r` recovers
   the exact permutation envelope `r! · fiber₀ ≤ (r!)² · #A^r · E₀`.

The depth census is now the feasible set of an explicit LP driven by the rung hierarchy —
linear constraints that survive every uniform-law counterexample.

**Honest scope.**  Constraints only; the fully-disjoint sector (weight 0 in every row `m ≥ 1`)
remains unconstrained — the wall.  CORE remains OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly
open ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset
open ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation
open ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity
open ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder

variable {α : Type*} [DecidableEq α]

/-- `valueBag` and `valueMultiset` agree on `Fin r` words. -/
theorem valueBag_eq_valueMultiset {r : ℕ} (v : Fin r → α) :
    valueBag v = valueMultiset v :=
  G123TriangularMomentLadder.valueBag_eq_map v

/-- **Visibility floor.**  A pair at cancellation depth `s` admits at least `(r−s)_m` ordered
`m`-matchings: the common padding carries an explicit matching of size `r−s`, and every
injective `m`-selection of it is a distinct `m`-matching. -/
theorem descFactorial_le_matchCountM {r m : ℕ}
    (y : (Fin r → α) × (Fin r → α)) :
    (r - cancelDepth y).descFactorial m ≤ matchCountM m y := by
  classical
  set s := cancelDepth y with hs
  have hsr : s ≤ r := cancelDepth_le y
  -- the G87 maximal-cancellation representation
  obtain ⟨coreL, coreR, e₁, e₂, pad, σ, _, _, _, hy1, hy2⟩ :=
    exists_maximalCancellation_assembly hsr y.1 y.2
      (by
        rw [← valueBag_eq_valueMultiset, ← valueBag_eq_valueMultiset]
        exact hs.symm)
  -- each g : Fin m ↪ Fin (r−s) yields a matching via the padding complements
  have hmatch : ∀ g : Fin m ↪ Fin (r - s),
      (∀ t, y.1 ((g.trans (σ.toEmbedding.trans (padSlots hsr e₁))) t)
          = y.2 ((g.trans (padSlots hsr e₂)) t)) := by
    intro g t
    have h1 : y.1 (padSlots hsr e₁ (σ (g t))) = pad (σ (g t)) := by
      rw [← hy1]
      exact assemble_pad hsr e₁ coreL pad (σ (g t))
    have h2 : y.2 (padSlots hsr e₂ (g t)) = (pad ∘ σ) (g t) := by
      rw [← hy2]
      exact assemble_pad hsr e₂ coreR (pad ∘ σ) (g t)
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [h1, h2]
    rfl
  -- inject the m-selections into the matching set
  have hcard : (univ : Finset (Fin m ↪ Fin (r - s))).card ≤ matchCountM m y := by
    unfold matchCountM
    apply Finset.card_le_card_of_injOn
      (fun g => (g.trans (σ.toEmbedding.trans (padSlots hsr e₁)),
        g.trans (padSlots hsr e₂)))
    · intro g _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmatch g⟩
    · intro g₁ _ g₂ _ hg
      have hsnd := congrArg Prod.snd hg
      ext t
      have hgt := congrArg (fun e : Fin m ↪ Fin r => e t) hsnd
      simp only [Function.Embedding.trans_apply] at hgt
      exact congrArg Fin.val ((padSlots hsr e₂).injective hgt)
  calc
    (r - s).descFactorial m
        = (univ : Finset (Fin m ↪ Fin (r - s))).card := by
      rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_fin]
    _ ≤ matchCountM m y := hcard

section LP

variable [AddCancelCommMonoid α]

/-- **The moment LP.**  For every `m ≤ r`, the `(r−s)_m`-weighted depth fibers are linearly
bounded by the rung-`(r−m)` energy: a triangular system of linear constraints on the depth
census whose data are the lower-rung energies.  Deep rows vanish automatically. -/
theorem moment_LP_row (A : Finset α) {r m : ℕ} (hm : m ≤ r) :
    ∑ s ∈ Finset.range (r + 1),
        (r - s).descFactorial m * depthFiber A r s
      ≤ (r.descFactorial m) ^ 2 * (A.card ^ m * Finset.addREnergy (r - m) A) := by
  classical
  have hfib : ∀ s, (r - s).descFactorial m * depthFiber A r s
      = ∑ y ∈ (energySet A r).filter (fun y => cancelDepth y = s),
          (r - cancelDepth y).descFactorial m := by
    intro s
    rw [Finset.sum_congr rfl (fun y hy => by
      rw [(Finset.mem_filter.mp hy).2] :
        ∀ y ∈ (energySet A r).filter (fun y => cancelDepth y = s), _ = _)]
    rw [Finset.sum_const, smul_eq_mul]
    unfold depthFiber
    ring
  have hpart : ∑ s ∈ Finset.range (r + 1),
      (r - s).descFactorial m * depthFiber A r s
      = ∑ y ∈ energySet A r, (r - cancelDepth y).descFactorial m := by
    rw [Finset.sum_congr rfl (fun s _ => hfib s)]
    exact Finset.sum_fiberwise_of_maps_to
      (fun y _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (cancelDepth_le y)))
      (fun y => (r - cancelDepth y).descFactorial m)
  rw [hpart, ← sum_matchCountM_energySet A hm]
  exact Finset.sum_le_sum (fun y _ => descFactorial_le_matchCountM y)

/-- Row `m = r` of the LP recovers the exact permutation envelope for the fully-cancelled
sector: `r! · fiber₀ ≤ (r!)² · #A^r`. -/
theorem moment_LP_top_row (A : Finset α) (r : ℕ) :
    r.factorial * depthFiber A r 0
      ≤ (r.factorial) ^ 2 * A.card ^ r := by
  have h := moment_LP_row A (le_refl r)
  have hzero : ∀ s ∈ Finset.range (r + 1), s ≠ 0 →
      (r - s).descFactorial r * depthFiber A r s = 0 := by
    intro s hsmem hs
    have hsr := Finset.mem_range.mp hsmem
    have : (r - s).descFactorial r = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [this, Nat.zero_mul]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos r)) hzero]
    at h
  simp only [Nat.sub_zero, Nat.sub_self, Nat.descFactorial_self] at h
  calc
    r.factorial * depthFiber A r 0 ≤
        (r.factorial) ^ 2 * (A.card ^ r * Finset.addREnergy 0 A) := h
    _ = (r.factorial) ^ 2 * A.card ^ r := by
      have : Finset.addREnergy 0 A = 1 := by
        rw [Finset.addREnergy_def]
        simp
      rw [this, mul_one]
end LP

end ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints.descFactorial_le_matchCountM
#print axioms ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints.moment_LP_row
#print axioms ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints.moment_LP_top_row
