/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4GeneralStratumRepCorrelation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4DilationDivisibility

/-!
# DQR-4 stratum integrality: `n ∣ N_{k,j}(a)` — every ledger stratum is `n`-divisible — #466

Fourteenth result; extracted from the exact integer stratum tables (which showed `n | T_k` at
every probed stratum). The free diagonal dilation `(y⃗, z⃗) ↦ (u·y⃗, u·z⃗)` preserves the mixed
equation `∑y + a·∑z = 0`, so first-coordinate normalization factorizes the solution set:

* `dilation_dvd_mixedCount` — `n ∣ N_{k,j}(a)` for `k ≥ 1`, any `a`.

Consequence: `T_{k,j} = q·N_{k,j}(a) − n^{k+j}` satisfies `n ∣ T` at every stratum — combined
with the closed-form twist average, the `n·r` zero-count law, and the palindrome, the seven
unknowns of the working equation are integer multiples of `n = 2³⁰`.

**Falsify-first record (from the exact tables, `probe` in the KB arc doc):** there is NO
universal sign law for the strata — at `(p, n) = (193, 16)` the signs alternate with `k`
(−,+,−,+,−,+,−), while at `(97, 8)` and `(257, 16)` all seven are positive. Any conjectured
stratum positivity, negativity, or alternation is refuted at these instances; viable stratum
bounds must be magnitude bounds. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification
open ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation
open ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility

namespace ArkLib.ProximityGap.Frontier.DQR4StratumIntegrality

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Stratum integrality**: `n ∣ N_{k,j}(a)` for `k ≥ 1` — the free diagonal dilation
factorizes the mixed solution set by first-coordinate normalization. -/
theorem dilation_dvd_mixedCount {G : Finset F} (hG : MulClosed G)
    {k : ℕ} (hk : 0 < k) (j : ℕ) (a : F) :
    G.card ∣ mixedSolutionCount G k j a := by
  classical
  set i0 : Fin k := ⟨0, hk⟩
  set S := ((Fintype.piFinset (fun _ : Fin k => G)) ×ˢ
      (Fintype.piFinset (fun _ : Fin j => G))).filter
    (fun p => (∑ i, p.1 i) + a * (∑ l, p.2 l) = 0) with hS
  set T := S.filter (fun p => p.1 i0 = 1) with hT
  have hcard : S.card = G.card * T.card := by
    rw [← Finset.card_product]
    apply Finset.card_nbij'
      (i := fun (p : (Fin k → F) × (Fin j → F)) =>
        (p.1 i0, (fun i => (p.1 i0)⁻¹ * p.1 i, fun l => (p.1 i0)⁻¹ * p.2 l)))
      (j := fun (q : F × ((Fin k → F) × (Fin j → F))) =>
        (fun i => q.1 * q.2.1 i, fun l => q.1 * q.2.2 l))
    · intro p hp
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Fintype.mem_piFinset] at hp
      have h0G : p.1 i0 ∈ G := hp.1.1 i0
      have h00 : p.1 i0 ≠ 0 := fun h => hG.zero_not_mem (h ▸ h0G)
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨h0G, ⟨⟨⟨fun i => hG.mul_mem _ (inv_mem hG h0G) _ (hp.1.1 i),
        fun l => hG.mul_mem _ (inv_mem hG h0G) _ (hp.1.2 l)⟩, ?_⟩, ?_⟩⟩
      · rw [← Finset.mul_sum, ← Finset.mul_sum]
        have : (p.1 i0)⁻¹ * (∑ i, p.1 i) + a * ((p.1 i0)⁻¹ * ∑ l, p.2 l)
            = (p.1 i0)⁻¹ * ((∑ i, p.1 i) + a * (∑ l, p.2 l)) := by ring
        rw [this, hp.2, mul_zero]
      · rw [inv_mul_cancel₀ h00]
    · intro q hq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hq
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Fintype.mem_piFinset]
      refine ⟨⟨fun i => hG.mul_mem _ hq.1 _ (hq.2.1.1.1 i),
        fun l => hG.mul_mem _ hq.1 _ (hq.2.1.1.2 l)⟩, ?_⟩
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have : q.1 * (∑ i, q.2.1 i) + a * (q.1 * ∑ l, q.2.2 l)
          = q.1 * ((∑ i, q.2.1 i) + a * (∑ l, q.2.2 l)) := by ring
      rw [this, hq.2.1.2, mul_zero]
    · intro p hp
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Fintype.mem_piFinset] at hp
      have h00 : p.1 i0 ≠ 0 := fun h => hG.zero_not_mem (h ▸ hp.1.1 i0)
      apply Prod.ext
      · funext i
        simp [mul_inv_cancel_left₀ h00]
      · funext l
        simp [mul_inv_cancel_left₀ h00]
    · intro q hq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hq
      have hq0 : q.1 ≠ 0 := fun h => hG.zero_not_mem (h ▸ hq.1)
      have hnorm : q.2.1 i0 = 1 := hq.2.2
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [hnorm, hq0]
      · funext i
        simp [hnorm, hq0, inv_mul_cancel_left₀ hq0]
      · funext l
        simp [hnorm, hq0, inv_mul_cancel_left₀ hq0]
  have : mixedSolutionCount G k j a = S.card := rfl
  rw [this, hcard]
  exact Dvd.intro _ rfl

end ArkLib.ProximityGap.Frontier.DQR4StratumIntegrality

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4StratumIntegrality.dilation_dvd_mixedCount
