/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The quadratic additive-energy floor for negation-closed sets (#389)

> **`addEnergy_ge_three_mul`** — if `G ⊆ F` (char ≠ 2) is closed under negation and has no
> `2`-torsion (`-x ≠ x` on `G`), then `3·|G|·(|G|−1) ≤ E(G)`.

For a smooth multiplicative subgroup `G = μ_n` with `n` even (so `-1 ∈ G`), this gives
`E(μ_n) ≥ 3n(n−1)` — additive energy of *quadratic* order, the sharp floor. Combined with the exact
generic value `E(μ_{2^k}) = 3n(n−1)` (numerically confirmed: `n=8→168, 16→720, 32→2976, 64→12096`),
the smooth subgroup energy is `Θ(n²)`.

This is the **good-side** companion to the **bad-side** cubic bound `E(QR) ≳ |QR|³/2`
(`qr_energy_cubic_lower`): together they bracket the δ\* small-vs-large-subgroup dichotomy with a
clean factor-`n` separation (good `Θ(n²)` vs bad `Θ(n³)`). The floor is forced purely by the `-1`
symmetry: the three solution families `(a,a',a,a')`, `(a,a',a',a)` (trivial) and `(a,-a,c,-c)` (the
zero-sum pairs), of total size `3n(n−1)`. Axiom-clean. Issue #389.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.SubgroupEnergyFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The inner double indicator sum equals the representation count `#{c ∈ G : s − c ∈ G}`. -/
theorem inner_eq_filter_card (G : Finset F) (s : F) :
    (∑ c ∈ G, ∑ c' ∈ G, (if s = c + c' then (1 : ℕ) else 0))
      = (G.filter (fun c => s - c ∈ G)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hcong : (∑ c' ∈ G, (if s = c + c' then (1 : ℕ) else 0))
       = ∑ c' ∈ G, (if c' = s - c then (1 : ℕ) else 0) :=
    Finset.sum_congr rfl (fun c' _ =>
      if_congr ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩ rfl rfl)
  rw [hcong, Finset.sum_ite_eq' G (s - c) (fun _ => (1 : ℕ))]

/-- **Quadratic additive-energy floor.** `3·|G|·(|G|−1) ≤ E(G)` for negation-closed torsion-free `G`. -/
theorem addEnergy_ge_three_mul (G : Finset F)
    (hneg : ∀ x ∈ G, -x ∈ G) (htf : ∀ x ∈ G, -x ≠ x) :
    3 * G.card * (G.card - 1) ≤ addEnergy G := by
  classical
  set L : F → F → ℕ := fun a a' => if a' = -a then G.card else if a' = a then 1 else 2 with hL
  -- addEnergy = ∑_{a,a'} #{c ∈ G : a+a'-c ∈ G}
  have hE : addEnergy G = ∑ a ∈ G, ∑ a' ∈ G, (G.filter (fun c => a + a' - c ∈ G)).card := by
    rw [addEnergy]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ =>
      inner_eq_filter_card G (a + a')))
  -- per-pair lower bound  L a a' ≤ #{c}
  have hpt : ∀ a ∈ G, ∀ a' ∈ G, L a a' ≤ (G.filter (fun c => a + a' - c ∈ G)).card := by
    intro a ha a' ha'
    simp only [hL]
    by_cases h1 : a' = -a
    · rw [if_pos h1]
      exact le_of_eq (congrArg Finset.card
        (Finset.filter_true_of_mem (fun c hc => by
          rw [h1, show a + -a - c = -c by ring]; exact hneg c hc)).symm)
    · rw [if_neg h1]
      by_cases h2 : a' = a
      · rw [if_pos h2]
        exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr
          ⟨ha, by rw [show a + a' - a = a' by ring]; exact ha'⟩⟩
      · rw [if_neg h2]
        have hlt : 1 < (G.filter (fun c => a + a' - c ∈ G)).card := by
          rw [Finset.one_lt_card_iff]
          refine ⟨a, a', ?_, ?_, Ne.symm h2⟩
          · exact Finset.mem_filter.mpr ⟨ha, by rw [show a + a' - a = a' by ring]; exact ha'⟩
          · exact Finset.mem_filter.mpr ⟨ha', by rw [show a + a' - a' = a by ring]; exact ha⟩
        omega
  have hge : (∑ a ∈ G, ∑ a' ∈ G, L a a') ≤ addEnergy G := by
    rw [hE]
    exact Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun a' ha' => hpt a ha a' ha'))
  -- evaluate ∑∑ L = 3·|G|·(|G|−1)
  have hsum : (∑ a ∈ G, ∑ a' ∈ G, L a a') = 3 * G.card * (G.card - 1) := by
    have hinner : ∀ a ∈ G, (∑ a' ∈ G, L a a') = 3 * (G.card - 1) := by
      intro a ha
      have hna : -a ∈ G := hneg a ha
      have hne : -a ≠ a := htf a ha
      have hmem : a ∈ G.erase (-a) := Finset.mem_erase.mpr ⟨Ne.symm hne, ha⟩
      have hcard2 : 2 ≤ G.card := by
        have hsub : ({-a, a} : Finset F) ⊆ G := by
          intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl; exacts [hna, ha]
        calc 2 = ({-a, a} : Finset F).card := (Finset.card_pair hne).symm
          _ ≤ G.card := Finset.card_le_card hsub
      have e1 : L a (-a) = G.card := by simp [hL]
      have e2 : L a a = 1 := by simp [hL, Ne.symm hne]
      have hrest : ∀ x ∈ (G.erase (-a)).erase a, L a x = 2 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase] at hx
        simp only [hL]; rw [if_neg hx.2.1, if_neg hx.1]
      have hc2 : ((G.erase (-a)).erase a).card = G.card - 2 := by
        rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem hna]; omega
      rw [← Finset.add_sum_erase G (fun a' => L a a') hna, e1,
        ← Finset.add_sum_erase (G.erase (-a)) (fun a' => L a a') hmem, e2,
        Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul, hc2]
      omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    ring
  rw [← hsum]; exact hge

end ArkLib.ProximityGap.SubgroupEnergyFloor

#print axioms ArkLib.ProximityGap.SubgroupEnergyFloor.addEnergy_ge_three_mul
