/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

set_option linter.style.longLine false

/-!
# The exact per-pairing antipodal-consistent count (#407 lower companion)

The K1 upper bound `NegationClosedWalkBound.antipodalConsistent_card_le` proves, for a fixed
pairing `σ` of `Fin (2r)`, that the antipodal-consistent set
`A_σ = {c : Fin (2r) → G | ∀ i, c (σ i) = −c i}` has cardinality `≤ n^r` (the transversal values
determine `c`). This file lands the matching **lower** direction for a **negation-closed** `G`:

> `antipodalConsistent_card_ge` :  `n^r ≤ #A_σ`,
> `antipodalConsistent_card_eq` :  `#A_σ = n^r`.

The mechanism is the explicit inverse of the upper-bound restriction: a free value vector
`t : Fin r → G` on the transversal `lowerHalf σ` extends to a consistent tuple by setting the
upper-half slots to the negatives of their partners (which land back in `G` by negation-closure).
The map `t ↦ buildConsistent σ t` is an injection `G^r ↪ A_σ`, giving `n^r ≤ #A_σ`; combined with
the proven `≤ n^r` it is an equality.

This makes the per-`σ` term in the `(2r−1)‼` `card_biUnion` lower-bound assembly EXACT (it is the
`(n/2)_r·2^r → n^r` overcount form on the non-distinct-class locus, and the exact mass on each
single pairing). It is the dual brick of `antipodalConsistent_card_le`, probe-verified exact in
`scripts/probes/probe_persigma_exact_count.py` for `n ∈ {2,4,6}`, `r ∈ {1,2,3}`, all pairings, on
both a neg-closed integer model and actual `μ_n ⊂ ℂ`.

**Honest scope (rules 1, 3, 6).** Negation-closed combinatorics — NOT thinness-essential, does NOT
close CORE. It is the EXACT per-pairing count, the dual companion of the proven upper bound; it does
NOT by itself assemble the full `(2r−1)‼` lower bound (that still needs the cross-pairing
disjointness on the distinct-class generic locus, the `NOTE` brick of `CharZeroEnergyLowerBound`).
Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.PerPairingExactCount

open ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-- For a pairing `σ` and `i ∉ lowerHalf σ`, the partner `σ i` lies in `lowerHalf σ`. -/
theorem partner_mem_lowerHalf {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)
    {i : Fin (2 * r)} (hi : i ∉ lowerHalf σ) : σ i ∈ lowerHalf σ := by
  obtain ⟨hinv, hfix⟩ := hσ
  have hilt : ¬ i < σ i := by simpa [lowerHalf] using hi
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinv i]
  rcases lt_trichotomy i (σ i) with h | h | h
  · exact absurd h hilt
  · exact absurd h.symm (hfix i)
  · exact h

/-- The explicit consistent tuple built from a transversal value vector `t : Fin r → F`.
On the transversal slot `e k` it is `t k`; on the upper-half slot `i` (partner of a transversal
slot) it is the negative of the transversal value at `σ i`. -/
noncomputable def buildConsistent {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) (hσ : IsPairing σ)
    (t : Fin r → F) : Fin (2 * r) → F :=
  fun i =>
    let e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ)
    if h : i ∈ lowerHalf σ then t (e.symm ⟨i, h⟩)
    else - t (e.symm ⟨σ i, partner_mem_lowerHalf hσ h⟩)

/-- `buildConsistent` lands in `G^{2r}` for a negation-closed `G` when `t` takes values in `G`. -/
theorem buildConsistent_mem {r : ℕ} (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) {t : Fin r → F} (ht : ∀ k, t k ∈ G) :
    buildConsistent σ hσ t ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G) := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  simp only [buildConsistent]
  split
  · exact ht _
  · exact hneg _ (ht _)

/-- Value of `buildConsistent` on a transversal slot `i ∈ lowerHalf σ`. -/
theorem buildConsistent_lower {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)
    (t : Fin r → F) {i : Fin (2 * r)} (hi : i ∈ lowerHalf σ) :
    buildConsistent σ hσ t i
      = t (((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ)).symm ⟨i, hi⟩) := by
  simp only [buildConsistent]
  rw [dif_pos hi]

/-- Value of `buildConsistent` on an upper slot `i ∉ lowerHalf σ`: the negative of the
transversal value at the partner `σ i`. -/
theorem buildConsistent_upper {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)
    (t : Fin r → F) {i : Fin (2 * r)} (hi : i ∉ lowerHalf σ) :
    buildConsistent σ hσ t i
      = - t (((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ)).symm
              ⟨σ i, partner_mem_lowerHalf hσ hi⟩) := by
  simp only [buildConsistent]
  rw [dif_neg hi]

/-- `buildConsistent` is antipodally consistent for `σ`: `c (σ i) = −c i` for every `i`. -/
theorem buildConsistent_antipodal {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)
    (t : Fin r → F) : ∀ i, buildConsistent σ hσ t (σ i) = - buildConsistent σ hσ t i := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hfix : ∀ i, σ i ≠ i := hσ.2
  intro i
  by_cases hi : i ∈ lowerHalf σ
  · -- i is a lower slot, so σ i is an upper slot
    have hσi : σ i ∉ lowerHalf σ := by
      simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [hinv i]
      simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact le_of_lt hi
    rw [buildConsistent_upper hσ t hσi, buildConsistent_lower hσ t hi]
    -- the partner of (σ i) is σ (σ i) = i, so the two subtype indices agree
    have hsub : (⟨σ (σ i), partner_mem_lowerHalf hσ hσi⟩ : {x // x ∈ lowerHalf σ})
        = ⟨i, hi⟩ := by
      apply Subtype.ext
      exact hinv i
    rw [hsub]
  · -- i is an upper slot, so σ i is a lower slot
    have hσi : σ i ∈ lowerHalf σ := partner_mem_lowerHalf hσ hi
    rw [buildConsistent_lower hσ t hσi, buildConsistent_upper hσ t hi, neg_neg]

/-- Restricting `buildConsistent σ hσ t` to the transversal recovers `t`. -/
theorem buildConsistent_restrict {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)
    (t : Fin r → F) (k : Fin r) :
    buildConsistent σ hσ t
        (((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) k : Fin (2 * r))) = t k := by
  classical
  set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
  have hmem : ((e k : Fin (2 * r))) ∈ lowerHalf σ := (e k).2
  rw [buildConsistent_lower hσ t hmem]
  congr 1
  -- e.symm ⟨e k, _⟩ = k
  have hcoe : (⟨(e k : Fin (2 * r)), hmem⟩ : {x // x ∈ lowerHalf σ}) = e k := by
    apply Subtype.ext; rfl
  rw [hcoe, OrderIso.symm_apply_apply]

/-- `t ↦ buildConsistent σ hσ t` is injective: restriction to the transversal recovers `t`. -/
theorem buildConsistent_injective {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) :
    Function.Injective (buildConsistent (F := F) σ hσ) := by
  intro t t' h
  funext k
  have := congrFun h ((((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ)) k : Fin (2 * r)))
  rwa [buildConsistent_restrict hσ t k, buildConsistent_restrict hσ t' k] at this

/-- **The exact per-pairing antipodal-consistent count, lower direction.** For a negation-closed
`G` and a fixed pairing `σ`, the antipodal-consistent set has cardinality at least `n^r`, witnessed
by the injection `t ↦ buildConsistent σ hσ t` from `G^r`. -/
theorem antipodalConsistent_card_ge {r : ℕ} (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) :
    G.card ^ r ≤
      ((Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
        (fun c => ∀ i, c (σ i) = - c i)).card := by
  classical
  set P := Fintype.piFinset (fun _ : Fin (2 * r) => G) with hP
  set A := P.filter (fun c => ∀ i, c (σ i) = - c i) with hA
  -- the injection image of G^r sits inside A
  have hsub : (Fintype.piFinset (fun _ : Fin r => G)).image (buildConsistent σ hσ) ⊆ A := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    rw [Fintype.mem_piFinset] at ht
    rw [hA, Finset.mem_filter]
    exact ⟨buildConsistent_mem G hneg hσ ht, buildConsistent_antipodal hσ t⟩
  calc G.card ^ r
      = (Fintype.piFinset (fun _ : Fin r => G)).card := by
        rw [Fintype.card_piFinset]; simp
    _ = ((Fintype.piFinset (fun _ : Fin r => G)).image (buildConsistent σ hσ)).card := by
        rw [Finset.card_image_of_injective _ (buildConsistent_injective hσ)]
    _ ≤ A.card := Finset.card_le_card hsub

/-- **The exact per-pairing antipodal-consistent count.** Combining the proven upper bound
`antipodalConsistent_card_le` with the lower bound above: for a negation-closed `G` and a fixed
pairing `σ`, the antipodal-consistent set has cardinality EXACTLY `n^r`. -/
theorem antipodalConsistent_card_eq {r : ℕ} (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) :
    ((Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
      (fun c => ∀ i, c (σ i) = - c i)).card = G.card ^ r :=
  le_antisymm (antipodalConsistent_card_le G hσ) (antipodalConsistent_card_ge G hneg hσ)

end ProximityGap.Frontier.PerPairingExactCount

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PerPairingExactCount.antipodalConsistent_card_ge
#print axioms ProximityGap.Frontier.PerPairingExactCount.antipodalConsistent_card_eq
