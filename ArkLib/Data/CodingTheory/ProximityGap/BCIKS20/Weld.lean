/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Kill
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

/-!
# The hlin weld — heavy branches are `Y`-linear (#302, B3)

The composition of the per-point Claim 5.10 kill (`Claim510Kill`) with the Vandermonde
Claim 5.9 globalization (`Claim59Vandermonde`), the monic `P2` lift-identity supply
(`P2MatchMonic.restrictedFaaDiBrunoMatch_of_monic`, PROVEN), and the proven curve collapse
(`ZLinearClosureAudit`): a **monic branch `H` carrying heavy per-place data is `Y`-linear**.
This is `hlin` — the single deep gate of the below-Johnson mutual correlated agreement
program ([BCIKS20] §5 Steps 5–7, [Hab25] Claim 1) — reduced to finitely-producible inputs.

`natDegree_eq_one_of_heavy_data` consumes, per evaluation node `j` of `n` distinct nodes:
* the coefficient tail `αGenuine t = 0` for `t ≥ n` (Claim 5.8′ — supplied by the in-tree
  truncation capstones, e.g. `GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc`
  via `Claim59Lagrange.alphaGenuine_tail_zero_of_trunc`);
* a place set `matchingSet j` with, at every place: the **per-place coefficient pinning**
  `π_z (βHensel t) = c t·ξ_z^{2t−1}` (Hensel uniqueness over `F` — the
  `DecodedProximateRoot`/`PlaceSeriesCanonical` lane) and the **agreement**
  `∑_t c t·e_j^t = u₀ j + z·u₁ j` (the decoded value matches the affine fold);
* a weight bound `W` for the kill target and the cardinality `W·d_H < |matchingSet j|`
  (the heavy-point budget, `Hab25HeavyPoints` + the dichotomy threshold).

Conclusion: `H.natDegree = 1`.  Equivalently (`false_of_heavy_data_of_two_le`): **no
`Y`-degree ≥ 2 branch carries heavy data** — per-`z` decoded roots cannot hide in a
`Y`-degree ≥ 2 factor.

## Main results

* `liftIdentity_of_monic` — the lift identity for monic `H` (in-tree `P2` monic match).
* `largeness_of_card` — membership + weight + cardinality ⟹ the `Lemma_A_1` largeness.
* `natDegree_eq_one_of_heavy_data` — **the hlin weld** (collapse form).
* `false_of_heavy_data_of_two_le` — **hlin** (contradiction form at `d_H ≥ 2`).

## References

* [BCIKS20] ePrint 2020/654 — §5.2.6–5.2.7, Appendix A.
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Weld

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

/-- The per-`t` lift identity for monic `H`, supplied by the PROVEN in-tree monic `P2`
match (`restrictedFaaDiBrunoMatch_of_monic`). -/
theorem liftIdentity_of_monic (hlc : H.leadingCoeff = 1) (t : ℕ) :
    S5Genuine.LiftIdentityAt H x₀ R hHyp t :=
  S5Genuine.LiftIdentityAt.of_restrictedMatch H hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc) t

/-- **Membership + weight + cardinality ⟹ `Lemma_A_1` largeness** for the kill target:
if every place of `matchingSet` is pinned and agreeing (hence in `S_β`), the weight is at
most `W`, and `W·d_H < |matchingSet|`, then the vanishing set is large enough. -/
theorem largeness_of_card [Fintype F] {n : ℕ} (e a b : F) {D : ℕ}
    (matchingSet : Finset F)
    (hmem : ∀ z ∈ matchingSet, z ∈ S_β (killTarget H x₀ R hHyp n e a b))
    {W : ℕ}
    (hweight : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n e a b) D ≤ (W : WithBot ℕ))
    (hcard : W * H.natDegree < matchingSet.card) :
    Set.ncard (S_β (killTarget H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTarget H x₀ R hHyp n e a b) D) * H.natDegree := by
  have hsub : (↑matchingSet : Set F) ⊆ S_β (killTarget H x₀ R hHyp n e a b) := by
    intro z hz
    exact hmem z (by simpa using hz)
  have hncard : matchingSet.card ≤ Set.ncard (S_β (killTarget H x₀ R hHyp n e a b)) := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  have hWd : (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTarget H x₀ R hHyp n e a b) D) * H.natDegree
      ≤ ((W * H.natDegree : ℕ) : WithBot ℕ) := by
    rcases hweq : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n e a b) D with _ | w
    · exact le_trans (le_of_eq (WithBot.bot_mul (by
        exact_mod_cast (Fact.out (p := 0 < H.natDegree)).ne'))) bot_le
    · have hwW : w ≤ W := by
        have h := hweq ▸ hweight
        exact WithBot.coe_le_coe.mp h
      show ((w : WithBot ℕ)) * (H.natDegree : WithBot ℕ)
          ≤ ((W * H.natDegree : ℕ) : WithBot ℕ)
      exact_mod_cast Nat.mul_le_mul_right H.natDegree hwW
  calc (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTarget H x₀ R hHyp n e a b) D) * H.natDegree
      ≤ ((W * H.natDegree : ℕ) : WithBot ℕ) := hWd
    _ < (matchingSet.card : WithBot ℕ) := by exact_mod_cast hcard
    _ ≤ (Set.ncard (S_β (killTarget H x₀ R hHyp n e a b)) : WithBot ℕ) := by
        exact_mod_cast hncard

/-- **The hlin weld (collapse form).**  A monic branch carrying heavy per-place data at `n`
distinct nodes — coefficient tail, per-place pinning + agreement, weight bound, and the
heavy cardinality — has `H.natDegree = 1`. -/
theorem natDegree_eq_one_of_heavy_data [Fintype F] (hlc : H.leadingCoeff = 1)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (c : Fin n → F → ℕ → F)
    (hpin : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∀ t, t < n → π_z z root (βHensel H x₀ R hHyp t)
          = c j z t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) ∧
      (∑ t ∈ Finset.range n, c j z t * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  refine natDegree_eq_one_of_vandermonde_values H hHyp htail e he u₀ u₁ fun j => ?_
  refine coeff_sum_eq_ground_of_large_fin H x₀ R hHyp hlc
    (fun t _ => liftIdentity_of_monic H x₀ R hHyp hlc t) (e j) (u₀ j) (u₁ j) hD ?_
  refine largeness_of_card H x₀ R hHyp (e j) (u₀ j) (u₁ j) (matchingSet j)
    (fun z hz => ?_) (hweight j) (hcard j)
  obtain ⟨root, hroot, hagree⟩ := hpin j z hz
  exact mem_S_β_killTarget_of_pin_agree H x₀ R hHyp (e j) (u₀ j) (u₁ j) z root
    (c j z) hroot hagree

/-- **hlin (contradiction form).**  No `Y`-degree ≥ 2 monic branch carries heavy per-place
data: per-`z` decoded roots cannot live on a `Y`-degree ≥ 2 factor.  [BCIKS20] §5 Steps
5–7 / [Hab25] Claim 1, at the in-tree genuine Hensel objects. -/
theorem false_of_heavy_data_of_two_le [Fintype F] (hlc : H.leadingCoeff = 1)
    (hdeg : 2 ≤ H.natDegree)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (c : Fin n → F → ℕ → F)
    (hpin : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∀ t, t < n → π_z z root (βHensel H x₀ R hHyp t)
          = c j z t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) ∧
      (∑ t ∈ Finset.range n, c j z t * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    False := by
  have h1 := natDegree_eq_one_of_heavy_data H x₀ R hHyp hlc htail e he u₀ u₁ hD
    matchingSet c hpin hweight hcard
  omega

end BCIKS20.Claim510Weld

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Weld.liftIdentity_of_monic
#print axioms BCIKS20.Claim510Weld.largeness_of_card
#print axioms BCIKS20.Claim510Weld.natDegree_eq_one_of_heavy_data
#print axioms BCIKS20.Claim510Weld.false_of_heavy_data_of_two_le
