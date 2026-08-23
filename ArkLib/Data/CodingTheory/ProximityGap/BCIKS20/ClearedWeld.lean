/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedKill
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.VandermondeAgreement

/-!
# Route-(a) brick 4: the cleared hlin weld (#371, finding 16)

The non-monic mirror of `Weld.lean` (`Claim510Weld.natDegree_eq_one_of_heavy_data`):
the collapse and contradiction forms of the [BCIKS20] §5 Steps 5–7 / [Hab25] Claim 1
weld, run on the CLEARED kill apparatus (`ClearedKill.lean`) instead of the monic one.

The monic lift identity (`liftIdentity_of_monic`) is replaced by the staged root
hypothesis `hroot : eval (βHenselAssembledC …) (Q …) = 0` through
`liftIdentityAtC_of_assembledSeries_isRoot`; the pinning shape carries the extra
`Ŵ_z^{t+1}` factor of the cleared recursion; largeness and membership are the
`killTargetC` forms.  Everything else — the Vandermonde collapse
(`natDegree_eq_one_of_vandermonde_values`, monicity-free) and the counting — is reused
verbatim.

* `largeness_of_cardC` — membership + weight + cardinality ⟹ `Lemma_A_1` largeness
  (statement identical to `Weld.largeness_of_card` at `killTargetC`);
* `natDegree_eq_one_of_heavy_dataC` — the collapse form: a branch carrying heavy
  per-place cleared data at `n` distinct nodes has `H.natDegree = 1`;
* `false_of_heavy_dataC_of_two_le` — the contradiction form.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill
open BCIKS20.Claim510KillC

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510WeldC

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

/-- **Membership + weight + cardinality ⟹ `Lemma_A_1` largeness** for the CLEARED kill
target: if every place of `matchingSet` is in `S_β`, the weight is at most `W`, and
`W·d_H < |matchingSet|`, the vanishing set is large enough. -/
theorem largeness_of_cardC [Fintype F] {n : ℕ} (e a b : F) {D : ℕ}
    (matchingSet : Finset F)
    (hmem : ∀ z ∈ matchingSet, z ∈ S_β (killTargetC H x₀ R hHyp n e a b))
    {W : ℕ}
    (hweight : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTargetC H x₀ R hHyp n e a b) D ≤ (W : WithBot ℕ))
    (hcard : W * H.natDegree < matchingSet.card) :
    Set.ncard (S_β (killTargetC H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTargetC H x₀ R hHyp n e a b) D) * H.natDegree := by
  have hsub : (↑matchingSet : Set F) ⊆ S_β (killTargetC H x₀ R hHyp n e a b) := by
    intro z hz
    exact hmem z (by simpa using hz)
  have hncard : matchingSet.card ≤ Set.ncard (S_β (killTargetC H x₀ R hHyp n e a b)) := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  have hWd : (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTargetC H x₀ R hHyp n e a b) D) * H.natDegree
      ≤ ((W * H.natDegree : ℕ) : WithBot ℕ) := by
    rcases hweq : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTargetC H x₀ R hHyp n e a b) D with _ | w
    · exact le_trans (le_of_eq (WithBot.bot_mul (by
        exact_mod_cast (Fact.out (p := 0 < H.natDegree)).ne'))) bot_le
    · have hwW : w ≤ W := by
        have h := hweq ▸ hweight
        exact WithBot.coe_le_coe.mp h
      show ((w : WithBot ℕ)) * (H.natDegree : WithBot ℕ)
          ≤ ((W * H.natDegree : ℕ) : WithBot ℕ)
      exact_mod_cast Nat.mul_le_mul_right H.natDegree hwW
  calc (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTargetC H x₀ R hHyp n e a b) D) * H.natDegree
      ≤ ((W * H.natDegree : ℕ) : WithBot ℕ) := hWd
    _ < (matchingSet.card : WithBot ℕ) := by exact_mod_cast hcard
    _ ≤ (Set.ncard (S_β (killTargetC H x₀ R hHyp n e a b)) : WithBot ℕ) := by
        exact_mod_cast hncard

/-- **The cleared hlin weld (collapse form).**  A branch carrying heavy per-place CLEARED
data at `n` distinct nodes — the staged root identity, coefficient tail, per-place
pinning + agreement (with the cleared `Ŵ_z^{t+1}` factor), weight bound, and the heavy
cardinality — has `H.natDegree = 1`.  Non-monic: the lift identities come from `hroot`
via `liftIdentityAtC_of_assembledSeries_isRoot`. -/
theorem natDegree_eq_one_of_heavy_dataC [Fintype F]
    (hroot : Polynomial.eval (βHenselAssembledC (H := H) x₀ R hHyp) (Q x₀ R H) = 0)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (c : Fin n → F → ℕ → F)
    (hpin : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∀ t, t < n → π_z z root (βHenselC (H := H) x₀ R hHyp t)
          = c j z t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
              * ((H.leadingCoeff).eval z) ^ (t + 1)) ∧
      (∑ t ∈ Finset.range n, c j z t * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTargetC H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  refine natDegree_eq_one_of_vandermonde_values H hHyp htail e he u₀ u₁ fun j => ?_
  refine coeff_sum_eq_ground_of_largeC_fin H x₀ R hHyp
    (fun t _ => liftIdentityAtC_of_assembledSeries_isRoot x₀ R hHyp hroot t)
    (e j) (u₀ j) (u₁ j) hD ?_
  refine largeness_of_cardC H x₀ R hHyp (e j) (u₀ j) (u₁ j) (matchingSet j)
    (fun z hz => ?_) (hweight j) (hcard j)
  obtain ⟨root, hroot', hagree⟩ := hpin j z hz
  exact mem_S_β_killTargetC_of_pin_agree H x₀ R hHyp (e j) (u₀ j) (u₁ j) z root
    (c j z) hroot' hagree

/-- **The cleared hlin weld (contradiction form).**  No `Y`-degree ≥ 2 branch carries
heavy per-place cleared data. -/
theorem false_of_heavy_dataC_of_two_le [Fintype F]
    (hroot : Polynomial.eval (βHenselAssembledC (H := H) x₀ R hHyp) (Q x₀ R H) = 0)
    (hdeg : 2 ≤ H.natDegree)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (c : Fin n → F → ℕ → F)
    (hpin : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∀ t, t < n → π_z z root (βHenselC (H := H) x₀ R hHyp t)
          = c j z t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
              * ((H.leadingCoeff).eval z) ^ (t + 1)) ∧
      (∑ t ∈ Finset.range n, c j z t * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTargetC H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    False := by
  have h1 := natDegree_eq_one_of_heavy_dataC H x₀ R hHyp hroot htail e he u₀ u₁ hD
    matchingSet c hpin hweight hcard
  omega

end BCIKS20.Claim510WeldC

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510WeldC.largeness_of_cardC
#print axioms BCIKS20.Claim510WeldC.natDegree_eq_one_of_heavy_dataC
#print axioms BCIKS20.Claim510WeldC.false_of_heavy_dataC_of_two_le
