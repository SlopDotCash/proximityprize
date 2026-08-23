/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyFromPairing
import ArkLib.Data.CodingTheory.ProximityGap.DyadicEnergyK1
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount

/-!
# The char-0 Wick / Gaussian energy bound, UNCONDITIONAL for `μ_{2^k}` (#407)

`GaussPeriodMomentBound.GaussianEnergyBound G r := E_r(G) ≤ (2r−1)‼·|G|^r` is the floor's char-0
input (the moment-method carrier that yields the Paley/Ramanujan per-frequency bound
`B ≤ √(2n ln q)`). The reduction `GaussianEnergyFromPairing.gaussianEnergyBound_of_pairing` derives
it from THREE inputs, two of which were left as **unproven hypotheses** even though the docstring
called them "pure combinatorics, no open content":

* `henergy : rEnergy G r = zeroSumCount G (2r)` — the **negation-closure bijection** `(v,w)↦v⧺(−w)`;
* `hcount : #{pairings of Fin (2r)} ≤ (2r−1)‼` — the perfect-matching count;
* `H` — the antipodal-pairing residual (the genuine char-0 Lam–Leung input).

This file **discharges all three for `μ_{2^k}` in characteristic 0**, giving a fully self-contained
energy bound with NO hypothesis:

1. `rEnergy_eq_zeroSumCount` — **the missing combinatorial brick (`henergy`), now proven**: for any
   negation-closed `G` (`∀ g ∈ G, −g ∈ G`, true for every even-order multiplicative subgroup, hence
   for `μ_n`), the `r`-fold additive energy equals the zero-sum count of `2r`-tuples, via the
   bijection `(v,w) ↦ Fin.append v (−∘w)` (concatenate `v` with the negation of `w`; sum is
   `∑v − ∑w`, which vanishes iff `∑v = ∑w`). This was the lone unformalized "pure-combinatorics"
   input passed as a hypothesis across the in-tree reduction.
2. `hcount` is discharged by the exact census `pairings_card_eq_doubleFactorial` (already in tree).
3. `H` is discharged for `μ_{2^k}` in char 0 by `DyadicEnergyK1` (Lam–Leung antipodal closure);
   here we route it through `zeroSumCount_le_doubleFactorial_dyadic` directly.

> **`gaussianEnergyBound_dyadic`** — for a finset `G` of `2^k`-th roots of unity (`k ≥ 1`) in a
> characteristic-zero field and any `r`, `GaussianEnergyBound G r` holds, i.e.
> `E_r(G) ≤ (2r−1)‼·|G|^r`. **No hypothesis** beyond `G ⊆ μ_{2^k}` (+ negation-closure, automatic
> for `μ_{2^k}` since `−1 = ζ^{n/2} ∈ G`) and char 0.

This is the **char-0 face** of the energy core, now fully in Lean. **Honest scope (the wall):** the
prize regime is char-`p` with `n = 2^30`, where `GaussianEnergyBound` is in fact FALSE (the DC term
beats Wick; see `DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt` and
`PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt`). So this brick closes the char-0
input the floor names, NOT the open char-`p` transfer — it discharges a load-bearing named
hypothesis (`henergy`) that was passed unproven across the in-tree reduction, and packages the
char-0 bound as a clean carrier.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option linter.style.longLine false

open Finset Nat
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.NegationClosedWalk

namespace ProximityGap.Frontier.CharZeroWickEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- `rEnergy G r` as the cardinality of the product-filtered set `{(v,w) : ∑v = ∑w}`. The defining
nested indicator double-sum is exactly this card. -/
theorem rEnergy_eq_card_product_filter (G : Finset F) (r : ℕ) :
    rEnergy G r =
      ((Fintype.piFinset (fun _ : Fin r => G) ×ˢ
          Fintype.piFinset (fun _ : Fin r => G)).filter
        (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
  classical
  rw [rEnergy, Finset.card_filter, Finset.sum_product]

/-- **The negation-closure energy↔zero-sum identity (`henergy`), proven.** For a negation-closed
`G` (`∀ g ∈ G, −g ∈ G`), the `r`-fold additive energy equals the zero-sum count of `2r`-tuples:

> `rEnergy G r = zeroSumCount G (2r)`.

The bijection is `(v,w) ↦ Fin.append v (−∘w)` (concatenate the first `r` coordinates `v` with the
negation of the second `r` coordinates `w`); its sum is `∑v + ∑(−w) = ∑v − ∑w`, which is `0` exactly
when `∑v = ∑w`. Negation-closure ensures `−∘w` lands in `G`. The inverse splits a `2r`-tuple `c`
into `(c ∘ castAdd, −∘(c ∘ natAdd))`. -/
theorem rEnergy_eq_zeroSumCount (G : Finset F) (r : ℕ) (hneg : ∀ g ∈ G, -g ∈ G) :
    rEnergy G r = zeroSumCount G (2 * r) := by
  classical
  rw [rEnergy_eq_card_product_filter]
  have htwo : 2 * r = r + r := two_mul r
  set Pprod := (Fintype.piFinset (fun _ : Fin r => G) ×ˢ
      Fintype.piFinset (fun _ : Fin r => G)).filter
        (fun p => ∑ i, p.1 i = ∑ i, p.2 i) with hPprod
  -- the zero-sum count over the `r + r` index (append-natural form)
  set Pzero := (Fintype.piFinset (fun _ : Fin (r + r) => G)).filter
      (fun c => ∑ i, c i = 0) with hPzero
  have hcard : Pprod.card = Pzero.card := by
    refine Finset.card_nbij'
      (fun p => Fin.append p.1 (fun i => - p.2 i))
      (fun c => (fun i => c (Fin.castAdd r i), fun i => - c (Fin.natAdd r i)))
      ?_ ?_ ?_ ?_
    · -- forward maps Pprod → Pzero
      intro p hp
      simp only [Finset.mem_coe, hPprod, Finset.mem_filter, Finset.mem_product,
        Fintype.mem_piFinset] at hp
      obtain ⟨⟨hv, hw⟩, hsum⟩ := hp
      simp only [Finset.mem_coe, hPzero, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]; exact hv _
        · rw [Fin.append_right]; exact hneg _ (hw _)
      · rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [Finset.sum_neg_distrib, hsum]; ring
    · -- backward maps Pzero → Pprod
      intro c hc
      simp only [Finset.mem_coe, hPzero, Finset.mem_filter, Fintype.mem_piFinset] at hc
      obtain ⟨hcmem, hcsum⟩ := hc
      simp only [Finset.mem_coe, hPprod, Finset.mem_filter, Finset.mem_product,
        Fintype.mem_piFinset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i; exact hcmem _
      · intro i; exact hneg _ (hcmem _)
      · show ∑ i, c (Fin.castAdd r i) = ∑ i, - c (Fin.natAdd r i)
        rw [Fin.sum_univ_add] at hcsum
        rw [Finset.sum_neg_distrib]
        linear_combination hcsum
    · -- left inverse on Pprod
      intro p _
      refine Prod.ext ?_ ?_
      · funext i; simp only; rw [Fin.append_left]
      · funext i; simp only; rw [Fin.append_right]; ring
    · -- right inverse on Pzero
      intro c _
      funext i
      simp only
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
      · rw [Fin.append_right]; ring
  rw [hcard, hPzero, zeroSumCount, htwo]

variable [CharZero F]

/-- **The char-0 Wick / Gaussian energy bound, unconditional for `μ_{2^k}`.** For a finset `G` of
`2^k`-th roots of unity (`k ≥ 1`) in a characteristic-zero field and any `r`,

> `GaussianEnergyBound G r` :  `E_r(G) ≤ (2r−1)‼·|G|^r`,

with NO hypothesis beyond `G ⊆ μ_{2^k}` and negation-closure (automatic for `μ_{2^k}`). Proof:
`rEnergy = zeroSumCount` (the negation-closure bijection `rEnergy_eq_zeroSumCount`), then
`zeroSumCount G (2r) ≤ (2r−1)‼·|G|^r` (Lam–Leung antipodal closure,
`zeroSumCount_le_doubleFactorial_dyadic`). -/
theorem gaussianEnergyBound_dyadic {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    GaussianEnergyBound G r := by
  unfold GaussianEnergyBound
  have hnat : rEnergy G r ≤ (2 * r - 1)‼ * G.card ^ r := by
    rw [rEnergy_eq_zeroSumCount G r hneg]
    exact zeroSumCount_le_doubleFactorial_dyadic hk G hG
  calc (rEnergy G r : ℝ)
      ≤ (((2 * r - 1)‼ * G.card ^ r : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by push_cast; ring

end ProximityGap.Frontier.CharZeroWickEnergy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroWickEnergy.rEnergy_eq_zeroSumCount
#print axioms ProximityGap.Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic
