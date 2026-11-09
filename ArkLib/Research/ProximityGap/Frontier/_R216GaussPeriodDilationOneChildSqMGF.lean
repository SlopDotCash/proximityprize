/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R216 Gauss-period one-child square MGF)
-/
import ArkLib.Research.ProximityGap.Frontier._R215OneChildDirectMGFLaw
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# R216 (#466): concrete Gauss-period dilation endpoint for one square-MGF child

R215 proves the abstract one-child direct-MGF consumer under a permutation of
the two normalized-square child spectra.  In the concrete Gauss-period dilation
recursion the children are

```text
rawLeft  b = ‖η_G(b)‖
rawRight b = ‖η_G(ζ * b)‖
```

and multiplication by nonzero `ζ` is a permutation of the full frequency set.
This file wires that structural fact into the R215 square-normalized endpoint.
The remaining analytic input is exactly the one-child law

```text
LargeIndexChildQuarterMGFLaw univ (fun b => ‖η_G(b)‖) σ.
```

**Correction (audit R-144, 2026-10-28): this is NOT an instantiable prize-index endpoint.**
The nonzero-dilation permutation and square-normalization algebra are valid, but:

* *Wrong carrier cardinality.*  The premise `hcard` equates the **full field** cardinality `q`
  with the **quotient-index** model `DyadicTowerIndex PrizeTopIndex depth`.  No finite field
  satisfies it at any depth (`card_ne_dyadicTowerIndex_prizeTop`): the right side is even with
  the odd factor `2^122 + 3 > 1`, while `q` is a prime power.  The theorem below is therefore
  vacuous as stated; a genuine endpoint must use the correct full / nonzero / coset carrier and
  its actual cardinality (cf. `R204PrizeTowerLargeIndex.productionQ_sub_one_eq_dyadicTowerIndex_thirty`).
* *Principal (DC) spike.*  The full-frequency child law includes `b = 0`, where `η_G(0) = |G|`.
  The quarter-MGF bound then forces `exp(|G|²/(4σ²)) ≤ 2q`, i.e. `|G|² ≤ 4σ²·log(2q)`
  (`dc_spike_of_fullFreq_childLaw`, `card_sq_le_of_fullFreq_childLaw`).  Under the intended
  variance normalization `σ² ≈ |G|` this fails for production-sized children (`|G| ≫ log q`).
  `σ` is a free parameter here, so this is not impossibility for every inflated `σ`; but the
  principal spike must be removed or separately accounted for, and `σ` tied to the actual
  variance scale, before this can serve as the concrete endpoint.  The nonzero-frequency
  variants (R217 onward) remove the DC term but carry their own carrier caveats.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw
open ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- **The full-field cardinality premise is unsatisfiable (audit R-144).**  For every finite
field `F` and every depth, `|F| ≠ DyadicTowerIndex PrizeTopIndex depth = (2^128+192)·2^depth`:
that number is even with odd factor `2^122 + 3 > 1`, so it is not a prime power. -/
theorem card_ne_dyadicTowerIndex_prizeTop (depth : ℕ) :
    Fintype.card F ≠ DyadicTowerIndex PrizeTopIndex depth := by
  obtain ⟨p, -, k, hp, hq⟩ := FiniteField.card' F
  intro h
  have hfac : DyadicTowerIndex PrizeTopIndex depth = (2 ^ 122 + 3) * 2 ^ (depth + 6) := by
    unfold DyadicTowerIndex PrizeTopIndex
    ring
  rw [hq, hfac] at h
  have h2 : 2 ∣ p ^ (k : ℕ) := ⟨(2 ^ 122 + 3) * 2 ^ (depth + 5), by rw [h]; ring⟩
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hp2
  have hN : (2 ^ 122 + 3) ∣ 2 ^ (k : ℕ) := ⟨2 ^ (depth + 6), h⟩
  have hodd : Nat.Coprime (2 ^ 122 + 3) 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨2 ^ 121 + 1, by ring⟩
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right (k : ℕ) hodd) hN
  norm_num at h1

omit [DecidableEq F] in
/-- **The full-frequency child law carries the DC spike (audit R-144).**  Since `η_G(0) = |G|`,
the quarter-MGF law over all of `F` forces `exp(|G|²/(4σ²)) ≤ 2q`. -/
theorem dc_spike_of_fullFreq_childLaw (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (h : LargeIndexChildQuarterMGFLaw (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖) σ) :
    Real.exp ((G.card : ℝ) ^ 2 / (4 * σ ^ 2)) ≤ 2 * (Fintype.card F : ℝ) := by
  have hsum : (∑ b : F, Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)))
      ≤ 2 * ((Finset.univ : Finset F).card : ℝ) := h
  have h0 : ‖eta ψ G 0‖ = (G.card : ℝ) := by simp [eta]
  have hsingle : Real.exp ((1 / 4 : ℝ) * (‖eta ψ G 0‖ ^ 2 / σ ^ 2))
      ≤ ∑ b : F, Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) :=
    Finset.single_le_sum (f := fun b => Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)))
      (fun b _ => (Real.exp_pos _).le) (Finset.mem_univ 0)
  have heq : (1 / 4 : ℝ) * ((G.card : ℝ) ^ 2 / σ ^ 2) = (G.card : ℝ) ^ 2 / (4 * σ ^ 2) := by
    ring
  rw [h0, heq] at hsingle
  rw [Finset.card_univ] at hsum
  linarith

omit [DecidableEq F] in
/-- Log form of the DC spike: for `σ > 0`, the full-frequency child law forces
`|G|² ≤ 4σ²·log(2q)`, which fails under the variance normalization `σ² ≈ |G|` once
`|G| > 4·log(2q)`. -/
theorem card_sq_le_of_fullFreq_childLaw (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hσ : 0 < σ)
    (h : LargeIndexChildQuarterMGFLaw (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖) σ) :
    (G.card : ℝ) ^ 2 ≤ 4 * σ ^ 2 * Real.log (2 * (Fintype.card F : ℝ)) := by
  have hq : (0 : ℝ) < 2 * (Fintype.card F : ℝ) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hlog := (Real.le_log_iff_exp_le hq).mpr (dc_spike_of_fullFreq_childLaw ψ G h)
  have h4 : (0 : ℝ) < 4 * σ ^ 2 := by positivity
  rw [div_le_iff₀ h4] at hlog
  linarith

/-- Concrete prize-square endpoint for the actual dilation-recursion parent,
using only the one-child square-normalized quarter-MGF law for `G`.

**Vacuous as stated (audit R-144):** its premise `hcard` is unsatisfiable for every finite
field (`card_ne_dyadicTowerIndex_prizeTop`), and the full-frequency child law `hLeft` carries
the DC spike (`dc_spike_of_fullFreq_childLaw`).  Only the deterministic dilation/Cauchy
wiring is meaningful; it is not a concrete prize-index endpoint. -/
theorem prize_sq_of_gaussPeriod_dilation_one_child_sqMGF
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (depth : ℕ) {σR Mmax n Q : ℝ} {r : ℕ}
    (hσR : 0 < σR)
    (hcard : (Finset.univ : Finset F).card = DyadicTowerIndex PrizeTopIndex depth)
    (hLeft : LargeIndexChildQuarterMGFLaw
      (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖) σR)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σR ^ 2)) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  let shift : Equiv.Perm F :=
    { toFun := fun b => ζ * b
      invFun := fun c => ζ⁻¹ * c
      left_inv := by
        intro b
        simp [hζ]
      right_inv := by
        intro c
        field_simp [hζ] }
  refine prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF
    (Finset.univ : Finset F)
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖)
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖)
    shift depth hσR hcard ?_ ?_ ?_ ?_ hLeft hMmax hn hQ ?_ hr hrQ ?_
  · intro b _
    exact norm_nonneg _
  · intro b _
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · intro b
    simp [shift]
  · intro b _
    rfl
  · simpa using hP
  · simpa using hmoment

end

end ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF.card_ne_dyadicTowerIndex_prizeTop
#print axioms
  ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF.card_sq_le_of_fullFreq_childLaw
#print axioms
  ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF.prize_sq_of_gaussPeriod_dilation_one_child_sqMGF
