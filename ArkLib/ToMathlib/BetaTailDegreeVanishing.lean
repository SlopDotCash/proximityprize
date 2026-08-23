/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine

/-!
# Issue #304 — the tail beyond the counting range: X-degree vanishing + window propagation

The faithful curve form (`FaithfulCurveExtraction.CurveFamilyData` via
`gammaGenuine_eq_curve_sum`) needs the genuine-coefficient tail `αGenuine t = 0` for **all**
`t ≥ n`, while the matching machinery
(`αGenuine_eq_zero_on_range_of_matching_monic`) only supplies it on a finite counting window
`[k, T]`.  This file settles what the `(A.1)` recursion itself can and cannot contribute to
that tail, and proves the strongest true propagation statement.

## The analysis (verified here, recorded for honesty)

Write the `(A.1)` recursion (in-tree: `βHensel_succ`)

`β_{T+1} = − ∑_{i₁ ≤ T+1} ∑_{λ ⊢ T+1−i₁, (T+1) ∉ λ} W^{i₁+δ−1} · ξ^{2i₁+Σλ−2} · B_{i₁,λ} · ∏_{l ∈ λ} β_l`.

* **The naive window propagation `[k, T] → T+1` is FALSE.**  A term at order `T+1` survives
  whenever **no** part of `λ` lies in the vanishing window.  Since every part of a surviving
  partition is `< T+1` (`surviving_parts_lt`), parts avoid `[k, T]` exactly when they are all
  `< k` — and partitions of `T+1−i₁` with all parts `< k` certainly exist (e.g. all parts
  equal to `1`).  The products of *small-index* `β_l ≠ 0` survive, so vanishing on `[k, T]`
  alone forces nothing at `T+1`.  (Not formalized as a refutation; recorded as the reason the
  hypotheses below have the shape they have.)

* **The true propagation needs the full initial segment `[1, T₀]`.**  If `β_l = 0` for **all**
  `1 ≤ l ≤ T₀` (note `β₀ = mk X ≠ 0` is never referenced: partition parts are positive), then
  at order `k+1 ≤ T₀+1` every partition with at least one part has that part in `[1, k] ⊆
  [1, T₀]`, killing the product.  The **only** surviving term is the empty partition `λ = ∅`
  at `i₁ = k+1`, contributing `−W^k · ξ^{2k} · B_{k+1,∅}`, i.e. the order-`(k+1)` **X-Hasse
  coefficient** of `R` (`βHensel_succ_eq_neg_hasse_of_window`, proven below with **no** degree
  hypothesis).  So full-segment vanishing alone does *not* propagate either — the honest tail
  is **algebraic-degree**:

* **`B_{i₁,λ}` vanishes above the X-degree of `R`** (`B_coeff_eq_zero_of_natDegree_coeff_lt`):
  `B_{i₁,λ}` is built from the `i₁`-th Hasse derivative on the lift-`X` layer
  (`hasseDerivX i1`), which kills every `Y`-coefficient of `X`-degree `< i₁`
  (`Polynomial.hasseDeriv_eq_zero_of_lt_natDegree`).  This is the `X`-side dual of the
  in-tree `Y`-side vanishing `B_coeff_eq_zero_of_natDegree_lt` (`BCoeffVanishing.lean`).

* **The capstone** (`βHensel_eq_zero_of_initial_window`): if `β_l = 0` on the full initial
  segment `[1, T₀]` and every `Y`-coefficient of `R` has `X`-degree `≤ T₀`, then `β_t = 0`
  for **all** `t ≥ 1` — by strong induction, each successor order `k+1 > T₀` reduces to the
  empty-partition Hasse coefficient of order `k+1 > T₀ ≥ deg_X R`, which vanishes by degree.

* **Transport to the genuine coefficients**: with the per-`t` lift identity
  (`S5Genuine.LiftIdentityAt`, the `(P2)` bridge carried as an explicit hypothesis exactly as
  in `claim58_genuine`), `βHensel`-vanishing and `αGenuine`-vanishing move both ways
  (`αGenuine_eq_zero_of_initial_window`, `βHensel_eq_zero_of_αGenuine_eq_zero`), giving the
  end-to-end tail producer `αGenuine_tail_eq_zero_of_window_of_lift` and the
  `htail`-shaped corollary `htail_of_window_of_lift` consumed by
  `FaithfulCurveExtraction.gammaGenuine_eq_curve_sum`.

## Honest caveat (cross-lane)

The genuine §5 chain supplies `αGenuine`-vanishing only on `[k, T]` with `k ≥ 1` the curve
degree — the coefficients **below** `k` are the curve itself and are *not* zero.  The
full-initial-segment hypothesis `[1, T₀]` of this file therefore matches the **recentered**
root (curve part subtracted), or the degenerate `k = 1` instantiation of the matching window.
Producing the recentered window from the matching machinery is a separate lane; this file
proves the strongest propagation that is actually true (the `[k, T]`-window version being
false, per the analysis above).

Everything is kernel-clean: no `sorry`/`admit`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5.2.6 (Claim 5.8/5.8′), Appendix A.4 (recursion (A.1)).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

namespace BCIKS20.HenselNumerator.BetaTail

variable {F : Type} [Field F]

/-! ## 1. X-side degree vanishing of the Hasse layers (the dual of `BCoeffVanishing`) -/

/-- The `Y`-layer Hasse derivative `Δ_Y^m` does not raise the **lift-`X` degree** of any
`Y`-coefficient: each coefficient of `Δ_Y^m R` is a `ℕ`-scalar multiple of a coefficient of
`R` (`Polynomial.hasseDeriv_coeff`), so a uniform `X`-degree bound transports. -/
theorem natDegree_coeff_hasseDerivY_le {dX : ℕ} (m : ℕ) (R : F[X][X][Y])
    (h : ∀ j, (R.coeff j).natDegree ≤ dX) (j : ℕ) :
    ((hasseDerivY m R).coeff j).natDegree ≤ dX := by
  unfold hasseDerivY
  rw [Polynomial.hasseDeriv_coeff]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_natCast, zero_add]
  exact h (j + m)

/-- **`Δ_X^{i₁}` kills `R` above its lift-`X` degree.**  If every `Y`-coefficient of `R` has
`X`-degree `≤ dX < i₁`, then the `i₁`-th lift-`X`-layer Hasse derivative vanishes — the
mechanical polynomial fact behind the algebraic-degree tail. -/
theorem hasseDerivX_eq_zero_of_natDegree_coeff_lt {i1 dX : ℕ} (R : F[X][X][Y])
    (h : ∀ j, (R.coeff j).natDegree ≤ dX) (hlt : dX < i1) :
    hasseDerivX i1 R = 0 := by
  unfold hasseDerivX
  rw [Polynomial.sum_def]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ ((h n).trans_lt hlt),
    Polynomial.monomial_zero_right]

variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The `𝒪`-representative of the iterated Hasse coefficient vanishes above the lift-`X`
degree of `R`, for **every** `Y`-Hasse order `m`. -/
theorem hasseCoeffRepr𝒪_eq_zero_of_natDegree_coeff_lt (x₀ : F) (R : F[X][X][Y])
    {i1 dX : ℕ} (m : ℕ) (h : ∀ j, (R.coeff j).natDegree ≤ dX) (hlt : dX < i1) :
    hasseCoeffRepr𝒪 H x₀ R i1 m = 0 := by
  unfold hasseCoeffRepr𝒪
  rw [hasseDerivX_eq_zero_of_natDegree_coeff_lt (hasseDerivY m R)
      (natDegree_coeff_hasseDerivY_le m R h) hlt,
    Polynomial.Bivariate.evalX_eq_map, Polynomial.map_zero, map_zero]

/-- **`B_{i₁,λ}` vanishes above the lift-`X` degree of `R`** — the `X`-side dual of
`B_coeff_eq_zero_of_natDegree_lt` (`BCoeffVanishing.lean`), for every partition `λ`. -/
theorem B_coeff_eq_zero_of_natDegree_coeff_lt (x₀ : F) (R : F[X][X][Y])
    {i1 dX : ℕ} {m : ℕ} (lam : Nat.Partition m)
    (h : ∀ j, (R.coeff j).natDegree ≤ dX) (hlt : dX < i1) :
    B_coeff H x₀ R i1 lam = 0 := by
  unfold B_coeff
  rw [hasseCoeffRepr𝒪_eq_zero_of_natDegree_coeff_lt H x₀ R (sigmaLambda lam) h hlt]
  simp

/-! ## 2. The window collapse: under full initial-segment vanishing, only the empty
partition survives -/

/-- **The window collapse (no degree hypothesis).**  If `βHensel l = 0` for all
`1 ≤ l ≤ k`, the `(A.1)` sum at order `k+1` collapses to its single empty-partition term:
`βHensel (k+1) = −(W^k · ξ^{2k} · hasseCoeffRepr𝒪 (k+1) 0)` — the order-`(k+1)` lift-`X`
Hasse coefficient of `R` at `(x₀, ·)` is the **exact** tail obstruction.  Every partition
with a part has all its parts in `[1, k]` (`surviving_parts_lt` + positivity), so its
`∏_l β_l` factor vanishes; the only partition without parts is `λ = ∅ ⊢ 0` at `i₁ = k+1`
(with `prefactor = multinomial ∅ = 1` and `∏ = 1`). -/
theorem βHensel_succ_eq_neg_hasse_of_window (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (hwin : ∀ l, 1 ≤ l → l ≤ k → βHensel H x₀ R hHyp l = 0) :
    βHensel H x₀ R hHyp (k + 1)
      = -(W𝒪 H ^ k * ClaimA2.ξ x₀ R H hHyp ^ (2 * k)
          * hasseCoeffRepr𝒪 H x₀ R (k + 1) 0) := by
  classical
  rw [βHensel_succ, Finset.sum_range_succ]
  -- (1) the `i₁ ≤ k` block vanishes: every surviving partition has a part in `[1, k]`.
  have hblock : (∑ i1 ∈ Finset.range (k + 1),
      ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                (fun lam => (k + 1) ∉ lam.parts),
        W𝒪 H ^ (i1 + deltaSave i1 - 1)
          * ClaimA2.ξ x₀ R H hHyp ^ (2 * i1 + sigmaLambda lam - 2)
          * B_coeff H x₀ R i1 lam
          * partitionProd lam
              (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i1 hi1 => Finset.sum_eq_zero fun lam hlam => ?_
    have hi1' : i1 < k + 1 := Finset.mem_range.mp hi1
    have hsurv : (k + 1) ∉ lam.parts := (Finset.mem_filter.mp hlam).2
    have hne : lam.parts ≠ 0 := by
      intro h0
      have hsum := lam.parts_sum
      rw [h0, Multiset.sum_zero] at hsum
      omega
    obtain ⟨l, hl⟩ := Multiset.exists_mem_of_ne_zero hne
    have hl1 : 0 < l := lam.parts_pos hl
    have hlk : l < k + 1 := surviving_parts_lt lam hsurv hl
    have hprod : partitionProd lam
        (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0) = 0 := by
      rw [partitionProd]
      have hmem : (0 : 𝒪 H) ∈ lam.parts.map
          (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0) :=
        Multiset.mem_map.mpr ⟨l, hl, by
          simp only [dif_pos hlk]
          exact hwin l hl1 (by omega)⟩
      exact Multiset.prod_eq_zero (M₀ := 𝒪 H) hmem
    rw [hprod, mul_zero]
  rw [hblock, zero_add]
  -- (2) the `i₁ = k+1` block: the unique (empty) partition contributes the Hasse term.
  refine congrArg Neg.neg ?_
  have hparts : ∀ lam : Nat.Partition (k + 1 - (k + 1)), lam.parts = 0 := by
    intro lam
    refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
    have h1 := lam.parts_pos ha
    have h2 := Multiset.le_sum_of_mem ha
    rw [lam.parts_sum] at h2
    omega
  have hconst : ∀ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - (k + 1)))).filter
      (fun lam => (k + 1) ∉ lam.parts),
      W𝒪 H ^ (k + 1 + deltaSave (k + 1) - 1)
        * ClaimA2.ξ x₀ R H hHyp ^ (2 * (k + 1) + sigmaLambda lam - 2)
        * B_coeff H x₀ R (k + 1) lam
        * partitionProd lam (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)
      = W𝒪 H ^ k * ClaimA2.ξ x₀ R H hHyp ^ (2 * k)
          * hasseCoeffRepr𝒪 H x₀ R (k + 1) 0 := by
    intro lam _
    have hp := hparts lam
    have hσ : sigmaLambda lam = 0 := by rw [sigmaLambda, hp, Multiset.card_zero]
    have he1 : k + 1 + deltaSave (k + 1) - 1 = k := by
      simp [deltaSave]
    have he2 : 2 * (k + 1) + sigmaLambda lam - 2 = 2 * k := by
      rw [hσ]; omega
    have hprod : partitionProd lam
        (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0) = 1 := by
      rw [partitionProd, hp, Multiset.map_zero, Multiset.prod_zero]
    have hB : B_coeff H x₀ R (k + 1) lam = hasseCoeffRepr𝒪 H x₀ R (k + 1) 0 := by
      unfold B_coeff prefactor
      rw [hσ, hp, Multiset.toFinset_zero, Nat.multinomial_empty, one_smul]
    rw [he1, he2, hB, hprod, mul_one]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  have hfilter : (Finset.univ : Finset (Nat.Partition (k + 1 - (k + 1)))).filter
      (fun lam => (k + 1) ∉ lam.parts) = Finset.univ := by
    refine Finset.filter_true_of_mem fun lam _ => ?_
    rw [hparts lam]
    exact Multiset.notMem_zero _
  have hcard : Fintype.card (Nat.Partition (k + 1 - (k + 1))) = 1 := by
    refine Fintype.card_eq_one_iff.mpr
      ⟨⟨0, by simp, by simp⟩, fun lam => Nat.Partition.ext (by rw [hparts lam])⟩
  rw [hfilter, Finset.card_univ, hcard, one_nsmul]

/-! ## 3. The algebraic-degree tail -/

/-- **One-step tail vanishing.**  Full window `[1, k]` vanishing plus the lift-`X` degree
bound `dX < k+1` on `R` force `βHensel (k+1) = 0`: the surviving empty-partition Hasse
coefficient dies by degree. -/
theorem βHensel_succ_eq_zero_of_window_of_natDegree_le (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) {dX : ℕ}
    (hdX : ∀ j, (R.coeff j).natDegree ≤ dX) (hdk : dX < k + 1)
    (hwin : ∀ l, 1 ≤ l → l ≤ k → βHensel H x₀ R hHyp l = 0) :
    βHensel H x₀ R hHyp (k + 1) = 0 := by
  rw [βHensel_succ_eq_neg_hasse_of_window H x₀ R hHyp k hwin,
    hasseCoeffRepr𝒪_eq_zero_of_natDegree_coeff_lt H x₀ R 0 hdX hdk, mul_zero, neg_zero]

/-- **The capstone — full tail propagation by strong induction.**  If `βHensel l = 0` on the
full initial segment `[1, T₀]` and every `Y`-coefficient of `R` has lift-`X` degree `≤ T₀`,
then `βHensel t = 0` for **all** `t ≥ 1`: each successor order `k+1 > T₀` collapses to the
order-`(k+1)` Hasse coefficient (window collapse, the inductive hypothesis extending the
window) which vanishes by degree (`k+1 > T₀ ≥ deg_X R`). -/
theorem βHensel_eq_zero_of_initial_window (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) {T₀ : ℕ}
    (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hwin : ∀ l, 1 ≤ l → l ≤ T₀ → βHensel H x₀ R hHyp l = 0) :
    ∀ t, 1 ≤ t → βHensel H x₀ R hHyp t = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht1
    by_cases hle : t ≤ T₀
    · exact hwin t ht1 hle
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      refine βHensel_succ_eq_zero_of_window_of_natDegree_le H x₀ R hHyp k hdX (by omega) ?_
      intro l hl1 hlk
      exact ih l (by omega) hl1

/-! ## 4. Transport to the genuine coefficients (via the per-`t` lift identity) -/

/-- **The genuine-coefficient tail.**  Under the window + degree hypotheses of the capstone
and the per-`t` lift identity (`LiftIdentityAt`, the `(P2)` bridge carried as an explicit
hypothesis exactly as in `claim58_genuine`), the genuine Hensel coefficient vanishes at every
`t ≥ 1`: `βHensel t = 0` (capstone), so `αGenuine t · (W^{t+1}·ξ^{2t−1}) = 0`, and the
denominator is nonzero (`den_ne_zero`). -/
theorem αGenuine_eq_zero_of_initial_window (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) {T₀ : ℕ}
    (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hwin : ∀ l, 1 ≤ l → l ≤ T₀ → βHensel H x₀ R hHyp l = 0)
    {t : ℕ} (ht1 : 1 ≤ t)
    (hlift : S5Genuine.LiftIdentityAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 := by
  have hβ : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t) = 0 := by
    rw [βHensel_eq_zero_of_initial_window H x₀ R hHyp hdX hwin t ht1, map_zero]
  unfold S5Genuine.LiftIdentityAt at hlift
  rw [hβ] at hlift
  have hprod : αGenuine H x₀ R hHyp t
      * (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1)
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) = 0 := by
    rw [← mul_assoc]
    exact hlift.symm
  exact (mul_eq_zero.mp hprod).resolve_right (den_ne_zero H x₀ R hHyp t)

/-- **The converse bridge — window supply from the genuine coefficients.**  At any `t` where
the lift identity holds, `αGenuine t = 0` forces `βHensel t = 0` (the embedding is injective).
This converts an `αGenuine`-vanishing window into the `βHensel`-vanishing window the capstone
consumes. -/
theorem βHensel_eq_zero_of_αGenuine_eq_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) {t : ℕ}
    (hlift : S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (hα : αGenuine H x₀ R hHyp t = 0) :
    βHensel H x₀ R hHyp t = 0 := by
  have h0 : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t) = embeddingOf𝒪Into𝕃 H 0 := by
    unfold S5Genuine.LiftIdentityAt at hlift
    rw [hlift, hα, zero_mul, zero_mul, map_zero]
  exact embeddingOf𝒪Into𝕃_injective (Fact.out (p := 0 < H.natDegree)) h0

/-- **End-to-end tail producer.**  From an `αGenuine`-vanishing window on the full initial
segment `[1, T₀]`, the lift identity at every order, and the lift-`X` degree bound
`deg_X R ≤ T₀`, the genuine coefficients vanish at **every** `t ≥ 1` — the recursion route
to the tail beyond the counting range. -/
theorem αGenuine_tail_eq_zero_of_window_of_lift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) {T₀ : ℕ}
    (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hlift : ∀ t, S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (hα : ∀ l, 1 ≤ l → l ≤ T₀ → αGenuine H x₀ R hHyp l = 0) :
    ∀ t, 1 ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  have hwin : ∀ l, 1 ≤ l → l ≤ T₀ → βHensel H x₀ R hHyp l = 0 := fun l h1 hT =>
    βHensel_eq_zero_of_αGenuine_eq_zero H x₀ R hHyp (hlift l) (hα l h1 hT)
  intro t ht1
  exact αGenuine_eq_zero_of_initial_window H x₀ R hHyp hdX hwin ht1 (hlift t)

/-- The `htail` shape consumed by `FaithfulCurveExtraction.gammaGenuine_eq_curve_sum`:
vanishing from any `n ≥ 1` on. -/
theorem htail_of_window_of_lift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) {T₀ n : ℕ} (hn : 1 ≤ n)
    (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hlift : ∀ t, S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (hα : ∀ l, 1 ≤ l → l ≤ T₀ → αGenuine H x₀ R hHyp l = 0) :
    ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 := fun t ht =>
  αGenuine_tail_eq_zero_of_window_of_lift H x₀ R hHyp hdX hlift hα t (hn.trans ht)

end BCIKS20.HenselNumerator.BetaTail

-- Axiom audit: every declaration must rest only on `[propext, Classical.choice, Quot.sound]`.
#print axioms BCIKS20.HenselNumerator.BetaTail.natDegree_coeff_hasseDerivY_le
#print axioms BCIKS20.HenselNumerator.BetaTail.hasseDerivX_eq_zero_of_natDegree_coeff_lt
#print axioms BCIKS20.HenselNumerator.BetaTail.hasseCoeffRepr𝒪_eq_zero_of_natDegree_coeff_lt
#print axioms BCIKS20.HenselNumerator.BetaTail.B_coeff_eq_zero_of_natDegree_coeff_lt
#print axioms BCIKS20.HenselNumerator.BetaTail.βHensel_succ_eq_neg_hasse_of_window
#print axioms BCIKS20.HenselNumerator.BetaTail.βHensel_succ_eq_zero_of_window_of_natDegree_le
#print axioms BCIKS20.HenselNumerator.BetaTail.βHensel_eq_zero_of_initial_window
#print axioms BCIKS20.HenselNumerator.BetaTail.αGenuine_eq_zero_of_initial_window
#print axioms BCIKS20.HenselNumerator.BetaTail.βHensel_eq_zero_of_αGenuine_eq_zero
#print axioms BCIKS20.HenselNumerator.BetaTail.αGenuine_tail_eq_zero_of_window_of_lift
#print axioms BCIKS20.HenselNumerator.BetaTail.htail_of_window_of_lift
