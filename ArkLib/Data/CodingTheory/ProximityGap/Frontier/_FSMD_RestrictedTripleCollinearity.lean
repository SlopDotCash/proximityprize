/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# Restricted-universe triple collinearity at P1: sharp rung + exact barrier

**Angle (issue #334, P1 rate-quarter predecessor pin):** sharpen the high-core
triple-collinearity trigger by restricting to the universe *outside* a pencil core.
Three scalars off a line `(a,r)` with core size `z` keep fresh agreement mass
`≥ t - (k-1)` inside `|universe| - z` coordinates; Bonferroni forces their triple
intersection `≥ 3(t-k+1) - 2(N-z)`, and any triple intersection `≥ k` forces slope
equality, i.e. collinearity of the three lifted points.

**Part A (positive, parametric):** we formalize that rung sharply:
`restricted_triple_slope_eq` — off-line triples above a core of size `z` are
collinear whenever `2*(N - z) + (k-1) < 3*(t - (k-1))` — and its secant-membership
corollary `restricted_triple_third_point_on_secant`.  This is the exact
restricted-universe strengthening of the legacy trigger `3t + 2z > 2N + 4(k-1)`.

**Part B (exact P1 arithmetic, the honest verdict):** at
`N = 2^30 = 1073741824`, `K = 2^28 = 268435456`, `T = 592794966` the trigger is
**dead for every admissible pencil and at every cascade depth**:

* `p1_trigger_iff`: the Part-A hypothesis holds iff `z ≥ 721420286`;
* `p1_admissible_core_never_triggers`: admissible cores (`z + 2 ≤ T`, required by
  the four-pencil extraction) never trigger — core shortfall
  `721420286 - (T-2) = 128625322`, mass shortfall
  `K - (3(T-K+1) - 2(N-(T-2))) = 268435456 - 11184813 = 257250643`
  (`p1_saturated_mass_shortfall`);
* `p1_offline_window`: the non-vacuous window `z ∈ [721420286, 749382313]`
  (width `27962027`) exists but every point of it is inadmissible;
* `p1_cascade_never_fires`: iterating the argument off `j` saturated pencils
  (mass `T - j(K-1)`, doubled universe bound `2N - 2j(T-2) + j(j-1)(K-1)` from
  pairwise core-rigidity `≤ K-1`) fails for **all** `j : ℤ` — the underlying
  quadratic `268435455 j² - 1029002581 j + 1275068412` has negative discriminant
  `-310247965620728279`, so no cascade depth ever fires (best case `j = 1`:
  triple mass `11184813`, `24×` below `K`);
* `p1_pairwise_forcing_dead` / `p1_corradi_vacuous`: even *pairwise*
  Plotkin/Corrádi counting on the fresh sets cannot force a single `K`-overlap
  pair inside the restricted universe: `(T-K+1)² = 105209092376159121` is below
  `(K-1)(N-T+2) = 129103189194921300` (slack `2.39 × 10¹⁶`), so the
  Cauchy–Schwarz/Corrádi bound places no constraint at any family size, and the
  `j → ∞` forced-overlap limit `m²/U ≈ 218753979 < K` never reaches `K`;
  the pairwise trigger would need `z ≥ 681807413` (`p1_pairwise_trigger_bound`),
  still `89012449` above the admissible cap.

Numeric companion: `scripts/probes/probe_FSMD_Bonferroni_restricted_cascade.py`.

**Conclusion (BARRIER for this angle):** restricted-universe Bonferroni — triple
or pairwise, at any cascade depth, even granting maximal saturation `z = T-2` of
every removed pencil — cannot produce the fourth pencil at P1.  The trigger
window is real but lives strictly above the admissible-core cap.  All
inequalities here are exact and machine-checked; nothing in this file assumes
the bad-count bound.
-/

set_option autoImplicit false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

namespace ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity

/-! ## Part A: the sharp restricted-universe triple rung (parametric) -/

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Restricted-universe triple slope forcing.**  Three lifted points strictly off
one polynomial line `(a,r)` whose joint core has size `z` retain fresh agreement
mass `≥ t - (k-1)` inside the `|ι| - z` coordinates off the core.  If
`2*(|ι| - z) + (k-1) < 3*(t - (k-1))` then Bonferroni forces a triple
intersection of size `≥ k`, and the slope polynomials (degree `< k`) coincide:
the three points are collinear.  This is the exact sharpening of the legacy
trigger `3t + 2z > 2|ι| + 4(k-1)` obtained by deleting the core from the
universe. -/
theorem restricted_triple_slope_eq
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k t : ℕ} (hk : 1 ≤ k)
    {a r : F[X]} (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    {gamma₁ gamma₂ gamma₃ : F} {q₁ q₂ q₃ : F[X]}
    (h12 : gamma₁ ≠ gamma₂) (h13 : gamma₁ ≠ gamma₃)
    (hq₁ : q₁.natDegree < k) (hq₂ : q₂.natDegree < k) (hq₃ : q₃.natDegree < k)
    (hoff₁ : q₁ ≠ a + C gamma₁ * r) (hoff₂ : q₂ ≠ a + C gamma₂ * r)
    (hoff₃ : q₃ ≠ a + C gamma₃ * r)
    (ht₁ : t ≤ (fullAgreement dom u₀ u₁ gamma₁ q₁).card)
    (ht₂ : t ≤ (fullAgreement dom u₀ u₁ gamma₂ q₂).card)
    (ht₃ : t ≤ (fullAgreement dom u₀ u₁ gamma₃ q₃).card)
    (hgap : 2 * (Fintype.card ι - (jointCore dom u₀ u₁ a r).card) + (k - 1) <
      3 * (t - (k - 1))) :
    slopePolynomial gamma₁ gamma₂ q₁ q₂ = slopePolynomial gamma₁ gamma₃ q₁ q₃ := by
  classical
  set D : Finset ι := jointCore dom u₀ u₁ a r with hD
  set A₁ : Finset ι := fullAgreement dom u₀ u₁ gamma₁ q₁ with hA₁
  set A₂ : Finset ι := fullAgreement dom u₀ u₁ gamma₂ q₂ with hA₂
  set A₃ : Finset ι := fullAgreement dom u₀ u₁ gamma₃ q₃ with hA₃
  -- off-line core caps
  have hcap₁ : (A₁ ∩ D).card ≤ k - 1 :=
    fullAgreement_inter_jointCore_card_le dom u₀ u₁ hk hq₁ hadeg hrdeg hoff₁
  have hcap₂ : (A₂ ∩ D).card ≤ k - 1 :=
    fullAgreement_inter_jointCore_card_le dom u₀ u₁ hk hq₂ hadeg hrdeg hoff₂
  have hcap₃ : (A₃ ∩ D).card ≤ k - 1 :=
    fullAgreement_inter_jointCore_card_le dom u₀ u₁ hk hq₃ hadeg hrdeg hoff₃
  -- fresh mass lower bounds
  have hsplit : ∀ A : Finset ι, (A \ D).card = A.card - (A ∩ D).card := by
    intro A
    rw [Finset.card_sdiff, Finset.inter_comm D A]
  have hfresh₁ : t - (k - 1) ≤ (A₁ \ D).card := by
    have h := hsplit A₁; omega
  have hfresh₂ : t - (k - 1) ≤ (A₂ \ D).card := by
    have h := hsplit A₂; omega
  have hfresh₃ : t - (k - 1) ≤ (A₃ \ D).card := by
    have h := hsplit A₃; omega
  -- restricted universe
  have hVcard : (Finset.univ \ D).card = Fintype.card ι - D.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hsub : ∀ A : Finset ι, A \ D ⊆ Finset.univ \ D := fun A =>
    Finset.sdiff_subset_sdiff (Finset.subset_univ A) (Finset.Subset.refl D)
  -- Bonferroni in the restricted universe
  have htriple : k - 1 < ((A₁ \ D) ∩ (A₂ \ D) ∩ (A₃ \ D)).card := by
    refine three_set_inter_card_gt (Finset.univ \ D) (A₁ \ D) (A₂ \ D) (A₃ \ D)
      (t - (k - 1)) (k - 1) (hsub A₁) (hsub A₂) (hsub A₃)
      hfresh₁ hfresh₂ hfresh₃ ?_
    rw [hVcard]; exact hgap
  -- transfer to the full agreement triple intersection
  have hmono : (A₁ \ D) ∩ (A₂ \ D) ∩ (A₃ \ D) ⊆ A₁ ∩ A₂ ∩ A₃ := by
    intro i hi
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hi
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hi.1.1.1, hi.1.2.1⟩, hi.2.1⟩
  have hbig : k - 1 < (A₁ ∩ A₂ ∩ A₃).card :=
    lt_of_lt_of_le htriple (Finset.card_le_card hmono)
  -- noncollinearity would cap the triple intersection at k-1
  by_contra hslope
  have hcap := triple_fullAgreement_card_le_pred_of_slope_ne dom u₀ u₁ hk
    h12 h13 hq₁ hq₂ hq₃ hslope
  rw [← hA₁, ← hA₂, ← hA₃] at hcap
  omega

/-- **Secant membership form.**  Under the restricted-universe trigger the third
off-line point lies on the polynomial secant through the first two. -/
theorem restricted_triple_third_point_on_secant
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k t : ℕ} (hk : 1 ≤ k)
    {a r : F[X]} (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    {gamma₁ gamma₂ gamma₃ : F} {q₁ q₂ q₃ : F[X]}
    (h12 : gamma₁ ≠ gamma₂) (h13 : gamma₁ ≠ gamma₃)
    (hq₁ : q₁.natDegree < k) (hq₂ : q₂.natDegree < k) (hq₃ : q₃.natDegree < k)
    (hoff₁ : q₁ ≠ a + C gamma₁ * r) (hoff₂ : q₂ ≠ a + C gamma₂ * r)
    (hoff₃ : q₃ ≠ a + C gamma₃ * r)
    (ht₁ : t ≤ (fullAgreement dom u₀ u₁ gamma₁ q₁).card)
    (ht₂ : t ≤ (fullAgreement dom u₀ u₁ gamma₂ q₂).card)
    (ht₃ : t ≤ (fullAgreement dom u₀ u₁ gamma₃ q₃).card)
    (hgap : 2 * (Fintype.card ι - (jointCore dom u₀ u₁ a r).card) + (k - 1) <
      3 * (t - (k - 1))) :
    q₃ = (q₁ - C gamma₁ * slopePolynomial gamma₁ gamma₂ q₁ q₂) +
      C gamma₃ * slopePolynomial gamma₁ gamma₂ q₁ q₂ := by
  have hslope : slopePolynomial gamma₁ gamma₃ q₁ q₃ =
      slopePolynomial gamma₁ gamma₂ q₁ q₂ :=
    (restricted_triple_slope_eq dom u₀ u₁ hk hadeg hrdeg h12 h13
      hq₁ hq₂ hq₃ hoff₁ hoff₂ hoff₃ ht₁ ht₂ ht₃ hgap).symm
  exact third_point_on_secant_line_of_slope_eq h13 hslope

/-! ## Part B: exact P1 arithmetic — the trigger is dead for admissible pencils -/

/-- `N = 2^30`, the P1 domain size. -/
def P1N : ℕ := 1073741824

/-- `K = 2^28`, the P1 Reed–Solomon dimension (degree bound). -/
def P1K : ℕ := 268435456

/-- `T = 592794966`, the P1 predecessor agreement threshold. -/
def P1T : ℕ := 592794966

/-- **Exact trigger characterization.**  The Part-A hypothesis at P1 parameters
(`k = P1K`, `t = P1T`, `Fintype.card ι = P1N`, core size `z`) holds iff
`z ≥ 721420286`. -/
theorem p1_trigger_iff (z : ℕ) (hz : z ≤ P1N) :
    (2 * (P1N - z) + (P1K - 1) < 3 * (P1T - (P1K - 1))) ↔ 721420286 ≤ z := by
  have hN : P1N = 1073741824 := rfl
  have hK : P1K = 268435456 := rfl
  have hT : P1T = 592794966 := rfl
  omega

/-- **Admissible vacuity.**  Pencils usable by the four-pencil extraction have
`z + 2 ≤ T`; no such core ever satisfies the restricted-universe triple trigger.
Core shortfall: `721420286 - (T - 2) = 128625322`. -/
theorem p1_admissible_core_never_triggers (z : ℕ) (hz : z + 2 ≤ P1T) :
    ¬ (2 * (P1N - z) + (P1K - 1) < 3 * (P1T - (P1K - 1))) := by
  have hN : P1N = 1073741824 := rfl
  have hK : P1K = 268435456 := rfl
  have hT : P1T = 592794966 := rfl
  omega

/-- Exact core shortfall of the trigger over the admissible cap. -/
theorem p1_core_shortfall : 721420286 = (P1T - 2) + 128625322 := by
  have hT : P1T = 592794966 := rfl
  omega

/-- **Exact mass shortfall at maximal saturation** `z = T - 2`: the Bonferroni
triple mass `3(T-K+1) - 2(N-(T-2)) = 11184813` misses the collinearity demand
`K` by exactly `257250643` (a factor of `24.0`). -/
theorem p1_saturated_mass_shortfall :
    2 * (P1N - (P1T - 2)) + P1K = 3 * (P1T - (P1K - 1)) + 257250643 := by
  have hN : P1N = 1073741824 := rfl
  have hK : P1K = 268435456 := rfl
  have hT : P1T = 592794966 := rfl
  omega

/-- **The non-vacuous window is real but inadmissible.**  Off-line scalars can
exist only while `z ≤ N - (T-K+1) = 749382313`; the trigger fires from
`z = 721420286`; the window has width `27962027` and sits strictly above the
admissible cap `T - 2 = 592794964`. -/
theorem p1_offline_window :
    P1N - (P1T - (P1K - 1)) = 749382313 ∧
    749382313 - 721420286 = 27962027 ∧
    P1T - 2 < 721420286 := by
  have hN : P1N = 1073741824 := rfl
  have hK : P1K = 268435456 := rfl
  have hT : P1T = 592794966 := rfl
  omega

/-- Fresh agreement mass (lower bound) of a scalar off `j` pencils, each core
stealing at most `K - 1` coordinates: `T - j*(K-1)`. -/
def cascadeMass (j : ℤ) : ℤ := 592794966 - j * 268435455

/-- Twice the restricted-universe size (upper bound) after removing `j`
saturated cores of size `T - 2` whose pairwise overlaps are `≤ K - 1` (line
rigidity): `2N - 2j(T-2) + j(j-1)(K-1)`. -/
def cascadeUniverse2 (j : ℤ) : ℤ :=
  2 * 1073741824 - 2 * j * 592794964 + j * (j - 1) * 268435455

/-- **Cascade no-go at every depth.**  The Bonferroni triple trigger off `j`
saturated pencils demands `3*cascadeMass j - 2*universe ≥ K`, i.e. (doubled)
`6*cascadeMass j ≥ 2*K + 2*cascadeUniverse2 j`.  This FAILS for every `j : ℤ`:
the margin quadratic `268435455 j² - 1029002581 j + 1275068412` has
discriminant `-310247965620728279 < 0`, hence is positive everywhere.  Best
case `j = 1` misses by `2 × 257250643`. -/
theorem p1_cascade_never_fires (j : ℤ) :
    6 * cascadeMass j < 2 * 268435456 + 2 * cascadeUniverse2 j := by
  simp only [cascadeMass, cascadeUniverse2]
  nlinarith [sq_nonneg (536870910 * j - 1029002581)]

/-- **Pairwise Plotkin forcing is also dead.**  Even counting pairs (not
triples): fresh sets of size `m = T-K+1` inside the universe off an admissible
core can never be forced to contain a `K`-overlap pair, because the `j → ∞`
Cauchy–Schwarz forcing limit is `m²/U` and `m² < K * (N - z)` for every
admissible `z`. -/
theorem p1_pairwise_forcing_dead (z : ℕ) (hz : z + 2 ≤ P1T) :
    (P1T - (P1K - 1)) ^ 2 < P1K * (P1N - z) := by
  have hbase : (P1T - (P1K - 1)) ^ 2 < P1K * (P1N - (P1T - 2)) := by
    have h1 : P1T - (P1K - 1) = 324359511 := rfl
    have h2 : P1N - (P1T - 2) = 480946860 := rfl
    rw [h1, h2]
    norm_num [P1K]
  refine lt_of_lt_of_le hbase (Nat.mul_le_mul_left P1K ?_)
  have hN : P1N = 1073741824 := rfl
  have hT : P1T = 592794966 := rfl
  omega

/-- **Corrádi/Cauchy–Schwarz vacuity at maximal saturation.**  With
`m = T-K+1` and `U = N-(T-2)`, the Corrádi family bound
`j*(m² - U*(K-1)) ≤ U*(m-(K-1))` constrains the family size only when
`m² > U*(K-1)`; at P1 instead `m² ≤ (K-1)*U` with slack
`23894096818762179`, so arbitrarily large fresh families with all pairwise
overlaps `≤ K-1` pass every counting test. -/
theorem p1_corradi_vacuous :
    (P1T - (P1K - 1)) ^ 2 + 23894096818762179 = (P1K - 1) * (P1N - (P1T - 2)) := by
  have h1 : P1T - (P1K - 1) = 324359511 := rfl
  have h2 : P1N - (P1T - 2) = 480946860 := rfl
  have h3 : P1K - 1 = 268435455 := rfl
  rw [h1, h2, h3]
  norm_num

/-- **Exact pairwise threshold.**  The pairwise forcing limit would fire only at
core size `z ≥ 681807413 = (T-2) + 89012449`; below that, `K*(N-z)` strictly
exceeds `m²`. -/
theorem p1_pairwise_trigger_bound (z : ℕ) (hz : z ≤ 681807412) :
    (P1T - (P1K - 1)) ^ 2 < P1K * (P1N - z) := by
  have hbase : (P1T - (P1K - 1)) ^ 2 < P1K * 391934412 := by
    have h1 : P1T - (P1K - 1) = 324359511 := rfl
    rw [h1]
    norm_num [P1K]
  refine lt_of_lt_of_le hbase (Nat.mul_le_mul_left P1K ?_)
  have hN : P1N = 1073741824 := rfl
  omega

/-- The pairwise threshold sits `89012449` above the admissible cap. -/
theorem p1_pairwise_core_shortfall : 681807413 = (P1T - 2) + 89012449 := by
  have hT : P1T = 592794966 := rfl
  omega

end ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity

#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.restricted_triple_slope_eq
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.restricted_triple_third_point_on_secant
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_trigger_iff
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_admissible_core_never_triggers
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_core_shortfall
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_saturated_mass_shortfall
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_offline_window
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_cascade_never_fires
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_pairwise_forcing_dead
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_corradi_vacuous
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_pairwise_trigger_bound
#print axioms
  ArkLib.ProximityGap.Frontier.FSMDRestrictedTripleCollinearity.p1_pairwise_core_shortfall
