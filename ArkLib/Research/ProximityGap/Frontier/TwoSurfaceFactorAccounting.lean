/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralLinearFactorExtraction
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface

/-! # Two-surface factor accounting and `NonlinearComponentCap` interface (Packet L4b)

Wires primary and companion received-row surfaces, primitive factorization up to associates,
disjoint label assignment, rich affine head extraction, residual degree/weight tracking,
and optional third-surface (weighted-jet) degree tightening into the degree-allocation interface
of `EighthRichHeadSafety`, `QuarterCoreWeightedJets`, `TangentHeadWindows`,
`ThreeHeadResidualSecant`, and `ThreeHeadSuccessorIncidence`.

Parameterized by `NonlinearComponentCap price` whose exact `logDerivPrice` signature matches
`LogarithmicComponentCap.logarithmic_component_cap` (Packet L1d).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction
open ArkLib.ProximityGap.Frontier.SecondPrimePrimitiveSurface
open ArkLib.ProximityGap.Frontier.SecondPrimeSectionResultant
open ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open scoped NNReal

section NonlinearInterface

/-- Exact algebraic nonlinear factor cap from `docs/research/proximity-gap/logarithmic-section-heights.md`,
matching `LogarithmicComponentCap.logDerivPrice`. -/
def logDerivPrice (n d t W m b : ℕ) : ℕ :=
  let A := (2 * b - 2) * W - b * (b - 1) * d
  let G := (2 * b - 2) * m - b * (b - 1)
  let C0 := 2 * A * G + 2 * W * m
  G + 2 * b * m + (2 * t * (G + m) * n + n * (2 * C0 + m * n)) / (t ^ 2 - n * d)

theorem logDerivPrice_mono {n d t W₁ W₂ m₁ m₂ b : ℕ} (hW : W₁ ≤ W₂) (hm : m₁ ≤ m₂) :
    logDerivPrice n d t W₁ m₁ b ≤ logDerivPrice n d t W₂ m₂ b := by
  unfold logDerivPrice
  dsimp only
  have hA : (2 * b - 2) * W₁ - b * (b - 1) * d ≤ (2 * b - 2) * W₂ - b * (b - 1) * d :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hW) _
  have hG : (2 * b - 2) * m₁ - b * (b - 1) ≤ (2 * b - 2) * m₂ - b * (b - 1) :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hm) _
  have hC0 : 2 * ((2 * b - 2) * W₁ - b * (b - 1) * d) * ((2 * b - 2) * m₁ - b * (b - 1)) +
      2 * W₁ * m₁ ≤
      2 * ((2 * b - 2) * W₂ - b * (b - 1) * d) * ((2 * b - 2) * m₂ - b * (b - 1)) +
      2 * W₂ * m₂ := by
    apply Nat.add_le_add
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hG
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hW) hm
  apply Nat.add_le_add (Nat.add_le_add hG (Nat.mul_le_mul_left (2 * b) hm))
  apply Nat.div_le_div_right
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left (2 * t) (Nat.add_le_add hG hm))
  · exact Nat.mul_le_mul_left n (Nat.add_le_add (Nat.mul_le_mul_left 2 hC0) (Nat.mul_le_mul_right n hm))

/-- Clean `K`-native nonlinear factor cap interface matching `LogarithmicComponentCap` (Packet L1d). -/
def NonlinearComponentCap (price : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ {K I : Type} [Field K] [Infinite K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (dom : I ↪ K) (u₀ u₁ : I → K)
    {d t W m : ℕ} (F : K[X][X][X]),
    Irreducible F → 2 ≤ F.natDegree →
    (∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m) →
    (∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W) →
    Fintype.card I * d < t ^ 2 →
    (∀ r : ℕ, 0 < r →
      r ≤ max ((2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d) F.natDegree →
      (r : K) ≠ 0) →
    ∀ (S : Finset K) (q : K → K[X]),
    (∀ z ∈ S, (q z).natDegree ≤ d) →
    (∀ z ∈ S, F.eval₂ (evalRingHom (C z)) (q z) = 0) →
    (∀ z ∈ S, t ≤ (Finset.univ.filter fun x => (q z).eval (dom x) = u₀ x + z * u₁ x).card) →
    S.card ≤ price (Fintype.card I) d t W m F.natDegree

/-- Convert `TotalDegreeLe f m` into the coefficient-level support inequality. -/
theorem coeff_totalDegree_of_totalDegreeLe {K : Type} [Field K] {f : K[X][X][X]} {m : ℕ}
    (htot : TotalDegreeLe f m) :
    ∀ j i a, ((f.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m := by
  intro j i a hne
  have hi : (f.coeff j).coeff i ≠ 0 := fun hz => hne (by simp [hz])
  have hj : f.coeff j ≠ 0 := fun hz => hi (by simp [hz])
  have h1 : i ≤ (f.coeff j).natDegree := le_natDegree_of_ne_zero hi
  have h2 : (f.coeff j).natDegree + j ≤ m := htot j hj
  omega

/-- Convert `weight d f ≤ W` into the coefficient-level weight inequality. -/
theorem coeff_weight_of_weight_le {K : Type} [Field K] {f : K[X][X][X]} {d W : ℕ}
    (hW : weight d f ≤ W) :
    ∀ j i a, ((f.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W := by
  intro j i a hne
  exact (coeff_weight_le d f hne).trans hW

/-- Lift a `BadScalarRichPointFamily` subset `G` on an irreducible nonlinear factor `f` over an
infinite extension `K` into `NonlinearComponentCap`. -/
theorem nonlinear_population_le_of_cap {F K I : Type}
    [Field F] [Fintype F] [DecidableEq F] [Field K] [Infinite K]
    [Fintype I] [DecidableEq I]
    {dom : I ↪ F} {d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    {price : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (hcap : NonlinearComponentCap price)
    (φ : F →+* K) (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    {t W m : ℕ} (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hJ : Fintype.card I * d < t ^ 2)
    (f : K[X][X][X]) (hIrr : Irreducible f) (hb : 2 ≤ f.natDegree)
    (hTot : TotalDegreeLe f m) (hWt : weight d f ≤ W)
    (hchar : ∀ r : ℕ, 0 < r →
      r ≤ max ((2 * f.natDegree - 2) * W - f.natDegree * (f.natDegree - 1) * d) f.natDegree →
      (r : K) ≠ 0)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    G.card ≤ price (Fintype.card I) d t W m f.natDegree := by
  classical
  let φEmb : F ↪ K := ⟨φ, φ.injective⟩
  let domK : I ↪ K := dom.trans φEmb
  let u₀K : I → K := fun x => φ (u 0 x)
  let u₁K : I → K := fun x => φ (u 1 x)
  let S : Finset K := G.map φEmb
  let qK : K → K[X] := Function.extend φ (fun z => (fam.q z).map φ) (fun _ => 0)
  have hqK (z : F) : qK (φ z) = (fam.q z).map φ := φ.injective.extend_apply _ _ z
  have hcard : S.card = G.card := Finset.card_map φEmb
  rw [← hcard]
  apply hcap domK u₀K u₁K f hIrr hb (coeff_totalDegree_of_totalDegreeLe hTot)
    (coeff_weight_of_weight_le hWt) hJ hchar S qK
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change (qK (φ z)).natDegree ≤ d
    rw [hqK z]
    have hdeg := fam.degree_lt z (hG hz)
    exact natDegree_map_le.trans (by omega)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change f.eval₂ (evalRingHom (C (φ z))) (qK (φ z)) = 0
    rw [hqK z]
    exact hroot z hz
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change t ≤ (Finset.univ.filter fun x => (qK (φ z)).eval (φ (dom x)) = φ (u 0 x) + φ z * φ (u 1 x)).card
    rw [hqK z]
    have hsub : fullAgreement dom (u 0) (u 1) z (fam.q z) ⊆
        Finset.univ.filter fun x => ((fam.q z).map φ).eval (φ (dom x)) = φ (u 0 x) + φ z * φ (u 1 x) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
      rw [eval_map_apply]
      have hag := (Finset.mem_filter.mp hx).2
      simpa only [map_add, map_mul] using congrArg φ hag
    exact (ht.trans (fam.threshold_le z (hG hz))).trans (Finset.card_le_card hsub)

end NonlinearInterface

section FactorDeduplication

variable {K : Type} [Field K]

/-- Every nonzero surface `f` satisfies `f.natDegree * d ≤ weight d f`. -/
theorem natDegree_mul_le_weight {f : K[X][X][X]} (hf : f ≠ 0) (d : ℕ) :
    f.natDegree * d ≤ weight d f := by
  have hj : f.coeff f.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hi : (f.coeff f.natDegree).coeff (f.coeff f.natDegree).natDegree ≠ 0 :=
    leadingCoeff_ne_zero.mpr hj
  have ha := leadingCoeff_ne_zero.mpr hi
  have h := coeff_weight_le d f ha
  omega

/-- Pairwise non-associated irreducible factors dividing a surface `Q` divide `Q` as a product. -/
theorem prod_nonassociated_dvd {Q : K[X][X][X]} (Fset : Finset K[X][X][X])
    (hIrr : ∀ f ∈ Fset, Irreducible f)
    (hDvd : ∀ f ∈ Fset, f ∣ Q)
    (hNonAssoc : ∀ f ∈ Fset, ∀ g ∈ Fset, f ≠ g → ¬ Associated f g) :
    (∏ f ∈ Fset, f) ∣ Q := by
  classical
  induction Fset using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have haIrr : Irreducible a := hIrr a (Finset.mem_insert_self a s)
    have haDvd : a ∣ Q := hDvd a (Finset.mem_insert_self a s)
    have hsDvd : (∏ f ∈ s, f) ∣ Q := ih
      (fun f hf => hIrr f (Finset.mem_insert_of_mem hf))
      (fun f hf => hDvd f (Finset.mem_insert_of_mem hf))
      (fun f hf g hg hne => hNonAssoc f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg) hne)
    obtain ⟨R, hR⟩ := hsDvd
    have hdiv : a ∣ (∏ f ∈ s, f) * R := by rwa [← hR]
    have haPrime : Prime a := UniqueFactorizationMonoid.irreducible_iff_prime.mp haIrr
    rcases haPrime.dvd_or_dvd hdiv with hbad | hR'
    · exfalso
      obtain ⟨b, hb, hab⟩ := (haPrime.dvd_finsetProd_iff _).mp hbad
      have hassoc : Associated a b :=
        haIrr.associated_of_dvd (hIrr b (Finset.mem_insert_of_mem hb)) hab
      exact hNonAssoc a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun (heq : a = b) => ha (heq ▸ hb)) hassoc
    · obtain ⟨T, hT⟩ := hR'
      exact ⟨T, by rw [hR, hT]; ring⟩

/-- Value degree, total `(Z, Y)`-degree, and `(1, 0, d)`-weight of a finite product of nonzero
surfaces are the sums of the factor degrees/weights. -/
theorem prod_degrees_and_weight (Fset : Finset K[X][X][X]) (hNe : ∀ f ∈ Fset, f ≠ 0) (d : ℕ) :
    (∏ f ∈ Fset, f) ≠ 0 ∧
    (∏ f ∈ Fset, f).natDegree = ∑ f ∈ Fset, f.natDegree ∧
    Bivariate.totalDegree (∏ f ∈ Fset, f) = ∑ f ∈ Fset, Bivariate.totalDegree f ∧
    weight d (∏ f ∈ Fset, f) = ∑ f ∈ Fset, weight d f := by
  classical
  induction Fset using Finset.induction_on with
  | empty =>
    refine ⟨by simp, by simp, ?_, ?_⟩
    · apply Nat.eq_zero_of_le_zero
      unfold Bivariate.totalDegree
      apply Finset.sup_le
      intro j hj
      have hj0 : j = 0 := by
        by_contra hne
        exact (mem_support_iff.mp hj) (by simp [coeff_one, hne])
      subst hj0
      simp
    · apply Nat.eq_zero_of_le_zero
      apply weight_le_of_coeff
      intro j i a hne
      have hj0 : j = 0 := by
        by_contra hne'
        exact hne (by simp [coeff_one, hne'])
      subst hj0
      have hi0 : i = 0 := by
        by_contra hne'
        exact hne (by simp [coeff_one, hne'])
      subst hi0
      have ha0 : a = 0 := by
        by_contra hne'
        exact hne (by simp [coeff_one, hne'])
      subst ha0
      simp
  | @insert a s ha ih =>
    have haNe : a ≠ 0 := hNe a (Finset.mem_insert_self a s)
    obtain ⟨hsNe, hsDeg, hsTot, hsWt⟩ := ih (fun f hf => hNe f (Finset.mem_insert_of_mem hf))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨mul_ne_zero haNe hsNe, ?_, ?_, ?_⟩
    · rw [natDegree_mul haNe hsNe, hsDeg]
    · rw [Bivariate.totalDegree_mul haNe hsNe, hsTot]
    · rw [weight_mul d _ _ haNe hsNe, hsWt]

/-- Deduplicate any finite set of irreducible factors up to `Associated`, keeping a pairwise
non-associated subset covering every associate class. -/
private theorem dedup_associated (U : Finset K[X][X][X]) :
    ∃ Fset ⊆ U,
      (∀ f ∈ Fset, ∀ g ∈ Fset, f ≠ g → ¬ Associated f g) ∧
      (∀ f ∈ U, ∃ g ∈ Fset, Associated f g) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨∅, Subset.rfl, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨Fset, hsub, hnon, hcov⟩ := ih
    by_cases hex : ∃ g ∈ Fset, Associated a g
    · refine ⟨Fset, hsub.trans (Finset.subset_insert a s), hnon, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hfs
      · exact hex
      · exact hcov f hfs
    · push Not at hex
      refine ⟨insert a Fset, Finset.insert_subset_insert a hsub, ?_, ?_⟩
      · intro f hf g hg hne
        rcases Finset.mem_insert.mp hf with rfl | hfs <;>
        rcases Finset.mem_insert.mp hg with rfl | hgs
        · exact absurd rfl hne
        · exact hex g hgs
        · exact fun hass => hex f hfs hass.symm
        · exact hnon f hfs g hgs hne
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hfs
        · exact ⟨f, Finset.mem_insert_self f Fset, Associated.refl f⟩
        · obtain ⟨g, hg, hass⟩ := hcov f hfs
          exact ⟨g, Finset.mem_insert_of_mem hg, hass⟩

/-- Every nonzero primitive surface `P` admits a finite set `Fset` of pairwise non-associated
irreducible positive-value-degree factors whose product divides `P` and whose zero sets cover
every polynomial section of `P`. -/
theorem nonassociated_factor_cover (P : K[X][X][X]) (hP : P ≠ 0) (hprim : P.IsPrimitive) :
    ∃ Fset : Finset K[X][X][X],
      (∀ f ∈ Fset, Irreducible f ∧ 0 < f.natDegree ∧ f ∣ P) ∧
      (∀ f ∈ Fset, ∀ g ∈ Fset, f ≠ g → ¬ Associated f g) ∧
      (∏ f ∈ Fset, f) ∣ P ∧
      (∑ f ∈ Fset, f.natDegree) ≤ P.natDegree ∧
      (∀ (z : K) (w : K[X]), P.eval₂ (evalRingHom (C z)) w = 0 →
        ∃ f ∈ Fset, f.eval₂ (evalRingHom (C z)) w = 0) := by
  classical
  obtain ⟨U, hU, _, _, hcov⟩ := factor_cover P hP hprim
  obtain ⟨Fset, hsub, hnon, hrep⟩ := dedup_associated U.toFinset
  have hmem (f : K[X][X][X]) (hf : f ∈ Fset) : Irreducible f ∧ 0 < f.natDegree ∧ f ∣ P :=
    hU f (Multiset.mem_toFinset.mp (hsub hf))
  have hprodDvd : (∏ f ∈ Fset, f) ∣ P :=
    prod_nonassociated_dvd Fset (fun f hf => (hmem f hf).1) (fun f hf => (hmem f hf).2.2) hnon
  obtain ⟨hProdNe, hProdDeg, _, _⟩ :=
    prod_degrees_and_weight Fset (fun f hf => (hmem f hf).1.ne_zero) 0
  have hsumDeg : (∑ f ∈ Fset, f.natDegree) ≤ P.natDegree := by
    rw [← hProdDeg]
    exact natDegree_le_of_dvd hprodDvd hP
  refine ⟨Fset, hmem, hnon, hprodDvd, hsumDeg, ?_⟩
  intro z w hzw
  obtain ⟨f, hfU, hfz⟩ := hcov z w hzw
  obtain ⟨g, hgF, hass⟩ := hrep f (Multiset.mem_toFinset.mpr hfU)
  refine ⟨g, hgF, ?_⟩
  let E := eval₂RingHom (evalRingHom (C z)) w
  exact (Associated.map E hass).eq_zero_iff.mp hfz

/-- Weight budget for an individual factor `f ∈ Fset` inside a product dividing `Q`:
every other factor `g ∈ Fset.erase f` consumes at least `g.natDegree * d` units of weight,
leaving `weight d f ≤ weight d Q - (l - f.natDegree) * d` where `l = ∑ g ∈ Fset, g.natDegree`. -/
theorem factor_weight_le_residual {Q : K[X][X][X]} (hQ : Q ≠ 0) (Fset : Finset K[X][X][X])
    (hNe : ∀ g ∈ Fset, g ≠ 0) (hProdDvd : (∏ g ∈ Fset, g) ∣ Q) (d : ℕ)
    {f : K[X][X][X]} (hf : f ∈ Fset) :
    weight d f ≤ weight d Q - ((∑ g ∈ Fset, g.natDegree) - f.natDegree) * d := by
  classical
  obtain ⟨hPne, _, _, hPwt⟩ := prod_degrees_and_weight Fset hNe d
  obtain ⟨R, hQR⟩ := hProdDvd
  have hRne : R ≠ 0 := right_ne_zero_of_mul (hQR ▸ hQ)
  have hsumWt : ∑ g ∈ Fset, weight d g ≤ weight d Q := by
    rw [← hPwt, hQR, weight_mul d _ _ hPne hRne]
    exact Nat.le_add_right _ _
  have hsplitWt : weight d f + ∑ g ∈ Fset.erase f, weight d g = ∑ g ∈ Fset, weight d g :=
    Finset.add_sum_erase Fset (fun g => weight d g) hf
  have hsplitDeg : f.natDegree + ∑ g ∈ Fset.erase f, g.natDegree = ∑ g ∈ Fset, g.natDegree :=
    Finset.add_sum_erase Fset natDegree hf
  have hother : (∑ g ∈ Fset.erase f, g.natDegree) * d ≤ ∑ g ∈ Fset.erase f, weight d g := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun g hg => natDegree_mul_le_weight (hNe g (Finset.mem_of_mem_erase hg)) d
  have hsubDeg : (∑ g ∈ Fset, g.natDegree) - f.natDegree = ∑ g ∈ Fset.erase f, g.natDegree := by
    omega
  rw [hsubDeg]
  omega

/-- Total `(Z, Y)`-degree budget for an individual factor `f ∈ Cset \ Hset` when `Cset` divides
a companion surface `Q₂` of total degree `≤ s₂` and `Hset ⊆ Cset` consists of `j` positive-degree
factors: `Bivariate.totalDegree f ≤ s₂ - Hset.card`. -/
theorem factor_totalDegree_le_residual {Q₂ : K[X][X][X]} (hQ₂ : Q₂ ≠ 0)
    (Cset Hset : Finset K[X][X][X]) (hHC : Hset ⊆ Cset)
    (hPos : ∀ g ∈ Cset, 0 < g.natDegree) (hProdDvd : (∏ g ∈ Cset, g) ∣ Q₂)
    {s₂ : ℕ} (hQ₂Tot : Bivariate.totalDegree Q₂ ≤ s₂)
    {f : K[X][X][X]} (hf : f ∈ Cset) (hfNotH : f ∉ Hset) :
    Bivariate.totalDegree f ≤ s₂ - Hset.card := by
  classical
  have hNe : ∀ g ∈ Cset, g ≠ 0 := fun g hg hz => by have := hPos g hg; simp [hz] at this
  obtain ⟨hPne, _, hPtot, _⟩ := prod_degrees_and_weight Cset hNe 0
  obtain ⟨R, hQR⟩ := hProdDvd
  have hRne : R ≠ 0 := right_ne_zero_of_mul (hQR ▸ hQ₂)
  have hsumTot : ∑ g ∈ Cset, Bivariate.totalDegree g ≤ s₂ := by
    rw [← hPtot]
    have hle : Bivariate.totalDegree (∏ g ∈ Cset, g) ≤ Bivariate.totalDegree Q₂ := by
      rw [hQR, Bivariate.totalDegree_mul hPne hRne]
      exact Nat.le_add_right _ _
    exact hle.trans hQ₂Tot
  have hHge : Hset.card ≤ ∑ g ∈ Hset, Bivariate.totalDegree g := by
    have h := Finset.sum_le_sum (s := Hset) (f := fun _ => 1) (g := Bivariate.totalDegree)
      (fun g hg => one_le_totalDegree_of_pos_natDegree (hPos g (hHC hg)))
    simpa using h
  have hsub : insert f Hset ⊆ Cset := Finset.insert_subset_iff.mpr ⟨hf, hHC⟩
  have hleSum := Finset.sum_le_sum_of_subset (f := Bivariate.totalDegree) hsub
  rw [Finset.sum_insert hfNotH] at hleSum
  omega

/-- Convert `TotalDegreeLe Q s` into `Bivariate.totalDegree Q ≤ s`. -/
theorem totalDegree_le_of_totalDegreeLe {Q : K[X][X][X]} {s : ℕ} (hQ : TotalDegreeLe Q s) :
    Bivariate.totalDegree Q ≤ s := by
  classical
  unfold Bivariate.totalDegree
  apply Finset.sup_le
  intro j hj
  exact hQ j (mem_support_iff.mp hj)

end FactorDeduplication

section DisjointAssignment

/-- Partition a covered set `G` into pairwise disjoint subsets assigned to factors in `Fset`. -/
theorem exists_disjoint_assignment {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset α) (Fset : Finset β) (P : α → β → Prop)
    (hcov : ∀ z ∈ G, ∃ f ∈ Fset, P z f) :
    ∃ assign : β → Finset α,
      (∀ f ∈ Fset, assign f ⊆ G) ∧
      (∀ f ∈ Fset, ∀ z ∈ assign f, P z f) ∧
      (∀ f ∈ Fset, ∀ g ∈ Fset, f ≠ g → Disjoint (assign f) (assign g)) ∧
      G.card = ∑ f ∈ Fset, (assign f).card := by
  classical
  let owner (z : α) : Option β :=
    if hz : z ∈ G then some (Classical.choose (hcov z hz)) else none
  let assign (f : β) : Finset α := G.filter fun z => owner z = some f
  refine ⟨assign, fun _ _ => Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro f _ z hz
    obtain ⟨hzG, hown⟩ := Finset.mem_filter.mp hz
    simp only [owner, hzG, ↓reduceDIte, Option.some.injEq] at hown
    rw [← hown]
    exact (Classical.choose_spec (hcov z hzG)).2
  · intro f _ g _ hne
    rw [Finset.disjoint_left]
    intro z hzf hzg
    have h1 := (Finset.mem_filter.mp hzf).2
    have h2 := (Finset.mem_filter.mp hzg).2
    exact hne (Option.some.inj (h1.symm.trans h2))
  · have hpart : G = Fset.biUnion assign := by
      ext z
      simp only [Finset.mem_biUnion, assign, Finset.mem_filter]
      constructor
      · intro hzG
        refine ⟨Classical.choose (hcov z hzG), (Classical.choose_spec (hcov z hzG)).1, hzG, ?_⟩
        simp [owner, hzG]
      · rintro ⟨_, _, hzG, _⟩
        exact hzG
    conv_lhs => rw [hpart]
    rw [Finset.card_biUnion]
    intro f hf g hg hne
    change Disjoint (assign f) (assign g)
    rw [Finset.disjoint_left]
    intro z hzf hzg
    have h1 := (Finset.mem_filter.mp hzf).2
    have h2 := (Finset.mem_filter.mp hzg).2
    exact hne (Option.some.inj (h1.symm.trans h2))

end DisjointAssignment

section CoreAndUnionBounds

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Rich head core floor from `pointsOn_card_mul_max_add_core_le`:
if a head carries strictly more than `L` bad labels (`0 < L`) at agreement count `t` (`t + e = n`),
then its joint core has size at least `t - e / L`. -/
theorem rich_head_core_ge [Nonempty I] {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    {n t e L : ℕ} (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hte : t + e = n)
    (hL : 0 < L) {h : LineParameter F} (hh : h ∈ lineParameters fam)
    (hrich : L < (pointsOn fam h).card) :
    t - e / L ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card := by
  let c := (jointCore dom (u 0) (u 1) h.1 h.2).card
  have hpack := pointsOn_card_mul_max_add_core_le fam hh
  rw [hn] at hpack
  have hsub : max 1 (t - c) ≤ max 1 (⌈(1 - δ) * (n : ℝ≥0)⌉₊ - c) :=
    max_le_max_left 1 (Nat.sub_le_sub_right (hn ▸ ht) c)
  have h1 : (pointsOn fam h).card * max 1 (t - c) + c ≤ n :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hsub) c).trans hpack
  change t - e / L ≤ c
  by_cases hct : t ≤ c
  · exact (Nat.sub_le t (e / L)).trans hct
  · have hpos : 1 ≤ t - c := by omega
    have hmax : max 1 (t - c) = t - c := max_eq_right hpos
    rw [hmax] at h1
    have hmul : (L + 1) * (t - c) + c ≤ n :=
      (Nat.add_le_add_right (Nat.mul_le_mul_right (t - c) hrich) c).trans h1
    have hmul' : L * (t - c) ≤ e := by
      rw [Nat.add_mul, one_mul] at hmul
      omega
    have hdiv : t - c ≤ e / L := (Nat.le_div_iff_mul_le hL).mpr (by rwa [Nat.mul_comm])
    omega

omit [Fintype I] in
/-- Second-order (Bonferroni) inclusion-exclusion union lower bound for `j` cores of size `≥ c`
and pairwise overlap `≤ d`. -/
theorem bonferroni_core_union {J : Type*} [DecidableEq J] (S : Finset J) (C : J → Finset I)
    {c d : ℕ} (hc : ∀ i ∈ S, c ≤ (C i).card)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (C i ∩ C j).card ≤ d) :
    S.card * c - S.card.choose 2 * d ≤ (S.biUnion C).card := by
  classical
  have h : S.card * c ≤ (S.biUnion C).card + S.card.choose 2 * d := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have hsub : S ⊆ insert i S := Finset.subset_insert i S
      have hrec := ih (fun j hj => hc j (hsub hj)) (fun x hx y hy => hd x (hsub hx) y (hsub hy))
      have hnew := hc i (Finset.mem_insert_self i S)
      have hov : (C i ∩ S.biUnion C).card ≤ S.card * d := by
        have hcov : C i ∩ S.biUnion C ⊆ S.biUnion (fun j => C i ∩ C j) := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
          obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx2
          exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hx1, hxj⟩⟩
        apply ((Finset.card_le_card hcov).trans Finset.card_biUnion_le).trans
        exact (Finset.sum_le_sum fun j hj =>
          hd i (Finset.mem_insert_self i S) j (hsub hj) (fun he => hi (he ▸ hj))).trans_eq (by simp)
      have hci := Finset.card_union_add_card_inter (C i) (S.biUnion C)
      have hch : (S.card + 1).choose 2 = S.card + S.card.choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ S.card 1
      rw [Finset.card_insert_of_notMem hi, Finset.biUnion_insert, Nat.add_mul, one_mul,
        hch, Nat.add_mul]
      omega
  omega

omit [Fintype I] in
/-- Cauchy–Schwarz union lower bound for `j` cores of size `≥ c` and pairwise overlap `≤ d`:
`(c + (j - 1) * d) * |⋃ C| ≥ j * c^2`, hence `⌈j * c^2 / (c + (j - 1) * d)⌉ ≤ |⋃ C|`. -/
theorem cauchy_core_union {J : Type*} [DecidableEq J] (S : Finset J) (C : J → Finset I)
    {c d : ℕ} (hc : ∀ i ∈ S, c ≤ (C i).card)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (C i ∩ C j).card ≤ d) :
    let denom := c + (S.card - 1) * d
    (S.card * c ^ 2 + denom - 1) / denom ≤ (S.biUnion C).card := by
  classical
  dsimp only
  let U := S.biUnion C
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, zero_mul, Nat.zero_sub, zero_add, add_zero]
    by_cases hc0 : c = 0
    · simp [hc0]
    · rw [Nat.div_eq_of_lt (by omega)]; exact Nat.zero_le _
  by_cases hc0 : c = 0
  · subst hc0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    by_cases hd0 : (S.card - 1) * d = 0
    · simp [hd0]
    · rw [Nat.div_eq_of_lt (by omega)]; exact Nat.zero_le _
  have hdenPos : 0 < c + (S.card - 1) * d := by omega
  let deg (x : I) : ℕ := (S.filter fun i => x ∈ C i).card
  have hsumDeg : ∑ x ∈ U, deg x = ∑ i ∈ S, (C i).card := by
    simp only [deg, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hsub : C i ⊆ U := Finset.subset_biUnion_of_mem C hi
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  have hsumSq : ∑ x ∈ U, deg x ^ 2 = ∑ i ∈ S, ∑ j ∈ S, (C i ∩ C j).card := by
    have hpoint (x : I) : deg x ^ 2 = ∑ i ∈ S, ∑ j ∈ S, if x ∈ C i ∩ C j then 1 else 0 := by
      rw [sq]
      simp only [deg, Finset.card_filter, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : x ∈ C i <;> by_cases hj : x ∈ C j <;> simp [hi, hj]
    simp_rw [hpoint]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : C i ∩ C j ⊆ U := Finset.inter_subset_left.trans (Finset.subset_biUnion_of_mem C hi)
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  have hCS : (∑ x ∈ U, deg x) ^ 2 ≤ U.card * ∑ x ∈ U, deg x ^ 2 := by
    have hnonneg : (0 : ℤ) ≤ ∑ x ∈ U, ∑ y ∈ U, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ∑ x ∈ U, ∑ y ∈ U, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 =
        2 * ((U.card : ℤ) * ∑ x ∈ U, (deg x : ℤ) ^ 2 - (∑ x ∈ U, (deg x : ℤ)) ^ 2) := by
      have h1 : ∀ x y : I, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 =
          (deg x : ℤ) ^ 2 + (deg y : ℤ) ^ 2 - 2 * ((deg x : ℤ) * (deg y : ℤ)) := fun x y => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    have hz : (∑ x ∈ U, (deg x : ℤ)) ^ 2 ≤ (U.card : ℤ) * ∑ x ∈ U, (deg x : ℤ) ^ 2 := by
      linarith
    exact_mod_cast hz
  have hsumPair : ∑ i ∈ S, ∑ j ∈ S, (C i ∩ C j).card ≤
      (∑ i ∈ S, (C i).card) + S.card * ((S.card - 1) * d) := by
    have hinner (i : J) (hi : i ∈ S) :
        ∑ j ∈ S, (C i ∩ C j).card ≤ (C i).card + (S.card - 1) * d := by
      rw [← Finset.add_sum_erase S (fun j => (C i ∩ C j).card) hi, Finset.inter_self]
      apply Nat.add_le_add_left
      calc ∑ j ∈ S.erase i, (C i ∩ C j).card
          ≤ ∑ _j ∈ S.erase i, d := Finset.sum_le_sum fun j hj =>
            hd i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
        _ = (S.card - 1) * d := by simp [Finset.card_erase_of_mem hi]
    calc ∑ i ∈ S, ∑ j ∈ S, (C i ∩ C j).card
        ≤ ∑ i ∈ S, ((C i).card + (S.card - 1) * d) := Finset.sum_le_sum hinner
      _ = (∑ i ∈ S, (C i).card) + S.card * ((S.card - 1) * d) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  let M := ∑ i ∈ S, (C i).card
  have hM : S.card * c ≤ M := by
    simpa using Finset.sum_le_sum hc
  have hCS' : M ^ 2 ≤ U.card * (M + S.card * ((S.card - 1) * d)) := by
    rw [hsumDeg, hsumSq] at hCS
    exact hCS.trans (Nat.mul_le_mul_left U.card hsumPair)
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.mul_pos (Finset.card_pos.mpr hne) (by omega)) hM
  -- Multiply by c: M * (S.card * c) ≤ M^2 ≤ U.card * (M + S.card * (S.card - 1) * d)
  -- and c * (M + S.card * (S.card - 1) * d) ≤ M * (c + (S.card - 1) * d) since S.card * c ≤ M!
  have hkey : M * (S.card * c ^ 2) ≤ M * (U.card * (c + (S.card - 1) * d)) := by
    have h1 : M * (S.card * c ^ 2) ≤ c * M ^ 2 := by
      calc M * (S.card * c ^ 2) = (c * M) * (S.card * c) := by ring
        _ ≤ (c * M) * M := Nat.mul_le_mul_left (c * M) hM
        _ = c * M ^ 2 := by ring
    have h2 : c * M ^ 2 ≤ U.card * (c * (M + S.card * ((S.card - 1) * d))) := by
      calc c * M ^ 2 ≤ c * (U.card * (M + S.card * ((S.card - 1) * d))) :=
            Nat.mul_le_mul_left c hCS'
        _ = U.card * (c * (M + S.card * ((S.card - 1) * d))) := by ring
    have h3 : c * (M + S.card * ((S.card - 1) * d)) ≤ M * (c + (S.card - 1) * d) := by
      calc c * (M + S.card * ((S.card - 1) * d))
          = c * M + (S.card * c) * ((S.card - 1) * d) := by ring
        _ ≤ c * M + M * ((S.card - 1) * d) :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hM) _
        _ = M * (c + (S.card - 1) * d) := by ring
    have h4 : U.card * (c * (M + S.card * ((S.card - 1) * d))) ≤
        M * (U.card * (c + (S.card - 1) * d)) := by
      calc U.card * (c * (M + S.card * ((S.card - 1) * d)))
          ≤ U.card * (M * (c + (S.card - 1) * d)) := Nat.mul_le_mul_left U.card h3
        _ = M * (U.card * (c + (S.card - 1) * d)) := by ring
    exact h1.trans (h2.trans h4)
  have hmain : S.card * c ^ 2 ≤ (c + (S.card - 1) * d) * (S.biUnion C).card := by
    have h := Nat.le_of_mul_le_mul_left hkey hMpos
    dsimp only [U] at h
    rwa [Nat.mul_comm (S.biUnion C).card] at h
  exact (Nat.div_le_iff_le_mul_add_pred hdenPos).mpr (by omega)

end CoreAndUnionBounds

section TwoSurfaceAccounting

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F] [Field K] [Infinite K]

/-- Main two-surface factor accounting engine (Packet L4b).

Given a bad-scalar family `fam` and primary/companion surfaces `Q₁, Q₂` over `K` vanishing on
every witness section of `fam`, together with:
- a cutoff `L` separating small factors from companion-dividing factors (`hComp`),
- the arbitrary-degree linear extraction gap `hLinGap` at degree `s₂` and threshold `L + 1`,
- an abstract `NonlinearComponentCap price` (discharged by L1d for `price = logDerivPrice`),

this theorem produces:
- total primary positive-value-degree `l ≤ b₁`,
- a finset `H ⊆ lineParameters fam` of `j = H.card ≤ l` distinct rich affine heads
  (each carrying strictly more than `L` bad labels),
- a finset `S` of remaining positive-value-degree factors with `∑ f ∈ S, f.natDegree = l - j`,
- nonnegative label counts `labels : K[X][X][X] → ℕ`

satisfying `fam.G.card ≤ s₁ + (H.biUnion (pointsOn fam)).card + ∑ f ∈ S, labels f` and
bounding each `f ∈ S` by `L` (if `f.natDegree = 1` or `labels f ≤ L`) or
`price n d t (W₁ - (l - f.natDegree) * d) (s₂ - j) f.natDegree` (and optionally tightened to
degree `≤ s₃` via an extra surface `Q₃` when `3 ≤ j`, as in `QuarterCoreWeightedJets`)! -/
theorem two_surface_accounting {dom : I ↪ F} {d n t : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hn : Fintype.card I = n) (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hdt : d < t) (hJ : n * d < t ^ 2)
    {b₁ s₁ W₁ s₂ L : ℕ} (hs₂ : 1 ≤ s₂) (hs₂L : s₂ < L + 1)
    (Q₁ Q₂ : K[X][X][X]) (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hQ₁Deg : Q₁.natDegree ≤ b₁) (hQ₁Tot : TotalDegreeLe Q₁ s₁) (hQ₁Wt : weight d Q₁ ≤ W₁)
    (hQ₂Tot : TotalDegreeLe Q₂ s₂)
    (hQ₁Root : ∀ z ∈ fam.G, Q₁.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0)
    (hComp : ∀ (f : K[X][X][X]) (G : Finset F), Irreducible f → 0 < f.natDegree → f ∣ Q₁ →
      G ⊆ fam.G → L < G.card →
      (∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) → f ∣ Q₂)
    (hLinGap : (s₂ * (L + 1 - s₂) + 3 * (L + 1) * (s₂ - 1)) * n <
      (L + 1) * (L + 1 - s₂) * (t - d))
    {price : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hcap : NonlinearComponentCap price)
    (hchar : ∀ r : ℕ, 0 < r → r ≤ max ((2 * b₁ - 2) * W₁) b₁ → (r : K) ≠ 0)
    (extraDeg : Finset (LineParameter F) → ℕ)
    (hExtra : ∀ (H : Finset (LineParameter F)),
      H ⊆ lineParameters fam → (∀ h ∈ H, L < (pointsOn fam h).card) →
      ∀ (f : K[X][X][X]) (G : Finset F), Irreducible f → 2 ≤ f.natDegree → f ∣ Q₁ → f ∣ Q₂ →
      G ⊆ fam.G → (∀ h ∈ H, Disjoint G (pointsOn fam h)) → L < G.card →
      (∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) →
      TotalDegreeLe f (extraDeg H)) :
    ∃ (l : ℕ) (H : Finset (LineParameter F)) (S : Finset K[X][X][X]) (labels : K[X][X][X] → ℕ),
      l ≤ b₁ ∧ H ⊆ lineParameters fam ∧ H.card ≤ l ∧
      (∀ h ∈ H, L < (pointsOn fam h).card) ∧
      (∀ f ∈ S, 0 < f.natDegree) ∧
      (∑ f ∈ S, f.natDegree = l - H.card) ∧
      fam.G.card ≤ s₁ + (H.biUnion (pointsOn fam)).card + ∑ f ∈ S, labels f ∧
      (∀ f ∈ S, labels f ≤
        if f.natDegree ≤ 1 then L
        else max L (price n d t (W₁ - (l - f.natDegree) * d)
          (min (s₂ - H.card) (extraDeg H)) f.natDegree)) := by
  classical
  -- Step 1: Primitive part of Q₁, losing at most s₁ scalar-only labels
  have hQ₁CoeffDeg : ∀ j, (Q₁.coeff j).natDegree ≤ s₁ := by
    intro j
    by_cases hj : Q₁.coeff j = 0
    · simp [hj]
    · have := hQ₁Tot j hj; omega
  obtain ⟨P₁, E₀, hP₁ne, hP₁prim, hP₁dvd, hP₁deg, hE₀sub, hE₀card, hP₁root⟩ :=
    primitive_surface φ hQ₁ fam.G (fun z => (fam.q z).map φ) s₁ hQ₁CoeffDeg hQ₁Root
  -- Step 2: Pairwise non-associated irreducible factor cover of P₁
  obtain ⟨Fset, hFmem, hFnon, hFprodDvd, hFsumDeg, hFcov⟩ :=
    nonassociated_factor_cover P₁ hP₁ne hP₁prim
  have hFne : ∀ f ∈ Fset, f ≠ 0 := fun f hf => (hFmem f hf).1.ne_zero
  have hFdvdQ₁ : ∀ f ∈ Fset, f ∣ Q₁ := fun f hf => (hFmem f hf).2.2.trans hP₁dvd
  have hFprodDvdQ₁ : (∏ f ∈ Fset, f) ∣ Q₁ := hFprodDvd.trans hP₁dvd
  let l := ∑ f ∈ Fset, f.natDegree
  have hl : l ≤ b₁ := hFsumDeg.trans (hP₁deg.le.trans hQ₁Deg)
  -- Step 3: Assign each z ∈ fam.G \ E₀ to a unique factor f ∈ Fset
  let G₀ := fam.G \ E₀
  have hG₀cov : ∀ z ∈ G₀, ∃ f ∈ Fset, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    intro z hz
    obtain ⟨hzG, hzE⟩ := Finset.mem_sdiff.mp hz
    exact hFcov (φ z) ((fam.q z).map φ) (hP₁root z hzG hzE)
  obtain ⟨assign, hAsub, hAroot, hAdis, hAcard⟩ :=
    exists_disjoint_assignment G₀ Fset
      (fun z f => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) hG₀cov
  have hAsubG : ∀ f ∈ Fset, assign f ⊆ fam.G := fun f hf =>
    (hAsub f hf).trans Finset.sdiff_subset
  -- Step 4: Identify rich linear factors Hset ⊆ Fset (f.natDegree = 1 and L < (assign f).card)
  let Hset := Fset.filter fun f => f.natDegree = 1 ∧ L < (assign f).card
  let S := Fset \ Hset
  -- Every rich factor in Fset divides Q₂
  have hRichDvdQ₂ (f : K[X][X][X]) (hf : f ∈ Fset) (hrich : L < (assign f).card) : f ∣ Q₂ :=
    hComp f (assign f) (hFmem f hf).1 (hFmem f hf).2.1 (hFdvdQ₁ f hf) (hAsubG f hf) hrich
      (hAroot f hf)
  -- Every f ∈ Hset gives a base-field affine head l_f ∈ lineParameters fam with Associated f (headFactor φ l_f)
  have hHeadExists (f : K[X][X][X]) (hf : f ∈ Hset) :
      ∃ h ∈ lineParameters fam, assign f ⊆ pointsOn fam h ∧ Associated f (headFactor φ h) := by
    obtain ⟨hfF, hfDeg, hfRich⟩ := Finset.mem_filter.mp hf
    have hfQ₂ : f ∣ Q₂ := hRichDvdQ₂ f hfF hfRich
    have hfTot : TotalDegreeLe f s₂ := by
      have hQ₂t := totalDegree_le_of_totalDegreeLe hQ₂Tot
      obtain ⟨R, hR⟩ := hfQ₂
      have hRne : R ≠ 0 := right_ne_zero_of_mul (hR ▸ hQ₂)
      have hft : Bivariate.totalDegree f ≤ s₂ := by
        rw [hR, Bivariate.totalDegree_mul (hFne f hfF) hRne] at hQ₂t
        omega
      exact fun j hj => (totalDegreeLe_self f j hj).trans hft
    obtain ⟨h, hhMem, hsub⟩ := linear_factor_is_head_of_gap φ fam hs₂ hs₂L hdt hn ht hLinGap
      f (hFmem f hfF).1 hfDeg hfTot (assign f) (hAsubG f hfF) hfRich (hAroot f hfF)
    -- Show headFactor φ h ∣ f, hence Associated f (headFactor φ h)
    have hHdvd : headFactor φ h ∣ f := by
      apply headFactor_dvd_of_many_points φ f hfTot h (assign f) (by omega)
      intro z hz
      have hqz := ((mem_pointsOn_iff fam h z).mp (hsub hz)).2
      rw [← hqz]
      exact hAroot f hfF z hz
    exact ⟨h, hhMem, hsub, ((headFactor_irreducible φ h).associated_of_dvd (hFmem f hfF).1 hHdvd).symm⟩
  -- Pick the unique head line for each f ∈ Hset
  let lineOf (f : {x // x ∈ Hset}) : LineParameter F := Classical.choose (hHeadExists f.1 f.2)
  have hLineSpec (f : {x // x ∈ Hset}) :
      lineOf f ∈ lineParameters fam ∧ assign f.1 ⊆ pointsOn fam (lineOf f) ∧
      Associated f.1 (headFactor φ (lineOf f)) :=
    Classical.choose_spec (hHeadExists f.1 f.2)
  have hLineInj : Function.Injective lineOf := by
    intro f₁ f₂ heq
    apply Subtype.ext
    by_contra hne
    have h1 := (hLineSpec f₁).2.2
    have h2 := (hLineSpec f₂).2.2
    rw [heq] at h1
    exact hFnon f₁.1 (Finset.mem_filter.mp f₁.2).1 f₂.1 (Finset.mem_filter.mp f₂.2).1 hne
      (h1.trans h2.symm)
  let H : Finset (LineParameter F) := Finset.univ.image lineOf
  have hHcard : H.card = Hset.card := by
    rw [Finset.card_image_of_injective _ hLineInj, Finset.card_univ, Fintype.card_coe]
  have hHsub : H ⊆ lineParameters fam := by
    intro h hh
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hh
    exact (hLineSpec f).1
  have hHrich : ∀ h ∈ H, L < (pointsOn fam h).card := by
    intro h hh
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hh
    have hfRich := (Finset.mem_filter.mp f.2).2.2
    exact hfRich.trans_le (Finset.card_le_card (hLineSpec f).2.1)
  -- For f ∈ S, redefine its effective assigned set after removing labels already covered by H
  let rem (f : K[X][X][X]) : Finset F := assign f \ H.biUnion (pointsOn fam)
  -- Check H.card ≤ l and ∑ f ∈ S, f.natDegree = l - H.card
  have hHsumDeg : ∑ f ∈ Hset, f.natDegree = Hset.card := by
    have h := Finset.sum_congr (s₁ := Hset) rfl (fun f hf => (Finset.mem_filter.mp hf).2.1)
    simpa using h
  have hFsplit : (∑ f ∈ S, f.natDegree) + (∑ f ∈ Hset, f.natDegree) = l := by
    dsimp only [S, l]
    exact Finset.sum_sdiff (Finset.filter_subset _ Fset)
  have hHle : H.card ≤ l := by omega
  have hSdeg : ∑ f ∈ S, f.natDegree = l - H.card := by omega
  -- Total label bound: fam.G.card ≤ s₁ + |H.biUnion pointsOn| + ∑ f ∈ S, (rem f).card
  have hTotCard : fam.G.card ≤ s₁ + (H.biUnion (pointsOn fam)).card + ∑ f ∈ S, (rem f).card := by
    have hE₀ : fam.G.card = E₀.card + G₀.card := by
      have h := Finset.card_sdiff_add_card_eq_card hE₀sub
      dsimp only [G₀]; omega
    -- Every z ∈ G₀ lies in assign f for some f ∈ Fset; if f ∈ Hset it's in H.biUnion pointsOn,
    -- if f ∈ S it's either in H.biUnion pointsOn or in rem f!
    have hG₀sub : G₀ ⊆ H.biUnion (pointsOn fam) ∪ S.biUnion rem := by
      intro z hz
      have hmem : z ∈ Fset.biUnion assign := by
        -- From hAcard and disjointness
        obtain ⟨f, hfF, hzf⟩ : ∃ f ∈ Fset, z ∈ assign f := by
          by_contra hno
          push Not at hno
          have hdis' : ∀ f ∈ Fset, z ∉ assign f := hno
          have hsub' : Fset.biUnion assign ⊆ G₀.erase z := by
            intro w hw
            obtain ⟨f, hfF, hwf⟩ := Finset.mem_biUnion.mp hw
            exact Finset.mem_erase.mpr ⟨fun heq => hdis' f hfF (heq ▸ hwf), hAsub f hfF hwf⟩
          have hcard1 := Finset.card_le_card hsub'
          rw [Finset.card_biUnion (fun f hf g hg hne => hAdis f hf g hg hne),
            ← hAcard, Finset.card_erase_of_mem hz] at hcard1
          have hpos := Finset.card_pos.mpr ⟨z, hz⟩
          omega
        exact Finset.mem_biUnion.mpr ⟨f, hfF, hzf⟩
      obtain ⟨f, hfF, hzf⟩ := Finset.mem_biUnion.mp hmem
      by_cases hfH : f ∈ Hset
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨lineOf ⟨f, hfH⟩, Finset.mem_image_of_mem lineOf (Finset.mem_univ _),
            (hLineSpec ⟨f, hfH⟩).2.1 hzf⟩)
      · by_cases hzH : z ∈ H.biUnion (pointsOn fam)
        · exact Finset.mem_union_left _ hzH
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨f, Finset.mem_sdiff.mpr ⟨hfF, hfH⟩, Finset.mem_sdiff.mpr ⟨hzf, hzH⟩⟩)
    have hG₀card : G₀.card ≤ (H.biUnion (pointsOn fam)).card + ∑ f ∈ S, (rem f).card :=
      (Finset.card_le_card hG₀sub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
    omega
  -- Now bound (rem f).card for each f ∈ S
  refine ⟨l, H, S, fun f => (rem f).card, hl, hHsub, hHle, hHrich,
    fun f hf => (hFmem f (Finset.mem_sdiff.mp hf).1).2.1, hSdeg, hTotCard, ?_⟩
  intro f hfS
  obtain ⟨hfF, hfNotH⟩ := Finset.mem_sdiff.mp hfS
  have hremSub : rem f ⊆ assign f := Finset.sdiff_subset
  by_cases hfDeg1 : f.natDegree ≤ 1
  · simp only [hfDeg1, ↓reduceIte]
    have hf1 : f.natDegree = 1 := by have := (hFmem f hfF).2.1; omega
    have hnotRich : ¬ L < (assign f).card := fun hr =>
      hfNotH (Finset.mem_filter.mpr ⟨hfF, hf1, hr⟩)
    exact (Finset.card_le_card hremSub).trans (by omega)
  · simp only [hfDeg1, ↓reduceIte]
    have hb2 : 2 ≤ f.natDegree := by omega
    by_cases hremSmall : (rem f).card ≤ L
    · exact hremSmall.trans (le_max_left _ _)
    · push Not at hremSmall
      apply le_trans _ (le_max_right _ _)
      have hassignRich : L < (assign f).card := hremSmall.trans_le (Finset.card_le_card hremSub)
      have hfQ₂ : f ∣ Q₂ := hRichDvdQ₂ f hfF hassignRich
      -- Bound total degree of f by min (s₂ - H.card) (extraDeg H)
      let Cset := insert f Hset
      have hCsub : Cset ⊆ Fset := Finset.insert_subset_iff.mpr ⟨hfF, Finset.filter_subset _ Fset⟩
      have hCdvdQ₂ : ∀ g ∈ Cset, g ∣ Q₂ := by
        intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hgH
        · exact hfQ₂
        · exact hRichDvdQ₂ g (Finset.mem_filter.mp hgH).1 (Finset.mem_filter.mp hgH).2.2
      have hCprodDvd : (∏ g ∈ Cset, g) ∣ Q₂ :=
        prod_nonassociated_dvd Cset
          (fun g hg => (hFmem g (hCsub hg)).1) hCdvdQ₂
          (fun g₁ hg₁ g₂ hg₂ hne => hFnon g₁ (hCsub hg₁) g₂ (hCsub hg₂) hne)
      have hftot1 : Bivariate.totalDegree f ≤ s₂ - H.card := by
        rw [hHcard]
        exact factor_totalDegree_le_residual hQ₂ Cset Hset (Finset.subset_insert f Hset)
          (fun g hg => (hFmem g (hCsub hg)).2.1) hCprodDvd
          (totalDegree_le_of_totalDegreeLe hQ₂Tot) (Finset.mem_insert_self f Hset) hfNotH
      have hremDisj : ∀ h ∈ H, Disjoint (rem f) (pointsOn fam h) := by
        intro h hh
        rw [Finset.disjoint_left]
        intro z hzr hzh
        exact (Finset.mem_sdiff.mp hzr).2 (Finset.mem_biUnion.mpr ⟨h, hh, hzh⟩)
      have hftot2 : TotalDegreeLe f (extraDeg H) :=
        hExtra H hHsub hHrich f (rem f) (hFmem f hfF).1 hb2 (hFdvdQ₁ f hfF) hfQ₂
          (hremSub.trans (hAsubG f hfF)) hremDisj hremSmall
          (fun z hz => hAroot f hfF z (hremSub hz))
      have hftotMin : TotalDegreeLe f (min (s₂ - H.card) (extraDeg H)) := by
        intro j hj
        exact le_min ((totalDegreeLe_self f j hj).trans hftot1) (hftot2 j hj)
      -- Bound weight of f by W₁ - (l - f.natDegree) * d
      have hfWt : weight d f ≤ W₁ - (l - f.natDegree) * d :=
        (factor_weight_le_residual hQ₁ Fset hFne hFprodDvdQ₁ d hfF).trans
          (Nat.sub_le_sub_right hQ₁Wt _)
      -- Check characteristic bound for f
      have hfDegLe : f.natDegree ≤ b₁ :=
        (Finset.single_le_sum (f := natDegree) (fun _ _ => Nat.zero_le _) hfF).trans hl
      have hcharF : ∀ r : ℕ, 0 < r →
          r ≤ max ((2 * f.natDegree - 2) * (W₁ - (l - f.natDegree) * d) -
            f.natDegree * (f.natDegree - 1) * d) f.natDegree →
          (r : K) ≠ 0 := by
        intro r hrpos hrle
        apply hchar r hrpos
        have h1 : (2 * f.natDegree - 2) * (W₁ - (l - f.natDegree) * d) -
            f.natDegree * (f.natDegree - 1) * d ≤ (2 * b₁ - 2) * W₁ := by
          apply (Nat.sub_le _ _).trans
          exact Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
        exact hrle.trans (max_le_max h1 hfDegLe)
      -- Apply nonlinear_population_le_of_cap!
      have hbound := nonlinear_population_le_of_cap hcap φ fam ht (hn ▸ hJ) f (hFmem f hfF).1
        hb2 hftotMin hfWt hcharF (rem f) (hremSub.trans (hAsubG f hfF))
        (fun z hz => hAroot f hfF z (hremSub hz))
      rwa [hn] at hbound

/-- Convenience specialization of `two_surface_accounting` when no third surface is used
(taking `extraDeg _ = s₂`, so `min (s₂ - H.card) s₂ = s₂ - H.card`). -/
theorem two_surface_accounting_simple {dom : I ↪ F} {d n t : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hn : Fintype.card I = n) (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hdt : d < t) (hJ : n * d < t ^ 2)
    {b₁ s₁ W₁ s₂ L : ℕ} (hs₂ : 1 ≤ s₂) (hs₂L : s₂ < L + 1)
    (Q₁ Q₂ : K[X][X][X]) (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hQ₁Deg : Q₁.natDegree ≤ b₁) (hQ₁Tot : TotalDegreeLe Q₁ s₁) (hQ₁Wt : weight d Q₁ ≤ W₁)
    (hQ₂Tot : TotalDegreeLe Q₂ s₂)
    (hQ₁Root : ∀ z ∈ fam.G, Q₁.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0)
    (hComp : ∀ (f : K[X][X][X]) (G : Finset F), Irreducible f → 0 < f.natDegree → f ∣ Q₁ →
      G ⊆ fam.G → L < G.card →
      (∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) → f ∣ Q₂)
    (hLinGap : (s₂ * (L + 1 - s₂) + 3 * (L + 1) * (s₂ - 1)) * n <
      (L + 1) * (L + 1 - s₂) * (t - d))
    {price : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hcap : NonlinearComponentCap price)
    (hchar : ∀ r : ℕ, 0 < r → r ≤ max ((2 * b₁ - 2) * W₁) b₁ → (r : K) ≠ 0) :
    ∃ (l : ℕ) (H : Finset (LineParameter F)) (S : Finset K[X][X][X]) (labels : K[X][X][X] → ℕ),
      l ≤ b₁ ∧ H ⊆ lineParameters fam ∧ H.card ≤ l ∧
      (∀ h ∈ H, L < (pointsOn fam h).card) ∧
      (∀ f ∈ S, 0 < f.natDegree) ∧
      (∑ f ∈ S, f.natDegree = l - H.card) ∧
      fam.G.card ≤ s₁ + (H.biUnion (pointsOn fam)).card + ∑ f ∈ S, labels f ∧
      (∀ f ∈ S, labels f ≤
        if f.natDegree ≤ 1 then L
        else max L (price n d t (W₁ - (l - f.natDegree) * d) (s₂ - H.card) f.natDegree)) := by
  obtain ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, hEach⟩ :=
    two_surface_accounting φ fam hn ht hdt hJ hs₂ hs₂L Q₁ Q₂ hQ₁ hQ₂ hQ₁Deg hQ₁Tot hQ₁Wt hQ₂Tot
      hQ₁Root hComp hLinGap hcap hchar (fun _ => s₂) (by
        intro _ _ _ f _ _ _ _ hfQ₂ _ _ _ _
        obtain ⟨R, hR⟩ := hfQ₂
        have hRne : R ≠ 0 := right_ne_zero_of_mul (hR ▸ hQ₂)
        have hQ₂t := totalDegree_le_of_totalDegreeLe hQ₂Tot
        have hft : Bivariate.totalDegree f ≤ s₂ := by
          rw [hR, Bivariate.totalDegree_mul (left_ne_zero_of_mul (hR ▸ hQ₂)) hRne] at hQ₂t
          omega
        exact fun j hj => (totalDegreeLe_self f j hj).trans hft)
  refine ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, ?_⟩
  intro f hf
  have h := hEach f hf
  rwa [min_eq_left (Nat.sub_le s₂ H.card)] at h

omit [Nonempty I] [DecidableEq I] [Fintype F] [Infinite K] in
/-- Standard resultant-based companion divisibility helper for `two_surface_accounting`:
if `f ∣ Q₁` (`TotalDegreeLe Q₁ s₁`, `Q₁.natDegree ≤ b₁`) carries strictly more than
`b₁ * s₂ + b₂ * s₁` labels that also vanish on `Q₂` (`TotalDegreeLe Q₂ s₂`, `Q₂.natDegree ≤ b₂`),
then `f ∣ Q₂`. -/
theorem companion_dvd_of_resultant {dom : I ↪ F} {d : ℕ} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    {b₁ s₁ b₂ s₂ L : ℕ}
    (Q₁ Q₂ : K[X][X][X]) (hQ₁ : Q₁ ≠ 0)
    (hQ₁Deg : Q₁.natDegree ≤ b₁) (hQ₁Tot : TotalDegreeLe Q₁ s₁)
    (hQ₂Deg : Q₂.natDegree ≤ b₂) (hQ₂Tot : TotalDegreeLe Q₂ s₂)
    (hQ₂Root : ∀ z ∈ fam.G, Q₂.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0)
    (hL : b₁ * s₂ + b₂ * s₁ ≤ L) :
    ∀ (f : K[X][X][X]) (G : Finset F), Irreducible f → 0 < f.natDegree → f ∣ Q₁ →
      G ⊆ fam.G → L < G.card →
      (∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) → f ∣ Q₂ := by
  intro f G hIrr hPos hfQ₁ hGsub hGL hroot
  have hfDeg : f.natDegree ≤ b₁ := (natDegree_le_of_dvd hfQ₁ hQ₁).trans hQ₁Deg
  have hfTot : TotalDegreeLe f s₁ := by
    have hQ₁t := totalDegree_le_of_totalDegreeLe hQ₁Tot
    obtain ⟨R, hR⟩ := hfQ₁
    have hft : Bivariate.totalDegree f ≤ s₁ := by
      rw [hR, Bivariate.totalDegree_mul hIrr.ne_zero (right_ne_zero_of_mul (hR ▸ hQ₁))] at hQ₁t
      omega
    exact fun j hj => (totalDegreeLe_self f j hj).trans hft
  apply divides_of_many_sections φ f Q₂ hIrr hPos hfTot hQ₂Tot G (fun z => (fam.q z).map φ)
    (fun z hz => ⟨hroot z hz, hQ₂Root z (hGsub hz)⟩)
  have h1 : f.natDegree * s₂ ≤ b₁ * s₂ := Nat.mul_le_mul_right s₂ hfDeg
  have h2 : Q₂.natDegree * s₁ ≤ b₂ * s₁ := Nat.mul_le_mul_right s₁ hQ₂Deg
  exact (Nat.sub_le _ _).trans_lt (by omega)

omit [Infinite K] in
/-- Extract `natDegree ≤ b`, `TotalDegreeLe Q s`, and `weight d Q ≤ W - 1` directly from the
standard `surface_support` shape predicate `∀ j h x, ... → j ≤ b ∧ h + j ≤ s ∧ x + j * d < W`. -/
theorem surface_bounds_of_support {Q : K[X][X][X]} {b s d W : ℕ}
    (hsupp : ∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * d < W) :
    Q.natDegree ≤ b ∧ TotalDegreeLe Q s ∧ weight d Q ≤ W - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext h x
    simp only [coeff_zero]
    by_contra hne
    exact hj.not_ge (hsupp j h x hne).1
  · intro j hj
    have hh : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hj
    have hx := leadingCoeff_ne_zero.mpr hh
    exact (hsupp j _ _ hx).2.1
  · apply weight_le_of_coeff
    intro j h x hne
    have := (hsupp j h x hne).2.2
    omega

end TwoSurfaceAccounting

#print axioms logDerivPrice_mono
#print axioms nonlinear_population_le_of_cap
#print axioms nonassociated_factor_cover
#print axioms factor_weight_le_residual
#print axioms factor_totalDegree_le_residual
#print axioms exists_disjoint_assignment
#print axioms rich_head_core_ge
#print axioms bonferroni_core_union
#print axioms cauchy_core_union
#print axioms two_surface_accounting
#print axioms two_surface_accounting_simple
#print axioms companion_dvd_of_resultant
#print axioms surface_bounds_of_support

end ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting
