/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R240GeneralRFoldVariance

/-!
# LANE B2 (#466 round 303): DEPTH-UNIFORM ORBIT CHEBYSHEV — the r300 machinery at every
  moment depth `r`

Round 300 landed the multi-orbit transversal bound and the orbit-level Chebyshev for the
DEPTH-3 deviation.  The moment tower consumes depths up to `r ≈ ln q`, so the machinery must
be depth-uniform.  R240 already has the general `repR`/`variance_identity`; this brick adds:

* **`repR_smul`** : the `r`-fold representation function is `G`-invariant at EVERY depth —
  `repR G r (a·c) = repR G r c` for `a ∈ G` (coordinatewise reindexing `v ↦ a·v`);
* **`deviationR_smul` / `sum_deviationR_zero`** : ditto for the deviation
  `dᵣ(c) = q·repR(c) − |G|^r`;
* **`deficit_ge_orbit_family`** : `|G| · Σ_{b∈R} dᵣ(b)² ≤ Σ_c dᵣ(c)²` for any pairwise
  `G`-inequivalent family `R` of nonzero frequencies;
* **`orbit_count_chebyshev`** / **`orbit_count_chebyshev_energy`** : hence
  `|R| · |G| · T² ≤ q·(q·Eᵣ − |G|^{2r})` when every `b ∈ R` has `|dᵣ(b)| ≥ T` — the
  moment→level-set step with the `/|G|` orbit saving, at every depth simultaneously.

With this, ANY future sub-Wick bound on the DC-subtracted `r`-energy — at whatever depth the
tower is entered — converts directly into a count of large-period orbits.  Does not touch
the wall (the `r`-energy at prize depth is the open Paley/BGK object).  Issue #466,
round 303, LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev

open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Depth-uniform `G`-invariance**: `repR G r (a·c) = repR G r c` for `a ∈ G`, at every
depth `r` — reindex each coordinate of the summation vector by multiplication by `a`. -/
theorem repR_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) {a : F} (ha : a ∈ G) (c : F) :
    repR G r (a * c) = repR G r c := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hainv : a⁻¹ ∈ G := hinv ha
  have hmemA : ∀ x : F, a * x ∈ G ↔ x ∈ G := by
    intro x
    constructor
    · intro hx
      have : a⁻¹ * (a * x) ∈ G := hmul hainv hx
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
    · intro hx; exact hmul ha hx
  unfold repR
  -- reindex `v ↦ a·v` (coordinatewise) on the vector cube
  refine Finset.sum_nbij' (i := fun v => fun j => a⁻¹ * v j)
    (j := fun v => fun j => a * v j) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [Fintype.mem_piFinset] at hv ⊢
    exact fun j => hmul hainv (hv j)
  · intro v hv
    rw [Fintype.mem_piFinset] at hv ⊢
    exact fun j => (hmemA (v j)).mpr (hv j)
  · intro v _
    funext j
    exact mul_inv_cancel_left₀ ha0 (v j)
  · intro v _
    funext j
    exact inv_mul_cancel_left₀ ha0 (v j)
  · intro v _
    have hsum : ∑ i, (a⁻¹ * v i) = a⁻¹ * ∑ i, v i := by rw [Finset.mul_sum]
    rw [hsum]
    by_cases h : ∑ i, v i = a * c
    · simp [h, inv_mul_cancel_left₀ ha0]
    · have h' : a⁻¹ * (∑ i, v i) ≠ c := fun hc => by
        apply h
        rw [← hc, mul_inv_cancel_left₀ ha0]
      simp [h, h']

/-- The depth-`r` **deviation function** `dᵣ(c) = q·repR G r c − |G|^r` — the summand of the
R240 general variance identity. -/
noncomputable def deviationR (G : Finset F) (r : ℕ) (c : F) : ℝ :=
  (Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r

/-- The deviation is `G`-invariant at every depth. -/
theorem deviationR_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) {a : F} (ha : a ∈ G) (c : F) :
    deviationR G r (a * c) = deviationR G r c := by
  unfold deviationR
  rw [repR_smul G hmul hinv h0 r ha c]

/-- The deviation is mean-zero at every depth: `∑_c dᵣ(c) = 0`. -/
theorem sum_deviationR_zero (G : Finset F) (r : ℕ) :
    ∑ c : F, deviationR G r c = 0 := by
  unfold deviationR
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ c : F, (repR G r c : ℝ) = (G.card : ℝ) ^ r := by
    calc ∑ c : F, (repR G r c : ℝ) = ((∑ c : F, repR G r c : ℕ) : ℝ) := by push_cast; rfl
      _ = ((G.card ^ r : ℕ) : ℝ) := by rw [sum_repR G r]
      _ = (G.card : ℝ) ^ r := by push_cast; ring
  have h2 : ∑ _c : F, (G.card : ℝ) ^ r = (Fintype.card F : ℝ) * (G.card : ℝ) ^ r := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, h2]; ring

/-- **Depth-uniform multi-orbit transversal bound**: for any family `R` of pairwise
`G`-inequivalent nonzero frequencies, `|G| · Σ_{b∈R} dᵣ(b)² ≤ Σ_c dᵣ(c)²`. -/
theorem deficit_ge_orbit_family (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b') :
    (G.card : ℝ) * ∑ b ∈ R, (deviationR G r b) ^ 2
      ≤ ∑ c : F, (deviationR G r c) ^ 2 := by
  classical
  set orb : F → Finset F := fun b => G.image (fun a => a * b) with horb
  have hpd : Set.PairwiseDisjoint (↑R : Set F) orb := by
    intro b hb b' hb' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [horb, Finset.mem_image] at hc hc'
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨a', ha', heq⟩ := hc'
    have hmem : a'⁻¹ * a ∈ G := hmul (hinv ha') ha
    have : (a'⁻¹ * a) * b = b' := by
      have ha'0 : a' ≠ 0 := fun h => h0 (h ▸ ha')
      field_simp
      rw [mul_comm a' b', ← heq]; ring
    exact hdisj b hb b' hb' hne (a'⁻¹ * a) hmem this
  have hsplit :
      ∑ c ∈ R.biUnion orb, (deviationR G r c) ^ 2
        = ∑ b ∈ R, ∑ c ∈ orb b, (deviationR G r c) ^ 2 :=
    Finset.sum_biUnion hpd
  have horbsum : ∀ b ∈ R, ∑ c ∈ orb b, (deviationR G r c) ^ 2
      = (G.card : ℝ) * (deviationR G r b) ^ 2 := by
    intro b hb
    have hb0 : b ≠ 0 := hR0 b hb
    have hconst : ∀ c ∈ orb b, (deviationR G r c) ^ 2 = (deviationR G r b) ^ 2 := by
      intro c hc
      simp only [horb, Finset.mem_image] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      rw [deviationR_smul G hmul hinv h0 r ha b]
    have hcard : (orb b).card = G.card := by
      rw [horb]
      exact Finset.card_image_of_injective _ (mul_left_injective₀ hb0)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  calc (G.card : ℝ) * ∑ b ∈ R, (deviationR G r b) ^ 2
      = ∑ b ∈ R, (G.card : ℝ) * (deviationR G r b) ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ b ∈ R, ∑ c ∈ orb b, (deviationR G r c) ^ 2 :=
        Finset.sum_congr rfl (fun b hb => (horbsum b hb).symm)
    _ = ∑ c ∈ R.biUnion orb, (deviationR G r c) ^ 2 := hsplit.symm
    _ ≤ ∑ c : F, (deviationR G r c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => sq_nonneg _)

/-- **Depth-uniform orbit Chebyshev**: at most `(Σ_c dᵣ(c)²)/(|G|·T²)` orbits carry a
`T`-large depth-`r` deviation. -/
theorem orbit_count_chebyshev (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |deviationR G r b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2) ≤ ∑ c : F, (deviationR G r c) ^ 2 := by
  have hfam := deficit_ge_orbit_family G hmul hinv h0 r R hR0 hdisj
  have hlower : (R.card : ℝ) * T ^ 2 ≤ ∑ b ∈ R, (deviationR G r b) ^ 2 := by
    calc (R.card : ℝ) * T ^ 2 = ∑ _b ∈ R, T ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ R, (deviationR G r b) ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          calc T ^ 2 ≤ |deviationR G r b| ^ 2 := pow_le_pow_left₀ hT (hbig b hb) 2
            _ = (deviationR G r b) ^ 2 := sq_abs _
  calc (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      = (G.card : ℝ) * ((R.card : ℝ) * T ^ 2) := by ring
    _ ≤ (G.card : ℝ) * ∑ b ∈ R, (deviationR G r b) ^ 2 :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
    _ ≤ ∑ c : F, (deviationR G r c) ^ 2 := hfam

/-- **Depth-uniform orbit Chebyshev, energy form** (via the R240 general variance identity):
`|R| · |G| · T² ≤ q·(q·Eᵣ − |G|^{2r})` — the large-period orbit count pays only the
DC-subtracted `r`-energy, at every moment depth simultaneously. -/
theorem orbit_count_chebyshev_energy (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |deviationR G r b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
              * (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
            - (G.card : ℝ) ^ (2 * r)) := by
  have h := orbit_count_chebyshev G hmul hinv h0 r R hR0 hdisj hT hbig
  rwa [show (∑ c : F, (deviationR G r c) ^ 2)
      = ∑ c : F, ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2 from rfl,
    variance_identity G r] at h

end ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.repR_smul
#print axioms ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.sum_deviationR_zero
#print axioms ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.deficit_ge_orbit_family
#print axioms ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.orbit_count_chebyshev
#print axioms ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.orbit_count_chebyshev_energy
