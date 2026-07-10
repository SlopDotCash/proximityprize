/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS4Depth3PatternDecomposition

/-!
# LANE FS11 (#466, Fable session 2026-07-09): THE DEPTH-GENERIC PATTERN DECOMPOSITION —
  `rEnergy(μ_n) r = trivialCountG r + wraparoundExcessG r` for EVERY depth `r`, and the
  field-independence of the trivial term

Generalizes FS4 from hard-coded sextuples to every depth `r` at once, on the `piFinset`
shape of the in-tree `rEnergy`:

* `patternPolyG m a b = Σᵢ μ(aᵢ) − Σᵢ μ(bᵢ)` — degree `< m`, coefficients `≤ 2r`
  (`patternPolyG_natDegree_lt`, `patternPolyG_coeff_abs_le` — the FS2/FS3 annihilator input
  shape at height exponent `b` with `2r ≤ 2^b`).
* `sum_eq_iff_aeval_patternPolyG` — the depth-`r` energy condition is pattern vanishing.
* **`rEnergy_eq_trivial_add_excess`** — the EXACT decomposition, every depth, every field
  with a primitive `2m`-th root: `rEnergy (μ_{2m}) r = trivialCountG m r +
  wraparoundExcessG ζ m r`, with `trivialCountG` FIELD-FREE (a pure ℤ[X] count).

Consequence available to the ledger (FS1–FS3 are already depth-generic): at every prime
where no nontrivial depth-`r` pattern vanishes, `rEnergy` takes EXACTLY its
characteristic-zero value — for every fixed `r`, at all but
`≤ n^{2r}·((k+1+b)·n/s)` primes of any family of primes `≥ 2^s` (`2r ≤ 2^b`).  The composed
theorem is the follow-up lane (spawned task "depth-generic T=1 ledger"); this brick lands
the decomposition engine it needs.

**Honest scope:** no Wick census at generic depth is claimed (the union bound
`trivialCountG ≤ (2r−1)‼·n^r` is the spawned task's pairing-induction); the deep-`r`
(`r ≈ ln q`) joint limit — the prize wall — is untouched (the exceptional-set budget grows
like `n^{2r+1}`, vastly exceeding any polynomial prime family at prize depths).

Issue #466, lane FS11.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition

open scoped Classical

/-- The depth-generic pattern polynomial of a pair of exponent `r`-tuples. -/
noncomputable def patternPolyG (m : ℕ) {r : ℕ} (a b : Fin r → ℕ) : ℤ[X] :=
  (∑ i, monomF m (a i)) - (∑ i, monomF m (b i))

section PolyFacts

/-- Degree bound: `deg < m` for in-range exponents. -/
theorem patternPolyG_natDegree_lt {m r : ℕ} (hm : 0 < m) {a b : Fin r → ℕ}
    (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m) :
    (patternPolyG m a b).natDegree < m := by
  unfold patternPolyG
  have hs : ∀ (c : Fin r → ℕ), (∀ i, c i < 2 * m) →
      (∑ i, monomF m (c i)).natDegree ≤ m - 1 := by
    intro c hc
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    have := monomF_natDegree_lt hm (hc i)
    omega
  have h1 := hs a ha
  have h2 := hs b hb
  have := Polynomial.natDegree_sub_le (∑ i, monomF m (a i)) (∑ i, monomF m (b i))
  omega

/-- Coefficient bound: `|coeff| ≤ 2r`. -/
theorem patternPolyG_coeff_abs_le (m : ℕ) {r : ℕ} (a b : Fin r → ℕ) (j : ℕ) :
    |(patternPolyG m a b).coeff j| ≤ 2 * r := by
  unfold patternPolyG
  rw [coeff_sub]
  have hs : ∀ (c : Fin r → ℕ), |(∑ i, monomF m (c i)).coeff j| ≤ r := by
    intro c
    rw [Polynomial.finset_sum_coeff]
    calc |∑ i, (monomF m (c i)).coeff j|
        ≤ ∑ i, |(monomF m (c i)).coeff j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin r, (1 : ℤ) := Finset.sum_le_sum (fun i _ => monomF_coeff_abs_le m _ j)
      _ = r := by simp
  calc |(∑ i, monomF m (a i)).coeff j - (∑ i, monomF m (b i)).coeff j|
      ≤ |(∑ i, monomF m (a i)).coeff j| + |(∑ i, monomF m (b i)).coeff j| := abs_sub _ _
    _ ≤ (r : ℤ) + r := add_le_add (hs a) (hs b)
    _ = 2 * r := by ring

end PolyFacts

section Eval

variable {F : Type*} [Field F]

/-- The depth-`r` energy condition is pattern vanishing. -/
theorem sum_eq_iff_aeval_patternPolyG {ζ : F} {m : ℕ} (hζ : ζ ^ m = -1) {r : ℕ}
    {a b : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m) :
    (∑ i, ζ ^ a i = ∑ i, ζ ^ b i) ↔ aeval ζ (patternPolyG m a b) = 0 := by
  unfold patternPolyG
  rw [map_sub, map_sum, map_sum]
  have hva : ∀ i : Fin r, aeval ζ (monomF m (a i)) = ζ ^ a i :=
    fun i => aeval_monomF hζ (ha i)
  have hvb : ∀ i : Fin r, aeval ζ (monomF m (b i)) = ζ ^ b i :=
    fun i => aeval_monomF hζ (hb i)
  rw [Finset.sum_congr rfl (fun i _ => hva i), Finset.sum_congr rfl (fun i _ => hvb i),
    sub_eq_zero]

end Eval

section Decomposition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exponent domain at depth `r`: `r`-tuples over `[0, n)`. -/
noncomputable def expTuples (n r : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ : Fin r => range n)

theorem expTuples_card (n r : ℕ) : (expTuples n r).card = n ^ r := by
  simp [expTuples, Fintype.card_piFinset]

/-- The field-free trivial count at depth `r`. -/
noncomputable def trivialCountG (m r : ℕ) : ℕ :=
  ((expTuples (2 * m) r ×ˢ expTuples (2 * m) r).filter
    (fun ab => patternPolyG m ab.1 ab.2 = 0)).card

/-- The char-`p` wraparound excess at depth `r`. -/
noncomputable def wraparoundExcessG (ζ : F) (m r : ℕ) : ℕ :=
  ((expTuples (2 * m) r ×ˢ expTuples (2 * m) r).filter
    (fun ab => patternPolyG m ab.1 ab.2 ≠ 0 ∧ aeval ζ (patternPolyG m ab.1 ab.2) = 0)).card

/-- **THE DEPTH-GENERIC EXACT DECOMPOSITION.**  For every depth `r`, every field with a
primitive `2m`-th root `ζ`:
`rEnergy (μ_{2m}) r = trivialCountG m r + wraparoundExcessG ζ m r`. -/
theorem rEnergy_eq_trivial_add_excess {ζ : F} {m : ℕ} (hm : 0 < m)
    (hprim : IsPrimitiveRoot ζ (2 * m)) (r : ℕ) :
    rEnergy ((range (2 * m)).image (ζ ^ ·)) r
      = trivialCountG m r + wraparoundExcessG ζ m r := by
  have hζm : ζ ^ m = -1 := by
    have hsq : ζ ^ m * ζ ^ m = 1 := by
      rw [← pow_add, show m + m = 2 * m by ring]
      exact hprim.pow_eq_one
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h (hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega))
    · exact h
  -- the pi-set over the image is the image of the pi-set
  have hset : Fintype.piFinset (fun _ : Fin r => (range (2 * m)).image (ζ ^ ·))
      = (expTuples (2 * m) r).image (fun g => fun i => ζ ^ g i) := by
    ext v
    simp only [Fintype.mem_piFinset, Finset.mem_image, expTuples]
    constructor
    · intro h
      choose g hg hgv using h
      exact ⟨g, hg, funext hgv⟩
    · rintro ⟨g, hg, rfl⟩
      intro i
      exact ⟨g i, hg i, rfl⟩
  have hinj : ∀ g ∈ expTuples (2 * m) r, ∀ g' ∈ expTuples (2 * m) r,
      (fun i => ζ ^ g i) = (fun i => ζ ^ g' i) → g = g' := by
    intro g hg g' hg' heq
    rw [expTuples, Fintype.mem_piFinset] at hg hg'
    funext i
    exact hprim.pow_inj (mem_range.mp (hg i)) (mem_range.mp (hg' i)) (congrFun heq i)
  have himg : ∀ f : (Fin r → F) → ℕ,
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => (range (2 * m)).image (ζ ^ ·)), f v
        = ∑ g ∈ expTuples (2 * m) r, f (fun i => ζ ^ g i) := by
    intro f
    rw [hset]
    exact Finset.sum_image hinj
  rw [rEnergy, himg]
  have hstep : ∀ g ∈ expTuples (2 * m) r,
      (∑ w ∈ Fintype.piFinset (fun _ : Fin r => (range (2 * m)).image (ζ ^ ·)),
        (if ∑ i, ζ ^ g i = ∑ i, w i then (1 : ℕ) else 0))
      = ∑ h ∈ expTuples (2 * m) r,
          ((if patternPolyG m g h = 0 then (1 : ℕ) else 0)
            + (if patternPolyG m g h ≠ 0 ∧ aeval ζ (patternPolyG m g h) = 0
                then (1 : ℕ) else 0)) := by
    intro g hg
    rw [himg]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [expTuples, Fintype.mem_piFinset] at hg hh
    have hga : ∀ i, g i < 2 * m := fun i => mem_range.mp (hg i)
    have hhb : ∀ i, h i < 2 * m := fun i => mem_range.mp (hh i)
    have hiff := sum_eq_iff_aeval_patternPolyG (m := m) hζm hga hhb
    by_cases hP : patternPolyG m g h = 0
    · have hE : aeval ζ (patternPolyG m g h) = 0 := by rw [hP]; simp
      rw [if_pos (hiff.mpr hE), if_pos hP, if_neg (by simp [hP])]
    · by_cases hE : aeval ζ (patternPolyG m g h) = 0
      · rw [if_pos (hiff.mpr hE), if_neg hP, if_pos ⟨hP, hE⟩]
      · rw [if_neg (fun hs => hE (hiff.mp hs)), if_neg hP, if_neg (by simp [hE])]
  calc ∑ g ∈ expTuples (2 * m) r,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin r => (range (2 * m)).image (ζ ^ ·)),
          (if ∑ i, ζ ^ g i = ∑ i, w i then (1 : ℕ) else 0)
      = ∑ g ∈ expTuples (2 * m) r, ∑ h ∈ expTuples (2 * m) r,
          ((if patternPolyG m g h = 0 then (1 : ℕ) else 0)
            + (if patternPolyG m g h ≠ 0 ∧ aeval ζ (patternPolyG m g h) = 0
                then (1 : ℕ) else 0)) :=
        Finset.sum_congr rfl hstep
    _ = trivialCountG m r + wraparoundExcessG ζ m r := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [trivialCountG, Finset.card_filter, Finset.sum_product]
        · rw [wraparoundExcessG, Finset.card_filter, Finset.sum_product]

end Decomposition

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms patternPolyG_natDegree_lt
#print axioms patternPolyG_coeff_abs_le
#print axioms sum_eq_iff_aeval_patternPolyG
#print axioms rEnergy_eq_trivial_add_excess

end ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
