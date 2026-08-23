/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# THE EXACT SUBSET-SUM FIBRE VALUE AT 2-POWER TOWERS (#389)

The quantitative half of the subset-sum fibre law (issue thread, comment "CONJECTURE:
the complete sub-Johnson exact list law") at the production towers `s = 2^(h+1)`:
the maximal subset-sum fibre of `μ_s` over `r`-subsets, in char 0, is EXACTLY

  **`N_fib(2^(h+1), r) = C(2^h − r % 2, r / 2)`**

(`C(s/2 − 1, (r−1)/2)` for `r` odd, `C(s/2, r/2)` for `r` even).  Mechanism: write
`μ_s` as signed half-system `±ζ^i`, `i < 2^h` (`ζ^(2^h) = −1`); a subset's sum is its
**signed core** `c ∈ {−1,0,1}^(2^h)` (antipodal pairs cancel), and the half-system
powers are linearly independent over `ℤ` (`Φ_{2^(h+1)} = X^(2^h) + 1` has degree
`2^h = φ(s)`) — so the sum pins the core, and a fibre is exactly "choose where the
`(r − u)/2` cancelled antipodal pairs sit": `C(2^h − u, (r−u)/2)` for core weight `u`.
The max is at the minimal parity-compatible weight `u = r % 2`.

Matches every probe value of the fibre-law thread: `N_fib(8,3) = 3`, `N_fib(16,3) = 7`,
`N_fib(8,2) = 4`, and reproduces the full `(8,3)` census (40 distinct sums, fibres
`8×3 + 32×1 = 56 = C(8,3)`).

**The split-prime transfer is q-CONDITIONAL** (probe, section B): the value transfers
to `μ_s ⊂ F_p` at `p = 12289` everywhere tested, but FAILS at the Fermat prime
`p = 65537` for `(s,r) = (32,3)`: fibre `16 > 15`, the singleton core
`−ζ − ζ⁷ + ζ¹²` colliding with the `ζ`-fibre because `ord_p(2) = 32` puts `2` INSIDE
`μ_32` — the same small-integer-in-subgroup degeneracy as the Frobenius/subplane
countermodels.  The char-0 value is a floor for every split prime; equality is a
generic-prime statement.

Probe: `scripts/probes/probe_two_power_fibre_value.py` (exact `ℤ[x]/(x^(2^h)+1)`
arithmetic; all 11 char-0 profiles exact — every fibre, not just the max).
Issue #389.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset Polynomial

namespace ProximityGap.PairRank

/-! ## The signed half-system index: `μ_{2^(h+1)}` as `Fin 2^h × Bool` -/

variable {h : ℕ}

/-- The signed half-system value: `(i, false) ↦ ζ^i`, `(i, true) ↦ −ζ^i`. -/
noncomputable def signedVal (ζ : ℂ) (x : Fin (2 ^ h) × Bool) : ℂ :=
  if x.2 then -ζ ^ (x.1 : ℕ) else ζ ^ (x.1 : ℕ)

/-- The subset sum of a signed-index set. -/
noncomputable def subsetSum (ζ : ℂ) (T : Finset (Fin (2 ^ h) × Bool)) : ℂ :=
  ∑ x ∈ T, signedVal ζ x

/-- The signed core of a subset: the antipodal-pair-reduced coefficient vector. -/
def coreInt (T : Finset (Fin (2 ^ h) × Bool)) (i : Fin (2 ^ h)) : ℤ :=
  (if (i, false) ∈ T then 1 else 0) - (if (i, true) ∈ T then 1 else 0)

/-- The doubled positions: antipodal pairs fully inside `T`. -/
def doubles (T : Finset (Fin (2 ^ h) × Bool)) : Finset (Fin (2 ^ h)) :=
  Finset.univ.filter (fun i => (i, false) ∈ T ∧ (i, true) ∈ T)

lemma coreInt_natAbs_le (T : Finset (Fin (2 ^ h) × Bool)) (i : Fin (2 ^ h)) :
    (coreInt T i).natAbs ≤ 1 := by
  unfold coreInt
  split_ifs <;> decide

/-- `ζ^(2^h) = −1` for a primitive `2^(h+1)`-th root of unity. -/
lemma pow_half_eq_neg_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1))) :
    ζ ^ (2 ^ h) = -1 := by
  have hsq : (ζ ^ (2 ^ h)) * (ζ ^ (2 ^ h)) = 1 := by
    rw [← pow_add]
    have : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by ring
    rw [this, hζ.pow_eq_one]
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    have hlt : (2:ℕ) ^ h < 2 ^ (h + 1) := by
      have hpos : (0:ℕ) < 2 ^ h := by positivity
      rw [pow_succ]
      omega
    have hne := hζ.pow_ne_one_of_pos_of_lt
      (pow_ne_zero h (two_ne_zero) : (2:ℕ) ^ h ≠ 0) hlt
    exact hne h1
  · exact h1

/-- The bridge to literal `μ_s` membership: `signedVal (i, b) = ζ^(i + b·2^h)`. -/
lemma signedVal_eq_pow {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    (x : Fin (2 ^ h) × Bool) :
    signedVal ζ x = ζ ^ ((x.1 : ℕ) + if x.2 then 2 ^ h else 0) := by
  unfold signedVal
  rcases x with ⟨i, b⟩
  cases b
  · simp
  · simp only [if_true, pow_add, pow_half_eq_neg_one hζ]
    ring

/-! ## The independence core: half-system powers are `ℤ`-independent -/

/-- **The half-system independence**: an integer combination of `ζ^i`, `i < 2^h`,
vanishes only trivially (`Φ_{2^(h+1)}` has degree `2^h`). -/
theorem half_system_independent {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    {c : Fin (2 ^ h) → ℤ}
    (hvan : ∑ i : Fin (2 ^ h), (c i : ℂ) * ζ ^ (i : ℕ) = 0) :
    c = 0 := by
  classical
  by_contra hc0
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc0
    exact ⟨i, by simpa using hi⟩
  set P : Polynomial ℤ := ∑ i : Fin (2 ^ h), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
    with hP
  have hcoeff : ∀ i : Fin (2 ^ h), P.coeff (i : ℕ) = c i := by
    intro i
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hji
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      intro hij
      exact hji (Fin.ext hij.symm)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hPne : P ≠ 0 := by
    intro h0
    apply hi₀
    rw [← hcoeff i₀, h0, Polynomial.coeff_zero]
  have hPdeg : P.natDegree < 2 ^ h := by
    have hle : P.natDegree ≤ 2 ^ h - 1 := by
      rw [hP]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      have := i.isLt
      omega
    have hpos : 0 < 2 ^ h := by positivity
    omega
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP]
    rw [map_sum]
    rw [← hvan]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    norm_num
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (by positivity)
  have hdvd : minpoly ℤ ζ ∣ P := minpoly.isIntegrallyClosed_dvd hint hPζ
  have hmindeg : (2 ^ (h + 1)).totient ≤ (minpoly ℤ ζ).natDegree :=
    hζ.totient_le_degree_minpoly
  have htot : (2 ^ (h + 1)).totient = 2 ^ h := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos h)]
    simp
  have hchain : (minpoly ℤ ζ).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hPne
  omega

/-! ## The core determines the sum, and the sum determines the core -/

lemma subsetSum_eq_core_sum (ζ : ℂ) (T : Finset (Fin (2 ^ h) × Bool)) :
    subsetSum ζ T = ∑ i : Fin (2 ^ h), (coreInt T i : ℂ) * ζ ^ (i : ℕ) := by
  classical
  have hT : subsetSum ζ T
      = ∑ x : Fin (2 ^ h) × Bool, if x ∈ T then signedVal ζ x else 0 := by
    rw [subsetSum, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hT, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  unfold signedVal coreInt
  by_cases hf : (i, false) ∈ T <;> by_cases ht : (i, true) ∈ T <;>
    simp only [hf, ht, if_true, if_false, Bool.cond_eq_ite] <;>
    push_cast <;> simp <;> ring

/-- Equal sums force equal cores. -/
theorem core_injective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    {T T' : Finset (Fin (2 ^ h) × Bool)}
    (hsum : subsetSum ζ T = subsetSum ζ T') : coreInt T = coreInt T' := by
  have hvan : ∑ i : Fin (2 ^ h), ((coreInt T i - coreInt T' i : ℤ) : ℂ) * ζ ^ (i : ℕ)
      = 0 := by
    have hexp : ∀ i : Fin (2 ^ h),
        ((coreInt T i - coreInt T' i : ℤ) : ℂ) * ζ ^ (i : ℕ)
          = (coreInt T i : ℂ) * ζ ^ (i : ℕ) - (coreInt T' i : ℂ) * ζ ^ (i : ℕ) := by
      intro i
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_sub_distrib,
      ← subsetSum_eq_core_sum, ← subsetSum_eq_core_sum, hsum, sub_self]
  have hzero := half_system_independent hζ hvan
  funext i
  have := congrFun hzero i
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Membership is determined by the core and the doubles. -/
lemma mem_iff_core_doubles {T : Finset (Fin (2 ^ h) × Bool)}
    (x : Fin (2 ^ h) × Bool) :
    x ∈ T ↔ (coreInt T x.1 = if x.2 then -1 else 1) ∨ x.1 ∈ doubles T := by
  classical
  rcases x with ⟨i, b⟩
  unfold coreInt doubles
  rw [Finset.mem_filter]
  cases b <;> by_cases hf : (i, false) ∈ T <;> by_cases ht : (i, true) ∈ T <;>
    simp [hf, ht]

/-- Subsets with equal cores and equal doubles are equal. -/
lemma eq_of_core_doubles {T T' : Finset (Fin (2 ^ h) × Bool)}
    (hcore : coreInt T = coreInt T') (hdoub : doubles T = doubles T') : T = T' := by
  ext x
  rw [mem_iff_core_doubles, mem_iff_core_doubles, hcore, hdoub]

/-- The size decomposition: `|T| = (core weight) + 2·(doubles)`. -/
lemma card_eq_core_add_doubles (T : Finset (Fin (2 ^ h) × Bool)) :
    T.card = (∑ i : Fin (2 ^ h), (coreInt T i).natAbs) + 2 * (doubles T).card := by
  classical
  have hcard : T.card
      = ∑ x : Fin (2 ^ h) × Bool, if x ∈ T then 1 else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  have hdoub : (doubles T).card
      = ∑ i : Fin (2 ^ h), if (i, false) ∈ T ∧ (i, true) ∈ T then 1 else 0 := by
    rw [doubles, Finset.card_filter]
  rw [hcard, Fintype.sum_prod_type, hdoub, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  unfold coreInt
  by_cases hf : (i, false) ∈ T <;> by_cases ht : (i, true) ∈ T <;>
    simp [hf, ht]

/-! ## The fibre theorem -/

open Classical in
/-- **THE FIBRE STRUCTURE THEOREM**: the subset-sum fibre through `T₀` (over `r`-sets,
`r = |T₀|`) has size EXACTLY `C(2^h − u, d)` where `u` is `T₀`'s core weight and `d`
its double count. -/
theorem fibre_card {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    (T₀ : Finset (Fin (2 ^ h) × Bool)) :
    (((Finset.univ : Finset (Fin (2 ^ h) × Bool)).powersetCard T₀.card).filter
        (fun T => subsetSum ζ T = subsetSum ζ T₀)).card
      = (2 ^ h - ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs).choose (doubles T₀).card := by
  classical
  set Z : Finset (Fin (2 ^ h)) :=
    Finset.univ.filter (fun i => coreInt T₀ i = 0) with hZ
  have hZcard : Z.card = 2 ^ h - ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs := by
    have hsplit : Z.card + (Finset.univ.filter (fun i => ¬ coreInt T₀ i = 0)).card
        = 2 ^ h := by
      rw [hZ, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ,
        Fintype.card_fin]
    have hsupp : (Finset.univ.filter (fun i => ¬ coreInt T₀ i = 0)).card
        = ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := coreInt_natAbs_le T₀ i
      by_cases h0 : coreInt T₀ i = 0
      · simp [h0]
      · rw [if_pos h0]
        omega
    omega
  rw [← hZcard, ← Finset.card_powersetCard]
  set recon : Finset (Fin (2 ^ h)) → Finset (Fin (2 ^ h) × Bool) := fun D =>
    Finset.univ.filter (fun x : Fin (2 ^ h) × Bool =>
      (coreInt T₀ x.1 = if x.2 then -1 else 1) ∨ x.1 ∈ D) with hrecon
  have hreconF : ∀ (D : Finset (Fin (2 ^ h))) (i : Fin (2 ^ h)),
      ((i, false) ∈ recon D ↔ (coreInt T₀ i = 1 ∨ i ∈ D)) := by
    intro D i
    simp [hrecon]
  have hreconT : ∀ (D : Finset (Fin (2 ^ h))) (i : Fin (2 ^ h)),
      ((i, true) ∈ recon D ↔ (coreInt T₀ i = -1 ∨ i ∈ D)) := by
    intro D i
    simp [hrecon]
  have hdoubMem : ∀ (T : Finset (Fin (2 ^ h) × Bool)) (i : Fin (2 ^ h)),
      (i ∈ doubles T ↔ ((i, false) ∈ T ∧ (i, true) ∈ T)) := by
    intro T i
    rw [doubles, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  have hbound3 : ∀ (T : Finset (Fin (2 ^ h) × Bool)) (i : Fin (2 ^ h)),
      coreInt T i = 1 ∨ coreInt T i = 0 ∨ coreInt T i = -1 := by
    intro T i
    have := coreInt_natAbs_le T i
    omega
  have hreconCore : ∀ D : Finset (Fin (2 ^ h)), (∀ i ∈ D, coreInt T₀ i = 0) →
      coreInt (recon D) = coreInt T₀ := by
    intro D hDz
    funext i
    rcases hbound3 T₀ i with h1 | h0 | hm1
    · have hf : (i, false) ∈ recon D := (hreconF D i).mpr (Or.inl h1)
      have ht : (i, true) ∉ recon D := by
        intro hc
        rcases (hreconT D i).mp hc with hm | hD
        · omega
        · have := hDz i hD
          omega
      rw [h1]; simp only [coreInt]; rw [if_pos hf, if_neg ht]; ring
    · by_cases hiD : i ∈ D
      · have hf : (i, false) ∈ recon D := (hreconF D i).mpr (Or.inr hiD)
        have ht : (i, true) ∈ recon D := (hreconT D i).mpr (Or.inr hiD)
        rw [h0]; simp only [coreInt]; rw [if_pos hf, if_pos ht]; ring
      · have hf : (i, false) ∉ recon D := by
          intro hc
          rcases (hreconF D i).mp hc with h1 | hD
          · omega
          · exact hiD hD
        have ht : (i, true) ∉ recon D := by
          intro hc
          rcases (hreconT D i).mp hc with hm | hD
          · omega
          · exact hiD hD
        rw [h0]; simp only [coreInt]; rw [if_neg hf, if_neg ht]; ring
    · have ht : (i, true) ∈ recon D := (hreconT D i).mpr (Or.inl hm1)
      have hf : (i, false) ∉ recon D := by
        intro hc
        rcases (hreconF D i).mp hc with h1 | hD
        · omega
        · have := hDz i hD
          omega
      rw [hm1]; simp only [coreInt]; rw [if_neg hf, if_pos ht]; ring
  have hreconDoub : ∀ D : Finset (Fin (2 ^ h)), (∀ i ∈ D, coreInt T₀ i = 0) →
      doubles (recon D) = D := by
    intro D hDz
    ext i
    constructor
    · intro hi
      obtain ⟨hf, ht⟩ := (hdoubMem _ i).mp hi
      rcases (hreconF D i).mp hf with h1 | hD
      · rcases (hreconT D i).mp ht with hm | hD'
        · omega
        · exact hD'
      · exact hD
    · intro hiD
      exact (hdoubMem _ i).mpr
        ⟨(hreconF D i).mpr (Or.inr hiD), (hreconT D i).mpr (Or.inr hiD)⟩
  have hreconCard : ∀ D : Finset (Fin (2 ^ h)), (∀ i ∈ D, coreInt T₀ i = 0) →
      (recon D).card = (∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs) + 2 * D.card := by
    intro D hDz
    rw [card_eq_core_add_doubles (recon D), hreconCore D hDz, hreconDoub D hDz]
  refine Finset.card_bij' (fun T _ => doubles T) (fun D _ => recon D) ?_ ?_ ?_ ?_
  · -- forward: doubles of a fibre member lands in Z.powersetCard
    intro T hT
    obtain ⟨hTp, hTsum⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTp
    have hcore : coreInt T = coreInt T₀ := core_injective hζ hTsum
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨hf, ht⟩ := (hdoubMem T i).mp hi
      rw [hZ, Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      have hzero : coreInt T i = 0 := by
        simp only [coreInt]
        rw [if_pos hf, if_pos ht]
        ring
      rw [← hcore]
      exact hzero
    · show (doubles T).card = (doubles T₀).card
      have h1 := card_eq_core_add_doubles T
      have h2 := card_eq_core_add_doubles T₀
      have hu : ∑ i : Fin (2 ^ h), (coreInt T i).natAbs
          = ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs := by
        rw [hcore]
      rw [hTcard, hu] at h1
      omega
  · -- backward: the reconstruction is in the fibre
    intro D hD
    obtain ⟨hDZ, hDcard⟩ := Finset.mem_powersetCard.mp hD
    have hDz : ∀ i ∈ D, coreInt T₀ i = 0 := by
      intro i hi
      have hmem := hDZ hi
      rw [hZ, Finset.mem_filter] at hmem
      exact hmem.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [hreconCard D hDz, hDcard]
      have h2 := card_eq_core_add_doubles T₀
      omega
    · rw [subsetSum_eq_core_sum, subsetSum_eq_core_sum, hreconCore D hDz]
  · -- left inverse: recon (doubles T) = T
    intro T hT
    obtain ⟨-, hTsum⟩ := Finset.mem_filter.mp hT
    have hcore : coreInt T = coreInt T₀ := core_injective hζ hTsum
    have hDz : ∀ i ∈ doubles T, coreInt T₀ i = 0 := by
      intro i hi
      obtain ⟨hf, ht⟩ := (hdoubMem T i).mp hi
      rw [← hcore]
      simp only [coreInt]
      rw [if_pos hf, if_pos ht]
      ring
    exact eq_of_core_doubles
      (by rw [hreconCore (doubles T) hDz, hcore])
      (hreconDoub (doubles T) hDz)
  · -- right inverse: doubles (recon D) = D
    intro D hD
    obtain ⟨hDZ, -⟩ := Finset.mem_powersetCard.mp hD
    have hDz : ∀ i ∈ D, coreInt T₀ i = 0 := by
      intro i hi
      have hmem := hDZ hi
      rw [hZ, Finset.mem_filter] at hmem
      exact hmem.2
    exact hreconDoub D hDz

/-! ## The maximum -/

lemma choose_step (a b : ℕ) : a.choose b ≤ (a + 2).choose (b + 1) :=
  calc a.choose b ≤ (a + 1).choose b := Nat.choose_le_choose b (Nat.le_succ a)
  _ ≤ (a + 1).choose b + (a + 1).choose (b + 1) := Nat.le_add_right _ _
  _ = (a + 2).choose (b + 1) := (Nat.choose_succ_succ (a + 1) b).symm

lemma choose_chain (M r : ℕ) (hrM : r ≤ M) :
    ∀ k, r % 2 + 2 * k ≤ r →
      (M - (r % 2 + 2 * k)).choose (r / 2 - k) ≤ (M - r % 2).choose (r / 2) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : r % 2 + 2 * k ≤ r := by omega
    refine le_trans ?_ (ih hk')
    have ha : M - (r % 2 + 2 * (k + 1)) + 2 = M - (r % 2 + 2 * k) := by omega
    have hb : r / 2 - (k + 1) + 1 = r / 2 - k := by omega
    calc (M - (r % 2 + 2 * (k + 1))).choose (r / 2 - (k + 1))
        ≤ (M - (r % 2 + 2 * (k + 1)) + 2).choose (r / 2 - (k + 1) + 1) :=
          choose_step _ _
      _ = (M - (r % 2 + 2 * k)).choose (r / 2 - k) := by rw [ha, hb]

open Classical in
/-- **THE FIBRE MAXIMUM**: every subset-sum fibre over `r`-sets has size at most
`C(2^h − r % 2, r / 2)`. -/
theorem fibre_card_le {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    {r : ℕ} (hr : r ≤ 2 ^ h) (T₀ : Finset (Fin (2 ^ h) × Bool))
    (hT₀ : T₀.card = r) :
    (((Finset.univ : Finset (Fin (2 ^ h) × Bool)).powersetCard r).filter
        (fun T => subsetSum ζ T = subsetSum ζ T₀)).card
      ≤ (2 ^ h - r % 2).choose (r / 2) := by
  classical
  set u := ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs with hu
  set d := (doubles T₀).card with hd
  have hrud : r = u + 2 * d := by
    rw [hu, hd, ← hT₀]
    exact card_eq_core_add_doubles T₀
  have hcard := fibre_card hζ T₀
  rw [hT₀] at hcard
  rw [hcard, ← hu, ← hd]
  have hk : u = r % 2 + 2 * ((u - r % 2) / 2) := by omega
  have hdk : d = r / 2 - (u - r % 2) / 2 := by omega
  rw [hdk]
  have := choose_chain (2 ^ h) r hr ((u - r % 2) / 2) (by omega)
  calc (2 ^ h - u).choose (r / 2 - (u - r % 2) / 2)
      = (2 ^ h - (r % 2 + 2 * ((u - r % 2) / 2))).choose (r / 2 - (u - r % 2) / 2) := by
        rw [← hk]
    _ ≤ (2 ^ h - r % 2).choose (r / 2) := this

open Classical in
open Classical in
/-- **ATTAINMENT**: the maximal fibre value `C(2^h − r % 2, r / 2)` is attained —
by all-pairs sets (`r` even, the fibre of `0`) and singleton-plus-pairs sets (`r`
odd, the fibre of `ζ^{i₀}`). -/
theorem fibre_card_attained {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ (h + 1)))
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 2 ^ h) :
    ∃ T₀ : Finset (Fin (2 ^ h) × Bool), T₀.card = r ∧
      (((Finset.univ : Finset (Fin (2 ^ h) × Bool)).powersetCard r).filter
          (fun T => subsetSum ζ T = subsetSum ζ T₀)).card
        = (2 ^ h - r % 2).choose (r / 2) := by
  classical
  have hpos : (0 : ℕ) < 2 ^ h := by positivity
  rcases Nat.even_or_odd r with hev | hodd
  · -- r even: T₀ = D₀ × Bool for any D₀ of size r/2
    have hrmod : r % 2 = 0 := Nat.even_iff.mp hev
    obtain ⟨D₀, hD₀sub, hD₀card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 ^ h)))) (n := r / 2)
      (by rw [Finset.card_univ, Fintype.card_fin]
          exact le_trans (Nat.div_le_self r 2) hr)
    set T₀ := D₀ ×ˢ (Finset.univ : Finset Bool) with hT₀def
    have hmem : ∀ (i : Fin (2 ^ h)) (b : Bool), ((i, b) ∈ T₀ ↔ i ∈ D₀) := by
      intro i b
      rw [hT₀def, Finset.mem_product]
      simp
    have hcore : ∀ i, coreInt T₀ i = 0 := by
      intro i
      simp only [coreInt]
      by_cases hi : i ∈ D₀
      · rw [if_pos ((hmem i false).mpr hi), if_pos ((hmem i true).mpr hi)]
        ring
      · rw [if_neg (fun hc => hi ((hmem i false).mp hc)),
          if_neg (fun hc => hi ((hmem i true).mp hc))]
        ring
    have hdoub : doubles T₀ = D₀ := by
      ext i
      rw [doubles, Finset.mem_filter]
      constructor
      · rintro ⟨-, hf, -⟩
        exact (hmem i false).mp hf
      · intro hi
        exact ⟨Finset.mem_univ i, (hmem i false).mpr hi, (hmem i true).mpr hi⟩
    have hzero : ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcore i]
      rfl
    have hcardT : T₀.card = r := by
      have hdecomp := card_eq_core_add_doubles T₀
      rw [hzero, hdoub, hD₀card] at hdecomp
      omega
    refine ⟨T₀, hcardT, ?_⟩
    have hfib := fibre_card hζ T₀
    rw [hcardT] at hfib
    rw [hfib, hzero, hdoub, hD₀card, hrmod]
  · -- r odd: T₀ = {(i₀, false)} ∪ D₀ × Bool, i₀ ∉ D₀, |D₀| = (r−1)/2
    have hrmod : r % 2 = 1 := Nat.odd_iff.mp hodd
    set i₀ : Fin (2 ^ h) := ⟨0, hpos⟩ with hi₀def
    obtain ⟨D₀, hD₀sub, hD₀card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 ^ h))).erase i₀) (n := r / 2)
      (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
          Fintype.card_fin]
        exact Nat.le_sub_one_of_lt (lt_of_lt_of_le
          (Nat.div_lt_self hr1 (by norm_num)) hr))
    have hi₀D : i₀ ∉ D₀ := fun hc =>
      (Finset.mem_erase.mp (hD₀sub hc)).1 rfl
    set T₀ := insert (i₀, false) (D₀ ×ˢ (Finset.univ : Finset Bool)) with hT₀def
    have hmem : ∀ (i : Fin (2 ^ h)) (b : Bool),
        ((i, b) ∈ T₀ ↔ (i = i₀ ∧ b = false) ∨ i ∈ D₀) := by
      intro i b
      rw [hT₀def, Finset.mem_insert, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h1
      · rintro (⟨h1, h2⟩ | h1)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, Finset.mem_univ b⟩
    have hcore : ∀ i, coreInt T₀ i = if i = i₀ then 1 else 0 := by
      intro i
      by_cases hii : i = i₀
      · have hf : (i, false) ∈ T₀ := (hmem i false).mpr (Or.inl ⟨hii, rfl⟩)
        have ht : (i, true) ∉ T₀ := by
          intro hc
          rcases (hmem i true).mp hc with ⟨-, hb⟩ | hD
          · simp at hb
          · exact hi₀D (hii ▸ hD)
        simp only [coreInt]
        rw [if_pos hf, if_neg ht, if_pos hii]
        ring
      · by_cases hi : i ∈ D₀
        · have hf : (i, false) ∈ T₀ := (hmem i false).mpr (Or.inr hi)
          have ht : (i, true) ∈ T₀ := (hmem i true).mpr (Or.inr hi)
          simp only [coreInt]
          rw [if_pos hf, if_pos ht, if_neg hii]
          ring
        · have hf : (i, false) ∉ T₀ := by
            intro hc
            rcases (hmem i false).mp hc with ⟨h1, -⟩ | hD
            · exact hii h1
            · exact hi hD
          have ht : (i, true) ∉ T₀ := by
            intro hc
            rcases (hmem i true).mp hc with ⟨h1, -⟩ | hD
            · exact hii h1
            · exact hi hD
          simp only [coreInt]
          rw [if_neg hf, if_neg ht, if_neg hii]
          ring
    have hdoub : doubles T₀ = D₀ := by
      ext i
      rw [doubles, Finset.mem_filter]
      constructor
      · rintro ⟨-, hf, ht⟩
        rcases (hmem i true).mp ht with ⟨-, hb⟩ | hD
        · simp at hb
        · exact hD
      · intro hi
        exact ⟨Finset.mem_univ i, (hmem i false).mpr (Or.inr hi),
          (hmem i true).mpr (Or.inr hi)⟩
    have hsum : ∑ i : Fin (2 ^ h), (coreInt T₀ i).natAbs = 1 := by
      have hterm : ∀ i : Fin (2 ^ h),
          (coreInt T₀ i).natAbs = if i = i₀ then 1 else 0 := by
        intro i
        rw [hcore i]
        by_cases hii : i = i₀
        · rw [if_pos hii, if_pos hii]
          rfl
        · rw [if_neg hii, if_neg hii]
          rfl
      rw [Finset.sum_congr rfl fun i _ => hterm i,
        Finset.sum_ite_eq' Finset.univ i₀ (fun _ => 1)]
      simp
    have hcardT : T₀.card = r := by
      have hdecomp := card_eq_core_add_doubles T₀
      rw [hsum, hdoub, hD₀card] at hdecomp
      omega
    refine ⟨T₀, hcardT, ?_⟩
    have hfib := fibre_card hζ T₀
    rw [hcardT] at hfib
    rw [hfib, hsum, hdoub, hD₀card, hrmod]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.half_system_independent
#print axioms ProximityGap.PairRank.core_injective
#print axioms ProximityGap.PairRank.fibre_card
#print axioms ProximityGap.PairRank.fibre_card_le
#print axioms ProximityGap.PairRank.fibre_card_attained
