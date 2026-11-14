/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.BatchedFri.Security

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov

[BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

Using {https://eprint.iacr.org/2020/654}, version 20210703:203025.
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Extensions.Data.CodingTheory.Basic.Distance
import ArkLib.Extensions.Data.CodingTheory.Basic.LinearCode
import ArkLib.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Extensions.Data.CodingTheory.InterleavedCode
import ArkLib.Extensions.Data.CodingTheory.Prelims
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
import ArkLib.Extensions.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.Domain.CosetFftDomain.Defs
import ArkLib.Extensions.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Probability.Notation
import ArkLib.Extensions.OracleReduction.Composition.Sequential.Append
import ArkLib.Extensions.ProofSystem.BatchedFri.Spec.General
import ArkLib.Extensions.ProofSystem.Fri.Spec.General
import ArkLib.Extensions.ProofSystem.Fri.Spec.SingleRound
import ArkLib.Extensions.OracleReduction.Security.Basic
import ToMathlib.Control.OptionT
import ArkLib.ToMathlib.List.Basic
import ArkLib.ToMathlib.Finset.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Security of the Batched FRI protocol

We develop the security analysis of the Batched FRI oracle reduction following [BCIKS20]. The file
sets up the coset-evaluation machinery (`cosetEnum`, `cosetG`, `VDM` and its inverse `VDMInv`, the
`fin_equiv_coset` reindexing) used to reason about proximity over the smooth coset FFT evaluation
domains, towards completeness and soundness statements for the batched protocol.
-/

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
private noncomputable local instance : SampleableType 𝔽 := SampleableType.ofFintype 𝔽

variable (n : ℕ)
variable (g : 𝔽ˣ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {i : Fin (k + 1)}
variable {ω : SmoothCosetFftDomain n 𝔽}

attribute [instance high] Spec.QueryRound.instOracleInterfaceMessagePSpec

instance {F : Type} [Field F] {a : F} [inst : NeZero a] : Invertible a where
  invOf := a⁻¹
  invOf_mul_self := by field_simp [inst.out]
  mul_invOf_self := by field_simp [inst.out]

section Completeness

abbrev evalDomainSigma {n k : ℕ} (s : Fin (k + 1) → ℕ+)
  (ω : SmoothCosetFftDomain n 𝔽) (i : ℕ) :=
  ω.subdomain (∑ j' ∈ finRangeTo (k + 1) i, s j')

def cosetEnum (s₀ : evalDomainSigma s ω i) (k_le_n : ∑ j', (s j').1 ≤ n)
    (j : Fin (2 ^ (s i).1)) : evalDomainSigma s ω ↑i :=
  let r : {x | x ∈ ω.toFftDomain.subdomain (n - ↑(s i))} :=
    ⟨ω.toFftDomain.subdomain (n - (s i).1)
      ⟨j.1,
        by
          have s_i_lim : (s i).1 < n + 1 := by
            apply Nat.lt_succ_of_le
            exact (Finset.single_le_sum (fun j _ => Nat.zero_le (s j).1)
              (Finset.mem_univ i)).trans k_le_n
          rcases j with ⟨j, h⟩
          have : n - (n - (s i).1) = (s i).1 := by
            apply Nat.sub_sub_self
            exact Nat.le_of_lt_succ s_i_lim
          rw [this]
          convert h
      ⟩,
      CosetFftDomainClass.mem_self
    ⟩
  let x : (evalDomainSigma s ω ↑i).toFinset := ⟨
    s₀.1 * r.1,
    by {
      rw [CosetFftDomainClass.mem_toFinset_iff_mem]
      exact CosetFftDomainClass.mem_subdomain_of_mem_subdomain_of_mem_fft_subdomain (by {
        apply Nat.le_sub_of_add_le
        apply le_trans
          (b := ∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1)
          (c := n)
        · constructor
        · rw [←sum_finRangeTo_add_one]
          apply le_trans (b := ∑ j', (s j').1) <;> try omega
          apply Finset.sum_le_sum_of_subset
          simp
      })  (by {
        rcases s₀ with ⟨s₀, hs₀⟩
        simp only
        simp only [evalDomainSigma] at hs₀
        rw [CosetFftDomain.mem_toFinset_iff_mem] at hs₀
        exact hs₀
      }) r.2
    }
  ⟩
  ↑x

def cosetG (s₀ : evalDomainSigma s ω ↑i)
    : Finset (evalDomainSigma s ω ↑i) :=
  if k_le_n : ∑ j', (s j').1 ≤ n
  then
    (Finset.univ).image (cosetEnum n s s₀ k_le_n)
  else ∅

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM (s₀ : evalDomainSigma s ω ↑i) :
    Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then Matrix.vandermonde (fun j => (cosetEnum n s s₀ k_le_n j).1)
  else 1

def cosetEnum' (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n)
  (j : Fin (2 ^ (s i).1)) : cosetG n s s₀ :=
  ⟨
    cosetEnum n s s₀ k_le_n j,
    by simp only [cosetG, k_le_n, ↓reduceDIte]; exact mem_image_of_mem _ (mem_univ _)
  ⟩

noncomputable def fin_equiv_coset (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG n s s₀ } := by
  apply Equiv.ofBijective (cosetEnum' n s s₀ k_le_n)
  constructor
  · intro a b hab
    have hs₀ : (s₀ : 𝔽) ≠ 0 := by
      intro hzero
      have hmem := CosetFftDomainClass.mem_toFinset_iff_mem.mp s₀.property
      exact CosetFftDomainClass.not_zero_mem (by simpa only [hzero] using hmem)
    have hval := congrArg (fun x => (x.1 : 𝔽)) hab
    dsimp only [cosetEnum', cosetEnum] at hval
    have hfin := FftDomain.injective (mul_left_cancel₀ hs₀ hval)
    have hvals := congrArg (fun z => z.val) hfin
    exact Fin.ext hvals
  · intro y
    have hy := y.property
    simp only [cosetG, dif_pos k_le_n] at hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy
    exact ⟨a, Subtype.ext ha⟩

def invertibleDomain (s₀ : evalDomainSigma s ω ↑i) : Invertible (VDM n s s₀) := by
  haveI : NeZero (VDM n s s₀).det := by
    constructor
    unfold VDM
    split_ifs with cond
    · simp only [Matrix.det_vandermonde]
      rw [Finset.prod_ne_zero_iff]
      intros i' _
      rw [Finset.prod_ne_zero_iff]
      intros j' h'
      have : i' ≠ j' := by
        rename_i a
        simp_all only [mem_univ, mem_Ioi, ne_eq]
        obtain ⟨val, property⟩ := s₀
        simp_all only [finRangeTo]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [lt_self_iff_false]
      intros contra
      apply this
      rw [sub_eq_zero] at contra
      dsimp only [cosetEnum] at contra
      simp only [finRangeTo,
        mul_eq_mul_left_iff] at contra
      rcases contra with contra | contra
      · have h := FftDomain.injective contra
        simp only [Fin.mk.injEq] at h
        ext
        exact (symm h)
      · rcases s₀ with ⟨s₀, hs₀⟩
        subst contra
        simp only [Nat.succ_eq_add_one, finRangeTo.eq_1, Fin.ofNat_eq_cast, Fin.val_natCast,
          evalDomainSigma] at hs₀
        rw [CosetFftDomainClass.mem_toFinset_iff_mem] at hs₀
        have hs₀ := CosetFftDomainClass.not_zero_mem hs₀
        simp at hs₀
    · simp
  apply @Matrix.invertibleOfDetInvertible

noncomputable def VDMInv (s₀ : evalDomainSigma s ω ↑i)
  (k_le_n : ∑ j', (s j').1 ≤ n) :
  Matrix (Fin (2 ^ (s i).1)) (cosetG n s s₀) 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset n s s₀ k_le_n)
  (invertibleDomain n s s₀).invOf

lemma g_elem_zpower_iff_exists_nat {G : Type} [Group G] [Finite G] {gen g : G} :
    g ∈ Subgroup.zpowers gen ↔ ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
  have := isOfFinOrder_of_finite gen
  refine ⟨fun h ↦ ?p₁, ?p₂⟩
  · obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h
    let k' := k % orderOf gen
    have pow_pos : 0 ≤ k' := by apply Int.emod_nonneg; simp [*]
    obtain ⟨n, h'⟩ : ∃ n : ℕ, n = k' := by rcases k' with k' | k' <;> [(use k'; grind); aesop]
    use n
    have : gen ^ n = gen ^ k := by have := zpow_mod_orderOf gen k; grind [zpow_natCast]
    have : n < orderOf gen := by zify; rw [h']; apply Int.emod_lt; simp [isOfFinOrder_of_finite gen]
    grind
  · grind [Subgroup.npow_mem_zpowers]

open Matrix in
noncomputable def f_succ'
  (f : evalDomainSigma s ω ↑i → 𝔽)
  (z : 𝔽) (k_le_n : ∑ j', ↑(s j') ≤ n)
  (s₀' : evalDomainSigma s ω (↑i + 1)) : 𝔽 :=
  have :
    ∃ s₀ : (ω.subdomain (∑ j' ∈ finRangeTo _ (i.1), (s j').1)).toFinset,
      s₀.1 ^ (2 ^ (s i).1) = s₀'.1 := by
    rcases s₀' with ⟨s₀', hs₀'⟩
    simp only [Fin.val_natCast]
    simp only [evalDomainSigma] at hs₀'
    rw [CosetFftDomain.mem_toFinset_iff_mem] at hs₀'
    rw [CosetFftDomainClass.mem_subdomain_of_eq_vals
      (ω := ω)
      (j := (∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1))
      (by {
        rw [←sum_finRangeTo_add_one]
        rfl
    })] at hs₀'
    obtain ⟨y, h1, h2⟩ := CosetFftDomainClass.root_exists (ω := ω)
      (i := (∑ j' ∈ finRangeTo (k + 1) ↑i, ↑(s j'))) (j := (s i).1) hs₀'
    exists ⟨y, by {
      rw [CosetFftDomain.mem_toFinset_iff_mem]
      exact h1
    }⟩
  let s₀ := Classical.choose this
  (pows z _ *ᵥ VDMInv n s s₀ k_le_n *ᵥ Finset.restrict (cosetG n s s₀) f) ()

private lemma rs_code_mem_of_card_le_degree
    {ι : Type} [Fintype ι] {F : Type} [Field F]
    {α : ι ↪ F} {deg : ℕ} (hcard : Fintype.card ι ≤ deg) (f : ι → F) :
    f ∈ ReedSolomon.code α deg := by
  letI : DecidableEq ι := Classical.decEq ι
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (Lagrange.interpolate Finset.univ α f) ?_ ?_
  · have hdeg_card : (Lagrange.interpolate (Finset.univ : Finset ι) α f).degree <
        (Fintype.card ι : WithBot ℕ) := by
      simpa using
        (Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset ι)) (v := α) (r := f)
          (by intro x _ y _ hxy; exact α.injective hxy))
    exact lt_of_lt_of_le hdeg_card (by exact_mod_cast hcard)
  · intro x
    exact (Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset ι))
      (v := α) (r := f)
      (by intro x _ y _ hxy; exact α.injective hxy)
      (Finset.mem_univ x)).symm

omit [Fintype 𝔽] in
/-- Folding stays in the next Reed–Solomon code — **full-rate form only**.

  This is stated with the degree bound `2 ^ (n - ∑_{j < i} s j)` on the `i`-th evaluation domain,
  which has exactly that many points, so both codes are the whole word space and the statement holds
  for *every* word (it is proved by Lagrange interpolation via `rs_code_mem_of_card_le_degree`,
  without using `f`'s membership or the folding formula).  It is therefore **not** Claim 8.1 of
  [BCIKS20]: the intended statement uses the round-`i` input degree
  `2 ^ (∑ j, s j - ∑_{j < i} s j) * d` (see `friDegree` and `Fri.Spec.Witness`) and needs the actual
  folding argument, which remains open here (audit finding L70). -/
lemma fri_round_consistency_completeness
    {f : ReedSolomon.code
    (⟨fun x => x, by simp⟩ : evalDomainSigma s ω i ↪ 𝔽)
    (2 ^ (n - (∑ j' ∈ finRangeTo _ i, (s j' : ℕ))))}
  {z : 𝔽}
  (k_le_n : ∑ j', ↑(s j') ≤ n)
  :
  f_succ' n s f.val z k_le_n ∈
    (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : (evalDomainSigma s ω (i.1 + 1)).toFinset ↪ 𝔽)
      (2 ^ (n - (∑ j' ∈ finRangeTo _ (i.1 + 1), (s j' : ℕ))))
    ).carrier
  := by
  refine rs_code_mem_of_card_le_degree ?_ _
  rw [Fintype.card_coe]
  refine le_of_eq ?_
  simp only [evalDomainSigma, Domain.CosetFftDomainClass.card_toFinset]
  exact Fintype.card_fin _

end Completeness

section Soundness

variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

/-- The Reed–Solomon degree bound tested by Batched FRI: the batched input words are evaluations of
witness polynomials of degree `< 2 ^ (∑ i, s i) * d` (`BatchedFri.Spec.Witness`,
`BatchedFri.Spec.batchCode`), and `domain_size_cond` says exactly `friDegree s d ≤ 2 ^ n`.

AUDIT REPAIR (2026-10-28, L70): the Claim 8.2 / 8.3 residuals and adapters in this file and its
companions (`QueryRoundProbability`, `QueryRoundSoundness`, `QueryRoundRSAffineLineSoundness`,
`QueryRoundRSCurveSoundness`, `QuerySoundnessSmallField`) used to test the Reed–Solomon code of
degree `2 ^ n` on the `2 ^ n`-point domain `ω.subdomain 0` (resp. `ω`).  That code is the whole word
space (`reedSolomon_code_subdomainZero_two_pow_eq_top`), so every `Code.jointAgreement` conclusion
held for every stack, the rate and square-root rate were `1`, every strict radius premise
`δ < 1 - √ρ` was unsatisfiable, and `fri_soundness_canonicalIndependent`'s success threshold
`εC + α ^ l` was at least `1`.  They now test the code of degree `friDegree s d`; below the domain
size that code is proper (`sqrtRate_friDegree_lt_one`) and the Claim 8.2 target is no longer a
tautology (`exists_not_fri_query_soundness`). -/
abbrev friDegree {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) : ℕ :=
  2 ^ (∑ i, (s i : ℕ)) * d

/-- The batched FRI degree bound is positive (needed by the BCIKS20 correlated-agreement API). -/
instance friDegree_neZero {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) : NeZero (friDegree s d) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.two_pow_pos _) d.pos)⟩

-- In the soundness section the protocol shape `s`, `d` is inferred from the code degree
-- `friDegree s d` (or from `domain_size_cond`) appearing in the hypotheses.
variable {s d}

omit [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽] in
/-- A Reed–Solomon code whose degree bound is at least its block length is the whole word space. -/
theorem reedSolomon_code_eq_top_of_card_le {ι F : Type} [Fintype ι] [Field F] {α : ι ↪ F}
    {deg : ℕ} (hcard : Fintype.card ι ≤ deg) : ReedSolomon.code α deg = ⊤ :=
  eq_top_iff.mpr fun f _ => rs_code_mem_of_card_le_degree hcard f

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- The round-zero Batched FRI domain has `2 ^ n` points. -/
theorem card_subdomainZero : Fintype.card (ω.subdomain 0) = 2 ^ n := by
  rw [Fintype.card_coe]
  simp

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- **The historical full-rate target (audit finding L70).**  On the `2 ^ n`-point domain
`ω.subdomain 0`, the Reed–Solomon code of degree `2 ^ n` is the whole word space, so a Claim 8.2 /
8.3 statement about that code is a tautology.  This is why the residuals below use the batched FRI
degree `friDegree s d`. -/
theorem reedSolomon_code_subdomainZero_two_pow_eq_top :
    ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n : ℕ) = ⊤ :=
  reedSolomon_code_eq_top_of_card_le (card_subdomainZero n).le

omit [Nontrivial 𝔽] in
/-- The FFT domain consists of distinct **nonzero** field elements, so it is strictly smaller than
the field.  Hence a small-field hypothesis `Fintype.card 𝔽 ≤ Fintype.card (ω.subdomain 0)` can never
hold (audit finding L70). -/
theorem card_subdomainZero_lt_card_field :
    Fintype.card (ω.subdomain 0) < Fintype.card 𝔽 := by
  rw [Fintype.card_coe]
  have hsub : CosetFftDomainClass.toFinset (ω.subdomain 0) ⊆ Finset.univ.erase (0 : 𝔽) := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    rw [CosetFftDomainClass.mem_toFinset_iff_mem] at hx
    exact CosetFftDomainClass.not_zero_mem hx
  calc (CosetFftDomainClass.toFinset (ω.subdomain 0)).card
      ≤ (Finset.univ.erase (0 : 𝔽)).card := Finset.card_le_card hsub
    _ < Finset.univ.card := Finset.card_erase_lt_of_mem (Finset.mem_univ 0)
    _ = Fintype.card 𝔽 := Finset.card_univ

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- **Nonempty low-rate regime.**  When the batched FRI degree bound is strictly below the domain
size, the square-root rate of the input code is `< 1`; hence `0 < 1 - √ρ` and the strict radius
premises `δ < 1 - √ρ` of the correlated-agreement front doors are satisfiable (e.g. by `δ = 0`),
unlike under the historical degree `2 ^ n`, where `√ρ = 1`. -/
theorem sqrtRate_friDegree_lt_one (hlt : friDegree s d < 2 ^ n) :
    ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) < 1 := by
  have hcard := card_subdomainZero n (ω := ω)
  have hpos : (0 : ℚ≥0) < 2 ^ n := by positivity
  have hrate : LinearCode.rate
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)) < 1 := by
    rw [ReedSolomon.rateOfLinearCode_eq_min_div, hcard, min_eq_left hlt.le]
    rw [div_lt_one (by exact_mod_cast hpos)]
    exact_mod_cast hlt
  unfold ReedSolomon.sqrtRate
  calc NNReal.sqrt (LinearCode.rate
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)) : ℝ≥0)
      < NNReal.sqrt 1 := NNReal.sqrt_lt_sqrt.mpr (by exact_mod_cast hrate)
    _ = 1 := NNReal.sqrt_one

omit [DecidableEq 𝔽] [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Below the block length a Reed–Solomon code is proper: some word lies outside it. -/
theorem exists_not_mem_reedSolomon_of_lt_card {ι : Type} [Fintype ι] {α : ι ↪ 𝔽} {deg : ℕ}
    (hlt : deg < Fintype.card ι) : ∃ w : ι → 𝔽, w ∉ ReedSolomon.code α deg := by
  by_contra h
  have htop : ReedSolomon.code α deg = ⊤ :=
    eq_top_iff.mpr fun w _ => Classical.byContradiction fun hw => h ⟨w, hw⟩
  have hdim := ReedSolomon.dim_eq_min_deg_card (α := α) (n := deg)
  rw [htop, min_eq_left hlt.le] at hdim
  have : LinearCode.dim (⊤ : Submodule 𝔽 (ι → 𝔽)) = Fintype.card ι := by
    unfold LinearCode.dim
    simp
  omega

omit [NonBinaryField 𝔽] [Fintype 𝔽] [Nontrivial 𝔽] in
/-- At radius `0` (exact agreement on all coordinates), `Code.jointAgreement` forces every row of
the stack into the code; so a stack of copies of a non-codeword fails it. -/
theorem not_jointAgreement_zero_of_not_mem {ι κ : Type} [Fintype ι] [Nonempty κ]
    {C : Set (ι → 𝔽)} {w : ι → 𝔽} (hw : w ∉ C) :
    ¬ Code.jointAgreement (F := 𝔽) (κ := κ) (ι := ι) (C := C) (δ := 0) (W := fun _ => w) := by
  classical
  rintro ⟨S, hS, v, hv⟩
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hcard : Fintype.card ι ≤ S.card := by
    have : ((Fintype.card ι : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by simpa using hS
    exact_mod_cast this
  have hSuniv : S = Finset.univ :=
    Finset.eq_univ_of_card S (le_antisymm (Finset.card_le_univ S) hcard)
  have hvw : v i = w := by
    funext j
    have hj : j ∈ S := hSuniv ▸ Finset.mem_univ j
    have := (hv i).2 hj
    simpa using this
  exact hw (hvw ▸ (hv i).1)

/-- The batched affine space of [BCIKS20] §8 spanned by a stack `f 0, …, f t`:
`Fₛ f = f 0 + span 𝔽 {f 1, …, f t}`, the translate by `f 0` of the **linear** span of the
directions `f 1, …, f t`.  Equivalently (`mem_Fₛ_iff`) it is the family
`{g | ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i}` of all combinations whose coefficient of
`f 0` is fixed to `1`; for `t = 0` it is `{f 0}` (`coe_Fₛ_zero`) and for `t = 1` it is the affine
line `{f 0 + z • f 1 | z ∈ 𝔽}` (`mem_Fₛ_one_iff`).

It is definitionally `Affine.affineSubspaceAtOrigin (f 0) (Fin.tail f)`, the subspace sampled
uniformly by `ProximityGap.δ_ε_correlatedAgreementAffineSpaces`, so `correlated_agreement_density`
is exactly that sampling probability (`correlated_agreement_density_Fₛ_eq_prob`), and for `t = 1`
it is the probability over the line `f 0 + z • f 1` sampled by the affine-line adapters
(`correlated_agreement_density_Fₛ_eq_prob_affineLine`).

AUDIT REPAIR (2026-10-28, L101): this was previously defined as
`f 0 +ᵥ affineSpan 𝔽 (Finset.univ.image (f ∘ Fin.succ))`, the translate of the *affine hull* of
the directions, whose coefficients must sum to one.  That carrier is the single point
`{f 0 + f 1}` for `t = 1` and is empty for `t = 0`, so it was not the documented family and did not
match the line `f 0 + z • f 1` sampled by the affine-line correlated-agreement adapters. -/
def Fₛ {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) : AffineSubspace 𝔽 (ι → 𝔽) :=
  Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f)

noncomputable def correlated_agreement_density {ι : Type} [Fintype ι]
  [Fintype 𝔽]
  (Fₛ : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) : ℝ :=
  haveI : Fintype Fₛ.carrier := Set.Finite.fintype (Set.toFinite _)
  haveI : Fintype V.carrier := Set.Finite.fintype (Set.toFinite _)
  let Fc := Fₛ.carrier.toFinset
  let Vc := V.carrier.toFinset
  (Fc ∩ Vc).card / Fc.card

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- `Fₛ f` is the documented family of combinations of `f 0, …, f t` whose coefficient of `f 0`
is `1` (the direction coefficients are arbitrary). -/
theorem mem_Fₛ_iff {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) (g : ι → 𝔽) :
    g ∈ Fₛ f ↔ ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i := by
  rw [Fₛ, Affine.mem_affineSubspaceFrom_iff]
  constructor
  · rintro ⟨β, rfl⟩
    refine ⟨Fin.cons 1 β, rfl, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [Fin.tail]
  · rintro ⟨x, hx0, rfl⟩
    refine ⟨Fin.tail x, ?_⟩
    rw [Fin.sum_univ_succ, hx0, one_smul]
    simp [Fin.tail]

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Zero-direction case: with no directions, `Fₛ f` is the single point `f 0`. -/
theorem mem_Fₛ_zero_iff {ι : Type} [Fintype ι] (f : Fin 1 → (ι → 𝔽)) (g : ι → 𝔽) :
    g ∈ Fₛ f ↔ g = f 0 := by
  rw [mem_Fₛ_iff]
  constructor
  · rintro ⟨x, hx0, rfl⟩
    simp [hx0]
  · rintro rfl
    exact ⟨fun _ => 1, rfl, by simp⟩

omit [Nontrivial 𝔽] in
/-- Zero-direction case as a set: `Fₛ f = {f 0}` (in particular it is nonempty). -/
theorem coe_Fₛ_zero {ι : Type} [Fintype ι] (f : Fin 1 → (ι → 𝔽)) :
    (Fₛ f : Set (ι → 𝔽)) = {f 0} := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_singleton_iff]
  exact mem_Fₛ_zero_iff f g

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- One-direction case: `Fₛ f` is the whole affine line `{f 0 + z • f 1 | z ∈ 𝔽}`. -/
theorem mem_Fₛ_one_iff {ι : Type} [Fintype ι] (f : Fin 2 → (ι → 𝔽)) (g : ι → 𝔽) :
    g ∈ Fₛ f ↔ ∃ z : 𝔽, g = f 0 + z • f 1 := by
  rw [mem_Fₛ_iff]
  constructor
  · rintro ⟨x, hx0, rfl⟩
    refine ⟨x 1, ?_⟩
    simp [Fin.sum_univ_two, hx0]
  · rintro ⟨z, rfl⟩
    refine ⟨![1, z], rfl, ?_⟩
    simp [Fin.sum_univ_two]

omit [Nontrivial 𝔽] in
/-- **Density = affine-space sampling law.**  `correlated_agreement_density (Fₛ f) V` is the
probability that a uniformly random point of `Fₛ f = Affine.affineSubspaceAtOrigin (f 0)
(Fin.tail f)` lies in `V`, i.e. the sampling law of
`ProximityGap.δ_ε_correlatedAgreementAffineSpaces` (at exact membership). -/
theorem correlated_agreement_density_Fₛ_eq_prob {ι : Type} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (f : Fin t.succ → (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) :
    correlated_agreement_density (Fₛ f) V =
      (Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f))}[
        y.1 ∈ V]).toReal := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  rw [ENNReal.toReal_div]
  simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast]
  unfold correlated_agreement_density
  simp only
  have hS : ∀ I : Fintype (Fₛ f).carrier, (@Set.toFinset _ (Fₛ f).carrier I).card =
      Fintype.card ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f)) := by
    intro I
    rw [Set.toFinset_card]
    exact Fintype.card_congr' rfl
  have hSV : ∀ (I : Fintype (Fₛ f).carrier) (J : Fintype V.carrier),
      (@Set.toFinset _ (Fₛ f).carrier I ∩ @Set.toFinset _ V.carrier J).card =
      (Finset.univ.filter
        (fun y : ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f)) =>
          y.1 ∈ V)).card := by
    intro I J
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext g
    simp only [Finset.mem_inter, Set.mem_toFinset, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hg, hgV⟩
      exact ⟨⟨g, hg⟩, hgV, rfl⟩
    · rintro ⟨y, hyV, rfl⟩
      exact ⟨y.2, hyV⟩
  rw [hS, hSV]

/-- **Density = affine-line sampling law.**  For a two-row stack,
`correlated_agreement_density (Fₛ f) V` is the probability, over a uniformly random `z ∈ 𝔽`, that
the sampled line point `f 0 + z • f 1` lies in `V` — the sampling law of the affine-line
correlated-agreement adapters (at exact membership).  This holds also when `f 1 = 0`, where both
sides are `1` or `0` according to whether `f 0 ∈ V`. -/
theorem correlated_agreement_density_Fₛ_eq_prob_affineLine {ι : Type} [Fintype ι]
    (f : Fin 2 → (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) :
    correlated_agreement_density (Fₛ f) V =
      (Pr_{let z ← $ᵖ 𝔽}[f 0 + z • f 1 ∈ V]).toReal := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  rw [ENNReal.toReal_div]
  simp only [ENNReal.coe_natCast, ENNReal.toReal_natCast]
  unfold correlated_agreement_density
  simp only
  -- the carrier of `Fₛ f` is the image of the sampled line `z ↦ f 0 + z • f 1`
  have hFc : ∀ I : Fintype (Fₛ f).carrier, @Set.toFinset _ (Fₛ f).carrier I =
      Finset.univ.image (fun z : 𝔽 => f 0 + z • f 1) := by
    intro I
    ext g
    rw [Set.mem_toFinset]
    change g ∈ Fₛ f ↔ _
    rw [mem_Fₛ_one_iff]
    simp [eq_comm]
  have hVc : ∀ J : Fintype V.carrier, @Set.toFinset _ V.carrier J =
      Finset.univ.filter (fun g => g ∈ V) := by
    intro J
    ext g
    rw [Set.mem_toFinset]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [hFc, hVc]
  have hinter : Finset.univ.image (fun z : 𝔽 => f 0 + z • f 1) ∩
      Finset.univ.filter (fun g => g ∈ V) =
      (Finset.univ.filter (fun z : 𝔽 => f 0 + z • f 1 ∈ V)).image
        (fun z : 𝔽 => f 0 + z • f 1) := by
    ext g
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨z, rfl⟩, hz⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, rfl⟩, hz⟩
  rw [hinter]
  have hcard𝔽 : (Fintype.card 𝔽 : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hf1 : f 1 = 0
  · -- zero direction: the line is the single point `f 0`
    have himg : ∀ S : Finset 𝔽, S.Nonempty →
        S.image (fun z : 𝔽 => f 0 + z • f 1) = {f 0} := by
      intro S hS
      rw [hf1]
      simp only [smul_zero, add_zero]
      exact Finset.image_const hS _
    rw [himg Finset.univ Finset.univ_nonempty]
    by_cases h0 : f 0 ∈ V
    · have hfilt : Finset.univ.filter (fun z : 𝔽 => f 0 + z • f 1 ∈ V) = Finset.univ := by
        ext z; simp [hf1, h0]
      rw [hfilt, himg Finset.univ Finset.univ_nonempty, Finset.card_univ, div_self hcard𝔽]
      simp
    · have hfilt : Finset.univ.filter (fun z : 𝔽 => f 0 + z • f 1 ∈ V) = ∅ := by
        ext z; simp [hf1, h0]
      rw [hfilt]
      simp
  · -- nonzero direction: `z ↦ f 0 + z • f 1` is injective
    have hinj : Function.Injective (fun z : 𝔽 => f 0 + z • f 1) := by
      intro z z' h
      simp only [add_right_inj] at h
      exact smul_left_injective 𝔽 hf1 h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj,
      Finset.card_univ]

open Polynomial

/-! ### Query-round acceptance analysis (Claim 8.2 combinatorial core)

The mathematical heart of the FRI query-round soundness analysis (Claim 8.2 of [BCIKS20])
is a purely combinatorial fact, independent of the oracle-reduction plumbing:

If a verifier makes `t` *independent uniform* queries into a domain `ι` of size `N`, and the
set `G ⊆ ι` of "good" positions (positions on which a query fails to detect the corruption)
has density `|G| / N ≤ 1 - δ`, then the probability that *all* `t` queries land in `G`
(the soundness-failure / accept-the-corrupted-word event) is at most `(1 - δ) ^ t`.

We formalise the failure probability as the ratio of the number of accepting query tuples
(`|G| ^ t`) to all query tuples (`N ^ t`), which equals `(|G| / N) ^ t ≤ (1 - δ) ^ t`.
These are real proved theorems (no `sorry`, no new axioms), and they are wired into the
`FriQuerySoundnessParts.query_round_acceptance_bound` frontier below via
`queryRoundAcceptanceBound`. -/

namespace QueryRound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The number of length-`t` query tuples landing entirely in a set `G` is `|G| ^ t`.
This counts the accepting (corruption-missing) query transcripts. -/
theorem card_allQueriesIn (G : Finset ι) (t : ℕ) :
    (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card = G.card ^ t := by
  classical
  have hpi : (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G))
      = Fintype.piFinset (fun _ : Fin t => G) := by
    ext q
    simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  simp

omit [DecidableEq ι] in
/-- **Per-round acceptance probability bound.** If the good set `G` has density at most
`1 - δ`, then a single uniform query lands in `G` with probability `|G| / N ≤ 1 - δ`. -/
theorem singleQuery_acceptance_le
    (G : Finset ι) (δ : ℝ≥0)
    (hN : 0 < (Fintype.card ι))
    (h_density : (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι)) :
    (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ := by
  rw [div_le_iff₀ (by exact_mod_cast hN)]
  exact h_density

/-- **Query-round acceptance bound (product form).** Over `t` independent uniform queries,
the probability that all of them land in the good set `G` (acceptance / soundness-failure
event) is `|G| ^ t / N ^ t = (|G| / N) ^ t ≤ (1 - δ) ^ t`.

This is the combinatorial core of Claim 8.2: a `δ`-far word is accepted by the `t`-query
round with probability at most `(1 - δ) ^ t`. -/
theorem queryRound_acceptance_le
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (hN : 0 < (Fintype.card ι))
    (h_density : (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι)) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t := by
  rw [card_allQueriesIn G t]
  push_cast
  rw [← div_pow]
  have hbase : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ :=
    singleQuery_acceptance_le G δ hN h_density
  exact pow_le_pow_left₀ (by positivity) hbase t

/-- **Query-round acceptance bound (density-ratio form).**  This is the same combinatorial
query-round bound as `queryRound_acceptance_le`, but with the natural density hypothesis
`|G| / N ≤ 1 - δ` exposed directly. -/
theorem queryRound_acceptance_le_of_density
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t := by
  rw [card_allQueriesIn G t]
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ (by positivity) h_density t

/-- Geometric amplification: when `0 < δ ≤ 1` the per-round acceptance bound `(1 - δ) ^ t`
is antitone in the number of query repetitions `t`, so the query phase drives the
soundness error to zero geometrically. -/
theorem queryRound_acceptance_antitone
    (δ : ℝ≥0) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (1 - δ) ^ t₂ ≤ (1 - δ) ^ t₁ :=
  pow_le_pow_of_le_one (by positivity) tsub_le_self h

end QueryRound

/-- The fully discharged query-round acceptance proposition used to instantiate the
`FriQuerySoundnessParts.query_round_acceptance_bound` frontier field. It packages the proved
combinatorial bound `|G| ^ t / N ^ t ≤ (1 - δ) ^ t` for the good (corruption-missing) set `G`
of density at most `1 - δ`. -/
def queryRoundAcceptanceBound
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) : Prop :=
  0 < (Fintype.card ι) →
    (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι) →
      ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
          / (Fintype.card ι) ^ t
        ≤ (1 - δ) ^ t

/-- `queryRoundAcceptanceBound` is a proved theorem: the query-round acceptance probability
is bounded by `(1 - δ) ^ t`. This discharges the query-round ingredient of Claim 8.2. -/
theorem queryRoundAcceptanceBound_holds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) :
    queryRoundAcceptanceBound G δ t := by
  intro hN h_density
  exact QueryRound.queryRound_acceptance_le G δ t hN h_density

/-- Public density-ratio front door for the proved query-round acceptance inequality.

This is useful when downstream proximity arguments have already produced the normalized density
bound `|G| / N ≤ 1 - δ`, avoiding a round trip through the multiplicative card form. -/
theorem queryRoundAcceptanceBound_of_density
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t :=
  QueryRound.queryRound_acceptance_le_of_density G δ t h_density

/-- Normalized-density variant of the proved query-round acceptance proposition.  This packages
the same count of accepting query tuples, but exposes the hypothesis in the normalized form that
proximity arguments usually produce. -/
def queryRoundDensityBound
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) : Prop :=
  (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ →
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t

/-- `queryRoundDensityBound` is proved by the density-ratio query-round theorem. -/
theorem queryRoundDensityBound_holds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) :
    queryRoundDensityBound G δ t := by
  intro h_density
  exact queryRoundAcceptanceBound_of_density G δ t h_density

/-- The current independent-coefficient batching round materializes its combined virtual
oracle before appending native FRI. This is a structural seam; probabilistic composition
and coding-theoretic hypotheses remain explicit in the wrappers below. -/
def batchedFRICanonicalSeam (l batchSize : ℕ) : Prop :=
  (BatchedFri.Spec.batchedFRIreduction
    (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l batchSize
    (CoreDefinitions.AffineSpaceGenerator 𝔽 batchSize)).verifier =
  OracleVerifier.append
    (BatchedFri.Spec.BatchingRound.batchOracleReduction
      (F := 𝔽) (n := n) (ω := ω) s d batchSize
      (CoreDefinitions.AffineSpaceGenerator 𝔽 batchSize)).verifier
    (Fri.Spec.reduction (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier

/-- The native batching-plus-FRI construction exposes its actual composition seam. -/
theorem batchedFRICanonicalSeam_holds (l batchSize : ℕ) :
    batchedFRICanonicalSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l batchSize := by
  rfl

noncomputable def oracleImpl
    (l : ℕ) (z : Fin (k + 1) → 𝔽) (f : (ω.subdomain 0) → 𝔽) :
  QueryImpl
    ([]ₒ + ([Spec.FinalOracleStatement s ω]ₒ + [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec (ω := ω) l).Message]ₒ) := by
  intro q
  rcases q with i | q
  · exact PEmpty.elim i
  · rcases q with q | q
    · rcases q with ⟨i, dom⟩
      let f0 := Lagrange.interpolate Finset.univ (fun v => v.1) f
      let chals : List (Fin (k + 1) × 𝔽) :=
        ((List.finRange (k + 1)).map fun i => (i, z i)).take i.1
      let fi : 𝔽[X] := List.foldl (fun f (i, α) => FoldingPolynomial.polyFold f (s i) α) f0 chals
      let st : Spec.FinalOracleStatement (F := 𝔽) s ω i :=
        if h : i.1 = k + 1 then
          cast (by simp [Spec.FinalOracleStatement, h]; rfl)
            (⟨fi.toImpl, CompPoly.CPolynomial.Raw.isCanonical_toImpl fi⟩ :
              CompPoly.CPolynomial 𝔽)
        else
          cast
            (by {
              simp [Spec.FinalOracleStatement, h]
              rfl
            })
            (fun x : ω.subdomain (∑ j' ∈ finRangeTo _ i.1, s j') => fi.eval x.1)
      exact pure <| (Spec.finalOracleStatementInterface s (ω := ω) i).answer st dom
    · rcases q with ⟨i, t⟩
      exact liftM <|
        cast
          (β := OracleQuery
            [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ
            (([]ₒ +
                ([Spec.FinalOracleStatement s (ω := ω)]ₒ +
                  [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ)).Range
              (Sum.inr (Sum.inr ⟨i, t⟩))))
          (by rfl)
          (query (spec := [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ) ⟨i, t⟩)

instance {l : ℕ} : ∀ q, Inhabited ((([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ)).Range q) := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

instance {l : ℕ} : ∀ q, Fintype ((([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ)).Range q) := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

open ENNReal in
noncomputable def εC
    (𝔽 : Type) [Fintype 𝔽] (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+) (m : ℕ) (ρ_sqrt : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / ((2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽))
      + (∑ i, 2 ^ (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)

private abbrev fullChallengeProtocol (t l : ℕ) (ω : SmoothCosetFftDomain n 𝔽) :=
  (BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
    (Spec.pSpecFold k (ω := ω) s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec l (ω := ω))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Inhabited
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge j) := by
    rintro ⟨j, hj⟩
    have hz : j = 0 := Fin.eq_zero j
    subst j
    exact ⟨fun _ => 0⟩
  letI : ∀ j, Inhabited ((Spec.pSpecFold k (ω := ω) s).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.pSpecFold k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Inhabited
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).dir)
    (β₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Type)
    (β₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).Type)
    (fun i h =>
      inferInstanceAs (Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Fintype
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Fintype ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Fintype
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).dir)
    (β₁ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Type)
    (β₂ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec l (ω := ω)).Type)
    (fun i h =>
      inferInstanceAs (Fintype ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Fintype
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec l (ω := ω)).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Inhabited ((([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ)).Range q) := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Inhabited
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l ω).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Fintype ((([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ)).Range q) := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Fintype
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l (ω := ω)).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Inhabited
      (((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
          (Spec.pSpecFold k (ω := ω) s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Inhabited
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Fintype
      (((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Fintype
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Inhabited ((([((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)).Range q) := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Fintype ((([((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)).Range q) := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Inhabited ((([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)).Range q) := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Inhabited
              (([((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} : ∀ q, Fintype ((([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)).Range q) := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Fintype
              (([((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

open ENNReal in
private noncomputable local instance {t l : ℕ} :
    OracleSpec.UniformAnswerMeasure
      ([]ₒ + [(fullChallengeProtocol n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ) :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

/-- Corresponds to Claim 8.2 of [BCIKS20] (the query-phase soundness of batched FRI).

  **Statement-bug repair / named residual.** This declaration previously had the *degenerate*
  conclusion `True` (proved by `trivial`), so it did not state Claim 8.2 at all and silently
  discarded its hypotheses `h_agreement` and `m_ge_3`. A `True` conclusion is strictly weaker than
  an honest named residual: it asserts nothing. Following the same treatment already applied to the
  sibling Claim 8.3 (`fri_soundness_canonicalIndependent`, which is a `def … : Prop` named-residual specification rather
  than an unfinished theorem body), this is converted into a `def … : Prop` that records the actual
  mathematical content of Claim 8.2 as a precisely-named residual `Prop`. No degenerate `True`
  conclusion remains.

  **Content.** The batched input functions `f : Fin t.succ → (ω.subdomain 0 → 𝔽)` are assumed to
  have correlated-agreement density at most `α` against the Reed–Solomon code of degree
  `friDegree s d = 2 ^ (∑ i, s i) * d` (the batched FRI input degree) on the evaluation domain
  `ω.subdomain 0` (hypothesis `h_agreement`: `correlated_agreement_density (Fₛ f) (RS code) ≤ α`),
  and the repetition/soundness parameter satisfies `m ≥ 3` (`m_ge_3`). The query
  phase then enforces *joint agreement* of the batch with the code on a `(1 - α)`-fraction of the
  domain: `Code.jointAgreement` at relative distance `δ = 1 - α`. This is the per-query consistency
  consequence underlying the end-to-end Claim 8.3, phrased over the same `Code.jointAgreement`
  predicate used by `fri_soundness_canonicalIndependent`.

  AUDIT REPAIR (2026-10-28, L70): the code used to have degree `2 ^ n` on the `2 ^ n`-point domain,
  i.e. it was the whole word space (`reedSolomon_code_subdomainZero_two_pow_eq_top`), which made
  this `Prop` true for every stack.  With the input degree `friDegree s d` it is a genuine target:
  below the domain size it fails for some stack (`exists_not_fri_query_soundness`).

  This is kept as a `Prop` (a named residual) rather than a closed theorem because the in-tree
  query-round acceptance bounds still have to be connected to the protocol-specific
  correlated-agreement/proximity trigger and the `OracleReduction.run` plumbing.  The proved
  query-round counting and density bounds feed the split frontier below; what remains is deriving
  the required `Code.jointAgreement` witness from the Batched FRI transcript semantics, then lifting
  it through the sibling Claim 8.3 residual `fri_soundness_canonicalIndependent`. -/
def fri_query_soundness
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  : Prop :=
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω.subdomain 0)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (δ := 1 - α)
        (W := f)

omit [Nontrivial 𝔽] in
/-- Complete-codeword extreme of the correlated-agreement bridge for Claim 8.2.

If every word in the queried stack is already a Reed-Solomon codeword on `ω.subdomain 0`, then
the `Code.jointAgreement` conclusion in `fri_query_soundness` holds on the full coordinate set.
The general correlated-agreement-to-joint-agreement bridge remains the open case. -/
theorem fri_query_soundness_of_forall_mem
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (_h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (_m_ge_3 : m ≥ 3)
    (h_mem :
      ∀ i, f i ∈
        (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := _h_agreement) (m_ge_3 := _m_ge_3) := by
  exact Code.jointAgreement_of_forall_mem
    (F := 𝔽) (κ := Fin t.succ) (ι := ω.subdomain 0)
    (C := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
    (δ := 1 - α) (W := f) h_mem

omit [Nontrivial 𝔽] in
/-- Proximity-form bridge into the Claim 8.2 `Code.jointAgreement` residual.

This exposes the coding-theoretic part of the correlated-agreement frontier as the existing
`Code.jointProximity` predicate.  The bridge itself is the proved equivalence
`Code.jointAgreement_iff_jointProximity`; the hard remaining work is deriving this proximity
witness from the BCIKS20 correlated-agreement/proximity-gap analysis. -/
theorem fri_query_soundness_of_jointProximity
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (u := f) (δ := 1 - α)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) :=
  (Code.jointAgreement_iff_jointProximity
    (C := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
    (u := f) (δ := 1 - α)).mpr h_proximity

omit [Nontrivial 𝔽] in
/-- `correlated_agreement_density` is a ratio of cardinalities, hence at most `1`. -/
theorem correlated_agreement_density_le_one {ι : Type} [Fintype ι]
    (A : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) :
    correlated_agreement_density A V ≤ 1 := by
  unfold correlated_agreement_density
  simp only
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)
    (by positivity)

omit [Nontrivial 𝔽] in
/-- **The corrected Claim 8.2 target is not a tautology** (audit finding L70).  If the batched FRI
degree bound is below the domain size, some one-row stack makes `fri_query_soundness` false at
`α = 1` (exact agreement, `δ = 0`): a word outside the degree-`friDegree s d` code cannot jointly
agree with it on every coordinate.  Under the historical degree `2 ^ n` the conclusion held for
every stack (`reedSolomon_code_subdomainZero_two_pow_eq_top`). -/
theorem exists_not_fri_query_soundness (hlt : friDegree s d < 2 ^ n) :
    ∃ f : Fin 1 → (ω.subdomain 0 → 𝔽),
      ¬ fri_query_soundness (n := n) (s := s) (d := d) (ω := ω) (α := 1) (f := f)
        (h_agreement := correlated_agreement_density_le_one _ _) (m_ge_3 := le_refl 3) := by
  obtain ⟨w, hw⟩ := exists_not_mem_reedSolomon_of_lt_card
    (α := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (deg := friDegree s d)
    (by rw [card_subdomainZero]; exact hlt)
  refine ⟨fun _ => w, ?_⟩
  unfold fri_query_soundness
  rw [tsub_self]
  exact not_jointAgreement_zero_of_not_mem
    (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
    hw

/-- Split frontier for Claim 8.2.  The existing `fri_query_soundness` residual is the final
`Code.jointAgreement` conclusion, while the proof should be assembled from three independent
ingredients:

* the probabilistic acceptance bound for the query round,
* the batching/oracle-lens reduction connecting batched queries to the underlying FRI query phase,
* the coding-theoretic step from correlated-agreement density to joint agreement.

The fields are deliberately `Prop`s plus an implication into `fri_query_soundness`: downstream work
can discharge or refine each ingredient without replacing the faithful Claim 8.2 statement by a
monolithic assumption. -/
structure FriQuerySoundnessParts
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3) where
  query_round_acceptance_bound : Prop
  batching_oracle_lens_reduction : Prop
  correlated_agreement_to_jointAgreement : Prop
  pieces_imply_claim :
    query_round_acceptance_bound →
    batching_oracle_lens_reduction →
    correlated_agreement_to_jointAgreement →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)

/-- Reassemble Claim 8.2 from the split frontier.  This theorem is intentionally small: it makes
the residual boundaries usable by callers while the three substantive proof ingredients remain
separate targets. -/
theorem fri_query_soundness_of_parts
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  (parts : FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
    (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_query : parts.query_round_acceptance_bound)
  (h_lens : parts.batching_oracle_lens_reduction)
  (h_ca : parts.correlated_agreement_to_jointAgreement) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) :=
  parts.pieces_imply_claim h_query h_lens h_ca

/-- Instantiate the Claim 8.2 frontier with the proved query-round acceptance proposition.

This constructor only fills the query-round field with `queryRoundAcceptanceBound G δ queries`.
The batching/oracle-lens reduction and the correlated-agreement bridge remain explicit frontier
fields, and `pieces_imply_claim` records how those pieces would imply the faithful
`fri_query_soundness` residual. -/
def FriQuerySoundnessParts.of_queryRoundAcceptanceBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  (lensReduction agreementBridge : Prop)
  (pieces_imply_claim :
    queryRoundAcceptanceBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := queryRoundAcceptanceBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with
`queryRoundAcceptanceBound_holds`.

The remaining hypotheses are exactly the two still-open frontier fields: the batching/oracle-lens
reduction and the correlated-agreement-to-joint-agreement bridge. -/
theorem fri_query_soundness_of_queryRoundAcceptanceBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  {lensReduction agreementBridge : Prop}
  (pieces_imply_claim :
    queryRoundAcceptanceBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_lens : lensReduction)
  (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundAcceptanceBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (queryRoundAcceptanceBound_holds G δ queries) h_lens h_agreementBridge

/-- Instantiate the Claim 8.2 frontier with the normalized-density query-round proposition. -/
def FriQuerySoundnessParts.of_queryRoundDensityBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  (lensReduction agreementBridge : Prop)
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := queryRoundDensityBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with the normalized-density
form of the proved query-round bound. -/
theorem fri_query_soundness_of_queryRoundDensityBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  {lensReduction agreementBridge : Prop}
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_lens : lensReduction)
  (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundDensityBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (queryRoundDensityBound_holds G δ queries) h_lens h_agreementBridge

/-- Instantiate the Claim 8.2 frontier with both proved local ingredients: the normalized-density
query-round bound and the structural Batched FRI oracle-lens package.  The remaining explicit field
is the coding-theoretic correlated-agreement-to-`Code.jointAgreement` bridge. -/
def FriQuerySoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
  (agreementBridge : Prop)
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    batchedFRICanonicalSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := queryRoundDensityBound G δ queries
  batching_oracle_lens_reduction :=
    batchedFRICanonicalSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the normalized-density query-round bound and the
structural Batched FRI oracle-lens package.

This narrows the remaining Claim 8.2 frontier to the correlated-agreement bridge plus the explicit
map from those ingredients into the faithful `fri_query_soundness` statement. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
  {agreementBridge : Prop}
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    batchedFRICanonicalSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond)
      (f := f) (h_agreement := h_agreement) (m_ge_3 := m_ge_3)
      G δ queries l agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (queryRoundDensityBound_holds G δ queries)
    (batchedFRICanonicalSeam_holds
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t)
    h_agreementBridge

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.2 from the normalized-density query-round theorem, the structural Batched
FRI oracle lens, and a concrete `Code.jointProximity` witness.

This is the density-route analogue of the probability adapter's concrete proximity front door: the
remaining coding-theoretic obligation is the proved-equivalent proximity predicate rather than an
arbitrary `agreementBridge : Prop`. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (u := f) (δ := 1 - α)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond)
      f h_agreement m_ge_3 G δ queries l
      (agreementBridge :=
        Code.jointProximity
          (C := (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          (u := f) (δ := 1 - α))
      (fun _h_query _h_lens h_joint =>
        fri_query_soundness_of_jointProximity
          (n := n) (ω := ω) f h_agreement m_ge_3 h_joint)
      h_proximity

omit [Nontrivial 𝔽] in
/-- Density-route Claim 8.2 front door from the affine-spaces correlated-agreement predicate.

This composes the proved query-density/lens pieces with the BCIKS20 affine-spaces CA predicate
adapter. The remaining coding-theoretic input is now the actual CA predicate plus its probability
trigger, rather than a pre-built `Code.jointProximity` witness. -/
theorem
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpacesCA
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f))}[
        δᵣ(y.1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] > ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Density-route Claim 8.2 front door from the affine-line correlated-agreement predicate.

This is the two-row query-level analogue of the full-domain affine-line CA adapter.  The
probability trigger samples the line `f 0 + z • f 1` directly and routes the resulting CA witness
through `Code.jointProximity`. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] > ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Density-route Claim 8.2 affine-line front door specialized to the BCIKS20 Reed-Solomon
affine-line correlated-agreement theorem on the Batched FRI subdomain.

This is the density-route twin of the probability adapter in `QueryRoundProbability.lean`: callers
provide the BCIKS20 affine-line theorem inputs and the affine-line probability trigger, rather than
a pre-packaged `δ_ε_correlatedAgreementAffineLines` predicate. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hBoundaryCard :
      ProximityGap.BoundaryCardResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hδ :
      1 - α ≤
        1 - ReedSolomon.sqrtRate
          (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (h_prob :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] >
        ProximityGap.errorBound
          (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  haveI : NeZero (friDegree s d) := inferInstance
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hStrictCoeff
  have hBoundaryCard' :
      ProximityGap.BoundaryCardResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hBoundaryCard
  have hδ' :
      1 - α ≤ 1 - ReedSolomon.sqrtRate (friDegree s d) rsDomain := by
    simpa [rsDomain] using hδ
  have hprob' :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code rsDomain (friDegree s d)).carrier)
          ≤ 1 - α] >
        ProximityGap.errorBound (1 - α) (friDegree s d) rsDomain := by
    simpa [rsDomain] using h_prob
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound (1 - α) (friDegree s d) rsDomain)
      (ProximityGap.Compatibility.RS_correlatedAgreement_affineLines_closed
        (ι := ω.subdomain 0) (F := 𝔽) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α)
        hStrictCoeff' hBoundaryCard' hδ')
      hprob'

/-- Density-route Claim 8.2 front door from the polynomial-curve correlated-agreement predicate.

This is the query-level analogue of the full-domain curve CA adapter: callers supply the curve CA
predicate and its single-field-sample probability trigger, and the theorem routes it through the
concrete `Code.jointProximity` front door. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementCurves
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] > t * ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementCurves
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Density-route Claim 8.2 polynomial-curve front door specialized to the BCIKS20 Reed-Solomon
curve correlated-agreement theorem on the Batched FRI subdomain. -/
theorem fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSCurve
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hBoundary :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hδ :
      1 - α ≤
        1 - ReedSolomon.sqrtRate
          (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (h_prob :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] >
        t *
          ProximityGap.errorBound
            (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  haveI : NeZero (friDegree s d) := inferInstance
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hStrictCoeff
  have hBoundary' :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hBoundary
  have hδ' :
      1 - α ≤ 1 - ReedSolomon.sqrtRate (friDegree s d) rsDomain := by
    simpa [rsDomain] using hδ
  have hprob' :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code rsDomain (friDegree s d)).carrier)
          ≤ 1 - α] >
        t * ProximityGap.errorBound (1 - α) (friDegree s d) rsDomain := by
    simpa [rsDomain] using h_prob
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound (1 - α) (friDegree s d) rsDomain)
      (ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := friDegree s d)
        (domain := rsDomain) (δ := 1 - α)
        hδ' hStrictCoeff' hBoundary')
      hprob'

#print axioms Fri.FriQuerySoundnessParts
#print axioms Fri.QueryRound.queryRound_acceptance_le_of_density
#print axioms Fri.queryRoundAcceptanceBound_of_density
#print axioms Fri.queryRoundDensityBound
#print axioms Fri.queryRoundDensityBound_holds
#print axioms Fri.batchedFRICanonicalSeam
#print axioms Fri.batchedFRICanonicalSeam_holds
#print axioms Fri.fri_query_soundness_of_forall_mem
#print axioms Fri.fri_query_soundness_of_jointProximity
#print axioms Fri.fri_query_soundness_of_parts
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundAcceptanceBound
#print axioms Fri.fri_query_soundness_of_queryRoundAcceptanceBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBound
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpacesCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSCurve

/-
The old finite-range instance diagnostic scratch block has been removed.  The remaining
Claim 8.2 work is the correlated-agreement bridge and the surrounding probabilistic
soundness-preservation infrastructure described in the docstring above and in
`docs/kb/audits/issue-14-batched-fri-query-soundness-2026-06-06.md`.
-/

open ENNReal in
/-- Corresponds to Claim 8.3 of [BCIKS20], as a named residual `Prop` (conditional, not proved):
if some prover makes the batched FRI verifier succeed with probability above `εC + α ^ l`, the
input stack jointly agrees with the Reed–Solomon code of degree `friDegree s d` on a
`(1 - α)`-fraction of `ω`, where `α = √ρ · (1 + 1 / (2m))`.

AUDIT REPAIR (2026-10-28, L70): the code and `√ρ` used to be taken at degree `2 ^ n` on the
`2 ^ n`-point domain `ω`, i.e. the whole word space with `√ρ = 1`; then `α ≥ 1`, the success
threshold `εC + α ^ l` was at least `1` (so the antecedent could never hold), and the
`Code.jointAgreement` conclusion held for every stack.  Both now use the input degree
`friDegree s d`. -/
def fri_soundness_canonicalIndependent
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  : Prop :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (friDegree s d)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
    (∃ prov : OracleProver (WitOut := Unit) ..,
        Pr{let _ ← (OracleReduction.run () f ()
              ⟨
                prov,
                (BatchedFri.Spec.batchedFRIreduction
                  (ω := ω) (n := n) k s d domain_size_cond l t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
              ⟩)}[True] > εC 𝔽 n s m ρ_sqrt + α ^ l) →
      Code.jointAgreement
        (F := 𝔽)
        (κ := Fin t.succ)
        (ι := ω)
        (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
          (δ := 1 - α)
          (W := f)

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Complete-codeword extreme of the end-to-end Claim 8.3 residual.

If every full-domain row is already a Reed-Solomon codeword, then the `Code.jointAgreement`
conclusion of `fri_soundness_canonicalIndependent` holds regardless of the verifier-success premise.  The general
malicious-prover soundness argument remains open. -/
theorem fri_soundness_canonicalIndependent_of_forall_mem
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (_m_ge_3 : m ≥ 3)
    (h_mem :
      ∀ i, f i ∈
        (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f _m_ge_3 := by
  intro _h_accepts
  exact Code.jointAgreement_of_forall_mem
    (F := 𝔽) (κ := Fin t.succ) (ι := ω)
    (C := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
    (W := f) h_mem

/-- The round-zero Batched FRI subdomain is equivalent to the original evaluation domain. -/
noncomputable def subdomainZeroEquiv : ω.subdomain 0 ≃ ω :=
  CosetFftDomainClass.subdomainZeroEquiv ω

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Reed-Solomon codewords transport from `ω.subdomain 0` to `ω` along
`subdomainZeroEquiv`. -/
theorem reedSolomon_code_subdomainZero_transport
    (deg : ℕ)
    (v : ω.subdomain 0 → 𝔽)
    (hv :
      v ∈
        (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) deg : Set (ω.subdomain 0 → 𝔽))) :
      (fun y : ω => v ((subdomainZeroEquiv (n := n) (ω := ω)).symm y)) ∈
        (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) deg : Set (ω → 𝔽)) := by
  exact ReedSolomon.codeword_equiv_of_eval_eq
    (e := subdomainZeroEquiv (n := n) (ω := ω))
    (α₁ := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (α₂ := (⟨fun x => x, by simp⟩ : ω ↪ 𝔽))
    (fun x => by
      change ((subdomainZeroEquiv (n := n) (ω := ω)) x).1 = x.1
      rfl) hv

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Lift joint agreement from the query-round subdomain to the full Batched FRI domain. -/
theorem jointAgreement_subdomainZero_to_domain
    {κ : Type} (δ : ℝ≥0) (W : κ → ω → 𝔽) :
    Code.jointAgreement
      (F := 𝔽) (κ := κ) (ι := ω.subdomain 0)
      (C := (ReedSolomon.code
        (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
      (δ := δ)
      (W := fun k x => W k ((subdomainZeroEquiv (n := n) (ω := ω)) x)) →
    Code.jointAgreement
      (F := 𝔽) (κ := κ) (ι := ω)
      (C := (ReedSolomon.code
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (δ := δ)
      (W := W) := by
  intro h
  exact Code.jointAgreement_equiv_of_codeword_transport
    (e := subdomainZeroEquiv (n := n) (ω := ω))
    (C₁ := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
    (C₂ := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
    (δ := δ) (W₂ := W)
    (by
      intro v hv
      exact reedSolomon_code_subdomainZero_transport (n := n) (ω := ω) (friDegree s d) v hv)
    h

omit [Nontrivial 𝔽] in
/-- Claim 8.3 query-lift front door: a Claim 8.2 `fri_query_soundness` conclusion on
`ω.subdomain 0` gives the full-domain `Code.jointAgreement` conclusion. -/
theorem fri_query_soundness_lift_subdomainZero_to_domain
    {t m : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    (m_ge_3 : m ≥ 3)
    (h_query :
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (δ := 1 - α)
      (W := f) :=
  jointAgreement_subdomainZero_to_domain
    (n := n) (ω := ω) (δ := 1 - α) (W := f) h_query

omit [Nontrivial 𝔽] in
/-- Full-domain Claim 8.2 front door from the proved query-density and Batched FRI lens pieces.

This composes `fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam` with the
subdomain-zero/full-domain lift, leaving the coding-theoretic correlated-agreement bridge explicit.
-/
theorem fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t m : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    {agreementBridge : Prop}
    (pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (δ := 1 - α)
      (W := f) :=
  fri_query_soundness_lift_subdomainZero_to_domain
    (n := n) (ω := ω) (f := f) h_agreement m_ge_3
    (fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
      h_agreement m_ge_3 G δ queries l pieces_imply_claim h_agreementBridge)

omit [Nontrivial 𝔽] in
/-- The verifier of the concrete Batched FRI reduction is definitionally the append of the
batching-round verifier and the lifted FRI verifier.  This exposes the exact seam consumed by the
generic sequential-composition soundness theorem. -/
theorem batchedFRIreduction_canonicalVerifier_eq_append
    {t l : ℕ} :
    (BatchedFri.Spec.batchedFRIreduction
      (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier =
    OracleVerifier.append
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier := by
  rfl

omit [Nontrivial 𝔽] in
/-- Concrete Batched FRI sequential-composition soundness front door.

Given soundness for the batching round, soundness for the lifted FRI tail, and the generic
append-seam residual for arbitrary malicious provers, the appended verifier has additive
soundness error.  Together with `batchedFRIreduction_canonicalVerifier_eq_append`, this is the exact
protocol-level sequential-composition target for the `CanonicalFriSoundnessParts` frontier. -/
theorem batchedFRICanonicalSequentialCompositionSoundness_of_append
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {t l : ℕ}
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (Spec.Statement 𝔽 (0 : Fin (k + 1)) ×
      (∀ i, Spec.OracleStatement s ω (0 : Fin (k + 1)) i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      batchError)
    (h_fri : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      h_batch h_fri) :
    letI : ∀ i, SampleableType
      ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
          Spec.QueryRound.pSpec (ω := ω) l)).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₃
      (OracleVerifier.append
        (BatchedFri.Spec.BatchingRound.batchOracleReduction
          (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
        (Fri.Spec.reduction
          (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier)
      (batchError + friError) :=
  h_residual

/-- The concrete sequential-composition soundness proposition used by the Claim 8.3 frontier.

This is the `CanonicalFriSoundnessParts.sequential_composition_soundness` field specialized to the actual
`BatchedFri.Spec.batchedFRIreduction` verifier and the additive error obtained by composing the
batching round with the lifted FRI tail. -/
def friSoundnessCanonicalSequentialComposition
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {t l : ℕ}
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    (batchError friError : ℝ≥0) : Prop :=
  letI : ∀ i, SampleableType
    ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽) ++ₚ
      (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
  OracleVerifier.soundness
    (init := init) (impl := impl)
    lang₁ lang₃
    (BatchedFri.Spec.batchedFRIreduction
      (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
    (batchError + friError)

omit [Nontrivial 𝔽] in
/-- The generic append theorem supplies the concrete Batched FRI sequential-composition field. -/
theorem friSoundnessCanonicalSequentialComposition_of_append
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {t l : ℕ}
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (Spec.Statement 𝔽 (0 : Fin (k + 1)) ×
      (∀ i, Spec.OracleStatement s ω (0 : Fin (k + 1)) i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      batchError)
    (h_fri : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      h_batch h_fri) :
    friSoundnessCanonicalSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₃ batchError friError := by
  unfold friSoundnessCanonicalSequentialComposition
  simpa [batchedFRIreduction_canonicalVerifier_eq_append] using
    (batchedFRICanonicalSequentialCompositionSoundness_of_append
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₂ lang₃ h_batch h_fri h_residual)

open ENNReal in
/-- The concrete total-error accounting proposition used by the Claim 8.3 frontier.

This names the arithmetic budget comparison between the additive sequential-composition error
`batchError + friError` and the threshold appearing in `fri_soundness_canonicalIndependent`, namely
`εC 𝔽 n s m ρ_sqrt + α ^ l`. -/
def friSoundnessTotalErrorAccounting
    {l m : ℕ}
    (_m_ge_3 : m ≥ 3)
    (batchError friError : ℝ≥0) : Prop :=
  let ρ_sqrt :=
    ReedSolomon.sqrtRate
      (friDegree s d)
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
  let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
  ((batchError + friError : ℝ≥0) : ℝ≥0∞) ≤ εC 𝔽 n s m ρ_sqrt + α ^ l

open ENNReal in
/-- Named batching-phase error-bound target for Claim 8.3.

This is the exact `εC 𝔽 n s m ρ_sqrt` bound consumed by
`friSoundnessTotalErrorAccounting_of_phase_bounds`. -/
def friBatchPhaseErrorBound
    {m : ℕ}
    (_m_ge_3 : m ≥ 3)
    (batchError : ℝ≥0) : Prop :=
  let ρ_sqrt :=
    ReedSolomon.sqrtRate
      (friDegree s d)
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
  (batchError : ℝ≥0∞) ≤ εC 𝔽 n s m ρ_sqrt

open ENNReal in
/-- Named FRI-tail phase error-bound target for Claim 8.3.

This is the exact `α ^ l` bound consumed by
`friSoundnessTotalErrorAccounting_of_phase_bounds`. -/
def friTailPhaseErrorBound
    {l m : ℕ}
    (_m_ge_3 : m ≥ 3)
    (friError : ℝ≥0) : Prop :=
  let ρ_sqrt :=
    ReedSolomon.sqrtRate
      (friDegree s d)
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
  let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
  (friError : ℝ≥0∞) ≤ α ^ l

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Per-phase error bounds imply the concrete Claim 8.3 total-error accounting field. -/
theorem friSoundnessTotalErrorAccounting_of_phase_bounds
    {l m : ℕ}
    (m_ge_3 : m ≥ 3)
    {batchError friError : ℝ≥0}
    (h_batch :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       (batchError : ℝ≥0∞) ≤ εC 𝔽 n s m ρ_sqrt))
    (h_fri :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))));
       (friError : ℝ≥0∞) ≤ α ^ l)) :
    friSoundnessTotalErrorAccounting
      (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 batchError friError := by
  unfold friSoundnessTotalErrorAccounting
  rw [ENNReal.coe_add]
  exact add_le_add h_batch h_fri

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Named per-phase error-bound targets imply the concrete Claim 8.3 total-error accounting field.

This theorem is definitionally the same accounting step as
`friSoundnessTotalErrorAccounting_of_phase_bounds`, but exposes the two remaining phase-bound
obligations as reusable named propositions. -/
theorem friSoundnessTotalErrorAccounting_of_named_phase_bounds
    {l m : ℕ}
    (m_ge_3 : m ≥ 3)
    {batchError friError : ℝ≥0}
    (h_batch :
      friBatchPhaseErrorBound
        (n := n) (s := s) (d := d) (ω := ω) m_ge_3 batchError)
    (h_fri :
      friTailPhaseErrorBound
        (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 friError) :
    friSoundnessTotalErrorAccounting
      (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 batchError friError := by
  exact friSoundnessTotalErrorAccounting_of_phase_bounds
    (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 h_batch h_fri

/-- Split frontier for Claim 8.3.  The `fri_soundness_canonicalIndependent` residual is the end-to-end
verifier-failure statement for batched FRI, while the remaining proof should be assembled from
separate ingredients:

* lifting the query-soundness Claim 8.2 output to the full-domain statement used here,
* the sequential-composition soundness theorem for the composed batched FRI reduction,
* the accounting step showing `εC 𝔽 n s m ρ_sqrt + α ^ l` bounds the verifier failure event.

As with `FriQuerySoundnessParts`, these fields are intentionally named `Prop`s plus a reassembly
map.  This keeps Claim 8.3 faithful without hiding the missing probabilistic proof behind a
monolithic assumption. -/
structure CanonicalFriSoundnessParts
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3) where
  query_soundness_lift : Prop
  sequential_composition_soundness : Prop
  total_error_accounting : Prop
  pieces_imply_claim :
    query_soundness_lift →
    sequential_composition_soundness →
    total_error_accounting →
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3

/-- Reassemble Claim 8.3 from its split frontier.  The hard probabilistic and
sequential-composition ingredients remain separate named targets. -/
theorem fri_soundness_canonicalIndependent_of_parts
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  (parts : CanonicalFriSoundnessParts (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3)
  (h_query : parts.query_soundness_lift)
  (h_seq : parts.sequential_composition_soundness)
  (h_total : parts.total_error_accounting) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 :=
  parts.pieces_imply_claim h_query h_seq h_total

/-- The query-soundness-lift proposition used by Claim 8.3 at the exact `α` appearing in
`fri_soundness_canonicalIndependent`.  This names the first `CanonicalFriSoundnessParts` field as the full-domain joint-agreement
conclusion produced by the Claim 8.2 lift, for the Reed–Solomon code of the batched FRI input
degree `friDegree s d` (not the full-rate degree `2 ^ n`, under which it held for every stack;
audit finding L70). -/
def friSoundnessQueryLift
    {t m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (_m_ge_3 : m ≥ 3) : Prop :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (friDegree s d)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (δ := 1 - α)
      (W := f)

open ENNReal in
omit [Nontrivial 𝔽] in
/-- A full-domain query-lift witness closes the end-to-end `fri_soundness_canonicalIndependent` residual.

The remaining hard work is producing this query-lift witness from the query-round analysis and
coding-theoretic proximity gap; once the `Code.jointAgreement` conclusion is available, the
conditional `fri_soundness_canonicalIndependent` proposition is immediate. -/
theorem fri_soundness_canonicalIndependent_of_queryLift
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    (h_query : friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  intro _h_accepts
  exact h_query

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Complete-codeword extreme of the Claim 8.3 query-lift field.

If every full-domain row is already a Reed-Solomon codeword on `ω`, then the query-lift field holds
on the full coordinate set.  The general Claim 8.2 correlated-agreement bridge remains explicit in
the query-round wrappers. -/
theorem friSoundnessQueryLift_of_forall_mem
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (_m_ge_3 : m ≥ 3)
    (h_mem :
      ∀ i, f i ∈
        (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f _m_ge_3 := by
  unfold friSoundnessQueryLift
  exact Code.jointAgreement_of_forall_mem
    (F := 𝔽) (κ := Fin t.succ) (ι := ω)
    (C := (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
    (W := f) h_mem

omit [Fintype 𝔽] [Nontrivial 𝔽] in
/-- Full-domain proximity-form bridge into the Claim 8.3 query-lift field.

This is the Claim 8.3 analogue of `fri_query_soundness_of_jointProximity`: callers may supply the
proved-equivalent concrete `Code.jointProximity` witness instead of a raw `Code.jointAgreement`
witness. -/
theorem friSoundnessQueryLift_of_jointProximity
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
        (u := f)
        (δ :=
          let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
          let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
          1 - α)) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    (Code.jointAgreement_iff_jointProximity
      (C := (ReedSolomon.code
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (u := f)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)).mpr h_proximity

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Full-domain proximity-form bridge into the end-to-end Claim 8.3 residual.

Once the proximity-gap layer produces the concrete full-domain `Code.jointProximity` witness at the
Claim 8.3 radius, `fri_soundness_canonicalIndependent` follows directly from `friSoundnessQueryLift_of_jointProximity`.
-/
theorem fri_soundness_canonicalIndependent_of_jointProximity
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
        (u := f)
        (δ :=
          let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
          let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
          1 - α)) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_jointProximity
        (n := n) (ω := ω) f m_ge_3 h_proximity)

omit [Nontrivial 𝔽] in
/-- The proved query-density/oracle-lens front door supplies the Claim 8.3 query-lift field. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {agreementBridge : Prop}
    (pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      (f := f) h_agreement m_ge_3 G δ queries l pieces_imply_claim h_agreementBridge

omit [Nontrivial 𝔽] in
/-- The density-route query-round/lens front door supplies the Claim 8.3 query-lift field from a
concrete subdomain `Code.jointProximity` witness.

This is the Claim 8.3 query-lift analogue of
`fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity`: the
remaining coding-theoretic bridge is the proved-equivalent proximity predicate, not an arbitrary
`agreementBridge : Prop`. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (u := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (δ :=
          1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ queries l domain_size_cond h_proximity)

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Density-route Claim 8.3 residual from the concrete subdomain proximity witness.

This composes the concrete-proximity query-lift adapter with `fri_soundness_canonicalIndependent_of_queryLift`.  It does
not prove the proximity witness; it exposes that witness as the remaining coding-theoretic target.
-/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
        (u := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (δ :=
          1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ queries l domain_size_cond h_agreement h_proximity)

/-- Density-route Claim 8.3 query-lift from the affine-line correlated-agreement predicate.

This is the two-word analogue of the affine-space adapter below.  It routes the proved
affine-line CA predicate/probability trigger through the existing concrete `Code.jointProximity`
front door; it does not identify the Batched FRI density bound with that trigger. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{let z ← $ᵖ 𝔽}[δᵣ(u 0 + z • u 1, C) ≤ δ_fri] > ε_ca) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  let C :=
    (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
  let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let δ_fri : ℝ≥0 :=
    1 -
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
  have h_proximity :
      Code.jointProximity (C := C) (u := u) (δ := δ_fri) :=
    ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineLines
      (F := 𝔽) (C := C) (δ := δ_fri) (ε := ε_ca) (u := u)
      h_ca h_prob
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω) (t := 1)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_proximity

open ENNReal in
/-- Density-route Claim 8.3 residual from the affine-line correlated-agreement predicate. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
    {l m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{let z ← $ᵖ 𝔽}[δᵣ(u 0 + z • u 1, C) ≤ δ_fri] > ε_ca) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_ca h_prob)

/-- The fixed-radius RS affine-line inputs for the density-route Batched FRI wrappers.

This packages the BCIKS20 affine-line theorem inputs used by the query-level
`...AndRSAffineLine` density route. -/
def friRSAffineLineDensityInputs
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ) : Prop :=
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (friDegree s d)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  ProximityGap.StrictCoeffPolysResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
      (domain := rsDomain) (δ := δ_fri) ∧
    ProximityGap.BoundaryCardResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
      (domain := rsDomain) (δ := δ_fri) ∧
    δ_fri ≤ 1 - ReedSolomon.sqrtRate (friDegree s d) rsDomain ∧
    Pr_{let z ← $ᵖ 𝔽}[
      δᵣ(u 0 + z • u 1, (ReedSolomon.code rsDomain (friDegree s d)).carrier) ≤ δ_fri] >
      ProximityGap.errorBound δ_fri (friDegree s d) rsDomain

/-- Density-route Claim 8.3 query-lift specialized to the Batched FRI subdomain Reed-Solomon
affine-line correlated-agreement theorem. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_rs : friRSAffineLineDensityInputs (n := n) (s := s) (d := d) (ω := ω) f m) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (friDegree s d)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  dsimp [friRSAffineLineDensityInputs] at h_rs
  rcases h_rs with ⟨hStrictCoeff, hBoundaryCard, hδ, h_prob⟩
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff
  have hBoundaryCard' :
      ProximityGap.BoundaryCardResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := friDegree s d)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hBoundaryCard
  have hδ' : δ_fri ≤ 1 - ReedSolomon.sqrtRate (friDegree s d) rsDomain := by
    simpa [rsDomain, α_fri, δ_fri] using hδ
  have h_prob' :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(u 0 + z • u 1, (ReedSolomon.code rsDomain (friDegree s d)).carrier) ≤ δ_fri] >
        ProximityGap.errorBound δ_fri (friDegree s d) rsDomain := by
    simpa [rsDomain, u, α_fri, δ_fri] using h_prob
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ_query queries l domain_size_cond
        (by simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff')
        (by simpa [rsDomain, α_fri, δ_fri] using hBoundaryCard')
        (by simpa [rsDomain, α_fri, δ_fri] using hδ')
        (by simpa [rsDomain, u, α_fri, δ_fri] using h_prob'))

open ENNReal in
/-- Density-route Claim 8.3 residual specialized to the Batched FRI subdomain Reed-Solomon
affine-line correlated-agreement theorem. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
    {l m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_rs : friRSAffineLineDensityInputs (n := n) (s := s) (d := d) (ω := ω) f m) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs)

/-- Raw full-domain Claim 8.2 conclusion from the Batched FRI subdomain Reed-Solomon affine-line
density-route wrapper. -/
theorem fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_rs : friRSAffineLineDensityInputs (n := n) (s := s) (d := d) (ω := ω) f m) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin 2)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (friDegree s d)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  change friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs

omit [Nontrivial 𝔽] in
/-- Density-route Claim 8.3 query-lift from the affine-space correlated-agreement predicate.

This composes `ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineSpaces` with the
existing concrete `Code.jointProximity` front door.  It does not identify the Batched FRI
`correlated_agreement_density` bound with the affine-space probability trigger; both remain
explicit hypotheses. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (k := t) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (u 0) (Fin.tail u))
      }[δᵣ(y.1, C) ≤ δ_fri] > ε_ca) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  let C :=
    (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let δ_fri : ℝ≥0 :=
    1 -
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
  have h_proximity :
      Code.jointProximity (C := C) (u := u) (δ := δ_fri) :=
    ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineSpaces
      (F := 𝔽) (k := t) (C := C) (δ := δ_fri) (ε := ε_ca) (u := u)
      h_ca h_prob
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_proximity

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Density-route Claim 8.3 residual from the affine-space correlated-agreement predicate.

The remaining coding-theoretic inputs are the affine-space CA predicate and its probability
trigger at the FRI radius.  This is still a conditional adapter: it does not prove the Batched FRI
specific CA trigger, phase bounds, virtual-oracle preservation, or append residual. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (k := t) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (u 0) (Fin.tail u))
      }[δᵣ(y.1, C) ≤ δ_fri] > ε_ca) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_ca h_prob)

/-- Density-route Claim 8.3 query-lift from the polynomial-curve correlated-agreement predicate.

This composes `ProximityGap.jointProximity_of_δ_ε_correlatedAgreementCurves` with the existing
concrete `Code.jointProximity` front door.  The curve CA predicate and its single-field-sample
probability trigger remain explicit hypotheses. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementCurves
        (F := 𝔽) (k := t) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] > t * ε_ca) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  let C :=
    (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let δ_fri : ℝ≥0 :=
    1 -
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
  have h_proximity :
      Code.jointProximity (C := C) (u := u) (δ := δ_fri) :=
    ProximityGap.jointProximity_of_δ_ε_correlatedAgreementCurves
      (F := 𝔽) (k := t) (C := C) (δ := δ_fri) (ε := ε_ca) (u := u)
      h_ca h_prob
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_proximity

open ENNReal in
/-- Density-route Claim 8.3 residual from the polynomial-curve correlated-agreement predicate.

The remaining coding-theoretic inputs are the curve CA predicate and its probability trigger at the
FRI radius.  This wrapper only routes them to the density-route soundness residual surface. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {ε_ca : ℝ≥0}
    (h_ca :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      ProximityGap.δ_ε_correlatedAgreementCurves
        (F := 𝔽) (k := t) C δ_fri ε_ca)
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] > t * ε_ca) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_ca h_prob)

/-- Instantiate the Claim 8.3 frontier with the proved query-density plus Batched FRI oracle-lens
front door.  The sequential-composition and total-error-accounting fields remain explicit. -/
def CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  (sequentialCompositionSoundness totalErrorAccounting : Prop)
  (pieces_imply_claim :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
    sequentialCompositionSoundness →
    totalErrorAccounting →
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3) :
    CanonicalFriSoundnessParts (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 where
  query_soundness_lift := friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3
  sequential_composition_soundness := sequentialCompositionSoundness
  total_error_accounting := totalErrorAccounting
  pieces_imply_claim := pieces_imply_claim

/-- Instantiate the Claim 8.3 frontier with the proved query-density plus Batched FRI oracle-lens
front door and the concrete sequential-composition proposition for the actual Batched FRI
reduction.  The append residual can later discharge this sequential field via
`friSoundnessCanonicalSequentialComposition_of_append`; total-error accounting remains explicit. -/
def CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
  [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
  [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
    Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
  (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
  (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
  (batchError friError : ℝ≥0)
  (totalErrorAccounting : Prop)
  (pieces_imply_claim :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
    friSoundnessCanonicalSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₃ batchError friError →
    totalErrorAccounting →
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3) :
    CanonicalFriSoundnessParts (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 where
  query_soundness_lift := friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3
  sequential_composition_soundness :=
    friSoundnessCanonicalSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₃ batchError friError
  total_error_accounting := totalErrorAccounting
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.3 after discharging its query-lift field from the proved query-density and
Batched FRI oracle-lens pieces.  The two remaining hypotheses are exactly the sequential-composition
soundness and total-error-accounting frontier fields. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeam
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {agreementBridge sequentialCompositionSoundness totalErrorAccounting : Prop}
    (query_pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
      sequentialCompositionSoundness →
      totalErrorAccounting →
      fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge)
    (h_seq : sequentialCompositionSoundness)
    (h_total : totalErrorAccounting) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  let parts :=
    CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      f m_ge_3 sequentialCompositionSoundness totalErrorAccounting soundness_pieces_imply_claim
  exact fri_soundness_canonicalIndependent_of_parts (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3 parts
    (friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeam
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries l h_agreement query_pieces_imply_claim h_agreementBridge)
    h_seq h_total

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging both the query-lift field and the concrete Batched FRI
sequential-composition field.  The append residual, correlated-agreement bridge, virtual-oracle
preservation, and total-error accounting remain explicit inputs. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (Spec.Statement 𝔽 (0 : Fin (k + 1)) ×
      (∀ i, Spec.OracleStatement s ω (0 : Fin (k + 1)) i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      batchError)
    (h_fri : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      h_batch h_fri)
    {agreementBridge totalErrorAccounting : Prop}
    (query_pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
      friSoundnessCanonicalSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      totalErrorAccounting →
      fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge)
    (h_total : totalErrorAccounting) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeam
    (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
    f m_ge_3 G δ queries h_agreement query_pieces_imply_claim
    soundness_pieces_imply_claim h_agreementBridge
    (friSoundnessCanonicalSequentialComposition_of_append
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₂ lang₃ h_batch h_fri h_residual)
    h_total

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging the query-lift, concrete sequential-composition, and
concrete total-error-accounting fields.  The remaining explicit inputs are the Claim 8.2 bridge
and the deep append residual / virtual-oracle preservation hypotheses needed to supply the phase
soundness bounds. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialCompositionAndTotalError
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (Spec.Statement 𝔽 (0 : Fin (k + 1)) ×
      (∀ i, Spec.OracleStatement s ω (0 : Fin (k + 1)) i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      batchError)
    (h_fri_soundness_canonicalIndependent : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      h_batch_soundness h_fri_soundness_canonicalIndependent)
    (h_batch_error :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       (batchError : ℝ≥0∞) ≤ εC 𝔽 n s m ρ_sqrt))
    (h_fri_error :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))));
       (friError : ℝ≥0∞) ≤ α ^ l))
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
      friSoundnessCanonicalSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries h_agreement init impl lang₁ lang₂ lang₃
      h_batch_soundness h_fri_soundness_canonicalIndependent h_residual query_pieces_imply_claim
      soundness_pieces_imply_claim h_agreementBridge
      (friSoundnessTotalErrorAccounting_of_phase_bounds
        (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 h_batch_error h_fri_error)

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Density-route Claim 8.3 reassembly from named phase error-bound targets. -/
theorem fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialCompositionAndPhaseErrorBounds
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec (Fin t → 𝔽)).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (Spec.Statement 𝔽 (0 : Fin (k + 1)) ×
      (∀ i, Spec.OracleStatement s ω (0 : Fin (k + 1)) i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      batchError)
    (h_fri_soundness_canonicalIndependent : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t (CoreDefinitions.AffineSpaceGenerator 𝔽 t)).verifier
      (Fri.Spec.reduction
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l).verifier
      h_batch_soundness h_fri_soundness_canonicalIndependent)
    (h_batch_error :
      friBatchPhaseErrorBound
        (n := n) (s := s) (d := d) (ω := ω) m_ge_3 batchError)
    (h_fri_error :
      friTailPhaseErrorBound
        (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 friError)
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      queryRoundDensityBound G δ queries →
      batchedFRICanonicalSeam
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 →
      friSoundnessCanonicalSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (d := d) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 :=
  fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialCompositionAndTotalError
    (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
    f m_ge_3 G δ queries h_agreement init impl lang₁ lang₂ lang₃
    h_batch_soundness h_fri_soundness_canonicalIndependent h_residual h_batch_error h_fri_error
    query_pieces_imply_claim soundness_pieces_imply_claim h_agreementBridge

#print axioms Fri.CanonicalFriSoundnessParts
#print axioms Fri.subdomainZeroEquiv
#print axioms Fri.reedSolomon_code_subdomainZero_transport
#print axioms Fri.jointAgreement_subdomainZero_to_domain
#print axioms Fri.fri_query_soundness_lift_subdomainZero_to_domain
#print axioms Fri.fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
#print axioms Fri.batchedFRIreduction_canonicalVerifier_eq_append
#print axioms Fri.batchedFRICanonicalSequentialCompositionSoundness_of_append
#print axioms Fri.friSoundnessCanonicalSequentialComposition
#print axioms Fri.friSoundnessCanonicalSequentialComposition_of_append
#print axioms Fri.friSoundnessQueryLift
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryLift
#print axioms Fri.friSoundnessQueryLift_of_forall_mem
#print axioms Fri.friSoundnessQueryLift_of_jointProximity
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
#print axioms Fri.CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
#print axioms Fri.friSoundnessTotalErrorAccounting
#print axioms Fri.friBatchPhaseErrorBound
#print axioms Fri.friTailPhaseErrorBound
#print axioms Fri.friSoundnessTotalErrorAccounting_of_phase_bounds
#print axioms Fri.friSoundnessTotalErrorAccounting_of_named_phase_bounds
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialCompositionAndTotalError
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialCompositionAndPhaseErrorBounds
#print axioms Fri.fri_soundness_canonicalIndependent_of_forall_mem
#print axioms Fri.fri_soundness_canonicalIndependent_of_jointProximity
#print axioms Fri.fri_soundness_canonicalIndependent_of_parts

end Soundness

end Fri
end Fri

/-! ### Axiom audit (issues #14/#24 FRI soundness frontier) -/

#print axioms Fri.fri_query_soundness
#print axioms Fri.FriQuerySoundnessParts
#print axioms Fri.fri_query_soundness_of_parts
#print axioms Fri.QueryRound.queryRound_acceptance_le_of_density
#print axioms Fri.queryRoundAcceptanceBound_of_density
#print axioms Fri.queryRoundDensityBound
#print axioms Fri.queryRoundDensityBound_holds
#print axioms Fri.batchedFRICanonicalSeam
#print axioms Fri.batchedFRICanonicalSeam_holds
#print axioms Fri.fri_query_soundness_of_forall_mem
#print axioms Fri.fri_query_soundness_of_jointProximity
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundAcceptanceBound
#print axioms Fri.fri_query_soundness_of_queryRoundAcceptanceBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBound
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeam
#print axioms Fri.fri_soundness_canonicalIndependent
#print axioms Fri.fri_soundness_canonicalIndependent_of_forall_mem
#print axioms Fri.subdomainZeroEquiv
#print axioms Fri.reedSolomon_code_subdomainZero_transport
#print axioms Fri.jointAgreement_subdomainZero_to_domain
#print axioms Fri.fri_query_soundness_lift_subdomainZero_to_domain
#print axioms Fri.fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
#print axioms Fri.batchedFRIreduction_canonicalVerifier_eq_append
#print axioms Fri.batchedFRICanonicalSequentialCompositionSoundness_of_append
#print axioms Fri.CanonicalFriSoundnessParts
#print axioms Fri.friSoundnessQueryLift
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryLift
#print axioms Fri.friSoundnessQueryLift_of_forall_mem
#print axioms Fri.friSoundnessQueryLift_of_jointProximity
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
#print axioms Fri.CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.CanonicalFriSoundnessParts.of_queryRoundDensityBoundAndCanonicalBatchingSeamAndSequentialComposition
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeam
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineSpaceCA
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_canonicalIndependent_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
#print axioms Fri.friBatchPhaseErrorBound
#print axioms Fri.friTailPhaseErrorBound
#print axioms Fri.friSoundnessTotalErrorAccounting_of_named_phase_bounds
#print axioms Fri.fri_soundness_canonicalIndependent_of_jointProximity
#print axioms Fri.fri_soundness_canonicalIndependent_of_parts
