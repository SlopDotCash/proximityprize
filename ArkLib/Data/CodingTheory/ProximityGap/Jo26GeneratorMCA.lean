/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGapP

/-!
# Generator MCA and the [Jo26] interleaving factor (Theorems 4.2 and 4.4)

First formalization of the **coefficient-generator** mutual correlated agreement (MCA)
framework of [Jo26] (ePrint 2026/891, Definition 2.6) and of its two interleaving
theorems — the B1 residual of issue #334:

* **Theorem 4.2 (counting average).** For *any* finite seed set `Ω` and any generator
  `G : Ω → Fin ℓ → F`, the generator-MCA error of the `s`-fold interleaved code is at most
  `(q^s − 1)/(q^s − q^{s−1})` times the base error (`q = |F|`):

    `ε^gen_mca(C^⋈s, δ) ≤ (q^s − 1)/(q^s − q^{s−1}) · ε^gen_mca(C, δ)`.

  The proof is finite counting: each bad seed `ω` of the interleaved stack carries a
  *proper* subspace `K_ω ≤ F^s` of combination vectors that admit a joint codeword tuple
  on the witness set (`tupleJointSubmodule`, [Jo26] Lemma 4.1); every `λ ∉ K_ω` transports
  `ω` to a bad seed of the `λ`-combined base stack with the same witness set
  (`genMCAEvent_base_of_notMem`). Each proper subspace misses at least `q^s − q^{s−1}`
  vectors ([Jo26] Lemma 3.1, `card_compl_proper_submodule_ge`), so double counting the
  pairs `(ω, λ)` and pigeonholing over the `q^s − 1` nonzero `λ` produces a single `λ₀`
  carrying a `(q^s − q^{s−1})/(q^s − 1)` fraction of all bad seeds
  (`exists_combination_count_bound`).

* **Theorem 4.4 (small-seed exactness).** When `|Ω| ≤ q`, the factor disappears:

    `ε^gen_mca(C^⋈s, δ) = ε^gen_mca(C, δ)`.

  The seed-indexed family `ω ↦ K_ω` has at most `q` members, so the covering lemma
  ([Jo26] Lemma 3.2, in-tree as `exists_nonzero_notMem_of_proper_family`, reindexed here
  through an embedding `Ω ↪ F` in `exists_nonzero_notMem_of_proper_family_of_card_le`)
  yields one `λ` escaping *every* `K_ω` simultaneously — no averaging, no factor.
  The reverse inequality is the zero-row embedding (`epsMCAGen_le_epsMCAGen_interleaved`).

* **Bridges.** The generator framework subsumes the in-tree MCA layers:
  `epsMCAGen` at the affine-line generator `γ ↦ ![1, γ]` *equals* `ProximityGap.epsMCA`
  (`epsMCAGen_pairGen_eq_epsMCA`), and at the power generator `γ ↦ (γ^{exp j})_j` it
  *equals* `ProximityGapP.epsMCAP` (`epsMCAGen_powGen_eq_epsMCAP`). Hence Theorem 4.4
  instantiated at `Ω = F` re-derives the exact interleaving invariance of both layers,
  and Theorem 4.2 gives the first interleaving bound valid for *arbitrary* generators
  (seed sets larger than `F`, correlated coefficient tuples, etc.).

All proofs are finite counting plus the one `Pr ↦ card/|Ω|` conversion
(`prob_uniform_eq_card_filter_div_card`); no measure theory.

## Main definitions

* `genComb` — the `G`-combination `i ↦ ∑ⱼ G ω j • uⱼ i` of an `ℓ`-stack at seed `ω`
  ([Jo26] Definition 2.6).
* `genMCAEvent` — the generator-MCA bad event: a witness set `S`, `|S| ≥ (1−δ)·n`, on
  which the combination matches a codeword while no codeword tuple matches the stack.
* `epsMCAGen` — worst-case bad-seed probability `⨆ u, Pr_{ω ←$ᵖ Ω}[genMCAEvent …]`.
* `tupleJointSubmodule` — the subspace `K_ω` of [Jo26] Lemma 4.1.

## Main results

* `card_compl_proper_submodule_ge` — [Jo26] Lemma 3.1 as cardinality.
* `tupleJointSubmodule_ne_top`, `genMCAEvent_base_of_notMem` — [Jo26] Lemma 4.1.
* `exists_combination_count_bound` — the double-count/pigeonhole core of Theorem 4.2.
* `epsMCAGen_interleaved_le_factor` — **[Jo26] Theorem 4.2**.
* `exists_nonzero_notMem_of_proper_family_of_card_le` — [Jo26] Lemma 3.2 for `|Ω| ≤ q`.
* `epsMCAGen_le_epsMCAGen_interleaved` / `epsMCAGen_interleaved_le_of_card_le` /
  `epsMCAGen_interleaved_eq_of_card_le` — **[Jo26] Theorem 4.4**.
* `epsMCAGen_pairGen_eq_epsMCA`, `epsMCAGen_powGen_eq_epsMCAP` — bridges to the
  in-tree `epsMCA` ([ABF26] Definition 4.3) and `epsMCAP` layers.

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891. (Issue #334, hypothesis K2 / residual B1.)
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap.Jo26Gen

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {ℓ : ℕ}

/-! ### The generator framework ([Jo26] Definition 2.6) -/

/-- **[Jo26] Definition 2.6 (coefficient generator combination).** Given a generator
`G : Ω → Fin ℓ → F` (an arbitrary function from a finite seed set to coefficient tuples)
and an `ℓ`-stack `u`, the combination at seed `ω` is the word `i ↦ ∑ⱼ G ω j • uⱼ i`. -/
def genComb (G : Ω → Fin ℓ → F) (u : WordStack A (Fin ℓ) ι) (ω : Ω) : ι → A :=
  fun i => ∑ j, G ω j • u j i

/-- **Generator-MCA bad event.** Seed `ω` is *bad* for the stack `u` iff some witness set
`S` of size `≥ (1−δ)·n` carries a codeword matching the `G`-combination of `u` at `ω`,
while *no* tuple of codewords jointly matches `u` on `S`
(`ProximityGapP.pairJointAgreesOnP`, the `ℓ`-ary joint-agreement predicate). This is the
`Fin ℓ` / general-generator analogue of `ProximityGap.mcaEvent` and
`ProximityGapP.mcaEventP`. -/
def genMCAEvent (G : Ω → Fin ℓ → F) (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin ℓ) ι) (ω : Ω) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = genComb G u ω i) ∧
    ¬ ProximityGapP.pairJointAgreesOnP C S u

open Classical in
/-- **Generator-MCA error** `ε^gen_mca(G, C, δ)`: the worst case over `ℓ`-stacks `u` of
the probability over a uniform seed `ω ←$ᵖ Ω` of the generator-MCA bad event. Generalizes
`ProximityGap.epsMCA` (the generator `γ ↦ ![1, γ]`, see `epsMCAGen_pairGen_eq_epsMCA`)
and `ProximityGapP.epsMCAP` (the generator `γ ↦ (γ^{exp j})_j`, see
`epsMCAGen_powGen_eq_epsMCAP`). -/
noncomputable def epsMCAGen (G : Ω → Fin ℓ → F) (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin ℓ) ι,
    Pr_{let ω ← $ᵖ Ω}[genMCAEvent G C δ u ω]

/-! ### Probability ↦ counting bridge -/

/-- Uniform probability of an event as a cardinality ratio, with `ℕ`-casts directly into
`ℝ≥0∞` (normalized form of `prob_uniform_eq_card_filter_div_card`). -/
theorem Pr_uniform_eq_natCast_div {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    Pr_{let x ← $ᵖ α}[P x]
      = ((Finset.univ.filter P).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  simp [ENNReal.coe_natCast]

/-- **Counting transfer at the probability level.** If `a · #P ≤ b · #Q` as a count of
satisfying points (with `a > 0`), then `Pr[P] ≤ (b/a) · Pr[Q]` for the uniform measure.
This is the single `ℝ≥0∞` step of [Jo26] Theorem 4.2; everything before it is `ℕ`. -/
theorem Pr_le_factor_mul_Pr_of_card_le {α : Type} [Fintype α] [Nonempty α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] {a b : ℕ} (ha : 0 < a)
    (hcount : a * (Finset.univ.filter P).card ≤ b * (Finset.univ.filter Q).card) :
    Pr_{let x ← $ᵖ α}[P x]
      ≤ ((b : ℝ≥0∞) / (a : ℝ≥0∞)) * Pr_{let x ← $ᵖ α}[Q x] := by
  rw [Pr_uniform_eq_natCast_div, Pr_uniform_eq_natCast_div]
  have ha0 : (a : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have haT : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top a
  have hkey : ((Finset.univ.filter P).card : ℝ≥0∞)
      ≤ (b : ℝ≥0∞) * ((Finset.univ.filter Q).card : ℝ≥0∞) / (a : ℝ≥0∞) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl haT)]
    calc ((Finset.univ.filter P).card : ℝ≥0∞) * (a : ℝ≥0∞)
        = ((a * (Finset.univ.filter P).card : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((b * (Finset.univ.filter Q).card : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hcount
      _ = (b : ℝ≥0∞) * ((Finset.univ.filter Q).card : ℝ≥0∞) := by push_cast; ring
  calc ((Finset.univ.filter P).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞)
      ≤ ((b : ℝ≥0∞) * ((Finset.univ.filter Q).card : ℝ≥0∞) / (a : ℝ≥0∞))
          / (Fintype.card α : ℝ≥0∞) := by gcongr
    _ = ((b : ℝ≥0∞) / (a : ℝ≥0∞))
          * (((Finset.univ.filter Q).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞)) := by
        simp only [div_eq_mul_inv]; ring

/-! ### [Jo26] Lemma 3.1 as cardinality -/

open Classical in
/-- **[Jo26] Lemma 3.1 (escape count).** A proper subspace `K ⊊ F^s` has at most
`q^{s−1}` points, so at least `q^s − q^{s−1}` vectors of `F^s` lie outside `K`. -/
theorem card_compl_proper_submodule_ge {s : ℕ}
    (K : Submodule F (Fin s → F)) (hK : K ≠ ⊤) :
    Fintype.card F ^ s - Fintype.card F ^ (s - 1)
      ≤ (Finset.univ.filter (fun lam : Fin s → F => lam ∉ K)).card := by
  classical
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hmem_card : (Finset.univ.filter (fun lam : Fin s → F => lam ∈ K)).card
      ≤ Fintype.card F ^ (s - 1) := by
    have hfrTop : Module.finrank F (Fin s → F) = s := by
      rw [Module.finrank_pi, Fintype.card_fin]
    have hfr : Module.finrank F K < s := by
      have := Submodule.finrank_lt (s := K) hK
      rwa [hfrTop] at this
    have hsub : Finset.univ.filter (fun lam : Fin s → F => lam ∈ K)
        = (K : Set (Fin s → F)).toFinset := by
      ext lam
      simp [Set.mem_toFinset]
    rw [hsub, Set.toFinset_card]
    have hcg : Fintype.card (↑K : Set (Fin s → F)) = Fintype.card K := rfl
    have hM : Fintype.card K = Fintype.card F ^ Module.finrank F K :=
      Module.card_eq_pow_finrank
    rw [hcg, hM]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsplit : (Finset.univ.filter (fun lam : Fin s → F => lam ∈ K)).card
      + (Finset.univ.filter (fun lam : Fin s → F => lam ∉ K)).card
      = Fintype.card F ^ s := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
  omega

/-! ### The bad-seed subspace ([Jo26] Lemma 4.1) -/

open Classical in
/-- **[Jo26] Lemma 4.1 (the subspace `K_ω`).** The set of combination vectors
`λ ∈ F^s` whose `λ`-combination of the interleaved stack `U` admits a joint codeword
tuple on `S`. Linearity of `C` makes this a subspace: joint-tuple witnesses add, scale,
and the zero combination is witnessed by the zero tuple. This is the `ℓ`-ary tuple
analogue of `ProximityGap.jointPairSubmodule`. -/
def tupleJointSubmodule (C : Submodule F (ι → A)) (S : Finset ι) {s : ℕ}
    (U : WordStack (Fin s → A) (Fin ℓ) ι) : Submodule F (Fin s → F) where
  carrier := {lam | ProximityGapP.pairJointAgreesOnP (C : Set (ι → A)) S
    (fun j i => ∑ k, lam k • U j i k)}
  zero_mem' := by
    refine ⟨fun _ => 0, fun j => C.zero_mem, fun i hi j => ?_⟩
    simp
  add_mem' := by
    rintro lam lam' ⟨v, hv, hag⟩ ⟨w, hw, hag'⟩
    refine ⟨fun j => v j + w j, fun j => C.add_mem (hv j) (hw j), fun i hi j => ?_⟩
    have h1 := hag i hi j
    have h2 := hag' i hi j
    calc (v j + w j) i = (∑ k, lam k • U j i k) + ∑ k, lam' k • U j i k := by
          rw [Pi.add_apply, h1, h2]
      _ = ∑ k, (lam + lam') k • U j i k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
  smul_mem' := by
    rintro c lam ⟨v, hv, hag⟩
    refine ⟨fun j => c • v j, fun j => C.smul_mem c (hv j), fun i hi j => ?_⟩
    have h1 := hag i hi j
    calc (c • v j) i = c • ∑ k, lam k • U j i k := by rw [Pi.smul_apply, h1]
      _ = ∑ k, (c • lam) k • U j i k := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [Pi.smul_apply, smul_smul, smul_eq_mul]

open Classical in
/-- **Properness of `K_ω`** ([Jo26] Lemma 4.1, core step). If every combination vector
admitted a joint tuple on `S`, then in particular every standard basis vector would —
i.e. every *column* `k` of the interleaved stack would admit a joint tuple on `S` — and
the column witnesses assemble into a joint tuple for the interleaved stack itself on `S`,
contradicting the interleaved witness. -/
theorem tupleJointSubmodule_ne_top (C : Submodule F (ι → A)) {S : Finset ι} {s : ℕ}
    (U : WordStack (Fin s → A) (Fin ℓ) ι)
    (hnopair : ¬ ProximityGapP.pairJointAgreesOnP
      ((C : Set (ι → A))^⋈ (Fin s)) S U) :
    tupleJointSubmodule C S U ≠ ⊤ := by
  intro htop
  apply hnopair
  have hcol : ∀ k : Fin s, ProximityGapP.pairJointAgreesOnP (C : Set (ι → A)) S
      (fun j i => U j i k) := by
    intro k
    have hmem : (Pi.single k (1 : F)) ∈ tupleJointSubmodule C S U := by
      rw [htop]; trivial
    obtain ⟨v, hv, hag⟩ := hmem
    have hsum : ∀ (j : Fin ℓ) (i : ι),
        (∑ k', (Pi.single k (1 : F) : Fin s → F) k' • U j i k') = U j i k := by
      intro j i
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine ⟨v, hv, fun i hi j => ?_⟩
    have h1 := hag i hi j
    dsimp only at h1 ⊢
    rwa [hsum j i] at h1
  choose V hVmem hVag using hcol
  refine ⟨fun j i k => V k j i, ?_, fun i hi j => ?_⟩
  · intro j k
    exact hVmem k j
  · funext k
    exact hVag k i hi j

open Classical in
/-- **[Jo26] Lemma 4.1 (bad-seed transport).** If seed `ω` is bad for the interleaved
stack `U` with witness set `S` (closeness clause `hclose`), then for any combination
vector `λ ∉ K_ω = tupleJointSubmodule C S U`, the same seed `ω` is bad for the
`λ`-combined base stack with the *same* witness set `S`. The closeness clause transports
by bilinearity: `λ·(∑ⱼ G ω j • Uⱼ) = ∑ⱼ G ω j • (λ·Uⱼ)`. -/
theorem genMCAEvent_base_of_notMem (C : Submodule F (ι → A)) {s : ℕ}
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) (U : WordStack (Fin s → A) (Fin ℓ) ι)
    {ω : Ω} {S : Finset ι}
    (hcard : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hclose : ∃ w ∈ ((C : Set (ι → A))^⋈ (Fin s)), ∀ i ∈ S, w i = genComb G U ω i)
    {lam : Fin s → F} (hlam : lam ∉ tupleJointSubmodule C S U) :
    genMCAEvent G (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) ω := by
  obtain ⟨w, hwmem, hwagree⟩ := hclose
  refine ⟨S, hcard, ?_, ?_⟩
  · -- closeness: the λ-combination of the columns of `w`
    refine ⟨fun i => ∑ k, lam k • w i k, ?_, ?_⟩
    · have hcols : ∀ k : Fin s, (fun i => w i k) ∈ (C : Set (ι → A)) := hwmem
      have heq : (fun i => ∑ k, lam k • w i k)
          = ∑ k, lam k • (fun i => w i k) := by
        funext i
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun k _ => rfl
      rw [heq]
      exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hcols k)
    · intro i hi
      have hpt : ∀ k : Fin s, w i k = ∑ j, G ω j • U j i k := by
        intro k
        have := congrArg (fun f : Fin s → A => f k) (hwagree i hi)
        simpa [genComb, Finset.sum_apply] using this
      calc (fun i => ∑ k, lam k • w i k) i = ∑ k, lam k • w i k := rfl
        _ = ∑ k, lam k • ∑ j, G ω j • U j i k :=
            Finset.sum_congr rfl fun k _ => by rw [hpt k]
        _ = ∑ k, ∑ j, lam k • (G ω j • U j i k) :=
            Finset.sum_congr rfl fun k _ => Finset.smul_sum
        _ = ∑ j, ∑ k, lam k • (G ω j • U j i k) := Finset.sum_comm
        _ = ∑ j, G ω j • ∑ k, lam k • U j i k := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by
              rw [smul_smul, smul_smul, mul_comm]
        _ = genComb G (fun j i => ∑ k, lam k • U j i k) ω i := rfl
  · -- no joint tuple: exactly `λ ∉ K_ω`
    intro hpa
    exact hlam hpa

/-! ### [Jo26] Theorem 4.2: the counting average -/

open Classical in
/-- **Counting core of [Jo26] Theorem 4.2.** For any interleaved stack `U`, there is a
single combination vector `λ₀` whose combined base stack inherits at least a
`(q^s − q^{s−1})/(q^s − 1)` fraction of the interleaved bad seeds:

  `(q^s − q^{s−1}) · #bad(U) ≤ (q^s − 1) · #bad(λ₀ · U)`.

Double counting: each bad seed contributes `≥ q^s − q^{s−1}` escaping vectors (Lemma 3.1
applied to its proper subspace `K_ω`), all of them nonzero; pigeonhole over the
`q^s − 1` nonzero vectors yields `λ₀`; transport (Lemma 4.1) re-reads its column count
as base bad seeds. Entirely in `ℕ`. -/
theorem exists_combination_count_bound (C : Submodule F (ι → A)) {s : ℕ} (hs : 1 ≤ s)
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) (U : WordStack (Fin s → A) (Fin ℓ) ι) :
    ∃ lam₀ : Fin s → F,
      (Fintype.card F ^ s - Fintype.card F ^ (s - 1)) *
          (Finset.univ.filter
            (fun ω => genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω)).card
        ≤ (Fintype.card F ^ s - 1) *
          (Finset.univ.filter
            (fun ω => genMCAEvent G (C : Set (ι → A)) δ
              (fun j i => ∑ k, lam₀ k • U j i k) ω)).card := by
  classical
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set q := Fintype.card F with hq
  set B : Finset Ω :=
    Finset.univ.filter (fun ω => genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω)
    with hB
  set K : Ω → Submodule F (Fin s → F) := fun ω =>
    if h : genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω
    then tupleJointSubmodule C h.choose U else ⊥ with hKdef
  set Λ : Finset (Fin s → F) := Finset.univ.filter (fun lam : Fin s → F => lam ≠ 0)
    with hΛ
  -- per-seed escape count
  have hper : ∀ ω ∈ B, q ^ s - q ^ (s - 1)
      ≤ (Λ.filter (fun lam => lam ∉ K ω)).card := by
    intro ω hω
    have hev : genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω :=
      (Finset.mem_filter.mp hω).2
    have hKne : K ω ≠ ⊤ := by
      simp only [hKdef]
      rw [dif_pos hev]
      exact tupleJointSubmodule_ne_top C U hev.choose_spec.2.2
    have hfeq : Λ.filter (fun lam => lam ∉ K ω)
        = Finset.univ.filter (fun lam : Fin s → F => lam ∉ K ω) := by
      ext lam
      simp only [hΛ, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        exact ⟨fun h0 => h (h0 ▸ (K ω).zero_mem), h⟩
    rw [hfeq]
    exact card_compl_proper_submodule_ge (K ω) hKne
  -- double count over pairs (ω, λ)
  have hdouble : B.card * (q ^ s - q ^ (s - 1))
      ≤ ∑ lam ∈ Λ, (B.filter (fun ω => lam ∉ K ω)).card := by
    calc B.card * (q ^ s - q ^ (s - 1))
        = ∑ _ω ∈ B, (q ^ s - q ^ (s - 1)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ ω ∈ B, (Λ.filter (fun lam => lam ∉ K ω)).card := Finset.sum_le_sum hper
      _ = ∑ ω ∈ B, ∑ lam ∈ Λ, if lam ∉ K ω then 1 else 0 :=
          Finset.sum_congr rfl fun ω _ => Finset.card_filter _ _
      _ = ∑ lam ∈ Λ, ∑ ω ∈ B, if lam ∉ K ω then 1 else 0 := Finset.sum_comm
      _ = ∑ lam ∈ Λ, (B.filter (fun ω => lam ∉ K ω)).card :=
          Finset.sum_congr rfl fun lam _ => (Finset.card_filter _ _).symm
  -- the nonzero-vector count
  have hΛcard : Λ.card = q ^ s - 1 := by
    have herase : Λ = (Finset.univ : Finset (Fin s → F)).erase 0 := by
      rw [hΛ]
      exact Finset.filter_ne' _ _
    rw [herase, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
  have hqs2 : 2 ≤ q ^ s := by
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ s := Nat.pow_le_pow_right (by omega) hs
  have hΛne : Λ.Nonempty := by
    rw [← Finset.card_pos, hΛcard]
    omega
  -- pigeonhole over the nonzero vectors
  obtain ⟨lam₀, _, hpig⟩ :
      ∃ lam₀ ∈ Λ, B.card * (q ^ s - q ^ (s - 1))
        ≤ (q ^ s - 1) * (B.filter (fun ω => lam₀ ∉ K ω)).card := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ lam ∈ Λ, (q ^ s - 1) * (B.filter (fun ω => lam ∉ K ω)).card
        < ∑ _lam ∈ Λ, B.card * (q ^ s - q ^ (s - 1)) :=
      Finset.sum_lt_sum_of_nonempty hΛne hcon
    rw [Finset.sum_const, smul_eq_mul, hΛcard, ← Finset.mul_sum] at hlt
    have hge : (q ^ s - 1) * (B.card * (q ^ s - q ^ (s - 1)))
        ≤ (q ^ s - 1) * ∑ lam ∈ Λ, (B.filter (fun ω => lam ∉ K ω)).card :=
      mul_le_mul_right hdouble _
    exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)
  -- transport: every counted seed is bad for the λ₀-combined base stack
  have hsub : B.filter (fun ω => lam₀ ∉ K ω)
      ⊆ Finset.univ.filter
          (fun ω => genMCAEvent G (C : Set (ι → A)) δ
            (fun j i => ∑ k, lam₀ k • U j i k) ω) := by
    intro ω hω
    obtain ⟨hωB, hωK⟩ := Finset.mem_filter.mp hω
    have hev : genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω :=
      (Finset.mem_filter.mp hωB).2
    simp only [hKdef] at hωK
    rw [dif_pos hev] at hωK
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨hcard', hclose, _⟩ := hev.choose_spec
    exact genMCAEvent_base_of_notMem C G δ U hcard' hclose hωK
  refine ⟨lam₀, ?_⟩
  calc (q ^ s - q ^ (s - 1)) * B.card
      = B.card * (q ^ s - q ^ (s - 1)) := Nat.mul_comm _ _
    _ ≤ (q ^ s - 1) * (B.filter (fun ω => lam₀ ∉ K ω)).card := hpig
    _ ≤ (q ^ s - 1) * (Finset.univ.filter
          (fun ω => genMCAEvent G (C : Set (ι → A)) δ
            (fun j i => ∑ k, lam₀ k • U j i k) ω)).card :=
        mul_le_mul_right (Finset.card_le_card hsub) _

open Classical in
/-- **[Jo26] Theorem 4.2.** For *any* finite seed set `Ω` and any coefficient generator
`G : Ω → Fin ℓ → F`, the generator-MCA error of the `s`-fold interleaved code is at most
`(q^s − 1)/(q^s − q^{s−1})` times the base generator-MCA error (`q = |F|`, subtractions
in `ℕ` — non-truncating since `q ≥ 2` and `s ≥ 1`):

  `ε^gen_mca(G, C^⋈s, δ) ≤ (q^s − 1)/(q^s − q^{s−1}) · ε^gen_mca(G, C, δ)`.

Note the factor is `< q/(q−1) ≤ 2` for every `s`, and the bound needs **no relation
between `|Ω|` and `q`** — this is the general-generator interleaving stability that
Theorem 4.4 sharpens to equality when `|Ω| ≤ q`. -/
theorem epsMCAGen_interleaved_le_factor (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ ((Fintype.card F ^ s - 1 : ℕ) : ℝ≥0∞)
          / ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ℝ≥0∞)
          * epsMCAGen G (C : Set (ι → A)) δ := by
  classical
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hpow : Fintype.card F ^ (s - 1) < Fintype.card F ^ s :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hapos : 0 < Fintype.card F ^ s - Fintype.card F ^ (s - 1) := by omega
  unfold epsMCAGen
  refine iSup_le fun U => ?_
  obtain ⟨lam₀, hcount⟩ := exists_combination_count_bound C hs G δ U
  refine le_trans
    (Pr_le_factor_mul_Pr_of_card_le
      (fun ω => genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω)
      (fun ω => genMCAEvent G (C : Set (ι → A)) δ
        (fun j i => ∑ k, lam₀ k • U j i k) ω)
      hapos hcount) ?_
  exact mul_le_mul_right
    (le_iSup (fun w : WordStack A (Fin ℓ) ι =>
      Pr_{let ω ← $ᵖ Ω}[genMCAEvent G (C : Set (ι → A)) δ w ω])
      (fun j i => ∑ k, lam₀ k • U j i k)) _

/-! ### [Jo26] Theorem 4.4: exactness for small seed sets (`|Ω| ≤ q`) -/

/-- **[Jo26] Lemma 3.2, reindexed for `|Ω| ≤ q`.** A family of proper subspaces of `F^t`
indexed by *any* type of cardinality at most `q = |F|` cannot cover `F^t \ {0}`: some
nonzero vector escapes every member. Reindexes the in-tree `F`-indexed covering lemma
`ProximityGap.exists_nonzero_notMem_of_proper_family` through an embedding `Ω ↪ F`,
padding the unused indices with a copy of an arbitrary family member. -/
theorem exists_nonzero_notMem_of_proper_family_of_card_le
    {t : ℕ} (ht : 1 ≤ t) (hΩ : Fintype.card Ω ≤ Fintype.card F)
    (K : Ω → Submodule F (Fin t → F)) (hK : ∀ ω, K ω ≠ ⊤) :
    ∃ lam : Fin t → F, lam ≠ 0 ∧ ∀ ω, lam ∉ K ω := by
  classical
  obtain ⟨e⟩ : Nonempty (Ω ↪ F) := Function.Embedding.nonempty_of_card_le hΩ
  obtain ⟨lam, hlam0, hlam⟩ := ProximityGap.exists_nonzero_notMem_of_proper_family ht
    (fun γ => if h : ∃ ω, e ω = γ then K h.choose else K (Classical.arbitrary Ω))
    (fun γ => by
      dsimp only
      split_ifs with h
      · exact hK _
      · exact hK _)
  refine ⟨lam, hlam0, fun ω => ?_⟩
  have hex : ∃ ω', e ω' = e ω := ⟨ω, rfl⟩
  have hnot := hlam (e ω)
  rw [dif_pos hex] at hnot
  have hch : hex.choose = ω := e.injective hex.choose_spec
  rwa [hch] at hnot

open Classical in
/-- **[Jo26] Theorem 4.4, easy half: `ε^gen_mca(G, C, δ) ≤ ε^gen_mca(G, C^⋈s, δ)`.**
The zero-row embedding (column `0` carries the base stack, all other columns are `0`)
maps every base bad seed to an interleaved bad seed with the same witness set. -/
theorem epsMCAGen_le_epsMCAGen_interleaved (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) :
    epsMCAGen G (C : Set (ι → A)) δ
      ≤ epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ := by
  classical
  unfold epsMCAGen
  refine iSup_le fun v => ?_
  set u : WordStack (Fin s → A) (Fin ℓ) ι :=
    fun j i k => if k = (0 : Fin s) then v j i else 0 with hu
  have h_imp : ∀ ω : Ω, genMCAEvent G (C : Set (ι → A)) δ v ω →
      genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ u ω := by
    rintro ω ⟨S, hcard, ⟨w, hw, hagree⟩, hnopair⟩
    have hcomb : ∀ (i : ι) (k : Fin s),
        genComb G u ω i k = if k = (0 : Fin s) then genComb G v ω i else 0 := by
      intro i k
      show (∑ j, G ω j • u j i) k = _
      rw [Finset.sum_apply]
      by_cases hk : k = (0 : Fin s)
      · simp only [hk]
        exact Finset.sum_congr rfl fun j _ => by
          simp [hu]
      · simp only [if_neg hk]
        rw [Finset.sum_eq_zero]
        intro j _
        simp [hu, hk]
    refine ⟨S, hcard, ?_, ?_⟩
    · refine ⟨fun i k => if k = (0 : Fin s) then w i else 0, ?_, ?_⟩
      · intro k
        show (fun i => if k = (0 : Fin s) then w i else 0) ∈ (C : Set (ι → A))
        by_cases hk : k = (0 : Fin s)
        · simp only [if_pos hk]
          exact hw
        · simp only [if_neg hk]
          exact C.zero_mem
      · intro i hi
        funext k
        show (if k = (0 : Fin s) then w i else 0) = genComb G u ω i k
        rw [hcomb i k]
        by_cases hk : k = (0 : Fin s)
        · rw [if_pos hk, if_pos hk]
          exact hagree i hi
        · rw [if_neg hk, if_neg hk]
    · rintro ⟨V, hV, hVag⟩
      apply hnopair
      have hV' : ∀ j, ∀ k : Fin s, (fun i => V j i k) ∈ (C : Set (ι → A)) := hV
      refine ⟨fun j i => V j i 0, fun j => hV' j 0, fun i hi j => ?_⟩
      have := congrArg (fun f : Fin s → A => f 0) (hVag i hi j)
      simpa [hu] using this
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack (Fin s → A) (Fin ℓ) ι =>
      Pr_{let ω ← $ᵖ Ω}[genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ w ω])
    u

open Classical in
/-- **[Jo26] Theorem 4.4, hard half: `ε^gen_mca(G, C^⋈s, δ) ≤ ε^gen_mca(G, C, δ)` when
`|Ω| ≤ q`.** The bad-seed subspaces `K_ω` form a family of at most `q` proper subspaces,
so the covering lemma yields a single nonzero combination vector `λ` outside all of them;
the fixed base stack `λ·U` is then bad at every seed where the interleaved stack was bad
— same seed, same witness set. No averaging, no factor. -/
theorem epsMCAGen_interleaved_le_of_card_le (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) (hΩ : Fintype.card Ω ≤ Fintype.card F) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ epsMCAGen G (C : Set (ι → A)) δ := by
  classical
  unfold epsMCAGen
  refine iSup_le fun U => ?_
  obtain ⟨lam, _, hlamK⟩ := exists_nonzero_notMem_of_proper_family_of_card_le
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)) hΩ
    (fun ω => if h : genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω
      then tupleJointSubmodule C h.choose U else ⊥)
    (fun ω => by
      dsimp only
      split_ifs with h
      · exact tupleJointSubmodule_ne_top C U h.choose_spec.2.2
      · exact bot_ne_top)
  have h_imp : ∀ ω : Ω,
      genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) δ U ω →
      genMCAEvent G (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) ω := by
    intro ω h
    obtain ⟨hcard, hclose, _⟩ := h.choose_spec
    have hmem := hlamK ω
    rw [dif_pos h] at hmem
    exact genMCAEvent_base_of_notMem C G δ U hcard hclose hmem
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack A (Fin ℓ) ι =>
      Pr_{let ω ← $ᵖ Ω}[genMCAEvent G (C : Set (ι → A)) δ w ω])
    (fun j i => ∑ k, lam k • U j i k)

/-- **[Jo26] Theorem 4.4 (small-seed exactness).** When the seed set is no larger than
the field (`|Ω| ≤ q`), generator-MCA error is *exactly* invariant under `s`-fold
interleaving: `ε^gen_mca(G, C^⋈s, δ) = ε^gen_mca(G, C, δ)`. Combines the covering-lemma
half with the zero-row embedding. Instantiated at `Ω = F` and the affine-line / power
generators, this recovers (and generalizes) the in-tree
`ProximityGap.epsMCA_interleaved_eq`. -/
theorem epsMCAGen_interleaved_eq_of_card_le (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) (hΩ : Fintype.card Ω ≤ Fintype.card F) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ
      = epsMCAGen G (C : Set (ι → A)) δ :=
  le_antisymm (epsMCAGen_interleaved_le_of_card_le C s G δ hΩ)
    (epsMCAGen_le_epsMCAGen_interleaved C s G δ)

/-! ### Bridges to the in-tree MCA layers -/

/-- The affine-line generator `γ ↦ ![1, γ]` combines a two-row stack into the line
`u 0 + γ • u 1`. -/
theorem genComb_pairGen (u : WordStack A (Fin 2) ι) (γ : F) (i : ι) :
    genComb (fun γ : F => ![1, γ]) u γ i = u 0 i + γ • u 1 i := by
  simp [genComb, Fin.sum_univ_two]

/-- The generator-MCA bad event at the affine-line generator coincides with the in-tree
`ProximityGap.mcaEvent` ([ABF26] Definition 4.3). -/
theorem genMCAEvent_pairGen_iff (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F) :
    genMCAEvent (fun γ : F => ![1, γ]) C δ u γ
      ↔ ProximityGap.mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hagree⟩, hnopair⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩, fun hpa => hnopair ?_⟩
    · rw [hagree i hi]
      exact genComb_pairGen u γ i
    · exact (ProximityGapP.pairJointAgreesOnP_two_iff C S u).mpr hpa
  · rintro ⟨S, hcard, ⟨w, hw, hagree⟩, hnopair⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩, fun hpa => hnopair ?_⟩
    · rw [hagree i hi]
      exact (genComb_pairGen u γ i).symm
    · exact (ProximityGapP.pairJointAgreesOnP_two_iff C S u).mp hpa

/-- **Bridge (affine lines).** Generator-MCA error at the generator `γ ↦ ![1, γ]`
(seed set `Ω = F`) *equals* the in-tree MCA error `ProximityGap.epsMCA`
([ABF26] Definition 4.3). In particular [Jo26] Theorem 4.4 at this generator recovers
the exact interleaving invariance of `epsMCA`. -/
theorem epsMCAGen_pairGen_eq_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAGen (fun γ : F => ![1, γ]) C δ = ProximityGap.epsMCA (F := F) C δ := by
  unfold epsMCAGen ProximityGap.epsMCA
  exact iSup_congr fun u => Pr_congr fun γ => genMCAEvent_pairGen_iff C δ u γ

/-- **Affine-line exactness fence.**  Specializing the generator framework to
`γ ↦ ![1, γ]`, row-wise interleaving has exactly the original affine-line MCA
error.  Thus any general-generator interleaving improvement must use genuinely
larger or different seed geometry; on the affine-line surface there is no
interleaving-width loss to improve. -/
theorem epsMCAGen_pairGen_interleaved_eq_epsMCA (C : Submodule F (ι → A))
    (s : ℕ) [NeZero s] (δ : ℝ≥0) :
    epsMCAGen (F := F) (A := Fin s → A) (fun γ : F => ![1, γ])
        ((C : Set (ι → A))^⋈ (Fin s)) δ
      = ProximityGap.epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  rw [epsMCAGen_pairGen_eq_epsMCA, ProximityGap.epsMCA_interleaved_eq]

/-- The generator-MCA bad event at the power generator `γ ↦ (γ^{exp j})_j` coincides
with the general-`parℓ` event `ProximityGapP.mcaEventP`. Definitional: `genComb` at this
generator *is* `ProximityGapP.curveComb`. -/
theorem genMCAEvent_powGen_iff (C : Set (ι → A)) (exp : Fin ℓ → ℕ) (δ : ℝ≥0)
    (u : WordStack A (Fin ℓ) ι) (γ : F) :
    genMCAEvent (fun γ : F => fun j => γ ^ exp j) C δ u γ
      ↔ ProximityGapP.mcaEventP C exp δ u γ :=
  Iff.rfl

/-- **Bridge (power curves).** Generator-MCA error at the Reed–Solomon power generator
`γ ↦ (γ^{exp j})_j` (seed set `Ω = F`) *equals* the general-`parℓ` MCA error
`ProximityGapP.epsMCAP`. In particular [Jo26] Theorem 4.4 at this generator gives exact
interleaving invariance for `epsMCAP`, and Theorem 4.2 gives the factor bound for any
larger seed set. -/
theorem epsMCAGen_powGen_eq_epsMCAP (C : Set (ι → A)) (exp : Fin ℓ → ℕ) (δ : ℝ≥0) :
    epsMCAGen (fun γ : F => fun j => γ ^ exp j) C δ
      = ProximityGapP.epsMCAP (F := F) C exp δ := by
  unfold epsMCAGen ProximityGapP.epsMCAP
  exact iSup_congr fun u => Pr_congr fun γ => genMCAEvent_powGen_iff C exp δ u γ

/-! ### Canonical-curve bridges

The power-generator bridge above and `ProximityGapP.epsMCAP_val_eq_epsMCACurve` make the
fixed Vandermonde-curve API another specialization of the generator framework. These
lemmas close the triangle explicitly, so downstream code can move between the Jo26
generator theorem, the arbitrary-exponent `epsMCAP` theorem, and the older
`epsMCACurve` theorem without unfolding definitions. -/

/-- At the canonical exponent `j ↦ j`, the generator-MCA event is the fixed curve MCA
event `mcaEventCurve`. -/
theorem genMCAEvent_val_iff_mcaEventCurve (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin ℓ) ι) (γ : F) :
    genMCAEvent (fun γ : F => fun j : Fin ℓ => γ ^ (j : ℕ)) C δ u γ
      ↔ ProximityGap.mcaEventCurve C δ u γ := by
  rw [genMCAEvent_powGen_iff]
  exact ProximityGapP.mcaEventP_val_iff_mcaEventCurve C δ u γ

/-- Generator-MCA at the canonical power generator is exactly `epsMCACurve`. -/
theorem epsMCAGen_val_eq_epsMCACurve (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAGen (fun γ : F => fun j : Fin ℓ => γ ^ (j : ℕ)) C δ
      = ProximityGap.epsMCACurve (F := F) C ℓ δ := by
  rw [epsMCAGen_powGen_eq_epsMCAP,
    ProximityGapP.epsMCAP_val_eq_epsMCACurve]

/-- Reverse-orientation alias for callers starting from the fixed curve API. -/
theorem epsMCACurve_eq_epsMCAGen_val (C : Set (ι → A)) (δ : ℝ≥0) :
    ProximityGap.epsMCACurve (F := F) C ℓ δ =
      epsMCAGen (fun γ : F => fun j : Fin ℓ => γ ^ (j : ℕ)) C δ :=
  (epsMCAGen_val_eq_epsMCACurve (F := F) C δ).symm

/-- At two rows, the canonical power generator is another presentation of affine-line
MCA. This is the commuting-square version of `epsMCAGen_pairGen_eq_epsMCA`. -/
theorem epsMCAGen_val_two_eq_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAGen (ℓ := 2) (fun γ : F => fun j : Fin 2 => γ ^ (j : ℕ)) C δ
      = ProximityGap.epsMCA (F := F) C δ := by
  rw [epsMCAGen_val_eq_epsMCACurve,
    ProximityGap.epsMCACurve_two_eq_epsMCA]

/-- Event-level two-row version of `epsMCAGen_val_two_eq_epsMCA`. -/
theorem genMCAEvent_val_two_iff_mcaEvent (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F) :
    genMCAEvent (fun γ : F => fun j : Fin 2 => γ ^ (j : ℕ)) C δ u γ
      ↔ ProximityGap.mcaEvent C δ (u 0) (u 1) γ := by
  rw [genMCAEvent_val_iff_mcaEventCurve]
  exact ProximityGap.mcaEventCurve_pair_iff C δ u γ

/-- The fixed curve MCA error is exactly invariant under row-wise interleaving. This is
the `epsMCACurve` specialization of Jo26 exact small-seed interleaving invariance. -/
theorem epsMCACurve_interleaved_eq (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (L : ℕ) (δ : ℝ≥0) :
    ProximityGap.epsMCACurve (F := F) (A := Fin s → A)
        ((C : Set (ι → A))^⋈ (Fin s)) L δ
      = ProximityGap.epsMCACurve (F := F) (A := A) (C : Set (ι → A)) L δ := by
  rw [epsMCACurve_eq_epsMCAGen_val (F := F) (A := Fin s → A),
    epsMCACurve_eq_epsMCAGen_val (F := F) (A := A)]
  exact epsMCAGen_interleaved_eq_of_card_le C s
    (fun γ : F => fun j : Fin L => γ ^ (j : ℕ)) δ le_rfl

end ProximityGap.Jo26Gen

/-! ## Axiom audit -/
#print axioms ProximityGap.Jo26Gen.card_compl_proper_submodule_ge
#print axioms ProximityGap.Jo26Gen.tupleJointSubmodule_ne_top
#print axioms ProximityGap.Jo26Gen.genMCAEvent_base_of_notMem
#print axioms ProximityGap.Jo26Gen.exists_combination_count_bound
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_factor
#print axioms ProximityGap.Jo26Gen.exists_nonzero_notMem_of_proper_family_of_card_le
#print axioms ProximityGap.Jo26Gen.epsMCAGen_le_epsMCAGen_interleaved
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_of_card_le
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_eq_of_card_le
#print axioms ProximityGap.Jo26Gen.epsMCAGen_pairGen_eq_epsMCA
#print axioms ProximityGap.Jo26Gen.epsMCAGen_pairGen_interleaved_eq_epsMCA
#print axioms ProximityGap.Jo26Gen.epsMCAGen_powGen_eq_epsMCAP
#print axioms ProximityGap.Jo26Gen.genMCAEvent_val_iff_mcaEventCurve
#print axioms ProximityGap.Jo26Gen.epsMCAGen_val_eq_epsMCACurve
#print axioms ProximityGap.Jo26Gen.epsMCAGen_val_two_eq_epsMCA
#print axioms ProximityGap.Jo26Gen.epsMCACurve_interleaved_eq
