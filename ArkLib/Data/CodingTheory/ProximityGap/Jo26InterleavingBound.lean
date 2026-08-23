/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneratorMCA
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceAvoidance
import Mathlib

/-!
# [Jo26] Theorem 4.2: the field-size-weighted generator-MCA interleaving bound

This file proves [Jo26] (ePrint 2026/891) Theorem 4.2 on the generator-MCA surface of
[`GeneratorMCA.lean`](GeneratorMCA.lean):

  `ε_G(C, δ) ≤ ε_G(C^≡s, δ) ≤ A(q,s) · ε_G(C, δ)`,
  `A(q,s) = (q^s − 1)/(q^{s−1}(q−1))`.

## Proof shape

* **Lemma 4.1** (`jo26_mcaWitnessG_combine` / `jo26_bad_seed_preservation`): if `ω` is
  `G`-MCA-bad for an interleaved stack `U` with witness `T`, then every combination
  vector `λ` outside the bad-combiner subspace `K = jointStackSubmodule C T U`
  (proper, by `jointStackSubmodule_ne_top`) keeps `ω` `G`-MCA-bad for the row-combined
  base stack `(j, i) ↦ ∑ₖ λₖ • U j i k`, with the *same* witness `T`: the
  row-combination of the interleaved line codeword is a base codeword by linearity, and
  the non-joint-agreement clause *is* `λ ∉ K` by construction.
* **Lower half** (`jo26_epsMCAG_le_interleaved`): the zero-padding embedding (row `0`
  carries the base stack, rows `1..s−1` are `0`; uses `0 ∈ C`) transports every base
  bad seed to an interleaved one, with the same witness and the same coefficients.
* **Upper half**: pure counting (`jo26_bad_count_core`) — every bad seed survives at
  least `q^s − q^{s−1}` of the `q^s − 1` nonzero combiners
  (`SubspaceAvoidance.card_nonzero_avoiding_ge`; vectors avoiding `K` are automatically
  nonzero since `0 ∈ K`), so by double counting
  (`SubspaceAvoidance.exists_avoiding_count_ge`) one combiner preserves a
  `(q^s − q^{s−1})/(q^s − 1)` fraction of the bad set.  The `ENNReal` assembly
  (`jo26_interleaved_mul_le_epsMCAG`, multiplied headline; division corollary
  `jo26_interleaved_le_A_mul_epsMCAG`) converts the uniform-seed probability into a
  filter-card ratio via `prob_uniform_eq_card_filter_div_card`.

## Main results

* `jo26_mcaWitnessG_combine` — [Jo26] Lemma 4.1, witness level.
* `jo26_bad_seed_preservation` — [Jo26] Lemma 4.1, event level (with properness).
* `jo26_epsMCAG_le_interleaved` — Theorem 4.2, lower half.
* `jo26_bad_count_core` — Theorem 4.2 upper half, pure-counting core (in `ℕ`).
* `jo26_interleaved_mul_le_epsMCAG` — Theorem 4.2 upper half, multiplied form:
  `(q^s − q^{s−1}) · ε_G(C^≡s, δ) ≤ (q^s − 1) · ε_G(C, δ)`.
* `jo26_interleaved_le_A_mul_epsMCAG` — Theorem 4.2 upper half, divided form with
  `A(q,s) = (q^s − 1)/(q^{s−1}(q−1))`.
* `jo26_generator_interleaving_bound` — the two-sided Theorem 4.2 package.

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891.
-/

namespace ProximityGap

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### [Jo26] Lemma 4.1: bad-seed preservation under row combination -/

/-- **[Jo26] Lemma 4.1, witness level.**  If `T` is a `G`-MCA witness for the
interleaved stack `U` at coefficients `coeffs`, then for every combination vector
`λ ∉ jointStackSubmodule C T U` the *same* `T` is a `G`-MCA witness (over the base code
`C`) for the row-combined stack `(j, i) ↦ ∑ₖ λₖ • U j i k`, at the same `coeffs`:

* the size clause is literally the same;
* the line clause transfers by linearity — the `λ`-combination of the columns of the
  interleaved line codeword is a base codeword agreeing with the combined line on `T`;
* the non-joint-agreement clause **is** `λ ∉ jointStackSubmodule C T U`. -/
theorem jo26_mcaWitnessG_combine (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ}
    {U : Fin l → ι → Fin s → A} {coeffs : Fin l → F} {T : Finset ι}
    (hW : mcaWitnessG ((C : Set (ι → A))^⋈ (Fin s)) δ U coeffs T)
    {lam : Fin s → F} (hlam : lam ∉ jointStackSubmodule C T U) :
    mcaWitnessG (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) coeffs T := by
  obtain ⟨hcard, ⟨w, hwmem, hwagree⟩, _hno⟩ := hW
  refine ⟨hcard, ?_, ?_⟩
  · -- the λ-combination of the columns of `w`
    refine ⟨fun i => ∑ k, lam k • w i k, ?_, ?_⟩
    · have hrows : ∀ k : Fin s, (fun i => w i k) ∈ (C : Set (ι → A)) := hwmem
      have heq : (fun i => ∑ k, lam k • w i k)
          = ∑ k, lam k • (fun i => w i k) := by
        funext i
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun k _ => rfl
      rw [heq]
      exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hrows k)
    · intro i hi
      have hpt : ∀ k : Fin s, w i k = ∑ j, coeffs j • U j i k := by
        intro k
        calc w i k = (∑ j, coeffs j • U j i) k := congrFun (hwagree i hi) k
          _ = ∑ j, coeffs j • U j i k := by
              rw [Finset.sum_apply]
              exact Finset.sum_congr rfl fun j _ => rfl
      show (∑ k, lam k • w i k) = ∑ j, coeffs j • ∑ k, lam k • U j i k
      calc (∑ k, lam k • w i k)
          = ∑ k, lam k • ∑ j, coeffs j • U j i k :=
            Finset.sum_congr rfl fun k _ => by rw [hpt k]
        _ = ∑ k, ∑ j, lam k • (coeffs j • U j i k) :=
            Finset.sum_congr rfl fun k _ => Finset.smul_sum
        _ = ∑ j, ∑ k, lam k • (coeffs j • U j i k) := Finset.sum_comm
        _ = ∑ j, coeffs j • ∑ k, lam k • U j i k := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by
              rw [smul_smul, smul_smul, mul_comm]
  · -- non-joint-agreement is exactly `lam ∉ K`
    exact fun hstack => hlam hstack

/-- **[Jo26] Lemma 4.1, event level.**  For each `G`-MCA-bad seed (w.r.t. the
interleaved code) there is a witness `T` whose bad-combiner subspace
`K = jointStackSubmodule C T U` is **proper**, and every `λ ∉ K` keeps the seed
`G`-MCA-bad for the row-combined base stack. -/
theorem jo26_bad_seed_preservation (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ}
    (U : Fin l → ι → Fin s → A) (coeffs : Fin l → F)
    (h : mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U coeffs) :
    ∃ T : Finset ι, mcaWitnessG ((C : Set (ι → A))^⋈ (Fin s)) δ U coeffs T ∧
      jointStackSubmodule C T U ≠ ⊤ ∧
      ∀ lam : Fin s → F, lam ∉ jointStackSubmodule C T U →
        mcaEventG (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) coeffs := by
  obtain ⟨T, hW⟩ := h
  exact ⟨T, hW, jointStackSubmodule_ne_top C U hW.2.2,
    fun lam hlam => ⟨T, jo26_mcaWitnessG_combine C δ hW hlam⟩⟩

/-! ### Theorem 4.2, lower half: zero-padding embedding -/

open Classical in
/-- **[Jo26] Theorem 4.2, lower half.**  `ε_G(C, δ) ≤ ε_G(C^≡s, δ)`: embedding a base
stack into the interleaved code via the zero-padding embedding (row `0` carries the
stack, all other rows are `0`; uses `0 ∈ C`) maps every base `G`-MCA witness to an
interleaved one, with the same witness set and the same coefficients `G ω`. -/
theorem jo26_epsMCAG_le_interleaved (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (δ : ℝ≥0) {l : ℕ} {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F) :
    epsMCAG (A := A) (C : Set (ι → A)) δ G
      ≤ epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G := by
  classical
  unfold epsMCAG
  apply iSup_le
  intro v
  set u : WordStack (Fin s → A) (Fin l) ι :=
    fun j i k => if k = (0 : Fin s) then v j i else 0 with hu
  have h_imp : ∀ ω : Ω, mcaEventG (C : Set (ι → A)) δ v (G ω) →
      mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ u (G ω) := by
    rintro ω ⟨T, hcard, ⟨w, hw, hagree⟩, hno⟩
    refine ⟨T, hcard, ?_, ?_⟩
    · -- zero-padded line codeword
      refine ⟨fun i k => if k = (0 : Fin s) then w i else 0, ?_, ?_⟩
      · intro k
        change (fun i => if k = (0 : Fin s) then w i else 0) ∈ (C : Set (ι → A))
        by_cases hk : k = 0
        · subst hk; simpa using hw
        · simp only [if_neg hk]; exact C.zero_mem
      · intro i hi
        funext k
        have hsumk : (∑ j, G ω j • u j i) k = ∑ j, G ω j • u j i k := by
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun j _ => rfl
        rw [hsumk]
        by_cases hk : k = 0
        · subst hk
          simpa [hu] using hagree i hi
        · simp [hu, hk]
    · -- joint agreement of the padded stack collapses at column 0
      rintro ⟨cs, hcs, hag⟩
      apply hno
      refine ⟨fun j i => cs j i 0, fun j => ?_, fun i hi j => ?_⟩
      · have hcols : ∀ k : Fin s, (fun i => cs j i k) ∈ (C : Set (ι → A)) := hcs j
        exact hcols 0
      · have h := congrFun (hag i hi j) 0
        simpa [hu] using h
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun U : WordStack (Fin s → A) (Fin l) ι =>
      Pr_{let ω ← $ᵖ Ω}[mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)])
    u

/-! ### Theorem 4.2, upper half: the counting core -/

open Classical in
/-- **[Jo26] Theorem 4.2, upper half — pure-counting core (in `ℕ`).**  For a fixed
interleaved stack `U`: some single nonzero combiner `λ` preserves at least a
`(q^s − q^{s−1})/(q^s − 1)` fraction of the bad-seed set,

  `#B · (q^s − q^{s−1}) ≤ #{ω | λ-combined stack bad} · (q^s − 1)`,

where `B` is the set of `G`-MCA-bad seeds for `U` over the interleaved code.  Each
`ω ∈ B` survives at least `q^s − q^{s−1}` of the `q^s − 1` nonzero combiners
(avoidance of the proper subspace `K_ω` from Lemma 4.1 — avoiding vectors are nonzero
since `0 ∈ K_ω`), and double counting produces the single `λ`. -/
theorem jo26_bad_count_core (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ} (hs : 1 ≤ s)
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin s → A) :
    ∃ lam : Fin s → F, lam ≠ 0 ∧
      (univ.filter (fun ω : Ω =>
          mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω))).card
          * (Fintype.card F ^ s - Fintype.card F ^ (s - 1))
        ≤ (univ.filter (fun ω : Ω => mcaEventG (C : Set (ι → A)) δ
              (fun j i => ∑ k, lam k • U j i k) (G ω))).card
          * (Fintype.card F ^ s - 1) := by
  classical
  set B : Finset Ω := univ.filter (fun ω : Ω =>
    mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)) with hB
  set Λ : Finset (Fin s → F) := univ.filter (fun lam => lam ≠ 0) with hΛdef
  have hΛne : Λ.Nonempty := by
    refine ⟨Pi.single ⟨0, hs⟩ (1 : F), ?_⟩
    rw [hΛdef, mem_filter]
    refine ⟨mem_univ _, fun h0 => ?_⟩
    have := congrFun h0 ⟨0, hs⟩
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  have hΛcard : Λ.card = Fintype.card F ^ s - 1 := by
    have hΛerase : Λ = univ.erase (0 : Fin s → F) := by
      ext x
      simp [hΛdef]
    rw [hΛerase, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
  -- every bad seed survives at least `q^s − q^{s−1}` nonzero combiners
  have hsurv : ∀ ω ∈ B, Fintype.card F ^ s - Fintype.card F ^ (s - 1)
      ≤ (Λ.filter (fun lam : Fin s → F => mcaEventG (C : Set (ι → A)) δ
          (fun j i => ∑ k, lam k • U j i k) (G ω))).card := by
    intro ω hω
    rw [hB, mem_filter] at hω
    obtain ⟨T, _hW, hKne, hpres⟩ := jo26_bad_seed_preservation C δ U (G ω) hω.2
    refine le_trans
      (SubspaceAvoidance.card_nonzero_avoiding_ge (jointStackSubmodule C T U) hKne)
      (Finset.card_le_card ?_)
    intro lam hlam
    rw [mem_filter] at hlam
    have hnotK : lam ∉ jointStackSubmodule C T U := hlam.2
    rw [mem_filter]
    refine ⟨?_, hpres lam hnotK⟩
    rw [hΛdef, mem_filter]
    exact ⟨mem_univ _,
      fun h0 => hnotK (h0 ▸ (jointStackSubmodule C T U).zero_mem)⟩
  -- double counting: one combiner preserves the stated fraction
  obtain ⟨lam, hlamΛ, hcount⟩ := SubspaceAvoidance.exists_avoiding_count_ge B Λ hΛne
    (fun ω lam => mcaEventG (C : Set (ι → A)) δ
      (fun j i => ∑ k, lam k • U j i k) (G ω))
    (Fintype.card F ^ s - Fintype.card F ^ (s - 1)) hsurv
  refine ⟨lam, ?_, ?_⟩
  · rw [hΛdef, mem_filter] at hlamΛ
    exact hlamΛ.2
  · refine le_trans hcount ?_
    rw [hΛcard]
    exact Nat.mul_le_mul_right _ (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.subset_univ B)))

/-! ### Theorem 4.2, upper half: the `ENNReal` assembly -/

open Classical in
/-- **[Jo26] Theorem 4.2, upper half (multiplied headline).**

  `(q^s − q^{s−1}) · ε_G(C^≡s, δ) ≤ (q^s − 1) · ε_G(C, δ)`.

Stated multiplicatively to keep the `ENNReal` arithmetic division-free; the divided
form with `A(q,s)` is `jo26_interleaved_le_A_mul_epsMCAG`.  Per interleaved stack `U`,
the uniform-seed probabilities are filter-card ratios over `|Ω|`
(`prob_uniform_eq_card_filter_div_card`), and the counting core supplies the numerator
inequality at the `λ`-combined base stack, which then sits below the base supremum. -/
theorem jo26_interleaved_mul_le_epsMCAG (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (δ : ℝ≥0) {l : ℕ} {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F) :
    ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ENNReal)
        * epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
      ≤ ((Fintype.card F ^ s - 1 : ℕ) : ENNReal)
        * epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  classical
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  unfold epsMCAG
  rw [ENNReal.mul_iSup]
  refine iSup_le fun U => ?_
  obtain ⟨lam, _hlam0, hcore⟩ := jo26_bad_count_core C δ hs G U
  set v : WordStack A (Fin l) ι := fun j i => ∑ k, lam k • U j i k with hv
  set B₁ : Finset Ω := univ.filter (fun ω : Ω =>
    mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)) with hB₁
  set B₂ : Finset Ω := univ.filter (fun ω : Ω =>
    mcaEventG (C : Set (ι → A)) δ v (G ω)) with hB₂
  have hPrInt : Pr_{let ω ← $ᵖ Ω}[mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)]
      = (B₁.card : ENNReal) / (Fintype.card Ω : ENNReal) := by
    rw [prob_uniform_eq_card_filter_div_card, hB₁]
    simp only [ENNReal.coe_natCast]
  have hPrBase : Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ v (G ω)]
      = (B₂.card : ENNReal) / (Fintype.card Ω : ENNReal) := by
    rw [prob_uniform_eq_card_filter_div_card, hB₂]
    simp only [ENNReal.coe_natCast]
  set m : ℕ := Fintype.card F ^ s - Fintype.card F ^ (s - 1) with hm
  set c : ℕ := Fintype.card F ^ s - 1 with hc
  calc (m : ENNReal)
        * Pr_{let ω ← $ᵖ Ω}[mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)]
      = (m : ENNReal) * ((B₁.card : ENNReal) / (Fintype.card Ω : ENNReal)) := by
        rw [hPrInt]
    _ = ((B₁.card * m : ℕ) : ENNReal) / (Fintype.card Ω : ENNReal) := by
        rw [Nat.cast_mul, mul_comm ((B₁.card : ℕ) : ENNReal) ((m : ℕ) : ENNReal),
          mul_div_assoc]
    _ ≤ ((B₂.card * c : ℕ) : ENNReal) / (Fintype.card Ω : ENNReal) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcore) _
    _ = (c : ENNReal) * ((B₂.card : ENNReal) / (Fintype.card Ω : ENNReal)) := by
        rw [Nat.cast_mul, mul_comm ((B₂.card : ℕ) : ENNReal) ((c : ℕ) : ENNReal),
          mul_div_assoc]
    _ = (c : ENNReal) * Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ v (G ω)] := by
        rw [hPrBase]
    _ ≤ (c : ENNReal) * ⨆ f : WordStack A (Fin l) ι,
          Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ f (G ω)] :=
        mul_le_mul' le_rfl (le_iSup
          (fun f : WordStack A (Fin l) ι =>
            Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ f (G ω)]) v)

/-- The `ℕ` identity behind the `A(q,s)` denominator:
`q^{s−1}(q − 1) = q^s − q^{s−1}` (for `1 ≤ s`). -/
theorem jo26_denominator_eq {q : ℕ} (s : ℕ) (hs : 1 ≤ s) :
    q ^ (s - 1) * (q - 1) = q ^ s - q ^ (s - 1) := by
  rw [Nat.mul_sub, mul_one, ← pow_succ]
  congr 2
  omega

open Classical in
/-- **[Jo26] Theorem 4.2, upper half (divided form).**

  `ε_G(C^≡s, δ) ≤ A(q,s) · ε_G(C, δ)`,  `A(q,s) = (q^s − 1)/(q^{s−1}(q−1))`.

Follows from the multiplied headline since `q^{s−1}(q−1) = q^s − q^{s−1}` is nonzero
(`q ≥ 2` in a finite field, `s ≥ 1`) and finite in `ENNReal`. -/
theorem jo26_interleaved_le_A_mul_epsMCAG (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (δ : ℝ≥0) {l : ℕ} {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F) :
    epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
      ≤ (((Fintype.card F ^ s - 1 : ℕ) : ENNReal)
            / ((Fintype.card F ^ (s - 1) * (Fintype.card F - 1) : ℕ) : ENNReal))
        * epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [jo26_denominator_eq s hs]
  have hmpos : 0 < Fintype.card F ^ s - Fintype.card F ^ (s - 1) := by
    have hlt : Fintype.card F ^ (s - 1) < Fintype.card F ^ s :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hm0 : ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast hmpos.ne'
  have hmtop : ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hmain := jo26_interleaved_mul_le_epsMCAG (A := A) C s δ G
  have hdivmul : ((Fintype.card F ^ s - 1 : ℕ) : ENNReal)
        / ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ENNReal)
        * epsMCAG (A := A) (C : Set (ι → A)) δ G
      = (((Fintype.card F ^ s - 1 : ℕ) : ENNReal)
          * epsMCAG (A := A) (C : Set (ι → A)) δ G)
        / ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ENNReal) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [hdivmul, ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop), mul_comm]
  exact hmain

/-! ### The two-sided Theorem 4.2 package -/

/-- **[Jo26] Theorem 4.2 (two-sided).**  The generator-MCA error is interleaving-stable
up to the field-size factor `A(q,s) = (q^s − 1)/(q^{s−1}(q−1))`:

  `ε_G(C, δ) ≤ ε_G(C^≡s, δ) ≤ A(q,s) · ε_G(C, δ)`. -/
theorem jo26_generator_interleaving_bound (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (δ : ℝ≥0) {l : ℕ} {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F) :
    epsMCAG (A := A) (C : Set (ι → A)) δ G
        ≤ epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G ∧
      epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
        ≤ (((Fintype.card F ^ s - 1 : ℕ) : ENNReal)
              / ((Fintype.card F ^ (s - 1) * (Fintype.card F - 1) : ℕ) : ENNReal))
          * epsMCAG (A := A) (C : Set (ι → A)) δ G :=
  ⟨jo26_epsMCAG_le_interleaved C s δ G, jo26_interleaved_le_A_mul_epsMCAG C s δ G⟩

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.jo26_mcaWitnessG_combine
#print axioms ProximityGap.jo26_bad_seed_preservation
#print axioms ProximityGap.jo26_epsMCAG_le_interleaved
#print axioms ProximityGap.jo26_bad_count_core
#print axioms ProximityGap.jo26_interleaved_mul_le_epsMCAG
#print axioms ProximityGap.jo26_denominator_eq
#print axioms ProximityGap.jo26_interleaved_le_A_mul_epsMCAG
#print axioms ProximityGap.jo26_generator_interleaving_bound
