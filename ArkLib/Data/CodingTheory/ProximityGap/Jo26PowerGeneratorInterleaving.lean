/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorMCA
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGapP

/-!
# Interleaving stability for the power-generator MCA error — exact invariance

This file proves [Jo26] (ePrint 2026/891) Theorem 4.4 / Corollary 4.5 for the in-tree
**power-generator** mutual correlated agreement error `epsMCAP` (general `parℓ`, curve
combination `∑ⱼ γ^(exp j) • uⱼ`, seed set `Ω = F` so `|Ω| = q` automatically): the MCA
error is **exactly invariant** under row-wise interleaving,

  `ε_mcaP(C^≡t, exp, δ) = ε_mcaP(C, exp, δ)`.

This generalizes the affine-line (`Fin 2`) result `ProximityGap.epsMCA_interleaved_eq`
([`InterleavingStabilityMCA.lean`](InterleavingStabilityMCA.lean)) to arbitrary stack
width `parℓ` and arbitrary exponent maps `exp : Fin parℓ → ℕ` — in particular to the
Reed–Solomon power generator `exp j = j` used by `RSGenerator.genRSC`.  Since the power
generator's seeds are the field elements themselves, [Jo26] Theorem 4.4 applies with
**no** interleaving-width factor: the equality is exact, strictly sharper than the
generic [Jo26] Theorem 4.2 factor bound (also recorded here as a trivial corollary,
`epsMCAP_interleaved_le_factor`, issue #334 hypothesis K1).

## Proof shape ([Jo26] §3–4, mirrored from the `Fin 2` file)

* **Covering lemma** (`ProximityGap.exists_nonzero_notMem_of_proper_family`,
  [Jo26] Lemma 3.2): reused verbatim — at most `q = |F|` proper subspaces cannot
  cover `F^t`.
* **Bad-seed preservation** ([Jo26] Lemma 4.1, tuple case): for an interleaved
  `mcaEventP` at `γ` with witness `S`, the set `K_γ` of combination vectors `λ ∈ F^t`
  whose row-combination of the `parℓ`-stack admits a joint codeword tuple on `S` is a
  **proper subspace** (`jointTupleSubmodule` + `jointTupleSubmodule_ne_top`): were it
  everything, the standard basis vectors would give every row of the stack a joint tuple
  on `S`, which assembles column-by-column into an interleaved joint tuple — contradiction.
* **One `λ` for all seeds** ([Jo26] Theorem 4.4): the family `γ ↦ K_γ` is indexed by `F`
  itself, so the covering lemma yields a single nonzero `λ` outside every `K_γ`; the fixed
  `λ`-combined base stack is bad at every seed where the interleaved stack was — same `γ`,
  same witness set.  Key algebraic step: `λ`-combination commutes with the curve
  combination, `∑ₖ λₖ • (∑ⱼ γ^(exp j) • Uⱼ)ₖ = ∑ⱼ γ^(exp j) • (∑ₖ λₖ • Uⱼₖ)`.
* **Zero-row embedding** (`epsMCAP_le_epsMCAP_interleaved`, the easy `≥` half): a base
  bad stack embeds into the interleaved code with all rows but row `0` zero.

## Main results

* `jointTupleSubmodule` / `jointTupleSubmodule_ne_top` — the bad-seed subspace for
  `parℓ`-tuples and its properness ([Jo26] Lemma 4.1, tuple case).
* `epsMCAP_le_epsMCAP_interleaved` — `ε_mcaP(C, exp, δ) ≤ ε_mcaP(C^≡t, exp, δ)`.
* `epsMCAP_interleaved_le_epsMCAP` — `ε_mcaP(C^≡t, exp, δ) ≤ ε_mcaP(C, exp, δ)`.
* `epsMCAP_interleaved_eq` — **exact invariance** ([Jo26] Cor. 4.5, power-generator case).
* `epsMCAP_interleaved_le_factor` — the (weaker) [Jo26] Theorem 4.2 factor bound
  `ε_mcaP(C^≡t) ≤ (q^t−1)/(q^{t−1}(q−1)) · ε_mcaP(C)`, immediate from equality since the
  factor is `≥ 1`.

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891.  (Issue #334, hypothesis K1.)
* [KKH26] ePrint 2026/782 (context for issue #334).
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

namespace ProximityGapP

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The bad-seed subspace, tuple case ([Jo26] Lemma 4.1) -/

open Classical in
/-- The set of combination vectors `λ ∈ F^t` whose row-combinations of the interleaved
`parℓ`-stack `U` admit a joint codeword tuple on `S`.  Linearity of `C` makes this a
subspace: joint-tuple witnesses add, scale, and the zero combination is witnessed by the
zero tuple.  Generalizes `ProximityGap.jointPairSubmodule` from pairs to `parℓ`-tuples. -/
def jointTupleSubmodule (C : Submodule F (ι → A)) (S : Finset ι) {parℓ t : ℕ}
    (U : WordStack (Fin t → A) (Fin parℓ) ι) : Submodule F (Fin t → F) where
  carrier := {lam | pairJointAgreesOnP (C : Set (ι → A)) S
    (fun j i => ∑ k, lam k • U j i k)}
  zero_mem' := by
    refine ⟨fun _ => 0, fun _ => C.zero_mem, fun i hi j => ?_⟩
    simp
  add_mem' := by
    rintro lam lam' ⟨v, hv, hag⟩ ⟨w, hw, hag'⟩
    refine ⟨fun j => v j + w j, fun j => C.add_mem (hv j) (hw j), fun i hi j => ?_⟩
    have h1 : v j i = ∑ k, lam k • U j i k := hag i hi j
    have h2 : w j i = ∑ k, lam' k • U j i k := hag' i hi j
    show v j i + w j i = ∑ k, (lam + lam') k • U j i k
    rw [h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
  smul_mem' := by
    rintro c lam ⟨v, hv, hag⟩
    refine ⟨fun j => c • v j, fun j => C.smul_mem c (hv j), fun i hi j => ?_⟩
    have h1 : v j i = ∑ k, lam k • U j i k := hag i hi j
    show c • v j i = ∑ k, (c • lam) k • U j i k
    rw [h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, smul_smul, smul_eq_mul]

open Classical in
/-- **Properness of the bad-seed subspace** ([Jo26] Lemma 4.1, tuple case).  If every
combination vector admitted a joint tuple on `S`, then in particular every standard
basis vector would — i.e. every *row* of the interleaved stack `U` would admit a joint
tuple on `S` — and the row witnesses assemble column-by-column into a joint tuple for
the interleaved stack on `S`, contradicting the interleaved witness. -/
theorem jointTupleSubmodule_ne_top (C : Submodule F (ι → A)) {S : Finset ι} {parℓ t : ℕ}
    (U : WordStack (Fin t → A) (Fin parℓ) ι)
    (hnotuple : ¬ pairJointAgreesOnP ((C : Set (ι → A))^⋈ (Fin t)) S U) :
    jointTupleSubmodule C S U ≠ ⊤ := by
  intro htop
  apply hnotuple
  have hrow : ∀ k : Fin t, pairJointAgreesOnP (C : Set (ι → A)) S
      (fun j i => U j i k) := by
    intro k
    have hmem : (Pi.single k (1 : F)) ∈ jointTupleSubmodule C S U := by
      rw [htop]; trivial
    obtain ⟨v, hv, hag⟩ := hmem
    have hsum : ∀ (j : Fin parℓ) (i : ι),
        (∑ k', (Pi.single k (1 : F) : Fin t → F) k' • U j i k') = U j i k := by
      intro j i
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine ⟨v, hv, fun i hi j => ?_⟩
    have h1 : v j i = ∑ k', (Pi.single k (1 : F) : Fin t → F) k' • U j i k' :=
      hag i hi j
    show v j i = U j i k
    rw [h1, hsum j i]
  choose V hV hagree using hrow
  refine ⟨fun j i k => V k j i, fun j => ?_, fun i hi j => ?_⟩
  · intro k
    exact hV k j
  · funext k
    exact hagree k i hi j

/-! ### The easy direction: zero-row embedding -/

open Classical in
/-- **`ε_mcaP(C, exp, δ) ≤ ε_mcaP(C^≡t, exp, δ)`** ([Jo26] Theorem 4.2, lower half,
power-generator case).  Embedding a base `parℓ`-stack into the interleaved code via the
zero-row embedding (row `0` of every interleaved symbol carries the stack, all other rows
are `0`) maps every base `mcaEventP` witness to an interleaved one, with the same witness
set `S` and the same seed `γ`. -/
theorem epsMCAP_le_epsMCAP_interleaved (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ
      ≤ epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ := by
  classical
  unfold epsMCAP
  apply iSup_le
  intro v
  set u : WordStack (Fin t → A) (Fin parℓ) ι :=
    fun j i k => if k = (0 : Fin t) then v j i else 0 with hu
  have h_imp : ∀ γ : F, mcaEventP (C : Set (ι → A)) exp δ v γ →
      mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ := by
    rintro γ ⟨S, hcard, ⟨w, hw, hagree⟩, hnotuple⟩
    refine ⟨S, hcard, ?_, ?_⟩
    · refine ⟨fun i k => if k = (0 : Fin t) then w i else 0, ?_, ?_⟩
      · intro k
        show (fun i => if k = (0 : Fin t) then w i else 0) ∈ (C : Set (ι → A))
        by_cases hk : k = 0
        · subst hk; simpa using hw
        · simp only [if_neg hk]; exact C.zero_mem
      · intro i hi
        funext k
        show (if k = (0 : Fin t) then w i else 0) = curveComb exp u γ i k
        have hc : curveComb (A := Fin t → A) exp u γ i k
            = ∑ j, γ ^ exp j • u j i k := by
          simp only [curveComb, Finset.sum_apply, Pi.smul_apply]
        rw [hc]
        by_cases hk : k = 0
        · subst hk
          rw [if_pos rfl, hagree i hi]
          show curveComb exp v γ i = ∑ j, γ ^ exp j • u j i 0
          simp [curveComb, hu]
        · rw [if_neg hk]
          simp [hu, hk]
    · rintro ⟨V, hVmem, hVag⟩
      apply hnotuple
      have hVmem' : ∀ j, ∀ k : Fin t, (fun i => V j i k) ∈ (C : Set (ι → A)) := hVmem
      refine ⟨fun j i => V j i 0, fun j => hVmem' j 0, fun i hi j => ?_⟩
      have h := congrArg (fun f : Fin t → A => f 0) (hVag i hi j)
      show V j i 0 = v j i
      simpa [hu] using h
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack (Fin t → A) (Fin parℓ) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ w γ])
    u

/-! ### The hard direction: one combination vector preserves every bad seed -/

open Classical in
/-- **`ε_mcaP(C^≡t, exp, δ) ≤ ε_mcaP(C, exp, δ)`** ([Jo26] Theorem 4.4, power-generator
case).  The bad-seed subspaces `K_γ` are indexed by the seed set `F` itself, so the
covering lemma provides a single nonzero combination vector `λ` outside all of them; the
fixed `λ`-combined base stack is then bad at every seed where the interleaved stack was
bad — same `γ`, same witness set.  No averaging, no union bound, no interleaving-width
factor. -/
theorem epsMCAP_interleaved_le_epsMCAP (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ
      ≤ epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ := by
  classical
  unfold epsMCAP
  apply iSup_le
  intro u
  -- the per-seed bad subspace (⊥ off the bad-seed set)
  obtain ⟨lam, hlam0, hlamK⟩ := ProximityGap.exists_nonzero_notMem_of_proper_family
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne t))
    (fun γ => if h : mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ
      then jointTupleSubmodule C h.choose u else ⊥)
    (fun γ => by
      dsimp only
      split_ifs with h
      · exact jointTupleSubmodule_ne_top C u h.choose_spec.2.2
      · exact bot_ne_top)
  -- the λ-combined base stack
  set v : WordStack A (Fin parℓ) ι := fun j i => ∑ k, lam k • u j i k with hv
  have h_imp : ∀ γ : F,
      mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ →
      mcaEventP (C : Set (ι → A)) exp δ v γ := by
    intro γ h
    obtain ⟨hcard, ⟨w, hwmem, hwagree⟩, hnotuple⟩ := h.choose_spec
    refine ⟨h.choose, hcard, ?_, ?_⟩
    · -- closeness: the λ-combination of the rows of `w`
      refine ⟨fun i => ∑ k, lam k • w i k, ?_, ?_⟩
      · have hrows : ∀ k : Fin t, (fun i => w i k) ∈ (C : Set (ι → A)) := hwmem
        have heq : (fun i => ∑ k, lam k • w i k)
            = ∑ k, lam k • (fun i => w i k) := by
          funext i
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun k _ => rfl
        rw [heq]
        exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hrows k)
      · intro i hi
        have hw := hwagree i hi
        have hpt : ∀ k : Fin t, w i k = ∑ j, γ ^ exp j • u j i k := by
          intro k
          have := congrArg (fun f : Fin t → A => f k) hw
          simpa [curveComb, Finset.sum_apply, Pi.smul_apply] using this
        calc (fun i => ∑ k, lam k • w i k) i = ∑ k, lam k • w i k := rfl
          _ = ∑ k, lam k • ∑ j, γ ^ exp j • u j i k :=
              Finset.sum_congr rfl fun k _ => by rw [hpt k]
          _ = ∑ k, ∑ j, lam k • (γ ^ exp j • u j i k) :=
              Finset.sum_congr rfl fun k _ => Finset.smul_sum
          _ = ∑ j, ∑ k, lam k • (γ ^ exp j • u j i k) := Finset.sum_comm
          _ = ∑ j, γ ^ exp j • ∑ k, lam k • u j i k := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun k _ => by
                rw [smul_smul, smul_smul, mul_comm]
          _ = curveComb exp v γ i := rfl
    · -- no joint tuple: exactly `lam ∉ K_γ`
      intro htuple
      have hmem := hlamK γ
      rw [dif_pos h] at hmem
      exact hmem htuple
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack A (Fin parℓ) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventP (C : Set (ι → A)) exp δ w γ])
    v

/-! ### The headline: exact invariance -/

/-- **[Jo26] Corollary 4.5 (power-generator case): the general-`parℓ` MCA error is
exactly invariant under row-wise interleaving.**  `ε_mcaP(C^≡t, exp, δ) = ε_mcaP(C, exp, δ)`.
The power generator's seed set is `F` itself (`|Ω| = q`), so [Jo26] Theorem 4.4 applies
with no interleaving-width factor: interleaving is **free** for power-generator mutual
correlated agreement, at every stack width `parℓ` and every exponent map `exp`.
Issue #334, hypothesis K1. -/
theorem epsMCAP_interleaved_eq (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ
      = epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ :=
  le_antisymm (epsMCAP_interleaved_le_epsMCAP C exp t δ)
    (epsMCAP_le_epsMCAP_interleaved C exp t δ)

/-- **Power-generator exactness fence.**  The generic generator-MCA layer, specialized to
the Reed-Solomon power generator `γ ↦ (γ ^ exp j)_j`, agrees after row-wise interleaving
with the original in-tree `epsMCAP` error.  This is the power-generator analogue of the
affine-line fence in `Jo26GeneratorMCA.lean`: the generic framework adds no hidden
interleaving loss on the canonical power-generator surface. -/
theorem epsMCAGen_powGen_interleaved_eq_epsMCAP (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    ProximityGap.Jo26Gen.epsMCAGen (F := F) (A := Fin t → A) (Ω := F) (ℓ := parℓ)
        (fun γ : F => fun j : Fin parℓ => γ ^ exp j)
        ((C : Set (ι → A))^⋈ (Fin t)) δ
      = epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ := by
  rw [ProximityGap.Jo26Gen.epsMCAGen_powGen_eq_epsMCAP, epsMCAP_interleaved_eq]

/-! ### The [Jo26] Theorem 4.2 factor bound, as a corollary of equality -/

/-- **[Jo26] Theorem 4.2 factor bound (power-generator case), from exact invariance.**
`ε_mcaP(C^≡t, exp, δ) ≤ (q^t − 1)/(q^{t−1}(q−1)) · ε_mcaP(C, exp, δ)`.  Trivial from
`epsMCAP_interleaved_eq`: the generic [Jo26] Theorem 4.2 factor is `≥ 1` (in ℕ,
`q^{t−1}(q−1) = q^t − q^{t−1} ≤ q^t − 1`), so equality is strictly sharper. -/
theorem epsMCAP_interleaved_le_factor (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ
      ≤ ((Fintype.card F ^ t - 1 : ℝ≥0∞)
          / (Fintype.card F ^ (t - 1) * (Fintype.card F - 1)))
        * epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ := by
  rw [epsMCAP_interleaved_eq C exp t δ]
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set q : ℕ := Fintype.card F with hqdef
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (NeZero.ne t)
  -- numerator and denominator as casts of their ℕ values
  have hnum : ((q : ℝ≥0∞) ^ t - 1) = ((q ^ t - 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_one]
  have hden : ((q : ℝ≥0∞) ^ (t - 1) * ((q : ℝ≥0∞) - 1))
      = ((q ^ (t - 1) * (q - 1) : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_pow, ENNReal.natCast_sub, Nat.cast_one]
  have hdpos : 0 < q ^ (t - 1) * (q - 1) :=
    Nat.mul_pos (pow_pos (by omega) _) (by omega)
  -- the ℕ inequality: q^{t−1}(q−1) ≤ q^t − 1
  have hnat : q ^ (t - 1) * (q - 1) ≤ q ^ t - 1 := by
    have h2 : q ^ (t - 1) * q = q ^ t := by
      rw [← pow_succ]
      congr 1
      omega
    have hp1 : 1 ≤ q ^ (t - 1) := Nat.one_le_pow _ _ (by omega)
    have key : q ^ (t - 1) * (q - 1) + q ^ (t - 1) = q ^ t := by
      have h3 : q ^ (t - 1) * (q - 1) + q ^ (t - 1)
          = q ^ (t - 1) * (q - 1 + 1) := by ring
      rw [h3, Nat.sub_add_cancel (by omega), h2]
    omega
  -- the factor is ≥ 1
  have hfac : (1 : ℝ≥0∞)
      ≤ ((q : ℝ≥0∞) ^ t - 1) / ((q : ℝ≥0∞) ^ (t - 1) * ((q : ℝ≥0∞) - 1)) := by
    rw [hnum, hden, ENNReal.le_div_iff_mul_le
      (Or.inl (by exact_mod_cast hdpos.ne'))
      (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hnat
  calc epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ
      = 1 * epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ := (one_mul _).symm
    _ ≤ _ := mul_le_mul' hfac le_rfl

end ProximityGapP

/-! ## Axiom audit -/
#print axioms ProximityGapP.jointTupleSubmodule_ne_top
#print axioms ProximityGapP.epsMCAP_le_epsMCAP_interleaved
#print axioms ProximityGapP.epsMCAP_interleaved_le_epsMCAP
#print axioms ProximityGapP.epsMCAP_interleaved_eq
#print axioms ProximityGapP.epsMCAGen_powGen_interleaved_eq_epsMCAP
#print axioms ProximityGapP.epsMCAP_interleaved_le_factor
