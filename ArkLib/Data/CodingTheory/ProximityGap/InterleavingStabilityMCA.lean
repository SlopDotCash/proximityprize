/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib

/-!
# Interleaving stability for mutual correlated agreement — exact invariance

This file formalizes the headline MCA result of [Jo26] (ePrint 2026/891): for the
affine-line generator (seed set `Ω = F`, so `|Ω| ≤ q` automatically), the MCA error is
**exactly invariant** under row-wise interleaving:

  `ε_mca(C^≡t, δ) = ε_mca(C, δ)`.

This upgrades the in-tree union bound `epsMCA_interleaved_le`
(`ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`, [ABF26] Lemma 4.7) to equality, removing the linear
interleaving-width factor from every downstream analysis — in particular every
`δ*`-bracket recorded in the threshold ledger (issue #232) is interleaving-stable.

## Proof shape ([Jo26] §3–4, small-seed case)

* **Covering lemma** (`exists_nonzero_notMem_of_proper_family`, [Jo26] Lemma 3.2): at most
  `q = |F|` proper subspaces of `F^t` cannot cover it — each proper subspace has at most
  `q^{t−1}` points and they share `0`, so the union has at most `1 + q(q^{t−1}−1) < q^t`
  points.
* **Bad-seed preservation** ([Jo26] Lemma 4.1): for an interleaved `mcaEvent` at `γ` with
  witness `S`, the set `K_γ` of combination vectors `λ` whose row-combination admits a
  joint codeword pair on `S` is a **proper subspace** of `F^t` (`jointPairSubmodule` +
  `jointPairSubmodule_ne_top`): if it were everything, the standard basis vectors would
  give every row a joint pair on `S`, which assembles column-by-column into an interleaved
  joint pair on `S` — contradicting the witness.  Every `λ ∉ K_γ` therefore transports the
  bad event to the base code at the same `γ`, same `S`.
* **One `λ` for all seeds** ([Jo26] Theorem 4.4): the family `γ ↦ K_γ` is indexed by `F`
  itself, so the covering lemma yields a single nonzero `λ` avoiding **every** `K_γ`
  simultaneously; the fixed base stack `λ·u` is then bad at every `γ` where the
  interleaved stack was bad, giving `ε_mca(C^≡t, δ) ≤ ε_mca(C, δ)`
  (`epsMCA_interleaved_le_epsMCA`) with **no averaging and no union bound**.
* **Zero-row embedding** (`epsMCA_le_epsMCA_interleaved`, the easy `≥` half): a base bad
  stack embeds into the interleaved code with all rows but row `0` zero.

## Main results

* `exists_nonzero_notMem_of_proper_family` — the `q`-fold covering lemma.
* `jointPairSubmodule` / `jointPairSubmodule_ne_top` — the bad-seed subspace and its
  properness.
* `epsMCA_le_epsMCA_interleaved` — `ε_mca(C, δ) ≤ ε_mca(C^≡t, δ)`.
* `epsMCA_interleaved_le_epsMCA` — `ε_mca(C^≡t, δ) ≤ ε_mca(C, δ)`.
* `epsMCA_interleaved_eq` — **exact invariance** (the [Jo26] headline, affine-line case).

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891.
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

namespace ProximityGap

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-! ### The covering lemma ([Jo26] Lemma 3.2) -/

/-- **At most `q` proper subspaces cannot cover `F^t`.**  Each proper subspace of `F^t`
has at most `q^{t−1}` points, and all of them share `0`; a family indexed by `F` itself
therefore covers at most `1 + q(q^{t−1} − 1) < q^t` points, so some nonzero vector
escapes every member. -/
theorem exists_nonzero_notMem_of_proper_family {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {t : ℕ} (ht : 1 ≤ t)
    (K : F → Submodule F (Fin t → F)) (hK : ∀ γ, K γ ≠ ⊤) :
    ∃ lam : Fin t → F, lam ≠ 0 ∧ ∀ γ, lam ∉ K γ := by
  classical
  set q : ℕ := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hcardType : Fintype.card (Fin t → F) = q ^ t := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hfrTop : Module.finrank F (Fin t → F) = t := by
    rw [Module.finrank_pi, Fintype.card_fin]
  set m : ℕ := q ^ (t - 1) with hm
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
  have hcardK : ∀ γ, Fintype.card (K γ) ≤ m := by
    intro γ
    have hfr : Module.finrank F (K γ) < t := by
      have := Submodule.finrank_lt (s := K γ) (hK γ)
      rwa [hfrTop] at this
    have : Fintype.card (K γ) = q ^ Module.finrank F (K γ) :=
      Module.card_eq_pow_finrank
    rw [this, hm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  set U : Finset (Fin t → F) := univ.filter (fun lam => ∃ γ, lam ∈ K γ) with hU
  have hmemU : ∀ lam, lam ∈ U ↔ ∃ γ, lam ∈ K γ := by
    intro lam; rw [hU]; simp
  set B : Finset (Fin t → F) :=
    insert 0 (univ.biUnion (fun γ => (K γ : Set (Fin t → F)).toFinset.erase 0)) with hB
  have hsub : U ⊆ B := by
    intro lam hlam
    rw [hmemU] at hlam
    obtain ⟨γ, hγ⟩ := hlam
    rw [hB]
    by_cases h0 : lam = 0
    · rw [h0]; exact mem_insert_self 0 _
    · apply mem_insert_of_mem
      rw [mem_biUnion]
      exact ⟨γ, mem_univ γ, by
        rw [mem_erase]
        exact ⟨h0, by rw [Set.mem_toFinset]; exact hγ⟩⟩
  have hcardErase : ∀ γ, ((K γ : Set (Fin t → F)).toFinset.erase 0).card ≤ m - 1 := by
    intro γ
    have h0mem : (0 : Fin t → F) ∈ (K γ : Set (Fin t → F)).toFinset := by
      rw [Set.mem_toFinset]; exact Submodule.zero_mem _
    rw [card_erase_of_mem h0mem, Set.toFinset_card]
    have hcg : Fintype.card (↑(K γ) : Set (Fin t → F)) = Fintype.card (K γ) := rfl
    have := hcardK γ
    omega
  have hcardB : B.card ≤ 1 + q * (m - 1) := by
    rw [hB]
    refine le_trans (card_insert_le _ _) ?_
    have hbu : (univ.biUnion (fun γ => (K γ : Set (Fin t → F)).toFinset.erase 0)).card
        ≤ q * (m - 1) := by
      refine le_trans card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun γ _ => hcardErase γ)) ?_
      rw [Finset.sum_const, Finset.card_univ, ← hq, smul_eq_mul]
    omega
  have hcardU : U.card ≤ 1 + q * (m - 1) := le_trans (card_le_card hsub) hcardB
  have hqm : q * (m - 1) + q = q ^ t := by
    have hstep : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    have : q * (m - 1) + q = q * m := by
      calc q * (m - 1) + q = q * (m - 1) + q * 1 := by ring
        _ = q * (m - 1 + 1) := by ring
        _ = q * m := by rw [hstep]
    rw [this, hm, ← pow_succ']
    congr 1
    omega
  have hUlt : U.card < q ^ t := by omega
  have hUne : U ≠ univ := by
    intro h
    rw [h, card_univ, hcardType] at hUlt
    exact (lt_irrefl _ hUlt)
  rw [Ne, eq_univ_iff_forall, not_forall] at hUne
  obtain ⟨lam, hlam⟩ := hUne
  refine ⟨lam, ?_, ?_⟩
  · intro h0
    apply hlam
    rw [hmemU]
    exact ⟨0, by rw [h0]; exact Submodule.zero_mem _⟩
  · intro γ hγ
    apply hlam
    rw [hmemU]
    exact ⟨γ, hγ⟩

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The bad-seed subspace ([Jo26] Lemma 4.1) -/

open Classical in
/-- The set of combination vectors `λ ∈ F^t` whose row-combinations of the interleaved
stack `(U₀, U₁)` admit a joint codeword pair on `S`.  Linearity of `C` makes this a
subspace: joint-pair witnesses add, scale, and the zero combination is witnessed by
`(0, 0)`. -/
def jointPairSubmodule (C : Submodule F (ι → A)) (S : Finset ι) {t : ℕ}
    (U₀ U₁ : ι → Fin t → A) : Submodule F (Fin t → F) where
  carrier := {lam | pairJointAgreesOn (C : Set (ι → A)) S
    (fun j => ∑ k, lam k • U₀ j k) (fun j => ∑ k, lam k • U₁ j k)}
  zero_mem' := by
    refine ⟨0, C.zero_mem, 0, C.zero_mem, fun j hj => ?_⟩
    constructor <;> simp
  add_mem' := by
    rintro lam lam' ⟨v₀, hv₀, v₁, hv₁, hag⟩ ⟨w₀, hw₀, w₁, hw₁, hag'⟩
    refine ⟨v₀ + w₀, C.add_mem hv₀ hw₀, v₁ + w₁, C.add_mem hv₁ hw₁, fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hag j hj
    obtain ⟨h1', h2'⟩ := hag' j hj
    constructor
    · calc (v₀ + w₀) j = (∑ k, lam k • U₀ j k) + ∑ k, lam' k • U₀ j k := by
            rw [Pi.add_apply, h1, h1']
        _ = ∑ k, (lam + lam') k • U₀ j k := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
    · calc (v₁ + w₁) j = (∑ k, lam k • U₁ j k) + ∑ k, lam' k • U₁ j k := by
            rw [Pi.add_apply, h2, h2']
        _ = ∑ k, (lam + lam') k • U₁ j k := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
  smul_mem' := by
    rintro c lam ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨c • v₀, C.smul_mem c hv₀, c • v₁, C.smul_mem c hv₁, fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hag j hj
    constructor
    · calc (c • v₀) j = c • ∑ k, lam k • U₀ j k := by rw [Pi.smul_apply, h1]
        _ = ∑ k, (c • lam) k • U₀ j k := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by
              rw [Pi.smul_apply, smul_smul, smul_eq_mul]
    · calc (c • v₁) j = c • ∑ k, lam k • U₁ j k := by rw [Pi.smul_apply, h2]
        _ = ∑ k, (c • lam) k • U₁ j k := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by
              rw [Pi.smul_apply, smul_smul, smul_eq_mul]

open Classical in
/-- **Properness of the bad-seed subspace** ([Jo26] Lemma 4.1, core step).  If every
combination vector admitted a joint pair on `S`, then in particular every standard basis
vector would — i.e. every *row* of `(U₀, U₁)` would admit a joint pair on `S` — and the
row witnesses assemble column-by-column into a joint pair for the interleaved stack on
`S`, contradicting the interleaved witness. -/
theorem jointPairSubmodule_ne_top (C : Submodule F (ι → A)) {S : Finset ι} {t : ℕ}
    (U₀ U₁ : ι → Fin t → A)
    (hnopair : ¬ pairJointAgreesOn ((C : Set (ι → A))^⋈ (Fin t)) S U₀ U₁) :
    jointPairSubmodule C S U₀ U₁ ≠ ⊤ := by
  intro htop
  apply hnopair
  have hrow : ∀ k : Fin t, pairJointAgreesOn (C : Set (ι → A)) S
      (fun j => U₀ j k) (fun j => U₁ j k) := by
    intro k
    have hmem : (Pi.single k (1 : F)) ∈ jointPairSubmodule C S U₀ U₁ := by
      rw [htop]; trivial
    obtain ⟨v₀, hv₀, v₁, hv₁, hag⟩ := hmem
    have hsum : ∀ (U : ι → Fin t → A) (j : ι),
        (∑ k', (Pi.single k (1 : F) : Fin t → F) k' • U j k') = U j k := by
      intro U j
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine ⟨v₀, hv₀, v₁, hv₁, fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hag j hj
    dsimp only at h1 h2 ⊢
    rw [hsum U₀ j] at h1
    rw [hsum U₁ j] at h2
    exact ⟨h1, h2⟩
  choose V₀ hV₀ V₁ hV₁ hagree using hrow
  refine ⟨fun j k => V₀ k j, ?_, fun j k => V₁ k j, ?_, fun j hj => ?_⟩
  · intro k; exact hV₀ k
  · intro k; exact hV₁ k
  · constructor
    · funext k; exact (hagree k j hj).1
    · funext k; exact (hagree k j hj).2

/-! ### The easy direction: zero-row embedding -/

open Classical in
/-- **`ε_mca(C, δ) ≤ ε_mca(C^≡t, δ)`** ([Jo26] Theorem 4.2, lower half).  Embedding a
base stack into the interleaved code via the zero-row embedding (row `0` carries the
stack, all other rows are `0`) maps every base `mcaEvent` witness to an interleaved one,
with the same witness set `S`. -/
theorem epsMCA_le_epsMCA_interleaved (C : Submodule F (ι → A)) (t : ℕ) [NeZero t]
    (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ := by
  classical
  unfold epsMCA
  apply iSup_le
  intro v
  set u : WordStack (Fin t → A) (Fin 2) ι :=
    fun i j k => if k = (0 : Fin t) then v i j else 0 with hu
  have h_imp : ∀ γ : F, mcaEvent (C : Set (ι → A)) δ (v 0) (v 1) γ →
      mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (u 0) (u 1) γ := by
    rintro γ ⟨S, hcard, ⟨w, hw, hagree⟩, hnopair⟩
    refine ⟨S, hcard, ?_, ?_⟩
    · refine ⟨fun j k => if k = (0 : Fin t) then w j else 0, ?_, ?_⟩
      · intro k
        show (fun j => if k = (0 : Fin t) then w j else 0) ∈ (C : Set (ι → A))
        by_cases hk : k = 0
        · subst hk; simpa using hw
        · simp only [if_neg hk]; exact C.zero_mem
      · intro j hj
        funext k
        simp only [hu, Pi.add_apply, Pi.smul_apply]
        by_cases hk : k = 0
        · subst hk; simpa using hagree j hj
        · simp [hk]
    · rintro ⟨V₀, hV₀, V₁, hV₁, hpair⟩
      apply hnopair
      have hV₀' : ∀ k : Fin t, (fun j => V₀ j k) ∈ (C : Set (ι → A)) := hV₀
      have hV₁' : ∀ k : Fin t, (fun j => V₁ j k) ∈ (C : Set (ι → A)) := hV₁
      refine ⟨fun j => V₀ j 0, hV₀' 0, fun j => V₁ j 0, hV₁' 0, ?_⟩
      intro j hj
      obtain ⟨h0, h1⟩ := hpair j hj
      constructor
      · have h := congrArg (fun f : Fin t → A => f 0) h0
        simpa [hu] using h
      · have h := congrArg (fun f : Fin t → A => f 0) h1
        simpa [hu] using h
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack (Fin t → A) (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (w 0) (w 1) γ])
    u

/-! ### The hard direction: one combination vector preserves every bad seed -/

open Classical in
/-- **`ε_mca(C^≡t, δ) ≤ ε_mca(C, δ)`** ([Jo26] Theorem 4.4, affine-line case).  The
bad-seed subspaces `K_γ` are indexed by the seed set `F` itself, so the covering lemma
provides a single nonzero combination vector `λ` outside all of them; the fixed base
stack `λ·u` is then bad at every seed where the interleaved stack was bad — same `γ`,
same witness set.  No averaging, no union bound, no interleaving-width factor. -/
theorem epsMCA_interleaved_le_epsMCA (C : Submodule F (ι → A)) (t : ℕ) [NeZero t]
    (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ
      ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  classical
  unfold epsMCA
  apply iSup_le
  intro u
  -- the per-seed bad subspace (⊥ off the bad-seed set)
  obtain ⟨lam, hlam0, hlamK⟩ := exists_nonzero_notMem_of_proper_family
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne t))
    (fun γ => if h : mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (u 0) (u 1) γ
      then jointPairSubmodule C h.choose (u 0) (u 1) else ⊥)
    (fun γ => by
      dsimp only
      split_ifs with h
      · exact jointPairSubmodule_ne_top C (u 0) (u 1) h.choose_spec.2.2
      · exact bot_ne_top)
  -- the λ-combined base stack
  set v : WordStack A (Fin 2) ι := fun i j => ∑ k, lam k • u i j k with hv
  have h_imp : ∀ γ : F,
      mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (u 0) (u 1) γ →
      mcaEvent (C : Set (ι → A)) δ (v 0) (v 1) γ := by
    intro γ h
    obtain ⟨hcard, ⟨w, hwmem, hwagree⟩, hnopair⟩ := h.choose_spec
    refine ⟨h.choose, hcard, ?_, ?_⟩
    · -- closeness: the λ-combination of the rows of `w`
      refine ⟨fun j => ∑ k, lam k • w j k, ?_, ?_⟩
      · have hrows : ∀ k : Fin t, (fun j => w j k) ∈ (C : Set (ι → A)) := hwmem
        have heq : (fun j => ∑ k, lam k • w j k)
            = ∑ k, lam k • (fun j => w j k) := by
          funext j
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun k _ => rfl
        rw [heq]
        exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hrows k)
      · intro j hj
        have hw := hwagree j hj
        have hpt : ∀ k : Fin t, w j k = u 0 j k + γ • u 1 j k := by
          intro k
          have := congrArg (fun f : Fin t → A => f k) hw
          simpa [Pi.add_apply, Pi.smul_apply] using this
        calc (fun j => ∑ k, lam k • w j k) j = ∑ k, lam k • w j k := rfl
          _ = ∑ k, (lam k • u 0 j k + lam k • (γ • u 1 j k)) := by
              exact Finset.sum_congr rfl fun k _ => by rw [hpt k, smul_add]
          _ = (∑ k, lam k • u 0 j k) + ∑ k, lam k • (γ • u 1 j k) :=
              Finset.sum_add_distrib
          _ = (∑ k, lam k • u 0 j k) + γ • ∑ k, lam k • u 1 j k := by
              congr 1
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun k _ => by
                rw [smul_smul, smul_smul, mul_comm]
          _ = v 0 j + γ • v 1 j := rfl
    · -- no joint pair: exactly `lam ∉ K_γ`
      intro hpair
      have hmem := hlamK γ
      rw [dif_pos h] at hmem
      exact hmem hpair
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (w 0) (w 1) γ])
    v

/-! ### The headline: exact invariance -/

/-- **[Jo26] headline (affine-line case): MCA error is exactly invariant under row-wise
interleaving.**  `ε_mca(C^≡t, δ) = ε_mca(C, δ)`.  Upgrades the [ABF26] Lemma 4.7 union
bound (`≤ t·ε_mca`, in-tree as `epsMCA_interleaved_le`) to equality: interleaving width
is free for mutual correlated agreement on affine lines.  In particular every
`δ*`-bracket of the MCA threshold ledger transfers verbatim to interleaved codes. -/
theorem epsMCA_interleaved_eq (C : Submodule F (ι → A)) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ
      = epsMCA (F := F) (A := A) (C : Set (ι → A)) δ :=
  le_antisymm (epsMCA_interleaved_le_epsMCA C t δ) (epsMCA_le_epsMCA_interleaved C t δ)

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.exists_nonzero_notMem_of_proper_family
#print axioms ProximityGap.jointPairSubmodule_ne_top
#print axioms ProximityGap.epsMCA_le_epsMCA_interleaved
#print axioms ProximityGap.epsMCA_interleaved_le_epsMCA
#print axioms ProximityGap.epsMCA_interleaved_eq
