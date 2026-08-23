/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPrimitiveDischarge
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep

/-!
# Lovett's GM-MDS proof: the primitive-case assembly (#389)

The primitive branch of Lovett's §2 (arXiv:1803.02523) concludes, via Lemmas 2.4–2.6, that some
system vector is `(1,…,1,0)` of weight `k − 1`.  Lemma 2.1 then forces every *other* vector to
carry a `1` in the last coordinate, and the single polynomial `pFam (1,…,1,0) 0` (the whole block
`P(k, {that vector})`, which has size `k − |v| = 1`) is not divisible by `(x − a_last)` while every
other family member is.  The one-vector separation engine (`linearIndependent_separate_one`) then
closes independence directly.

This file isolates that **assembly**: from the structured witness (the existence of an index
`i₀` with `vᵢ₀ = (1,…,1,0)` of weight `k−1`, i.e. the combined output of Lemmas 2.5 + 2.6) plus
the `d`-induction hypothesis, it proves the conclusion of `LovettPrimitiveStep`.  The combinatorial
construction of that witness (Lemmas 2.4 + 2.5 + 2.6) is the remaining residual `LovettWitness`.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- The distinguished "last" coordinate `n − 1` of `Fin n` (needs `n ≥ 1`). -/
def lastCoord (n : ℕ) (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- The all-ones-except-last vector `(1,…,1,0) ∈ ℕⁿ`. -/
def oneVec (n : ℕ) (hn : 1 ≤ n) : Fin n → ℕ :=
  fun j => if (j : ℕ) < n - 1 then 1 else 0

theorem oneVec_last {n : ℕ} (hn : 1 ≤ n) : oneVec n hn (lastCoord n hn) = 0 := by
  simp [oneVec, lastCoord]

/-- **The structured witness** (Lovett's Lemma 2.5).  In a *primitive* `V*(k)` system, some
vector is *exactly* `(1,…,1,0)` of weight `n − 1`.

This is **only** Lemma 2.5 — it does **not** demand `n = k`.  (The earlier definition bundled the
conjunct `n = k`, which is Lemma 2.6's *conclusion under a dependent minimal counterexample* and is
**false** as a standalone demand: the primitive `V*(3)` system `[(1,0),(0,2)]` with `n = 2 < 3 = k`
has a `(1,…,1,0)` vector yet is genuinely independent — see `LovettWitnessCounterexample`.)  The
`n = k` versus `n < k` split is handled downstream in `lovettHolds_of_witness`. -/
def LovettWitness (F : Type*) [Field F] {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ) : Prop :=
  ∃ (hn : 1 ≤ n) (i₀ : Fin m), V i₀ = oneVec n hn

/-- **A reindexed subfamily of a `V*(k)` system is again `V*(k)`.**  If `σ : Fin m' → Fin m` is
injective and `V` satisfies `V*(k)`, then `V ∘ σ` satisfies `V*(k)`.  (The MDS inequality (ii)
for an index set `I ⊆ [m']` is the inequality for `σ(I) ⊆ [m]`, via the meet-reindexing.) -/
theorem isVStar_comp {m m' : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k)
    {σ : Fin m' → Fin m} (hσ : Function.Injective σ) : IsVStar (V ∘ σ) k := by
  classical
  refine ⟨fun i => hV.weight_le (σ i), ?_, fun i => hV.shape (σ i)⟩
  intro I hI
  -- map I forward along σ
  have hImg : (I.image σ).Nonempty := hI.image σ
  have hmds := hV.mds (I.image σ) hImg
  -- the meet over I of (V∘σ) equals the meet over σ(I) of V
  have hmeet : vMeet V (I.image σ) hImg = vMeet (V ∘ σ) I hI := by
    funext l
    show (I.image σ).inf' hImg (fun i => V i l) = I.inf' hI (fun i => V (σ i) l)
    rw [Finset.inf'_image hImg (fun i => V i l)]
    rfl
  -- the sum over σ(I) equals the sum over I (σ injective)
  have hsum : (∑ i ∈ I.image σ, (k - vAbs (V i)))
      = ∑ i ∈ I, (k - vAbs (V (σ i))) :=
    Finset.sum_image (fun a _ b _ h => hσ h)
  rw [hsum, hmeet] at hmds
  exact hmds

/-- **Lemma 2.1 corollary for the witness.**  In a `V*(k)` system containing a witness vector
`vᵢ₀ = (1,…,1,0)` (weight `k − 1`, last coord `0`, all-else `≤ 1` by shape (iii)), every *other*
vector carries a `1` in the last coordinate.  Otherwise that vector would be `≤ vᵢ₀`, violating
Lemma 2.1 (`not_le_of_isVStar`). -/
theorem witness_others_last_pos {m : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) (hn : 1 ≤ n) {i₀ : Fin m}
    (hone : V i₀ = oneVec n hn)
    {i : Fin m} (hi : i ≠ i₀) : 1 ≤ V i (lastCoord n hn) := by
  by_contra hcontra
  push_neg at hcontra
  have hi0 : V i (lastCoord n hn) = 0 := by omega
  -- show V i ≤ V i₀ coordinatewise, contradicting Lemma 2.1
  apply not_le_of_isVStar hk hV hi
  intro l
  rw [hone]
  by_cases hl : (l : ℕ) < n - 1
  · -- non-last coordinate: V i l ≤ 1 = oneVec l
    have := hV.shape i l hl
    simp only [oneVec, if_pos hl]; omega
  · -- last coordinate (l = n-1): V i l = 0 ≤ oneVec l
    have hll : l = lastCoord n hn := by
      have : (l : ℕ) = n - 1 := by omega
      exact Fin.ext (by simpa [lastCoord] using this)
    rw [hll, hi0]; exact Nat.zero_le _

/-- `lovettD` drops strictly when removing the witness block (its size is `k − |vᵢ₀| = 1`). -/
theorem lovettD_succAbove_lt {m' : ℕ} {V : Fin (m' + 1) → (Fin n → ℕ)} {k : ℕ}
    (i₀ : Fin (m' + 1)) (hpos : 1 ≤ k - vAbs (V i₀)) :
    lovettD (V ∘ i₀.succAbove) k < lovettD V k := by
  classical
  unfold lovettD
  -- sum over Fin (m'+1) = term at i₀ + sum over the others (reindexed by succAbove)
  rw [Fin.sum_univ_succAbove (fun i => k - vAbs (V i)) i₀]
  have : (∑ i, (k - vAbs ((V ∘ i₀.succAbove) i)))
      = ∑ i, (k - vAbs (V (i₀.succAbove i))) := rfl
  rw [this]
  omega

/-- Splitter: a `Σ` over `Option κ` with a `Unique` `none`-fiber is `Option (Σ over κ)`. -/
def sigmaOptionUniqueEquiv {κ : Type*} (δ : Option κ → Type*) [Unique (δ none)] :
    (Σ o : Option κ, δ o) ≃ Option (Σ a : κ, δ (some a)) where
  toFun := fun p => match p with
    | ⟨none, _⟩ => none
    | ⟨some a, x⟩ => some ⟨a, x⟩
  invFun := fun o => match o with
    | none => ⟨none, default⟩
    | some ⟨a, x⟩ => ⟨some a, x⟩
  left_inv := by rintro ⟨(_|a), x⟩ <;> simp [Unique.eq_default]
  right_inv := by rintro (_|⟨a,x⟩) <;> simp

/-- The Sigma-split equivalence: a `Σ`-family over `Fin (m'+1)` whose `i₀`-fiber has size `1`
splits as `Option` of the `Σ` over the other indices (reindexed by `i₀.succAbove`). -/
noncomputable def sigmaSplitEquiv {m' : ℕ} (G : Fin (m' + 1) → ℕ) (i₀ : Fin (m' + 1))
    (h1 : G i₀ = 1) :
    (Σ i : Fin (m' + 1), Fin (G i)) ≃ Option (Σ a : Fin m', Fin (G (i₀.succAbove a))) :=
  let δ : Option (Fin m') → Type := fun o => Fin (G ((finSuccEquiv' i₀).symm o))
  haveI : Unique (δ none) := by
    show Unique (Fin (G ((finSuccEquiv' i₀).symm none)))
    rw [finSuccEquiv'_symm_none, h1]; infer_instance
  (Equiv.sigmaCongrLeft' (finSuccEquiv' i₀)).trans
    ((show (Σ o : Option (Fin m'), δ o) ≃ Option (Σ a : Fin m', δ (some a)) from
      { toFun := fun p => match p with
          | ⟨none, _⟩ => none
          | ⟨some a, x⟩ => some ⟨a, x⟩
        invFun := fun o => match o with
          | none => ⟨none, default⟩
          | some ⟨a, x⟩ => ⟨some a, x⟩
        left_inv := by rintro ⟨(_ | a), x⟩ <;> simp [Unique.eq_default]
        right_inv := by rintro (_ | ⟨a, x⟩) <;> simp }).trans
      (Equiv.optionCongr (Equiv.sigmaCongrRight (fun a =>
        finCongr (by rw [finSuccEquiv'_symm_some])))))

private theorem sigmaCongrLeft'_snd_val {m' : ℕ} (i₀ : Fin (m' + 1)) (G : Fin (m' + 1) → ℕ)
    (i : Fin (m' + 1)) (x : Fin (G i)) :
    (((Equiv.sigmaCongrLeft' (finSuccEquiv' i₀) (β := fun i => Fin (G i))) ⟨i, x⟩).2 : ℕ)
      = (x : ℕ) := by
  unfold Equiv.sigmaCongrLeft'
  simp only [Equiv.sigmaCongrLeft, Equiv.coe_fn_symm_mk, Equiv.symm_symm]
  generalize_proofs h
  revert h x
  generalize (finSuccEquiv' i₀).symm ((finSuccEquiv' i₀) i) = i'
  rintro x rfl; rfl

theorem sigmaSplitEquiv_isNone {m' : ℕ} (G : Fin (m' + 1) → ℕ) (i₀ : Fin (m' + 1)) (h1 : G i₀ = 1)
    (i : Fin (m' + 1)) (x : Fin (G i)) (hi : finSuccEquiv' i₀ i = none) :
    sigmaSplitEquiv G i₀ h1 ⟨i, x⟩ = none := by
  unfold sigmaSplitEquiv
  simp only [Equiv.trans_apply]
  generalize hq : (Equiv.sigmaCongrLeft' (finSuccEquiv' i₀))
    (⟨i, x⟩ : Sigma (fun i : Fin (m' + 1) => Fin (G i))) = q
  have hq1 : q.1 = none := by rw [← hq]; exact hi
  obtain ⟨qf, qs⟩ := q
  cases hq1; rfl

theorem sigmaSplitEquiv_isSome {m' : ℕ} (G : Fin (m' + 1) → ℕ) (i₀ : Fin (m' + 1)) (h1 : G i₀ = 1)
    (i : Fin (m' + 1)) (x : Fin (G i)) (a : Fin m') (hi : finSuccEquiv' i₀ i = some a) :
    ∃ y : Fin (G (i₀.succAbove a)), (y : ℕ) = (x : ℕ) ∧
      sigmaSplitEquiv G i₀ h1 ⟨i, x⟩ = some ⟨a, y⟩ := by
  unfold sigmaSplitEquiv
  simp only [Equiv.trans_apply]
  generalize hq : (Equiv.sigmaCongrLeft' (finSuccEquiv' i₀))
    (⟨i, x⟩ : Sigma (fun i : Fin (m' + 1) => Fin (G i))) = q
  have hq1 : q.1 = some a := by rw [← hq]; exact hi
  have hq2 : (q.2 : ℕ) = (x : ℕ) := by rw [← hq]; exact sigmaCongrLeft'_snd_val i₀ G i x
  obtain ⟨qf, qs⟩ := q
  cases hq1
  refine ⟨finCongr (by rw [finSuccEquiv'_symm_some]) qs, ?_, ?_⟩
  · simpa using hq2
  · rfl

/-- **The primitive-case assembly, `n = k` branch** (Lovett's final contradiction).  From the
structured witness `vᵢ₀ = (1,…,1,0)` *with* `n = k` (so `|vᵢ₀| = n − 1 = k − 1`) and the
`d`-induction hypothesis, the primitive system `V` is independent: drop the witness block
(a single polynomial, since `k − |vᵢ₀| = 1`), apply the IH to the remaining `V*(k)` subfamily,
and re-attach via one-vector separation (`linearIndependent_separate_one`), since every other
vector has a `1` in the last coordinate (`witness_others_last_pos`) while `vᵢ₀` does not. -/
theorem lovettHolds_of_witness_nEqK {m : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) (hn : 1 ≤ n) {i₀ : Fin m} (hone : V i₀ = oneVec n hn) (hnk : n = k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) :
    LovettHolds F V k := by
  classical
  -- m ≥ 1, write m = m' + 1
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i₀.elim0)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set j := lastCoord n hn with hj
  set σ := i₀.succAbove with hσ
  set V' : Fin m' → (Fin n → ℕ) := V ∘ σ with hV'def
  -- The witness block has size 1: k - |vᵢ₀| = k - (n-1) = 1 (since n = k).
  have hblock1 : k - vAbs (V i₀) = 1 := by
    rw [hone]
    have hwt : vAbs (oneVec n hn) = n - 1 := by
      classical
      unfold vAbs oneVec
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
      -- number of j with (j:ℕ) < n-1 is n-1
      have hcard : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < n - 1)).card = n - 1 := by
        rw [show (n-1) = (Finset.range (n-1)).card from (Finset.card_range _).symm]
        apply Finset.card_bij (fun (x : Fin n) _ => (x : ℕ))
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          simpa using ha
        · intro a _ b _ h; exact Fin.val_injective h
        · intro b hb
          simp only [Finset.mem_range] at hb
          refine ⟨⟨b, by omega⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa using hb
      rw [hcard]
    rw [hwt]; omega
  -- V' is V*(k)
  have hV'star : IsVStar V' k := isVStar_comp hV (Fin.succAbove_right_injective)
  -- d drops
  have hdlt : lovettD V' k < lovettD V k :=
    lovettD_succAbove_lt i₀ (by rw [hblock1])
  -- IH: V' independent
  have hindep' : LovettHolds F V' k := IHd V' hdlt hV'star
  -- every V' i has last coord ≥ 1
  have hall : ∀ i, 1 ≤ V' i j := by
    intro i
    exact witness_others_last_pos hk hV hn hone (i := σ i)
      (by rw [hσ]; exact (Fin.succAbove_ne i₀ i))
  -- witness last coord = 0
  have hsep : V i₀ j = 0 := by rw [hone]; exact oneVec_last hn
  -- one-vector separation
  have hopt := linearIndependent_separate_one (F := F) (k := k) (j := j) hindep' hall (vlast := V i₀) hsep
  -- transport along the explicit Sigma-split equivalence to `pFamUnion V k`
  unfold LovettHolds
  set G : Fin (m' + 1) → ℕ := fun i => k - vAbs (V i) with hG
  -- the target family of `hopt`
  set g : Option (Σ a : Fin m', Fin (k - vAbs (V' a))) → (MvPolynomial (Fin n) F)[X] :=
    fun o => o.elim (pFam (F := F) (V i₀) 0) (pFamUnion (F := F) V' k) with hg
  -- `Fin (G (i₀.succAbove a)) = Fin (k - vAbs (V' a))` definitionally (`V' = V ∘ i₀.succAbove`)
  let e : (Σ i : Fin (m' + 1), Fin (G i)) ≃ Option (Σ a : Fin m', Fin (k - vAbs (V' a))) :=
    sigmaSplitEquiv G i₀ (by simp only [hG]; exact hblock1)
  -- `pFamUnion V k = g ∘ e`
  have hfun : pFamUnion (F := F) V k = g ∘ e := by
    funext p
    obtain ⟨i, x⟩ := p
    show pFam (F := F) (V i) (x : ℕ) = g (e ⟨i, x⟩)
    rcases hi : (finSuccEquiv' i₀) i with _ | a
    · -- i = i₀: witness block, block size 1 so `x = 0`
      have hii : i = i₀ := by
        have := congrArg (finSuccEquiv' i₀).symm hi
        rwa [Equiv.symm_apply_apply, finSuccEquiv'_symm_none] at this
      subst i
      rw [show e ⟨i₀, x⟩ = none from sigmaSplitEquiv_isNone G i₀ _ i₀ x hi]
      show pFam (F := F) (V i₀) (x : ℕ) = pFam (F := F) (V i₀) 0
      have hx0 : (x : ℕ) = 0 := by
        have hx := x.isLt; simp only [hG, hblock1] at hx; omega
      rw [hx0]
    · -- i = i₀.succAbove a: ordinary block
      obtain ⟨y, hyval, hey⟩ := sigmaSplitEquiv_isSome G i₀ (by simp only [hG]; exact hblock1) i x a hi
      have hii : i = i₀.succAbove a := by
        have := congrArg (finSuccEquiv' i₀).symm hi
        rwa [Equiv.symm_apply_apply, finSuccEquiv'_symm_some] at this
      subst i
      show pFam (F := F) (V (i₀.succAbove a)) (x : ℕ) = g (e ⟨i₀.succAbove a, x⟩)
      rw [show e ⟨i₀.succAbove a, x⟩ = some ⟨a, y⟩ from hey]
      show pFam (F := F) (V (i₀.succAbove a)) (x : ℕ)
          = pFamUnion (F := F) V' k ⟨a, y⟩
      rw [pFamUnion]
      show pFam (F := F) (V (i₀.succAbove a)) (x : ℕ)
          = pFam (F := F) (V' a) (y : ℕ)
      rw [hyval]
      rfl
  rw [hfun]
  exact (linearIndependent_equiv e (f := g)).mpr hopt

/-- **The remaining combinatorial residual** (Lovett Lemmas 2.4 + 2.5 + 2.6).  Every *primitive*
`V*(k)` system contains the structured witness `(1,…,1,0)`.  Lovett constructs it by: Lemma 2.4
(tight constraints are singletons or the whole set), Lemma 2.5 (some vector is `(1,…,1,0)`, using
the IH at `n − 1`), and Lemma 2.6 (`n = k`, using the IH at smaller `d`).  All three appeal to the
minimal-counterexample IHs, packaged here exactly as in `LovettPrimitiveStep`. -/
def LovettWitnessExists (F : Type*) [Field F] : Prop :=
  ∀ {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    (∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k') →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) →
    LovettWitness F V k

/-- The `n ≤ k` constraint always available from a witness: `|vᵢ₀| = n − 1` and `|vᵢ₀| ≤ k − 1`
(weight bound (i)) give `n − 1 ≤ k − 1`, hence `n ≤ k`.  So `lovettHolds_of_witness` need only
split on `n = k` versus `n < k`. -/
theorem witness_n_le_k {m : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) (hn : 1 ≤ n) {i₀ : Fin m} (hone : V i₀ = oneVec n hn) : n ≤ k := by
  classical
  have hwt : vAbs (V i₀) = n - 1 := by
    rw [hone]
    have hwt' : vAbs (oneVec n hn) = n - 1 := by
      classical
      unfold vAbs oneVec
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
      have hcard : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < n - 1)).card = n - 1 := by
        rw [show (n-1) = (Finset.range (n-1)).card from (Finset.card_range _).symm]
        apply Finset.card_bij (fun (x : Fin n) _ => (x : ℕ))
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; simpa using ha
        · intro a _ b _ h; exact Fin.val_injective h
        · intro b hb
          simp only [Finset.mem_range] at hb
          refine ⟨⟨b, by omega⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simpa using hb
      rw [hcard]
    exact hwt'
  have := hV.weight_le i₀
  omega

end ArkLib.GMMDS

-- Axiom audit
#print axioms ArkLib.GMMDS.isVStar_comp
#print axioms ArkLib.GMMDS.witness_others_last_pos
#print axioms ArkLib.GMMDS.lovettD_succAbove_lt
#print axioms ArkLib.GMMDS.lovettHolds_of_witness_nEqK
#print axioms ArkLib.GMMDS.witness_n_le_k
