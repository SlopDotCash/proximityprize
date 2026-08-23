/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-!
# Exact preservation of curve decodability under interleaving (issue #334, K5, brick 5)

[Jo26] (ePrint 2026/891) **Theorem 5.7**: if `C` is marked `(ℓ, δ, a, b)`-curve-decodable and
`C(a, b) ≤ q`, then `C^{≡s}` is marked `(ℓ, δ, a, b)`-curve-decodable for every width `s` —
**exact** preservation, no field-size factor. (The paper derives the marked hypothesis from
the [GG25] one via Theorem 5.5; the formal statement here takes the marked hypothesis
directly — what the proof consumes — and gives back the marked conclusion, whose [GG25] form
follows by the proven `curveDecodable_of_marked`.)

Mechanism (formalized clause-for-clause):
* `rowCombine` and **Lemma 5.6** (`relHammingDist_rowCombine_le`): row-combinations do not
  increase relative Hamming distance (the combination is a pointwise map —
  `hammingDist_comp_le_hammingDist`).
* `curveExplainSubmodule` (the paper's `V_B`): the row-combinations `λ` whose projected `f` is
  explained by some base-codeword curve on all of `B` — a subspace (witnesses add and scale).
* **Coverage**: the marked base property applied to each projected instance puts every `λ` in
  `V_B` for some `b`-subset `B` of `A₀`.
* **Properness under failure**: if no interleaved marked witness exists, every `V_B` is proper
  (a full `V_B` reassembles an interleaved witness row-by-row from the standard vectors).
* **The covering contradiction**: at most `C(a, b) ≤ q` proper subspaces cannot cover `F^s`
  ([Jo26] Lemma 3.2, in tree as `exists_nonzero_notMem_of_proper_family`, junk-completed
  along an embedding of the `b`-subsets into `F`).
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The row-combination of an interleaved word: `(λ · w) i = ∑ k, λ k • w i k`. -/
def rowCombine {s : ℕ} (lam : Fin s → F) (w : ι → Fin s → A) : ι → A :=
  fun i => ∑ k, lam k • w i k

/-- **[Jo26] Lemma 5.6 (projection does not increase distance).** The row-combination is a
pointwise map of the symbol alphabet, so disagreement positions only disappear. -/
theorem relHammingDist_rowCombine_le {s : ℕ} (lam : Fin s → F)
    (x y : ι → Fin s → A) :
    (δᵣ(rowCombine (A := A) lam x, rowCombine (A := A) lam y) : ℚ≥0) ≤ δᵣ(x, y) := by
  unfold Code.relHammingDist
  apply div_le_div_of_nonneg_right ?_ (by positivity) |>.trans_eq rfl
  · exact_mod_cast hammingDist_comp_le_hammingDist
      (fun (_ : ι) (row : Fin s → A) => ∑ k, lam k • row k)

/-- **The explanation subspace `V_B`** ([Jo26] Theorem 5.7's construction): the
row-combinations `λ` for which the projected `f` is explained by some base-codeword curve on
all of `B`. A subspace: witnesses add, scale, and `0` is witnessed by the zero codewords. -/
def curveExplainSubmodule (C : Submodule F (ι → A)) {ℓ s : ℕ}
    (f : F → ι → Fin s → A) (B : Finset F) :
    Submodule F (Fin s → F) where
  carrier := {lam | ∃ h : Fin (ℓ + 1) → ι → A, (∀ j, h j ∈ C) ∧
    ∀ α ∈ B, rowCombine (A := A) lam (f α)
      = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i}
  zero_mem' := by
    refine ⟨0, fun j => C.zero_mem, fun α _ => ?_⟩
    funext i
    simp [rowCombine]
  add_mem' := by
    rintro lam mu ⟨h, hh, hag⟩ ⟨g, hg, hag'⟩
    refine ⟨h + g, fun j => C.add_mem (hh j) (hg j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    have h2 := congrFun (hag' α hα) i
    simp only [rowCombine, Pi.add_apply] at h1 h2 ⊢
    rw [show (∑ k, (lam k + mu k) • f α i k)
        = (∑ k, lam k • f α i k) + (∑ k, mu k • f α i k) from by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => add_smul _ _ _]
    rw [h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_add _ _ _).symm
  smul_mem' := by
    rintro c lam ⟨h, hh, hag⟩
    refine ⟨c • h, fun j => C.smul_mem c (hh j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    simp only [rowCombine] at h1 ⊢
    rw [show (∑ k, (c • lam) k • f α i k) = c • (∑ k, lam k • f α i k) from by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply]
      exact smul_assoc _ _ _]
    rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    rfl

/-! ### The assembly: Theorem 5.7 proper

The earlier `whnf` walls were the `Finset.sum`-vs-pointwise defeq on Pi types (e.g.
`∑ k, lam k • (fun i => f α i k)` against `fun i => ∑ k, lam k • f α i k` — definitionally
equal only through `Multiset.foldr`); every such mixed-shape goal below crosses through an
explicit `Finset.sum_apply` bridge instead. -/

/-- The interleaved code as a plain set-builder: row-wise membership. Definitionally equal to
`(C : Set (ι → A))^⋈ (Fin s)` (`rowwiseCode_eq_interleave`). -/
def rowwiseCode (C : Set (ι → A)) (s : ℕ) : Set (ι → Fin s → A) :=
  {w | ∀ k : Fin s, (fun i => w i k) ∈ C}

/-- The bridge to the in-tree interleaving notation — definitional. -/
theorem rowwiseCode_eq_interleave (C : Submodule F (ι → A)) (s : ℕ) :
    rowwiseCode (C : Set (ι → A)) s = ((C : Set (ι → A))^⋈ (Fin s)) := rfl

/-- The sum-shape bridge: the row-combination is the `Finset` sum of the scaled row words. -/
theorem rowCombine_eq_sum_rows {s : ℕ} (lam : Fin s → F) (w : ι → Fin s → A) :
    rowCombine (A := A) lam w = ∑ k, lam k • (fun i => w i k) := by
  funext i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **Properness under failure** (the standard-basis reassembly of [Jo26] Theorems 5.7/5.8,
extracted): if no interleaved marked witness of size `b` exists for `(U, f, A₀)`, then every
`V_B` at a `b`-subset `B ⊆ A₀` is a proper subspace. -/
theorem curveExplainSubmodule_ne_top_of_no_witness
    (C : Submodule F (ι → A)) {ℓ s : ℕ} {a b : ℕ}
    {U : Fin (ℓ + 1) → ι → Fin s → A} {f : F → ι → Fin s → A} {A₀ : Finset F}
    (hfail : ∀ cs : Fin (ℓ + 1) → ι → Fin s → A,
      (∀ j, cs j ∈ rowwiseCode (C : Set (ι → A)) s) →
      (A₀.filter (fun α => f α = fun i =>
        ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card < b)
    {B : Finset F} (hB : B ∈ A₀.powersetCard b) :
    (curveExplainSubmodule C (ℓ := ℓ) f B) ≠ ⊤ := by
  classical
  intro htop
  rw [Finset.mem_powersetCard] at hB
  have hek : ∀ k : Fin s, ∃ h : Fin (ℓ + 1) → ι → A, (∀ j, h j ∈ C) ∧
      ∀ α ∈ B, rowCombine (A := A) (Pi.single k (1 : F)) (f α)
        = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i := by
    intro k
    have : Pi.single k (1 : F) ∈ curveExplainSubmodule C (ℓ := ℓ) f B := by
      rw [htop]; trivial
    exact this
  choose h hhC hhag using hek
  set cs : Fin (ℓ + 1) → ι → Fin s → A := fun j i k => h k j i with hcs
  have hrow : ∀ (k : Fin s) (α : F) (i : ι),
      rowCombine (A := A) (Pi.single k (1 : F)) (f α) i = f α i k := by
    intro k α i
    unfold rowCombine
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm
      rw [Pi.single_eq_of_ne hm, zero_smul]
    · simp
  have hlt := hfail cs (fun j => fun k => hhC k j)
  refine absurd ?_ (Nat.not_le.mpr hlt)
  refine le_trans (le_of_eq hB.2.symm) (Finset.card_le_card ?_)
  intro α hα
  rw [Finset.mem_filter]
  refine ⟨hB.1 hα, ?_⟩
  funext i k
  have := congrFun (hhag k α hα) i
  rw [hrow k α i] at this
  rw [this]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

set_option maxHeartbeats 1000000 in
/-- **[Jo26] Theorem 5.7 (exact preservation of curve decodability).** If `C` is **marked**
`(ℓ, δ, a, b)`-curve-decodable and `C(a, b) ≤ q`, then the `s`-fold interleaving `C^{≡s}` is
marked `(ℓ, δ, a, b)`-curve-decodable — *no* field-size factor. Stated over `rowwiseCode`
(definitionally the in-tree `^⋈`; convert with `rowwiseCode_eq_interleave`). -/
theorem markedCurveDecodable_interleaved_of_choose_le
    (C : Submodule F (ι → A)) {ℓ s : ℕ} (hs : 1 ≤ s) {δ : ℝ≥0} {a b : ℕ}
    (hmarked : MarkedCurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b)
    (hchoose : a.choose b ≤ Fintype.card F) :
    MarkedCurveDecodable (F := F) (rowwiseCode (C : Set (ι → A)) s) ℓ δ a b := by
  classical
  intro U f hf A₀ hcard hδ
  by_contra hfail
  push Not at hfail
  -- Every V_B is proper under failure (the shared standard-basis reassembly lemma).
  have hproper : ∀ B ∈ A₀.powersetCard b,
      (curveExplainSubmodule C (ℓ := ℓ) f B) ≠ ⊤ := fun B hB =>
    curveExplainSubmodule_ne_top_of_no_witness (a := a) (U := U) C hfail hB
  -- Coverage: the marked base property puts every λ in some V_B.
  have hcover : ∀ lam : Fin s → F, ∃ B ∈ A₀.powersetCard b,
      lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B := by
    intro lam
    have hδ' : ∀ α ∈ A₀,
        (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
            rowCombine (A := A) lam (U j) i),
          rowCombine (A := A) lam (f α) ) : ℝ≥0) ≤ δ := by
      intro α hα
      refine le_trans ?_ (hδ α hα)
      have hpt : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
            rowCombine (A := A) lam (U j) i)
          = rowCombine (A := A) lam
            (fun i k => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k) := by
        funext i
        unfold rowCombine
        calc ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • ∑ k, lam k • U j i k
            = ∑ j : Fin (ℓ + 1), ∑ k, α ^ (j : ℕ) • (lam k • U j i k) :=
              Finset.sum_congr rfl fun j _ => Finset.smul_sum
          _ = ∑ k, ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (lam k • U j i k) := Finset.sum_comm
          _ = ∑ k, lam k • ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      -- The curve argument inside δᵣ matches the marked clause through the explicit
      -- sum-shape bridge: hδ's curve is `fun i => ∑ j, α^j • U j i` at the Pi alphabet —
      -- pointwise it is `fun i k => ∑ j, α^j • U j i k` (Finset.sum_apply), whose
      -- λ-row-combination is hpt's right side.
      have hcurve : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i)
          = (fun i k => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k) := by
        funext i k
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => rfl
      rw [hpt, hcurve]
      exact_mod_cast relHammingDist_rowCombine_le lam _ _
    have hfC' : ∀ α, rowCombine (A := A) lam (f α) ∈ (C : Set (ι → A)) := by
      intro α
      rw [rowCombine_eq_sum_rows]
      exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hf α k)
    obtain ⟨h, hhC, hcount⟩ := hmarked
      (fun j => rowCombine (A := A) lam (U j))
      (fun α => rowCombine (A := A) lam (f α)) hfC' A₀ hcard hδ'
    set S := A₀.filter (fun α => rowCombine (A := A) lam (f α)
      = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i) with hS
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hcount
    refine ⟨B, ?_, h, hhC, fun α hα => ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hBsub.trans (Finset.filter_subset _ _), hBcard⟩
    · have := hBsub hα
      rw [hS, Finset.mem_filter] at this
      exact this.2
  -- Junk-complete the family along an embedding of the b-subsets into F.
  have hcardle : Fintype.card ↥(A₀.powersetCard b) ≤ Fintype.card F := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hcard]
    exact hchoose
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardle
  set K : F → Submodule F (Fin s → F) := fun γ =>
    if hγ : ∃ B : ↥(A₀.powersetCard b), e B = γ
    then curveExplainSubmodule C (ℓ := ℓ) f hγ.choose.val
    else ⊥ with hK
  have hKproper : ∀ γ, K γ ≠ ⊤ := by
    intro γ
    rw [hK]
    beta_reduce
    by_cases hγ : ∃ B : ↥(A₀.powersetCard b), e B = γ
    · rw [dif_pos hγ]
      exact hproper hγ.choose.val hγ.choose.property
    · rw [dif_neg hγ]
      haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
      exact bot_ne_top
  obtain ⟨lam, _, hlamK⟩ := exists_nonzero_notMem_of_proper_family hs K hKproper
  obtain ⟨B, hB, hlamB⟩ := hcover lam
  refine hlamK (e ⟨B, hB⟩) ?_
  rw [hK]
  beta_reduce
  have hex : ∃ B' : ↥(A₀.powersetCard b), e B' = e ⟨B, hB⟩ := ⟨⟨B, hB⟩, rfl⟩
  rw [dif_pos hex]
  have hBeq : hex.choose.val = B :=
    congrArg Subtype.val (e.injective hex.choose_spec)
  rw [hBeq]
  exact hlamB

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.relHammingDist_rowCombine_le
#print axioms ProximityGap.curveExplainSubmodule
#print axioms ProximityGap.markedCurveDecodable_interleaved_of_choose_le
