/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma25Opening
import ArkLib.Data.CodingTheory.GMMDS.LovettNLtK

/-!
# Lovett's GM-MDS proof: the corrected Lemma 2.5 reduction (#389)

The remaining open content of Lovett's Theorem 1.7 (after the master frame and the `n = k` /
`n < k` algebraic branches) is the *primitive step*.  This file makes that residual **both
correctly stated and `n = 0`-complete**, fixing two falsity bugs in the prior framing:

1. **`LovettWitnessExists` is false at `n = 0`** (`not_lovettWitness_emptyV`): the empty-vector
   system `emptyV : Fin 1 → (Fin 0 → ℕ)` is a genuine primitive `V*(1)` system, yet
   `LovettWitness F emptyV 1` demands `1 ≤ 0`.  So the literal witness residual is unprovable.

2. **The "no merge candidate" residual is also false** (`not_noMergeCandidate`): the system
   `mcV = [(0,0)] : Fin 1 → (Fin 2 → ℕ)` is a primitive `V*(1)` system that DOES contain a merge
   candidate (vector `0` has an interior zero at `j = 0 < 1` and a last-coordinate zero) — yet it
   is independent.  So "a primitive `V*(k)` system has no merge candidate" is a false demand: merge
   candidates genuinely occur in independent systems.  Ruling them out is the wrong residual.

The **correct** residual is therefore not "no merge candidate" but the substitution lemma itself:
*a primitive `V*(k)` system that contains a merge candidate is independent* (Lovett's `a_last ↦ a_{j*}`
substitution-divisibility argument, kernel `substVar` / `sub_X_dvd_of_subst_eq_zero` in
`LovettSubstitutionDvd`, collapses to dimension `n − 1` via the `n`-IH).  We name it
`LovettMergeIndep` and prove the genuinely-usable reduction:

> **`lovettPrimitiveStep_of_mergeIndep : LovettMergeIndep F → LovettPrimitiveStep F`** — routing
> `n = 0` directly (`lovettHolds_primitive_n0`), and `n ≥ 1` through the `witness_or_mergeCandidate`
> dichotomy: the witness branch via `lovettHolds_of_witness`, the merge branch via `LovettMergeIndep`.

`LovettMergeIndep` is a TRUE statement (vacuously so wherever no merge candidate occurs, and the
genuine substitution lemma where one does), so this is a usable residual — unlike the two refuted
forms.  Discharging it closes Theorem 1.7 and the prize route R3.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F]

/-! ## 1. The `n = 0` falsity of the literal `LovettWitnessExists` residual -/

/-- The empty-vector system over `Fin 0`: a single vector `Fin 0 → ℕ` (the empty function). -/
def emptyV : Fin 1 → (Fin 0 → ℕ) := fun _ => fun j => j.elim0

theorem emptyV_isVStar : IsVStar emptyV 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; simp [vAbs]
  · intro I hI
    have hIeq : I = {0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      obtain ⟨w, hw⟩ := hI
      exact ⟨by simpa [Fin.fin_one_eq_zero w] using hw, fun x _ => Fin.fin_one_eq_zero x⟩
    subst hIeq
    rw [Finset.sum_singleton]
    have h1 : vAbs (emptyV 0) = 0 := by simp [vAbs]
    have hmeet : vAbs (vMeet emptyV {0} (Finset.singleton_nonempty 0)) = 0 := by simp [vAbs, vMeet]
    rw [h1, hmeet]
  · intro i j; exact j.elim0

theorem emptyV_primitive : ∀ j : Fin 0, ∃ i, emptyV i j = 0 := fun j => j.elim0

/-- **The `n = 0` counterexample to the literal `LovettWitness`.**  Even though `emptyV` is a
primitive `V*(1)` system, `LovettWitness F emptyV 1` is false (it demands `hn : 1 ≤ 0`).  Hence
`LovettWitnessExists` is not provable as stated. -/
theorem not_lovettWitness_emptyV : ¬ LovettWitness F emptyV 1 := by
  rintro ⟨hn, _, _⟩
  exact absurd hn (by norm_num)

/-! ## 2. The primitive step at `n = 0`, discharged directly -/

/-- A `V*(k)` system over `Fin 0` (with `1 ≤ k`) has at most one vector: over the empty coordinate
set every vector is the empty function, so any two are equal — comparable, which Lemma 2.1
(`not_le_of_isVStar`) forbids for *distinct* indices. -/
theorem m_le_one_of_n_zero {m : ℕ} {V : Fin m → (Fin 0 → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) : m ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have h0 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h; simpa using congrArg (Fin.val) h
  exact not_le_of_isVStar hk hV h0 (fun l => l.elim0)

/-- **The primitive step at `n = 0`.**  A primitive `V*(k)` system over `Fin 0` is independent:
`m ≤ 1`, so `P(k,V)` is empty (`m = 0`) or one shifted monomial block (`m = 1`) — both independent. -/
theorem lovettHolds_primitive_n0 {m : ℕ} {V : Fin m → (Fin 0 → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) : LovettHolds F V k := by
  classical
  unfold LovettHolds
  rcases Nat.lt_or_ge m 1 with hm0 | hm1
  · obtain rfl : m = 0 := Nat.lt_one_iff.mp hm0
    haveI : IsEmpty (Σ i : Fin 0, Fin (k - vAbs (V i))) := by
      constructor; rintro ⟨i, _⟩; exact i.elim0
    exact linearIndependent_empty_type
  · have hm1' : m = 1 := le_antisymm (m_le_one_of_n_zero hk hV) hm1
    subst hm1'
    let e : (Σ i : Fin 1, Fin (k - vAbs (V i))) ≃ Fin (k - vAbs (V 0)) :=
      { toFun := fun p => Fin.fin_one_eq_zero p.1 ▸ p.2
        invFun := fun x => ⟨0, x⟩
        left_inv := by
          rintro ⟨i, x⟩
          obtain rfl : i = 0 := Fin.fin_one_eq_zero i
          rfl
        right_inv := fun x => rfl }
    have hbase : LinearIndependent (MvPolynomial (Fin 0) F)
        (fun x : Fin (k - vAbs (V 0)) => pFam (F := F) (V 0) (x : ℕ)) :=
      pFam_single_linearIndependent (V 0) (k - vAbs (V 0))
    have hcomp : (fun x : Fin (k - vAbs (V 0)) => pFam (F := F) (V 0) (x : ℕ)) ∘ e
        = pFamUnion (F := F) V k := by
      funext p
      obtain ⟨i, x⟩ := p
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    rw [← hcomp]
    exact hbase.comp e e.injective

/-! ## 3. The "no merge candidate" residual is ALSO false (merge candidates occur in independent
systems) -/

/-- `mcV = [(0,0)] : Fin 1 → (Fin 2 → ℕ)` — the zero vector over two coordinates. -/
def mcV : Fin 1 → (Fin 2 → ℕ) := fun _ => ![0, 0]

theorem mcV_isVStar : IsVStar mcV 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; simp [vAbs, mcV, Fin.sum_univ_two]
  · intro I hI
    have hIeq : I = {0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      obtain ⟨w, hw⟩ := hI
      exact ⟨by simpa [Fin.fin_one_eq_zero w] using hw, fun x _ => Fin.fin_one_eq_zero x⟩
    subst hIeq
    rw [Finset.sum_singleton]
    have h1 : vAbs (mcV 0) = 0 := by simp [vAbs, mcV, Fin.sum_univ_two]
    have hmeet : vAbs (vMeet mcV {0} (Finset.singleton_nonempty 0)) = 0 := by
      simp [vAbs, vMeet, mcV, Fin.sum_univ_two]
    rw [h1, hmeet]
  · intro i j _; fin_cases j <;> simp [mcV]

theorem mcV_primitive : ∀ j : Fin 2, ∃ i, mcV i j = 0 :=
  fun j => ⟨0, by fin_cases j <;> simp [mcV]⟩

/-- **The merge candidate genuinely occurs** in the primitive `V*(1)` system `mcV`: vector `0` has
an interior zero (`j = 0 < 2 − 1`) and a last-coordinate zero.  Yet `mcV` is independent (its family
is `{xᵉ : e < 1} = {1}`).  So "a primitive `V*(k)` system has no merge candidate" is FALSE — merge
candidates occur in genuinely independent systems, and the correct residual must *handle* them, not
forbid them. -/
theorem not_noMergeCandidate :
    ¬ (∀ {n m : ℕ} (_hn : 1 ≤ n) (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
        (∀ j : Fin n, ∃ i, V i j = 0) →
        ¬ (∃ (i : Fin m) (j : Fin n), (j : ℕ) < n - 1 ∧ V i j = 0 ∧ V i (lastCoord n _hn) = 0)) := by
  intro h
  have hlast : lastCoord 2 (by norm_num) = (1 : Fin 2) := by decide +kernel
  exact h (by norm_num) mcV 1 le_rfl mcV_isVStar mcV_primitive
    ⟨0, 0, by norm_num, by simp [mcV], by rw [hlast]; simp [mcV]⟩

/-! ## 4. The CORRECT merge residual and the usable primitive-step reduction -/

/-- **The correct merge residual** (Lovett's Lemma 2.5/2.6 substitution lemma).  A *primitive*
`V*(k)` system over `Fin n` (`1 ≤ n`, with the minimal-counterexample IHs) that contains a merge
candidate — an index `i` and interior coordinate `j* < n−1` with `V i j* = 0` and `V i (n−1) = 0` —
is itself independent.  (Proven, in Lovett, by the `a_last ↦ a_{j*}` substitution collapsing to a
dimension-`n−1` system handled by the `n`-IH; kernel in `LovettSubstitutionDvd`.)  Unlike the two
refuted "witness exists" / "no merge candidate" forms, this is a TRUE statement. -/
def LovettMergeIndep (F : Type*) [Field F] : Prop :=
  ∀ {n m : ℕ} (hn : 1 ≤ n) (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    (∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k') →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) →
    (∃ (i : Fin m) (j : Fin n), (j : ℕ) < n - 1 ∧ V i j = 0 ∧ V i (lastCoord n hn) = 0) →
    LovettHolds F V k

/-- **The primitive step, modulo the CORRECT merge residual `LovettMergeIndep`.**  Handles `n = 0`
directly and splits `n ≥ 1` via `witness_or_mergeCandidate`: the witness branch through
`lovettHolds_of_witness`, the merge branch through `LovettMergeIndep` (independence *given* a merge
candidate).  This reduction is genuinely usable — `LovettMergeIndep` is true — discharging it closes
Theorem 1.7 and the prize route R3. -/
theorem lovettPrimitiveStep_of_mergeIndep (hmi : LovettMergeIndep F) : LovettPrimitiveStep F := by
  intro n m V k hk hV hprim IHn IHd IHm
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; exact lovettHolds_primitive_n0 hk hV
  · rcases witness_or_mergeCandidate hnpos hV hprim with hwit | hmerge
    · obtain ⟨i₀, hone⟩ := hwit
      exact lovettHolds_of_witness hk hV ⟨hnpos, i₀, hone⟩ IHd
    · exact hmi hnpos V k hk hV hprim IHn IHd IHm hmerge

/-- **Theorem 1.7 (and `LovettPrimitiveCase`, full GM-MDS), modulo `LovettMergeIndep`.** -/
theorem lovettThm17_of_mergeIndep (hmi : LovettMergeIndep F) {n : ℕ} : LovettThm17 F n :=
  lovettThm17_of_primitiveStep (lovettPrimitiveStep_of_mergeIndep hmi)

theorem lovettPrimitiveCase_of_mergeIndep (hmi : LovettMergeIndep F) {n : ℕ} :
    LovettPrimitiveCase F n :=
  lovettPrimitiveCase_of_primitiveStep (lovettPrimitiveStep_of_mergeIndep hmi)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.not_lovettWitness_emptyV
#print axioms ArkLib.GMMDS.lovettHolds_primitive_n0
#print axioms ArkLib.GMMDS.not_noMergeCandidate
#print axioms ArkLib.GMMDS.lovettPrimitiveStep_of_mergeIndep
#print axioms ArkLib.GMMDS.lovettThm17_of_mergeIndep
