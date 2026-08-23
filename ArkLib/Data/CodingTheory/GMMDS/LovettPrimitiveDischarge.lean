/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettReducibleDischarge
import ArkLib.Data.CodingTheory.GMMDS.LovettCounting
import ArkLib.Data.CodingTheory.GMMDS.LovettFractionField
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep

/-!
# Lovett's GM-MDS proof: the primitive case via joint minimal-counterexample induction (#389)

This file discharges `LovettPrimitiveCase` — and in fact the full `LovettThm17` — by Lovett's
minimal-counterexample argument (arXiv:1803.02523, §2), as a single nested strong induction on
the lexicographic measure `(n, k, d)` where `d = |P(k,V)| = Σᵢ (k − |vᵢ|)`, with the system
`V` and the (type-level) size `m` universally quantified.

The induction frame `lovettThm17_master` reduces the whole theorem to **one** local obligation,
`LovettPrimitiveStep`: discharge a *primitive* instance (`∀ j, ∃ i, vᵢ(j) = 0`) given the
theorem at all strictly smaller `(n, k, d)`.  The reducible branch is handled by the already
proven Lemma 2.2 (`pFamUnion_indep_of_reduced`), and the base cases (`m = 0`, `k = 0` excluded
by `1 ≤ k`) are immediate.

`LovettPrimitiveStep` packages exactly the three induction hypotheses Lovett uses:
* IH on `n` (Lemma 2.5: pass to `n − 1`),
* IH on `k` (the reducible peel, already inside the frame),
* IH on `d` (Lemmas 2.4, 2.6 and the final contradiction: pass to strictly fewer polynomials).

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F]

/-- The induction measure `d = |P(k,V)| = Σᵢ (k − |vᵢ|)`. -/
def lovettD {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ) : ℕ := ∑ i, (k - vAbs (V i))

/-- The abstract conclusion "Theorem 1.7 holds for the instance `(n, m, V, k)`". -/
def LovettHolds (F : Type*) [Field F] {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ) : Prop :=
  LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k)

/-- **The primitive step with the full minimal-counterexample induction hypothesis.**
Given that Theorem 1.7 holds at every strictly smaller `(n, k, d)` (lexicographically), a
*primitive* `V*(k)` instance (no globally peelable coordinate) is itself independent.  This is
the entire mathematical content of Lovett §2 (Lemmas 2.4–2.6 + final contradiction). -/
def LovettPrimitiveStep (F : Type*) [Field F] : Prop :=
  ∀ {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    -- IH on n: anything with strictly smaller ambient dimension
    (∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k') →
    -- IH on d at the same (n, k): strictly fewer polynomials
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) →
    -- IH on m at the same (n, k, d): EQUAL measure d, strictly fewer vectors (Lemma 2.4)
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) →
    LovettHolds F V k

/-- **The master induction frame.**  Nested strong induction on `(n, k, d)`; the reducible
branch is Lemma 2.2, the primitive branch is `LovettPrimitiveStep`. -/
theorem lovettThm17_master (hstep : LovettPrimitiveStep F) : ∀ {n : ℕ}, LovettThm17 F n := by
  -- Strong induction on n, then k, then d.
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
    -- `IHn` : ∀ n' < n, LovettThm17 F n'
    -- Re-package the n-level IH in `LovettHolds` form for any smaller dimension.
    have IHn' : ∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ),
        n' < n → 1 ≤ k' → IsVStar V' k' → LovettHolds F V' k' := by
      intro n' m' V' k' hlt hk' hV'
      exact IHn n' hlt V' k' hk' hV'
    -- Now strong induction on k (at fixed n), then on d.
    -- Prove: ∀ k, ∀ m V, 1 ≤ k → IsVStar V k → LovettHolds F V k, by induction on k then d.
    suffices H : ∀ k : ℕ, ∀ {m : ℕ} (V : Fin m → (Fin n → ℕ)), 1 ≤ k → IsVStar V k →
        LovettHolds F V k by
      intro m V k; exact H k V
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      -- `IHk` : ∀ k' < k, ∀ m V, 1 ≤ k' → IsVStar V k' → LovettHolds F V k'
      -- Now strong induction on the measure d, then on the number of vectors m.
      suffices Hd : ∀ d : ℕ, ∀ m : ℕ, ∀ (V : Fin m → (Fin n → ℕ)),
          lovettD V k = d → 1 ≤ k → IsVStar V k → LovettHolds F V k by
        intro m V hk hV; exact Hd (lovettD V k) m V rfl hk hV
      intro d
      induction d using Nat.strong_induction_on with
      | _ d IHd =>
        -- `IHd` : ∀ d' < d, ∀ m V, lovettD V k = d' → … → LovettHolds.  Now induct on m at fixed d.
        intro m
        induction m using Nat.strong_induction_on with
        | _ m IHm =>
        intro V hdV hk hV
        -- IH on d (at this n, k): strictly smaller measure, any number of vectors.
        have IHdstep : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
            lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k := by
          intro m' V' hlt hV'
          exact IHd (lovettD V' k) (by rw [hdV] at hlt; exact hlt) m' V' rfl hk hV'
        -- IH on m (at this n, k, d): EQUAL measure, strictly fewer vectors.
        have IHmstep : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
            lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k := by
          intro m' V' heq hmlt hV'
          exact IHm m' hmlt V' (by rw [heq, hdV]) hk hV'
        -- Dichotomy: reducible vs primitive.
        by_cases hred : ∃ j : Fin n, ∀ i, 1 ≤ V i j
        · -- reducible: peel (x − aⱼ) and use the k-level IH at k − 1.
          obtain ⟨j, hjj⟩ := hred
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0
            haveI : IsEmpty (Σ i : Fin 0, Fin (k - vAbs (V i))) := by
              constructor; rintro ⟨i, _⟩; exact i.elim0
            exact linearIndependent_empty_type
          · have hV' : IsVStar (fun i => Function.update (V i) j (V i j - 1)) (k - 1) :=
              isVStar_reduce hk hV hjj
            have hk1 : 1 ≤ k - 1 := by
              have i₀ : Fin m := ⟨0, hmpos⟩
              have hwi := hV.weight_le i₀
              have hjle : V i₀ j ≤ vAbs (V i₀) := single_le_vAbs (V i₀) j
              have hji := hjj i₀
              omega
            have hIH : LovettHolds F (fun i => Function.update (V i) j (V i j - 1)) (k - 1) :=
              IHk (k - 1) (by omega) _ hk1 hV'
            exact pFamUnion_indep_of_reduced hk hjj hIH
        · -- primitive
          push_neg at hred
          have hprim : ∀ j : Fin n, ∃ i, V i j = 0 := by
            intro j; obtain ⟨i, hi⟩ := hred j; exact ⟨i, by omega⟩
          exact hstep V k hk hV hprim IHn' IHdstep IHmstep

/-- **Theorem 1.7 modulo the primitive step.**  With `LovettPrimitiveStep`, full GM-MDS. -/
theorem lovettThm17_of_primitiveStep (hstep : LovettPrimitiveStep F) {n : ℕ} :
    LovettThm17 F n := lovettThm17_master hstep

/-- **The primitive case modulo the primitive step.**  `LovettPrimitiveCase` is a special case
of `LovettThm17` (it has the extra hypothesis `∀ j, ∃ i, vᵢ(j) = 0`), so it follows from the
master frame.  Thus discharging `LovettPrimitiveStep` discharges `LovettPrimitiveCase`. -/
theorem lovettPrimitiveCase_of_primitiveStep (hstep : LovettPrimitiveStep F) {n : ℕ} :
    LovettPrimitiveCase F n := by
  intro m V k hk hV _hprim
  exact lovettThm17_master hstep V k hk hV

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.lovettThm17_master
#print axioms ArkLib.GMMDS.lovettPrimitiveCase_of_primitiveStep
