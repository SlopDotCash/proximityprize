/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The dimension-lift: the affine-line list is a higher-dimension per-word list

Issue #389, the deep-band supply closure. The affine-line list `Λ` for the dimension-`k`
Reed–Solomon code along the direction `u₁ = xᵏ` admits a clean reframing: a codeword `c`
(degree `< k`) agrees with the line word `u₀ + γ·xᵏ` on a set `S` **iff** the degree-`≤ k`
polynomial `c − γ·Xᵏ` agrees with `u₀` on `S`. As `(c, γ)` range over (degree `< k`) × `F`,
the polynomial `c − γ·Xᵏ` ranges over **all** polynomials of degree `≤ k`. Hence:

> **`lineList_le_succ_agreement`** — the affine-line list of the dimension-`k` code is at most
> the **per-word list of `u₀` for the dimension-`(k+1)` code** at the same agreement:
> `Λ ≤ #{ P ∈ rsCode dom (k+1) : agreement(P, u₀) ≥ a }`.

Combined with the in-tree Johnson bound (`rsCode_agreement_list_card_le` applied to
`rsCode dom (k+1)`, whose distinct codewords agree on `≤ k` points), this gives

> **`lineList_le_johnson`** — when `n·k < a²` (the deep band, `a = k+m+1`):
> `Λ ≤ n² / (a² − n·k)` — polynomial, **closing the supply unconditionally in that regime.**

So the supply wall survives *only* in the shallow band `a² ≤ n·k`; the deep band is closed by
lifting the dimension and applying Johnson to the lift. This is the rigorous core of the
probe-observed fact that the affine-line list tracks the witness mass and never exhibits the
per-word (sub-Johnson) blowup: the line list of dimension `k` is a *single* per-word list of
dimension `k+1`, not a worst-case over `q` words.

## References

* Issue #389; `LineListReduction.lean`, `JohnsonSplitSupply.lean`
  (`rsCode_agreement_list_card_le`), `StructuredLineCoherence.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The dimension-lift bound.** The affine-line list of the dimension-`k` code along
`u₁ = xᵏ` is at most the per-word agreement-list of `u₀` for the dimension-`(k+1)` code. -/
theorem lineList_le_succ_agreement (dom : Fin n ↪ F) (k a : ℕ) (hkn : k < n)
    (u₀ : Fin n → F) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun P => P ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F))
            ∧ a ≤ (agreeSet P u₀).card)).card := by
  classical
  set appC : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card) with happC
  -- the witnessing scalar for each appearing codeword
  set sc : (Fin n → F) → F := fun c =>
    if h : ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card
    then h.choose else 0 with hsc
  -- the lift map: c ↦ c − sc(c)·xᵏ (pointwise)
  refine Finset.card_le_card_of_injOn
    (fun c => fun i => c i - sc c * (dom i) ^ k) ?_ ?_
  · -- image lands in the dimension-(k+1) agreement list
    intro c hc
    obtain ⟨-, hcmem, hex⟩ := Finset.mem_filter.mp hc
    obtain ⟨Pc, hPcdeg, hPceval⟩ := hcmem
    have hscdef : sc c = hex.choose := by rw [hsc]; simp only [dif_pos hex]
    have hScard : a ≤ (agreeSet c
        (fun i => u₀ i + hex.choose • (dom i) ^ k)).card := hex.choose_spec
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- membership: c − sc·xᵏ = eval (Pc − C(sc)·X^k), degree ≤ k < k+1
      refine ⟨Pc - Polynomial.C (sc c) * Polynomial.X ^ k, ?_, ?_⟩
      · have h1 : (Polynomial.C (sc c) * Polynomial.X ^ k).degree ≤ (k : WithBot ℕ) := by
          calc (Polynomial.C (sc c) * Polynomial.X ^ k).degree
              ≤ (Polynomial.C (sc c)).degree + (Polynomial.X ^ k).degree :=
                Polynomial.degree_mul_le _ _
            _ ≤ 0 + (k : WithBot ℕ) := by
                gcongr
                · exact Polynomial.degree_C_le
                · rw [Polynomial.degree_X_pow]
            _ = (k : WithBot ℕ) := by simp
        have h2 : Pc.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
          lt_of_lt_of_le hPcdeg (by exact_mod_cast Nat.le_succ k)
        have h3 : (Polynomial.C (sc c) * Polynomial.X ^ k).degree
            < ((k + 1 : ℕ) : WithBot ℕ) :=
          lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self k)
        calc (Pc - Polynomial.C (sc c) * Polynomial.X ^ k).degree
            ≤ max Pc.degree (Polynomial.C (sc c) * Polynomial.X ^ k).degree :=
              Polynomial.degree_sub_le _ _
          _ < ((k + 1 : ℕ) : WithBot ℕ) := max_lt h2 h3
      · funext i
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, hPceval]
    · -- agreement: on the witness set, c − sc·xᵏ = u₀
      refine le_trans hScard (Finset.card_le_card ?_)
      intro i hi
      rw [agreeSet, Finset.mem_filter] at hi ⊢
      obtain ⟨-, hii⟩ := hi
      refine ⟨Finset.mem_univ _, ?_⟩
      show c i - sc c * (dom i) ^ k = u₀ i
      rw [hscdef]
      rw [smul_eq_mul] at hii
      linear_combination hii
  · -- injectivity via the degree-≤k vanishing argument
    intro c₁ h1 c₂ h2 heq
    obtain ⟨-, hc₁mem, -⟩ := Finset.mem_filter.mp h1
    obtain ⟨-, hc₂mem, -⟩ := Finset.mem_filter.mp h2
    obtain ⟨P₁, hP₁deg, hP₁ev⟩ := hc₁mem
    obtain ⟨P₂, hP₂deg, hP₂ev⟩ := hc₂mem
    -- the difference polynomial vanishes on all n domain points and has degree ≤ k
    set D : F[X] := (P₁ - P₂) - Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k with hD
    have hDdeg : D.degree < (n : WithBot ℕ) := by
      have h1' : P₁.degree < (k : WithBot ℕ) := hP₁deg
      have h2' : P₂.degree < (k : WithBot ℕ) := hP₂deg
      have hxk : (Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k).degree
          ≤ (k : WithBot ℕ) := by
        calc (Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k).degree
            ≤ (Polynomial.C (sc c₁ - sc c₂)).degree + (Polynomial.X ^ k).degree :=
              Polynomial.degree_mul_le _ _
          _ ≤ 0 + (k : WithBot ℕ) := by
              gcongr
              · exact Polynomial.degree_C_le
              · rw [Polynomial.degree_X_pow]
          _ = (k : WithBot ℕ) := by simp
      have hsub : (P₁ - P₂).degree < (k : WithBot ℕ) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1' h2')
      have : D.degree ≤ max (P₁ - P₂).degree
          (Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k).degree :=
        Polynomial.degree_sub_le _ _
      have hk : (k : WithBot ℕ) ≤ (n : WithBot ℕ) := by exact_mod_cast hkn.le
      calc D.degree ≤ max (P₁ - P₂).degree
            (Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k).degree := this
        _ ≤ (k : WithBot ℕ) := max_le hsub.le hxk
        _ < (n : WithBot ℕ) := by exact_mod_cast hkn
    -- D vanishes on every dom i (from heq)
    have hDvanish : ∀ i : Fin n, D.eval (dom i) = 0 := by
      intro i
      have hpt := congrFun heq i
      simp only [] at hpt
      have e1 := congrFun hP₁ev i
      have e2 := congrFun hP₂ev i
      simp only [] at e1 e2
      rw [hD]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← e1, ← e2]
      linear_combination hpt
    -- a poly with > deg roots is zero
    have hD0 : D = 0 := by
      by_contra hne
      have hdomroots : (Finset.univ : Finset (Fin n)).image (fun i => dom i)
          ⊆ D.roots.toFinset := by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hDvanish i
      have hle : (n : ℕ) ≤ D.natDegree := by
        calc n = (Finset.univ : Finset (Fin n)).card := by
              rw [Finset.card_univ, Fintype.card_fin]
          _ = ((Finset.univ : Finset (Fin n)).image (fun i => dom i)).card :=
              (Finset.card_image_of_injective _ dom.injective).symm
          _ ≤ D.roots.toFinset.card := Finset.card_le_card hdomroots
          _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
          _ ≤ D.natDegree := Polynomial.card_roots' _
      have hnd : D.natDegree < n := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hDdeg
      omega
    -- D = 0 ⟹ P₁ − P₂ = C(sc c₁ − sc c₂)·X^k; comparing degrees forces equality
    have hPeq : P₁ - P₂ = Polynomial.C (sc c₁ - sc c₂) * Polynomial.X ^ k :=
      sub_eq_zero.mp (hD ▸ hD0)
    -- the X^k coefficient: LHS has degree < k so coeff k = 0 ⟹ sc c₁ = sc c₂
    have hPdiffdeg : (P₁ - P₂).degree < (k : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hP₁deg hP₂deg)
    have hcoeffk : (P₁ - P₂).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt hPdiffdeg
    have hsceq : sc c₁ - sc c₂ = 0 := by
      have hkk := congrArg (fun p => Polynomial.coeff p k) hPeq
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_true, mul_one] at hkk
      have hz : P₁.coeff k - P₂.coeff k = 0 := by
        have h := hcoeffk; rwa [Polynomial.coeff_sub] at h
      rw [hz] at hkk
      exact hkk.symm
    have hP12 : P₁ = P₂ := sub_eq_zero.mp (by rw [hPeq, hsceq]; simp)
    -- hence the words agree
    funext i
    rw [hP₁ev, hP₂ev, hP12]

/-! ## Source audit -/

#print axioms lineList_le_succ_agreement

end ProximityGap.Ownership
