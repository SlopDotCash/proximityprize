/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeVStar
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeReindex
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeReduction
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Lovett's GM-MDS proof: the merge-branch substitution finish (`LovettMergeIndep`) (#389)

This file discharges the last open residual of Lovett's Theorem 1.7 — `LovettMergeIndep` — giving
the **unconditional** GM-MDS / Lovett 2018 theorem.  It is the merge branch of Lovett's Lemma 2.5
(arXiv:1803.02523, p.9): a primitive `V*(k)` system containing a merge candidate `(i₀, j*)` (with
`V i₀ j* = 0`, `j* < n−1`, `V i₀ (n−1) = 0`) is linearly independent.

## The argument

Work by contradiction (`hcex : ¬ LovettHolds F V k`).

1. **The merged system is `V*(k)`** (`mergeSys_isVStar`, file `LovettMergeVStar`), so by the `n`-IH
   (`IHn` at `n−1 < n`) the merged family `pFamUnion (mergeSys j* V) k` over `Fin (n−1)` is linearly
   independent.  Reindexed by the weight-preserving sigma equiv, the family
   `q p := pFam (mergeVec j* (V p.1)) p.2` (indexed by the *original* sigma `ι_V`) is independent
   over `R' = MvPolynomial (Fin (n−1)) F`.

2. **The substitution transport.**  `S := substVarP F j* last` realizes `a_last ↦ a_{j*}`.  The
   reindex `ρ := renameP (mergeRho j*)` (injective, `mergeRho_injective`) satisfies the transport
   identity `ρ (q p) = S (pFamUnion V k p)` (`renameP_pFam_eq_substVarP_pFam`).  A section
   `mergeSec : Fin n → Fin (n−1)` with `mergeRho (mergeSec c) = (if c = last then j* else c)`
   (`mergeRho_mergeSec`) provides an algebra section `mergeSecAlg` with
   `rename (mergeRho j*) ∘ mergeSecAlg = substVar last j*` (`rename_mergeRho_mergeSecAlg`).

3. **Minimal-degree descent.**  Given any dependence `∑ g p • pFamUnion V k p = 0`, applying `S`
   and pulling back through the injective `ρ` gives `∑ mergeSecAlg (g p) • q p = 0` over `R'`; by
   step 1 each `mergeSecAlg (g p) = 0`, hence `substVar last j* (g p) = 0`, hence
   `(X j* − X last) ∣ g p` for **all** `p` (`sub_X_dvd_of_subst_eq_zero`).  Dividing every `g p` by
   the nonzero factor `(X j* − X last)` (exact, in the domain `R`) gives a strictly smaller
   dependence, so by strong induction on `∑ (g p).totalDegree` every `g p = 0`.  Therefore
   `pFamUnion V k` is independent: `LovettHolds F V k`, contradicting `hcex`.

The capstone `lovettMergeIndep` proves `LovettMergeIndep F`, and `lovettThm17_unconditional`
delivers the unconditional `LovettThm17 F n` (route R3 closed).

Issue #389.
-/

open Polynomial Finset MvPolynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-! ## The section of the reindex map `mergeRho` -/

/-- A section `Fin n → Fin (n−1)` of the reindex map `mergeRho j*` over `Fin n ∖ {last}`, extended
to `last` by the new-last coordinate `n−2` (which `mergeRho` sends to `j*`).  Concretely: `j*` and
`last` both map to the new-last coordinate `n−2`; an interior `c < j*` maps to itself; an interior
`c > j*` (other than `last`) maps to `c−1`. -/
def mergeSec {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) (c : Fin n) : Fin (n - 1) :=
  if c = j then ⟨n - 1 - 1, by omega⟩
  else if h : (c : ℕ) < (j : ℕ) then ⟨c, by omega⟩
  else ⟨(c : ℕ) - 1, by have h := c.isLt; omega⟩

/-- The value of `mergeIdx` as a nat. -/
theorem mergeIdx_val {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1)) :
    (mergeIdx hn j t : ℕ) = if (t : ℕ) < (j : ℕ) then (t : ℕ) else (t : ℕ) + 1 := by
  rw [mergeIdx, apply_ite (Fin.val)]

/-- The value of `mergeRho` as a nat. -/
theorem mergeRho_val {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1)) :
    (mergeRho hn j t : ℕ)
      = if (t : ℕ) = n - 1 - 1 then (j : ℕ)
        else if (t : ℕ) < (j : ℕ) then (t : ℕ) else (t : ℕ) + 1 := by
  rw [mergeRho, apply_ite (Fin.val), mergeIdx_val]

/-- The value of `mergeSec` as a nat. -/
theorem mergeSec_val {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) (c : Fin n) :
    (mergeSec hn2 j hjlt c : ℕ)
      = if c = j then n - 1 - 1
        else if (c : ℕ) < (j : ℕ) then (c : ℕ) else (c : ℕ) - 1 := by
  rw [mergeSec, apply_ite (Fin.val), apply_dite (Fin.val), dite_eq_ite]

/-- **The section identity.**  `mergeRho j* (mergeSec c) = j*` if `c = last`, else `c`. -/
theorem mergeRho_mergeSec {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) (c : Fin n) :
    mergeRho (by omega : 1 ≤ n) j (mergeSec hn2 j hjlt c)
      = if c = lastCoord n (by omega) then j else c := by
  apply Fin.ext
  rw [mergeRho_val, mergeSec_val]
  have hcle : (c : ℕ) < n := c.isLt
  have hclast : (c = lastCoord n (by omega)) ↔ (c : ℕ) = n - 1 := by
    rw [← Fin.val_eq_val]; rfl
  by_cases hcj : c = j
  · subst hcj
    have hcne : ¬ (c = lastCoord n (by omega)) := by rw [hclast]; omega
    rw [if_neg hcne]; simp
  · by_cases hcl : c = lastCoord n (by omega)
    · rw [if_pos hcl]
      have hcv : (c : ℕ) = n - 1 := hclast.mp hcl
      rw [if_neg hcj, if_neg (by omega : ¬ (c : ℕ) < (j : ℕ))]
      simp only [if_pos (show ((c : ℕ) - 1) = n - 1 - 1 by omega)]
    · rw [if_neg hcl]
      have hcv : (c : ℕ) ≠ n - 1 := fun h => hcl (hclast.mpr h)
      rw [if_neg hcj]
      by_cases hclt : (c : ℕ) < (j : ℕ)
      · rw [if_pos hclt, if_neg (by omega : ¬ (c : ℕ) = n - 1 - 1), if_pos hclt]
      · rw [if_neg hclt, if_neg (by omega : ¬ ((c : ℕ) - 1) = n - 1 - 1),
          if_neg (by omega : ¬ ((c : ℕ) - 1) < (j : ℕ))]; omega

/-- The algebra section `R = MvPolynomial (Fin n) F →ₐ[F] R' = MvPolynomial (Fin (n−1)) F`
substituting `X c ↦ X (mergeSec c)`. -/
noncomputable def mergeSecAlg {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin (n - 1)) F :=
  aeval (fun c => X (mergeSec hn2 j hjlt c))

/-- **The section factors the substitution.**  `rename (mergeRho j*) (mergeSecAlg a) =
substVar last j* a`: composing the section with the reindex recovers the `a_last ↦ a_{j*}`
substitution. -/
theorem rename_mergeRho_mergeSecAlg {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (a : MvPolynomial (Fin n) F) :
    MvPolynomial.rename (mergeRho (by omega : 1 ≤ n) j) (mergeSecAlg hn2 j hjlt a)
      = substVar (F := F) (lastCoord n (by omega)) j a := by
  have hn : 1 ≤ n := by omega
  -- both sides are F-algebra homs in `a`; check on generators.
  have hcomp : (MvPolynomial.rename (mergeRho hn j)).comp (mergeSecAlg hn2 j hjlt)
      = substVar (F := F) (lastCoord n hn) j := by
    apply MvPolynomial.algHom_ext
    intro c
    rw [AlgHom.comp_apply]
    show MvPolynomial.rename (mergeRho hn j) (mergeSecAlg hn2 j hjlt (X c)) = _
    unfold mergeSecAlg
    rw [MvPolynomial.aeval_X, MvPolynomial.rename_X, mergeRho_mergeSec hn2 j hjlt c]
    -- substVar last j (X c) = if c = last then X j else X c
    unfold substVar
    rw [MvPolynomial.aeval_X]
    by_cases hc : c = lastCoord n hn
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
  have := congrArg (fun φ => φ a) hcomp
  simpa using this

/-! ## The reindexed merged family is independent -/

/-- The reindexed merged family over `R' = MvPolynomial (Fin (n−1)) F`, indexed by the *original*
sigma `ι_V`: `qFam p = pFam (mergeVec j* (V p.1)) p.2`. -/
noncomputable def qFam {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (V : Fin m → (Fin n → ℕ)) (k : ℕ) :
    (Σ i : Fin m, Fin (k - vAbs (V i))) → (MvPolynomial (Fin (n - 1)) F)[X] :=
  fun p => pFam (F := F) (mergeVec (by omega : 1 ≤ n) j (V p.1)) (p.2 : ℕ)

/-- The weight-preserving sigma reindex equiv between the original and merged index types. -/
noncomputable def mergeIdxEquiv {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (k : ℕ) :
    (Σ i : Fin m, Fin (k - vAbs (V i)))
      ≃ (Σ i : Fin m, Fin (k - vAbs (mergeSys (by omega : 1 ≤ n) j V i))) :=
  Equiv.sigmaCongrRight (fun i => finCongr (by
    rw [mergeSys, mergeVec_vAbs hn2 j hjlt]))

/-- `qFam` equals the merged `pFamUnion` precomposed with the reindex equiv. -/
theorem qFam_eq_comp {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (k : ℕ) :
    qFam (F := F) hn2 j V k
      = pFamUnion (F := F) (mergeSys (by omega : 1 ≤ n) j V) k ∘ mergeIdxEquiv hn2 j hjlt V k := by
  funext p
  obtain ⟨i, e⟩ := p
  show qFam (F := F) hn2 j V k ⟨i, e⟩ = _
  unfold qFam pFamUnion mergeIdxEquiv mergeSys
  simp only [Function.comp_apply, Equiv.sigmaCongrRight_apply, finCongr_apply]
  rfl

/-- **The reindexed merged family is independent** over `R'`, by the `n`-IH applied to the
`V*(k)` merged system (via `mergeSys_isVStar`). -/
theorem qFam_linearIndependent {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hV : IsVStar V k)
    {i₀ : Fin m} (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0)
    (hcex : ¬ LovettHolds F V k)
    (IHn : ∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k')
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) :
    LinearIndependent (MvPolynomial (Fin (n - 1)) F) (qFam (F := F) hn2 j V k) := by
  have hmergeStar : IsVStar (mergeSys (by omega : 1 ≤ n) j V) k :=
    mergeSys_isVStar hn2 j hjlt hk hV hj0 hlast0 hcex IHd IHm
  have hmergeIndep : LovettHolds F (mergeSys (by omega : 1 ≤ n) j V) k :=
    IHn (mergeSys (by omega : 1 ≤ n) j V) k (by omega) hk hmergeStar
  rw [qFam_eq_comp hn2 j hjlt V k]
  exact (hmergeIndep.comp _ (mergeIdxEquiv hn2 j hjlt V k).injective)

/-! ## The substitution transport and the minimal-degree descent -/

/-- `renameP (mergeRho j)` is injective (it is `Polynomial.map` of the injective `rename`). -/
theorem renameP_mergeRho_injective {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    Function.Injective (renameP F (mergeRho (by omega : 1 ≤ n) j)) := by
  unfold renameP
  rw [Polynomial.coe_mapAlgHom]
  exact Polynomial.map_injective _
    (MvPolynomial.rename_injective _ (mergeRho_injective (by omega) j hjlt))

/-- **The substitution kills every coefficient.**  From a dependence `∑ g p • pFamUnion V k p = 0`,
applying `substVarP` and pulling back through the injective reindex `renameP (mergeRho j)` (using the
`n`-IH independence of `qFam`), every coefficient `g p` is killed by the substitution
`a_last ↦ a_{j*}`. -/
theorem substVar_g_eq_zero {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hV : IsVStar V k)
    {i₀ : Fin m} (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0)
    (hcex : ¬ LovettHolds F V k)
    (IHn : ∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k')
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k)
    (g : (Σ i : Fin m, Fin (k - vAbs (V i))) → MvPolynomial (Fin n) F)
    (hrel : ∑ p, g p • pFamUnion (F := F) V k p = 0) (p : Σ i : Fin m, Fin (k - vAbs (V i))) :
    substVar (F := F) (lastCoord n (by omega)) j (g p) = 0 := by
  classical
  have hn : 1 ≤ n := by omega
  set S := substVarP F j (lastCoord n hn) with hS
  set ρ := renameP F (mergeRho hn j) with hρ
  -- apply S to the relation
  have hSrel : ∑ p, substVar (F := F) (lastCoord n hn) j (g p) • S (pFamUnion (F := F) V k p) = 0 := by
    have := congrArg S hrel
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    symm
    rw [hS, Polynomial.smul_eq_C_mul, map_mul, substVarP_C, ← Polynomial.smul_eq_C_mul]
  -- S (pFamUnion p) = ρ (qFam p)
  have hSq : ∀ p, S (pFamUnion (F := F) V k p) = ρ (qFam (F := F) hn2 j V k p) := by
    intro p
    rw [hS, hρ]
    show substVarP F j (lastCoord n hn) (pFam (V p.1) (p.2 : ℕ)) = _
    rw [← renameP_pFam_eq_substVarP_pFam hn2 j hjlt (V p.1) (p.2 : ℕ)]
    rfl
  -- ρ (∑ mergeSecAlg (g p) • qFam p) = 0
  have hρeq : ρ (∑ p, mergeSecAlg hn2 j hjlt (g p) • qFam (F := F) hn2 j V k p) = 0 := by
    rw [map_sum, ← hSrel]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Polynomial.smul_eq_C_mul, map_mul, renameP_C, ← Polynomial.smul_eq_C_mul,
      rename_mergeRho_mergeSecAlg hn2 j hjlt, hSq p]
  -- ρ injective ⟹ the merged-side relation vanishes
  have hmerged : ∑ p, mergeSecAlg hn2 j hjlt (g p) • qFam (F := F) hn2 j V k p = 0 :=
    renameP_mergeRho_injective hn2 j hjlt (by rw [hρeq, map_zero])
  -- qFam independence ⟹ mergeSecAlg (g p) = 0 ⟹ substVar (g p) = 0
  have hindep := qFam_linearIndependent hn2 j hjlt hk hV hj0 hlast0 hcex IHn IHd IHm
  have hzero := (Fintype.linearIndependent_iff.mp hindep) (fun p => mergeSecAlg hn2 j hjlt (g p)) hmerged p
  have := rename_mergeRho_mergeSecAlg hn2 j hjlt (g p)
  rw [hzero] at this
  rw [← this, map_zero]

/-- The merge difference `X_last − X_{j*}` is nonzero in `R = MvPolynomial (Fin n) F`. -/
theorem X_last_sub_X_j_ne_zero {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    (MvPolynomial.X (lastCoord n (by omega)) - MvPolynomial.X j : MvPolynomial (Fin n) F) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have heq : lastCoord n (by omega) = j := MvPolynomial.X_injective h
  have hv : (lastCoord n (by omega) : ℕ) = n - 1 := rfl
  rw [heq] at hv
  omega

/-- **`X_last − X_{j*}` has positive total degree.** -/
theorem totalDegree_X_last_sub_X_j {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    1 ≤ (MvPolynomial.X (lastCoord n (by omega)) - MvPolynomial.X j :
        MvPolynomial (Fin n) F).totalDegree := by
  have hjlast : lastCoord n (by omega) ≠ j := by
    intro h
    have hv : (lastCoord n (by omega) : ℕ) = n - 1 := rfl
    rw [h] at hv
    omega
  have hmem : (Finsupp.single (lastCoord n (by omega)) 1)
      ∈ (MvPolynomial.X (lastCoord n (by omega)) - MvPolynomial.X j :
          MvPolynomial (Fin n) F).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X', MvPolynomial.coeff_X',
      if_pos rfl,
      if_neg (by rw [Finsupp.single_left_inj (one_ne_zero)]; exact fun h => hjlast h.symm)]
    norm_num
  have := MvPolynomial.le_totalDegree hmem
  simpa using this

/-- **The merge-branch substitution finish (`LovettMergeIndep`).**  A primitive `V*(k)` system
containing a merge candidate is independent — the last open residual of Lovett's Theorem 1.7. -/
theorem lovettMergeIndep : LovettMergeIndep F := by
  classical
  intro n m hn V k hk hV hprim IHn IHd IHm hmerge
  obtain ⟨i₀, j, hjlt, hj0, hlast0⟩ := hmerge
  by_contra hcex
  have hn2 : 2 ≤ n := by have := j.isLt; omega
  set d : MvPolynomial (Fin n) F := MvPolynomial.X (lastCoord n hn) - MvPolynomial.X j with hd
  have hdne : d ≠ 0 := X_last_sub_X_j_ne_zero hn2 j hjlt
  have hdtd : 1 ≤ d.totalDegree := totalDegree_X_last_sub_X_j hn2 j hjlt
  -- strong-induction descent on the total-degree sum of the dependence coefficients
  have key : ∀ N : ℕ, ∀ g : (Σ i : Fin m, Fin (k - vAbs (V i))) → MvPolynomial (Fin n) F,
      (∑ p, g p • pFamUnion (F := F) V k p = 0) →
      (∑ p, (g p).totalDegree) ≤ N → ∀ p, g p = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro g hrel hbud
      by_cases hall : ∀ p, g p = 0
      · exact hall
      · exfalso
        -- every coefficient is killed by the substitution, hence divisible by d
        have hsub0 : ∀ p, substVar (F := F) (lastCoord n hn) j (g p) = 0 := fun p =>
          substVar_g_eq_zero hn2 j hjlt hk hV hj0 hlast0 hcex IHn IHd IHm g hrel p
        have hdvd : ∀ p, d ∣ g p := fun p => by
          rw [hd]; exact sub_X_dvd_of_subst_eq_zero (hsub0 p)
        choose h hh using hdvd
        -- divide out d: a strictly smaller dependence
        have hcancel : d • (∑ p, h p • pFamUnion (F := F) V k p) = 0 := by
          rw [Finset.smul_sum, ← hrel]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hh p, smul_smul]
        have hrel' : ∑ p, h p • pFamUnion (F := F) V k p = 0 := by
          rw [Polynomial.smul_eq_C_mul] at hcancel
          exact (mul_eq_zero.mp hcancel).resolve_left
            (fun hc => hdne (Polynomial.C_eq_zero.mp hc))
        -- pointwise degree non-increase, strict at a nonzero coefficient
        have hle : ∀ p, (h p).totalDegree ≤ (g p).totalDegree := by
          intro p
          by_cases hgp : g p = 0
          · have hhp : h p = 0 := by
              have : d * h p = 0 := by rw [← hh p, hgp]
              exact (mul_eq_zero.mp this).resolve_left hdne
            rw [hhp]; simp
          · have hhp : h p ≠ 0 := fun h0 => hgp (by rw [hh p, h0, mul_zero])
            rw [hh p, MvPolynomial.totalDegree_mul_of_isDomain hdne hhp]; omega
        push_neg at hall
        obtain ⟨p₀, hp₀⟩ := hall
        have hstrict : (h p₀).totalDegree < (g p₀).totalDegree := by
          have hhp : h p₀ ≠ 0 := fun h0 => hp₀ (by rw [hh p₀, h0, mul_zero])
          rw [hh p₀, MvPolynomial.totalDegree_mul_of_isDomain hdne hhp]; omega
        have hdrop : (∑ p, (h p).totalDegree) < ∑ p, (g p).totalDegree :=
          Finset.sum_lt_sum (fun p _ => hle p) ⟨p₀, Finset.mem_univ p₀, hstrict⟩
        -- apply the IH at the smaller measure
        have hltN : (∑ p, (h p).totalDegree) < N := lt_of_lt_of_le hdrop hbud
        have hhzero := IH (∑ p, (h p).totalDegree) hltN h hrel' le_rfl
        exact hp₀ (by rw [hh p₀, hhzero p₀, mul_zero])
  -- the dependence asserted by hcex is killed: contradiction
  apply hcex
  rw [LovettHolds, Fintype.linearIndependent_iff]
  intro g hg p
  exact key (∑ p, (g p).totalDegree) g hg le_rfl p

/-- **Theorem 1.7 (unconditional GM-MDS / Lovett 2018), full algebraic form.** -/
theorem lovettThm17_unconditional {n : ℕ} : LovettThm17 F n :=
  lovettThm17_of_mergeIndep lovettMergeIndep

/-- **The full primitive case, unconditional.** -/
theorem lovettPrimitiveCase_unconditional {n : ℕ} : LovettPrimitiveCase F n :=
  lovettPrimitiveCase_of_mergeIndep lovettMergeIndep

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.mergeRho_mergeSec
#print axioms ArkLib.GMMDS.rename_mergeRho_mergeSecAlg
#print axioms ArkLib.GMMDS.qFam_linearIndependent
#print axioms ArkLib.GMMDS.substVar_g_eq_zero
#print axioms ArkLib.GMMDS.lovettMergeIndep
#print axioms ArkLib.GMMDS.lovettThm17_unconditional
