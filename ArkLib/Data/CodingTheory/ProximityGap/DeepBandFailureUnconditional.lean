/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreSupplyInstance

/-!
# The unconditional deep-band failure (#389): the supply, proven for the words
that arise

The supply wall asked: bound explainable cores for off-code words.  For the
words the averaging engine actually produces — evaluations of polynomials of
degree `< M = 2k+m+2` — the answer is a THEOREM: any codeword difference is a
nonzero polynomial of degree `≤ M−1`, so every agreement is capped at
`A = M−1 = 2k+m+1`; at this cap the agreement-capped supply instance evaluates
to exactly `C(n,k)` per value fiber (`C(M−1−k, m+1) = C(k+m+1, k)` cancels by
binomial symmetry).  Excluding the degenerate stacks (coefficients above `k`
all zero — at most `q^{k+1}` of `q^M`, always at most half the average), the
witness-mass law converts unconditionally:

  **`∃ Q₀ : C(n, k+m+1) ≤ 2 · #badSet(Q₀, x^k) · q^m · C(n,k)`** —

at EVERY band radius, with NO hypotheses beyond the radius window.  This is
the first unconditional multi-scalar deep-band failure bound: nonvacuous
whenever `C(n,k+m+1) > 2·q^m·C(n,k)` (low-rate and/or small-field regimes,
e.g. full-domain RS with `k = n^{1/3}`, `q = Θ(n)` gives `Ω(n^{1/3})` bad
scalars at band `1`).  The high-rate production regime remains governed by the
`C(n,k+m+1)/C(n,k)` ratio — the residual wall, unchanged — but the supply
statement is now PROVEN for every word the deep-band programme generates.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The degree-capped agreement bound**: a word given by a polynomial of
degree ≤ `A` that is not itself a code polynomial agrees with every codeword
on at most `A` points. -/
theorem agreeSet_card_le_of_natDegree_le (dom : Fin n ↪ F) {k A : ℕ}
    (hkA : k ≤ A + 1) {Q : F[X]} (hQdeg : Q.natDegree ≤ A)
    (hne : ∀ P : F[X], P.degree < (k : ℕ) → Q ≠ P) :
    ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q.eval (dom i))).card ≤ A := by
  rintro c ⟨P, hPdeg, rfl⟩
  have hD0 : Q - P ≠ 0 := sub_ne_zero.mpr (hne P hPdeg)
  have hPk : P.natDegree ≤ A := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  have hDdeg : (Q - P).natDegree ≤ A :=
    le_trans (natDegree_sub_le Q P) (max_le hQdeg hPk)
  have hsub : (agreeSet (fun i => P.eval (dom i))
        (fun i => Q.eval (dom i))).card
      ≤ (Q - P).roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun i => dom i) ?_ ?_
    · intro i hi
      have hi' : i ∈ agreeSet (fun i => P.eval (dom i))
          (fun i => Q.eval (dom i)) := Finset.mem_coe.mp hi
      rw [agreeSet, Finset.mem_filter] at hi'
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD0]
      show (Q - P).eval (dom i) = 0
      rw [eval_sub, sub_eq_zero]
      exact hi'.2.symm
    · exact fun i _ j _ h => dom.injective h
  calc (agreeSet (fun i => P.eval (dom i))
        (fun i => Q.eval (dom i))).card
      ≤ (Q - P).roots.toFinset.card := hsub
    _ ≤ Multiset.card (Q - P).roots := Multiset.toFinset_card_le _
    _ ≤ (Q - P).natDegree := Polynomial.card_roots' _
    _ ≤ A := hDdeg

open Classical in
/-- **THE UNCONDITIONAL DEEP-BAND FAILURE**: at every band radius, with no
side conditions, some stack satisfies
`C(n,k+m+1) ≤ 2 · #badSet · q^m · C(n,k)`. -/
theorem deep_band_failure_unconditional (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ 2 * (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m * n.choose k := by
  set q := Fintype.card F with hq
  set M := 2 * k + m + 2 with hM
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set Nm := Pm.card with hNm
  have hNmval : Nm = n.choose (k + m + 1) := by
    rw [hNm, hPm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos Nm with hNm0 | hNmpos
  · exact ⟨0, by rw [← hNmval, hNm0]; exact Nat.zero_le _⟩
  set Qc : (Fin M → F) → F[X] :=
    fun c => ∑ j : Fin M, C (c j) * X ^ (j : ℕ) with hQc
  -- coefficients of the family polynomial
  have hQccoeff : ∀ (c : Fin M → F) (j : Fin M), (Qc c).coeff (j : ℕ) = c j := by
    intro c j
    rw [hQc, Polynomial.finset_sum_coeff]
    calc ∑ i : Fin M, (C (c i) * X ^ (i : ℕ)).coeff (j : ℕ)
        = ∑ i : Fin M, (if i = j then c i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coeff_C_mul, coeff_X_pow]
          by_cases h : i = j
          · subst h
            simp
          · have : ((j : ℕ) = (i : ℕ)) ↔ False := by
              constructor
              · intro hji
                exact h (Fin.ext hji.symm)
              · exact False.elim
            rw [if_neg (by
              intro hji
              exact h (Fin.ext hji.symm)), if_neg h, mul_zero]
      _ = c j := by
          rw [Finset.sum_ite_eq' Finset.univ j (fun i => c i)]
          simp
  have hQcdeg : ∀ c : Fin M → F, (Qc c).natDegree ≤ M - 1 := by
    intro c
    rw [hQc]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    calc (C (c j) * X ^ (j : ℕ)).natDegree
        ≤ (C (c j)).natDegree + (X ^ (j : ℕ) : F[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ M - 1 := by
          rw [natDegree_C, natDegree_X_pow]
          have := j.2
          omega
  -- the degenerate stacks: all coefficients above k vanish
  set degen : Finset (Fin M → F) := Finset.univ.filter
    (fun c => ∀ j : Fin M, k < (j : ℕ) → c j = 0) with hdegen
  have hdegencard : degen.card ≤ q ^ (k + 1) := by
    have hk1M : k + 1 ≤ M := by rw [hM]; omega
    calc degen.card
        ≤ Fintype.card (Fin (k + 1) → F) := by
          refine Finset.card_le_card_of_injOn
            (fun c => fun i : Fin (k + 1) => c (Fin.castLE hk1M i))
            (fun c _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
          intro a ha b hb hab
          have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
          funext j
          by_cases hj : (j : ℕ) < k + 1
          · have := congrFun hab ⟨(j : ℕ), hj⟩
            simpa [Fin.castLE] using this
          · rw [ha' j (by omega), hb' j (by omega)]
      _ = q ^ (k + 1) := by
          rw [Fintype.card_fun, Fintype.card_fin, hq]
  -- nondegenerate stacks have all their lines degree-capped off-code
  have hlinecap : ∀ c : Fin M → F, c ∉ degen → ∀ γ : F,
      ∀ P : F[X], P.degree < (k : ℕ) → Qc c + C γ * X ^ k ≠ P := by
    intro c hc γ P hPdeg heq2
    rw [hdegen, Finset.mem_filter] at hc
    push Not at hc
    obtain ⟨j, hjk, hjne⟩ := hc (Finset.mem_univ c)
    have h1 : (Qc c + C γ * X ^ k).coeff (j : ℕ) = c j := by
      rw [coeff_add, hQccoeff, coeff_C_mul, coeff_X_pow,
        if_neg (by omega), mul_zero, add_zero]
    have h2 : P.coeff (j : ℕ) = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      exact lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_of_lt hjk)
    rw [heq2, h2] at h1
    exact hjne h1.symm
  -- ── per-core averaging (the multi-kernel bound, as in the witness mass) ──
  have hsubQc : ∀ x y : Fin M → F, Qc (x - y) = Qc x - Qc y := by
    intro x y
    rw [hQc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show C (x j - y j) * X ^ (j : ℕ) = _
    rw [C_sub]
    ring
  have hsubI : ∀ (T : Finset (Fin n)) (x y : Fin M → F),
      coreInterp dom T (Qc (x - y))
        = coreInterp dom T (Qc x) - coreInterp dom T (Qc y) := by
    intro T x y
    rw [coreInterp, coreInterp, coreInterp, hsubQc]
    have hvals : (fun i => (Qc x - Qc y).eval (dom i))
        = (fun i => (Qc x).eval (dom i)) - (fun i => (Qc y).eval (dom i)) := by
      funext i
      simp [eval_sub]
    rw [hvals, map_sub]
  have hpercore : ∀ T ∈ Pm,
      q ^ M ≤ (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m := by
    intro T _
    have h := card_multiKernel_ge
      (φ := fun (j : Fin m) (c : Fin M → F) =>
        (coreInterp dom T (Qc c)).coeff (k + 1 + j))
      (fun j x y => by
        show (coreInterp dom T (Qc (x - y))).coeff (k + 1 + (j : ℕ))
            = (coreInterp dom T (Qc x)).coeff (k + 1 + (j : ℕ))
              - (coreInterp dom T (Qc y)).coeff (k + 1 + (j : ℕ))
        rw [hsubI T x y, coeff_sub])
    have hfeq : (Finset.univ.filter
          (fun c : Fin M → F => IsCoherent dom k m T (Qc c)))
        = (Finset.univ.filter (fun c : Fin M → F => ∀ j : Fin m,
            (fun (j : Fin m) (c : Fin M → F) =>
              (coreInterp dom T (Qc c)).coeff (k + 1 + j)) j c = 0)) :=
      Finset.filter_congr fun c _ => Iff.rfl
    rw [hq, hfeq]
    exact h
  -- total coherent mass, with the degenerate mass subtracted
  have hcohbound : ∀ c : Fin M → F,
      (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card ≤ Nm := by
    intro c
    rw [hNm]
    exact Finset.card_filter_le _ _
  have hswap : ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (Qc c))).card
      = ∑ T ∈ Pm, (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have htotal : Nm * q ^ M ≤ (∑ c : Fin M → F, (Pm.filter
      (fun T => IsCoherent dom k m T (Qc c))).card) * q ^ m := by
    calc Nm * q ^ M = ∑ T ∈ Pm, q ^ M := by
          rw [Finset.sum_const, smul_eq_mul, hNm]
      _ ≤ ∑ T ∈ Pm, (Finset.univ.filter
            (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m :=
          Finset.sum_le_sum hpercore
      _ = _ := by rw [← Finset.sum_mul, ← hswap]
  -- pigeonhole over the nondegenerate stacks
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Fintype.one_lt_card
  have hgoodpigeon : ∃ c : Fin M → F, c ∉ degen ∧
      Nm ≤ 2 * (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card
        * q ^ m := by
    by_contra hall
    push Not at hall
    -- every stack is either degenerate or low-mass
    have hsplit : ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
        < Nm * q ^ M + Nm * q ^ M := by
      have hbound : ∀ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
          ≤ if c ∈ degen then Nm * (2 * q ^ m) else Nm - 1 := by
        intro c
        by_cases hc : c ∈ degen
        · rw [if_pos hc]
          exact Nat.mul_le_mul_right _ (hcohbound c)
        · rw [if_neg hc]
          have h := hall c hc
          have h2 : 2 * (Pm.filter
              (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m
              ≤ Nm - 1 := by omega
          calc (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card
                * (2 * q ^ m)
              = 2 * (Pm.filter
                (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m := by
                ring
            _ ≤ Nm - 1 := h2
      calc ∑ c : Fin M → F, (Pm.filter
            (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
          ≤ ∑ c : Fin M → F, (if c ∈ degen then Nm * (2 * q ^ m)
              else Nm - 1) := Finset.sum_le_sum fun c _ => hbound c
        _ = degen.card * (Nm * (2 * q ^ m))
            + (q ^ M - degen.card) * (Nm - 1) := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
              smul_eq_mul, smul_eq_mul]
            have hf1 : (Finset.univ.filter
                (fun c : Fin M → F => c ∈ degen)) = degen := by
              rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            have hf2 : (Finset.univ.filter
                (fun c : Fin M → F => ¬ c ∈ degen)).card
                = q ^ M - degen.card := by
              have h := Finset.card_filter_add_card_filter_not
                (s := (Finset.univ : Finset (Fin M → F)))
                (fun c => c ∈ degen)
              rw [hf1] at h
              have hcu : (Finset.univ : Finset (Fin M → F)).card = q ^ M := by
                rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq]
              omega
            rw [hf1, hf2]
        _ < Nm * q ^ M + Nm * q ^ M := by
            have hdc := hdegencard
            have hqM : q ^ (k + 1) * (2 * q ^ m) ≤ q ^ M := by
              have hexp : k + 1 + (m + 1) ≤ M := by rw [hM]; omega
              calc q ^ (k + 1) * (2 * q ^ m)
                  ≤ q ^ (k + 1) * (q * q ^ m) :=
                    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq2)
                _ = q ^ (k + 1 + (m + 1)) := by ring
                _ ≤ q ^ M := Nat.pow_le_pow_right (by omega) hexp
            have h1 : degen.card * (Nm * (2 * q ^ m)) ≤ Nm * q ^ M := by
              calc degen.card * (Nm * (2 * q ^ m))
                  = Nm * (degen.card * (2 * q ^ m)) := by ring
                _ ≤ Nm * (q ^ (k + 1) * (2 * q ^ m)) := by
                    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdc)
                _ ≤ Nm * q ^ M := Nat.mul_le_mul_left _ hqM
            have h2 : (q ^ M - degen.card) * (Nm - 1) < Nm * q ^ M := by
              have hqMpos : 0 < q ^ M := pow_pos (by omega) M
              calc (q ^ M - degen.card) * (Nm - 1)
                  ≤ q ^ M * (Nm - 1) :=
                    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                _ < q ^ M * Nm := (Nat.mul_lt_mul_left hqMpos).mpr (by omega)
                _ = Nm * q ^ M := by ring
            omega
    have htot2 : Nm * q ^ M + Nm * q ^ M
        ≤ ∑ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m) := by
      calc Nm * q ^ M + Nm * q ^ M
          = 2 * (Nm * q ^ M) := by ring
        _ ≤ 2 * ((∑ c : Fin M → F, (Pm.filter
            (fun T => IsCoherent dom k m T (Qc c))).card) * q ^ m) :=
            Nat.mul_le_mul_left _ htotal
        _ = _ := by
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by ring
    exact absurd (lt_of_le_of_lt htot2 hsplit) (lt_irrefl _)
  obtain ⟨c, hcgood, hcmass⟩ := hgoodpigeon
  refine ⟨Qc c, ?_⟩
  -- fibers of the value map are capped at C(n,k)
  set coh := Pm.filter (fun T => IsCoherent dom k m T (Qc c)) with hcoh
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (Qc c).eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  set val : Finset (Fin n) → F :=
    fun T => -(coreInterp dom T (Qc c)).coeff k with hval
  have hmaps : ∀ T ∈ coh, val T ∈ bad := by
    intro T hT
    obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hT
    have hTcard : T.card = k + m + 1 :=
      (Finset.mem_powersetCard.mp hTmem).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mcaEvent_of_coherent dom hk hhi hTcard hTc⟩
  have hfiber : ∀ γ, (coh.filter (fun T => val T = γ)).card ≤ n.choose k := by
    intro γ
    -- the fiber consists of explainable cores of one degree-capped line
    have hsub2 : coh.filter (fun T => val T = γ)
        ⊆ Pm.filter (fun T => ExplainableOn dom k
            (fun i => (Qc c + C γ * X ^ k).eval (dom i)) T) := by
      intro T hT
      obtain ⟨hTcoh, hTval⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hTcoh
      have hTcard : T.card = k + m + 1 :=
        (Finset.mem_powersetCard.mp hTmem).2
      refine Finset.mem_filter.mpr ⟨hTmem, ?_⟩
      have h := coherent_explains_line dom hTcard hTc
      rw [show -(coreInterp dom T (Qc c)).coeff k = val T from rfl,
        hTval] at h
      obtain ⟨cw, hcwC, hcwag⟩ := h
      refine ⟨cw, hcwC, fun i hi => ?_⟩
      rw [hcwag i hi]
      simp [eval_add, eval_mul]
    -- the line's agreements are capped at M − 1 = 2k+m+1
    have hagcap : ∀ cw ∈ (rsCode dom k : Submodule F (Fin n → F)),
        (agreeSet cw (fun i => (Qc c + C γ * X ^ k).eval (dom i))).card
          ≤ M - 1 := by
      refine agreeSet_card_le_of_natDegree_le dom (by rw [hM]; omega) ?_
        (hlinecap c hcgood γ)
      calc (Qc c + C γ * X ^ k).natDegree
          ≤ max (Qc c).natDegree (C γ * X ^ k).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ M - 1 := by
            refine max_le (hQcdeg c) ?_
            calc (C γ * X ^ k).natDegree
                ≤ (C γ).natDegree + (X ^ k : F[X]).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ M - 1 := by
                  rw [natDegree_C, natDegree_X_pow, hM]
                  omega
    -- apply the agreement-capped supply at the cap
    have hsupply := explainable_cores_card_of_agreement_le dom
      (m := m) hk hagcap
    have hMk : M - 1 - k = k + m + 1 := by rw [hM]; omega
    rw [hMk] at hsupply
    have hsymm : (k + m + 1).choose (m + 1) = (k + m + 1).choose k := by
      have h := Nat.choose_symm (n := k + m + 1) (k := k) (by omega)
      rw [show k + m + 1 - k = m + 1 from by omega] at h
      exact h
    rw [hsymm] at hsupply
    have hchoosepos : 0 < (k + m + 1).choose k :=
      Nat.choose_pos (by omega)
    have hle : (coh.filter (fun T => val T = γ)).card
        ≤ (Pm.filter (fun T => ExplainableOn dom k
            (fun i => (Qc c + C γ * X ^ k).eval (dom i)) T)).card :=
      Finset.card_le_card hsub2
    have h2 : (coh.filter (fun T => val T = γ)).card * (k + m + 1).choose k
        ≤ n.choose k * (k + m + 1).choose k := by
      calc (coh.filter (fun T => val T = γ)).card * (k + m + 1).choose k
          ≤ (Pm.filter (fun T => ExplainableOn dom k
              (fun i => (Qc c + C γ * X ^ k).eval (dom i)) T)).card
              * (k + m + 1).choose k := Nat.mul_le_mul_right _ hle
        _ ≤ n.choose k * (k + m + 1).choose k := hsupply
    exact Nat.le_of_mul_le_mul_right h2 hchoosepos
  -- assemble
  have hcount : coh.card ≤ bad.card * n.choose k := by
    calc coh.card
        = ∑ γ ∈ bad, (coh.filter (fun T => val T = γ)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ γ ∈ bad, n.choose k := Finset.sum_le_sum fun γ _ => hfiber γ
      _ = bad.card * n.choose k := by rw [Finset.sum_const, smul_eq_mul]
  calc n.choose (k + m + 1) = Nm := hNmval.symm
    _ ≤ 2 * coh.card * q ^ m := hcmass
    _ ≤ 2 * (bad.card * n.choose k) * q ^ m := by
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcount)
    _ = 2 * bad.card * q ^ m * n.choose k := by ring

open Classical in
/-- Quotient form of `deep_band_failure_unconditional`: the same product inequality exposes
the residual wall as an explicit Nat floor
`C(n,k+m+1) / (2*q^m*C(n,k))` bad scalars on one generated stack. -/
theorem deep_band_failure_badSet_card_ge_div (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1) / (2 * (Fintype.card F) ^ m * n.choose k)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card := by
  obtain ⟨Q₀, hQ₀⟩ := deep_band_failure_unconditional dom hk hhi
  set bad : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)
  refine ⟨Q₀, ?_⟩
  have hmul :
      n.choose (k + m + 1)
        ≤ (2 * (Fintype.card F) ^ m * n.choose k) * bad.card := by
    calc n.choose (k + m + 1)
        ≤ 2 * bad.card * (Fintype.card F) ^ m * n.choose k := by
          simpa [bad] using hQ₀
      _ = (2 * (Fintype.card F) ^ m * n.choose k) * bad.card := by ring
  exact Nat.div_le_of_le_mul hmul

open Classical in
/-- Product-inequality consumer for `deep_band_failure_unconditional`: if a
target `B` is below the proven quotient
`C(n,k+m+1)/(2 q^m C(n,k))`, then some generated stack has more than `B`
bad scalars.  This division-free form is the safest way to instantiate the
unconditional deep-band failure theorem in concrete parameter budgets. -/
theorem deep_band_failure_badSet_card_gt_of_mul_lt (dom : Fin n ↪ F)
    {k m B : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hB : B * (2 * (Fintype.card F) ^ m * n.choose k)
      < n.choose (k + m + 1)) :
    ∃ Q₀ : F[X],
      B < (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card := by
  obtain ⟨Q₀, hQ₀⟩ := deep_band_failure_unconditional dom hk hhi
  refine ⟨Q₀, ?_⟩
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)
  have hQ : n.choose (k + m + 1)
      ≤ 2 * bad.card * (Fintype.card F) ^ m * n.choose k := by
    simpa [bad] using hQ₀
  by_contra hnot
  have hleB : bad.card ≤ B := by omega
  have hprod : 2 * bad.card * (Fintype.card F) ^ m * n.choose k
      ≤ B * (2 * (Fintype.card F) ^ m * n.choose k) := by
    calc 2 * bad.card * (Fintype.card F) ^ m * n.choose k
        = bad.card * (2 * (Fintype.card F) ^ m * n.choose k) := by ring
      _ ≤ B * (2 * (Fintype.card F) ^ m * n.choose k) :=
        Nat.mul_le_mul_right _ hleB
  exact (lt_irrefl (B * (2 * (Fintype.card F) ^ m * n.choose k)))
    (lt_of_lt_of_le (lt_of_lt_of_le hB hQ) hprod)

open Classical in
/-- Nonempty-band corollary: whenever there is at least one `(k+m+1)`-core,
some generated stack has at least one bad scalar at the band radius. -/
theorem deep_band_failure_badSet_card_pos (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hcore : 0 < n.choose (k + m + 1)) :
    ∃ Q₀ : F[X],
      0 < (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card := by
  simpa using deep_band_failure_badSet_card_gt_of_mul_lt
    (dom := dom) (k := k) (m := m) (B := 0) hk hhi (by simpa using hcore)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.agreeSet_card_le_of_natDegree_le
#print axioms ProximityGap.Ownership.deep_band_failure_unconditional
#print axioms ProximityGap.Ownership.deep_band_failure_badSet_card_ge_div
#print axioms ProximityGap.Ownership.deep_band_failure_badSet_card_gt_of_mul_lt
#print axioms ProximityGap.Ownership.deep_band_failure_badSet_card_pos
