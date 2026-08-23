/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilLinearBudget

/-!
# The w = 2 window law: bad scalars ≤ n/2, SHARP (#371)

The first completely classified window slack.  For genuinely rational coprime
stacks with quadratic denominators at slack `w = 2` (whose open window is exactly
`n = k + 5`; deeper is the ladder), the bad-scalar count is at most `n/2` — and the
normalizer-pair family attains `(n−2)/2` (DISPROOF_LOG 2026-06-12), so this is
sharp to within one scalar.

**The mechanism (secant disjointness).**  Each bad scalar's explainer agreement set
is EXACTLY `n − 2` points (the residual `M_γ := ℓ₁R₀ + γ·ℓ₀R₁ − P_γ·ℓ₀ℓ₁` is a
nonzero polynomial of degree ≤ `k+3 = n−2`).  If two distinct bad scalars' missing
pairs `T_γ = D ∖ S_γ` shared a point, their agreement sets would share `≥ n − 3`
points, forcing the secant bracket `(γ−γ')·R₁ − (P_γ−P_{γ'})·ℓ₁` — degree
`≤ k+1 < n−3` — to vanish identically, i.e. `ℓ₁ ∣ R₁`: contradiction with
genuineness.  So the missing pairs are PAIRWISE DISJOINT: `2·#bad ≤ n`.

With the refuted `w+3` budget replaced by this n/2 law and the normalizer-pair
floor, the `w = 2` extremal value is pinned to `{(n−2)/2, n/2}` for every
field and every domain — the first sharp window slack of the programme.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The agreement-residual polynomial of an explainer `P` at scalar `γ`:
`M := ℓ₁·R₀ + γ·ℓ₀·R₁ − P·ℓ₀·ℓ₁`.  At domain points it vanishes exactly where `P`
explains the line. -/
noncomputable def w2Residual (ℓ₀ ℓ₁ R₀ R₁ P : F[X]) (γ : F) : F[X] :=
  ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁)

theorem w2Residual_eval_zero_iff {ℓ₀ ℓ₁ R₀ R₁ P : F[X]} {γ : F} {x : F}
    (h₀ : ℓ₀.eval x ≠ 0) (h₁ : ℓ₁.eval x ≠ 0) :
    (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).eval x = 0 ↔
      P.eval x = R₀.eval x / ℓ₀.eval x + γ * (R₁.eval x / ℓ₁.eval x) := by
  rw [w2Residual]
  simp only [eval_sub, eval_add, eval_mul, eval_C]
  constructor
  · intro h
    field_simp
    first
      | linear_combination h
      | linear_combination -h
      | linear_combination eval x ℓ₀ * eval x ℓ₁ * h
  · intro h
    rw [h]
    field_simp
    ring

theorem w2Residual_natDegree_le {ℓ₀ ℓ₁ R₀ R₁ P : F[X]} {γ : F} {k : ℕ}
    (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ 2) (hℓ₁d : ℓ₁.natDegree ≤ 2)
    (hR₀d : R₀.natDegree ≤ k + 1) (hR₁d : R₁.natDegree ≤ k + 1)
    (hPd : P.natDegree ≤ k - 1) :
    (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).natDegree ≤ k + 3 := by
  rw [w2Residual]
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_add_le _ _)
    (max_le ?_ ?_)) ?_)
  · calc (ℓ₁ * R₀).natDegree ≤ ℓ₁.natDegree + R₀.natDegree := natDegree_mul_le
      _ ≤ 2 + (k + 1) := Nat.add_le_add hℓ₁d hR₀d
      _ = k + 3 := by omega
  · calc (C γ * (ℓ₀ * R₁)).natDegree
        ≤ (C γ).natDegree + (ℓ₀ * R₁).natDegree := natDegree_mul_le
      _ ≤ 0 + (ℓ₀.natDegree + R₁.natDegree) :=
          Nat.add_le_add (le_of_eq (natDegree_C _)) natDegree_mul_le
      _ ≤ 0 + (2 + (k + 1)) :=
          Nat.add_le_add_left (Nat.add_le_add hℓ₀d hR₁d) 0
      _ ≤ k + 3 := by omega
  · calc (P * (ℓ₀ * ℓ₁)).natDegree
        ≤ P.natDegree + (ℓ₀ * ℓ₁).natDegree := natDegree_mul_le
      _ ≤ (k - 1) + (ℓ₀.natDegree + ℓ₁.natDegree) :=
          Nat.add_le_add hPd natDegree_mul_le
      _ ≤ (k - 1) + (2 + 2) := by omega
      _ ≤ k + 3 := by omega

/-- A nonzero polynomial of degree ≤ `d` vanishing on the embedded image of a set of
size > `d` is impossible (root counting through the embedding). -/
theorem eq_zero_of_vanishing_card_gt (dom : Fin n ↪ F) {Q : F[X]} {S : Finset (Fin n)}
    (hvan : ∀ i ∈ S, Q.eval (dom i) = 0) (hdeg : Q.natDegree < S.card) : Q = 0 := by
  by_contra hQne
  have hroots : (S.image dom).card ≤ Q.roots.toFinset.card := by
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hQne]
    exact hvan i hi
  have himg : (S.image dom).card = S.card :=
    Finset.card_image_of_injective _ dom.injective
  have h1 := Q.roots.toFinset_card_le
  have h2 := Q.card_roots'
  omega

section MainCount

variable (dom : Fin n ↪ F) {k : ℕ}
variable {ℓ₀ ℓ₁ R₀ R₁ : F[X]}

/-- The full agreement set of an explainer at a scalar. -/
noncomputable def w2Agr (ℓ₀ ℓ₁ R₀ R₁ P : F[X]) (γ : F) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).eval (dom i) = 0)

open Classical in
/-- **The secant-disjointness step.**  Two scalars with degree-`< k` explainers whose
agreement sets share `≥ n − 3` points are EQUAL, provided `u₁` is genuinely rational
(`ℓ₁ ∤ R₁`) and `n ≥ k + 5`. -/
theorem w2_shared_forces_eq (hk : 1 ≤ k) (hn : k + 5 ≤ n)
    (hℓ₁d : ℓ₁.natDegree ≤ 2) (hR₁d : R₁.natDegree ≤ k + 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {γ γ' : F} {P P' : F[X]}
    (hPd : P.natDegree ≤ k - 1) (hP'd : P'.natDegree ≤ k - 1)
    {I : Finset (Fin n)} (hIcard : n - 3 ≤ I.card)
    (hI : ∀ i ∈ I, (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).eval (dom i) = 0 ∧
      (w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ').eval (dom i) = 0) :
    γ = γ' := by
  by_contra hne
  -- the secant bracket
  set B : F[X] := C (γ - γ') * R₁ - (P - P') * ℓ₁ with hB
  -- B vanishes on I
  have hBvan : ∀ i ∈ I, B.eval (dom i) = 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hI i hi
    -- M_γ − M_γ' = ℓ₀ * B  evaluated at dom i
    have hdiff : (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ
        - w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ').eval (dom i) = 0 := by
      rw [eval_sub, h1, h2, sub_zero]
    have hfact : w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ - w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ'
        = ℓ₀ * B := by
      rw [hB, w2Residual, w2Residual, C_sub]
      ring
    rw [hfact, eval_mul] at hdiff
    exact (mul_eq_zero.mp hdiff).resolve_left (hℓ₀v i)
  -- degree of B
  have hBdeg : B.natDegree ≤ k + 1 := by
    rw [hB]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · calc (C (γ - γ') * R₁).natDegree
          ≤ (C (γ - γ')).natDegree + R₁.natDegree := natDegree_mul_le
        _ ≤ 0 + (k + 1) := Nat.add_le_add (le_of_eq (natDegree_C _)) hR₁d
        _ = k + 1 := by omega
    · calc ((P - P') * ℓ₁).natDegree
          ≤ (P - P').natDegree + ℓ₁.natDegree := natDegree_mul_le
        _ ≤ (k - 1) + 2 :=
            Nat.add_le_add (le_trans (natDegree_sub_le _ _)
              (max_le hPd hP'd)) hℓ₁d
        _ ≤ k + 1 := by omega
  -- forcing: B = 0
  have hB0 : B = 0 := by
    refine eq_zero_of_vanishing_card_gt dom hBvan ?_
    omega
  -- divisibility contradiction
  have hdvd : ℓ₁ ∣ C (γ - γ') * R₁ := by
    refine ⟨P - P', ?_⟩
    have := sub_eq_zero.mp hB0
    linear_combination this
  have h2 : ℓ₁ ∣ C (γ - γ')⁻¹ * (C (γ - γ') * R₁) := Dvd.dvd.mul_left hdvd _
  have h3 : C (γ - γ')⁻¹ * (C (γ - γ') * R₁) = R₁ := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]
  exact hgen₁ (h3 ▸ h2)

open Classical in
/-- The residual of a genuine coprime stack is never the zero polynomial. -/
theorem w2Residual_ne_zero {P : F[X]} {γ : F}
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀) :
    w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ ≠ 0 := by
  intro h0
  rw [w2Residual] at h0
  have hdvd : ℓ₀ ∣ ℓ₁ * R₀ := ⟨P * ℓ₁ - C γ * R₁, by linear_combination h0⟩
  exact hgen₀ (hcop.dvd_of_dvd_mul_left hdvd)

open Classical in
/-- **The canonical explainer**: every `mcaEvent`-bad scalar of a genuine coprime
quadratic-denominator stack at radius `δ ≤ 2/n` has an explainer of degree `< k`
whose full agreement set has size EXACTLY `n − 2`. -/
theorem w2_explainer (hk : 1 ≤ k) (hn : k + 5 ≤ n)
    (hℓ₀d : ℓ₀.natDegree ≤ 2) (hℓ₁d : ℓ₁.natDegree ≤ 2)
    (hR₀d : R₀.natDegree ≤ k + 1) (hR₁d : R₁.natDegree ≤ k + 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ 2) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) :
    ∃ P : F[X], P.natDegree ≤ k - 1 ∧
      (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card + 2 = n := by
  obtain ⟨S, hsz, ⟨c, hc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hc
  have hPd : P.natDegree ≤ k - 1 := by
    by_cases hP0 : P = 0
    · subst hP0; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  refine ⟨P, hPd, ?_⟩
  -- the witness size: n ≤ S.card + 2
  have hsize : n ≤ S.card + 2 := by
    have h1 : ((n - 2 : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - 2 : ℕ) : ℝ≥0) = (n : ℝ≥0) - (2 : ℝ≥0) := by
        rw [Nat.cast_tsub]; norm_num
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - 2 : ℕ) : ℝ≥0) = (n : ℝ≥0) - 2 := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact_mod_cast hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [tsub_mul, one_mul, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    have : (n - 2 : ℕ) ≤ S.card := by exact_mod_cast h1
    omega
  -- S sits inside the full agreement set
  have hsub : S ⊆ w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ := by
    intro i hi
    rw [w2Agr, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [w2Residual_eval_zero_iff (hℓ₀v i) (hℓ₁v i)]
    have := hag i hi
    simpa [smul_eq_mul] using this
  have hge : n - 2 ≤ (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card := by
    have := Finset.card_le_card hsub
    omega
  -- and is capped by the residual degree
  have hle : (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card ≤ k + 3 := by
    by_contra hbig
    push_neg at hbig
    have hM0 : w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ = 0 := by
      refine eq_zero_of_vanishing_card_gt dom
        (S := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ) (fun i hi => ?_) ?_
      · rw [w2Agr, Finset.mem_filter] at hi
        exact hi.2
      · have := w2Residual_natDegree_le (γ := γ) hk hℓ₀d hℓ₁d hR₀d hR₁d hPd
        omega
    exact w2Residual_ne_zero hcop hgen₀ hM0
  omega

open Classical in
/-- **THE w = 2 WINDOW LAW (sharp)**: a genuine coprime stack with quadratic
denominators has at most `n/2` bad scalars at every radius `δ ≤ 2/n`:
`2·#bad ≤ n`.  The normalizer-pair family attains `(n−2)/2`. -/
theorem w2_bad_card_le (hk : 1 ≤ k) (hn : k + 5 ≤ n)
    (hℓ₀d : ℓ₀.natDegree ≤ 2) (hℓ₁d : ℓ₁.natDegree ≤ 2)
    (hR₀d : R₀.natDegree ≤ k + 1) (hR₁d : R₁.natDegree ≤ k + 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀) (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ 2) :
    2 * (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ)).card ≤ n := by
  set Γ : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) with hΓ
  -- canonical explainers via choice
  have key : ∀ γ ∈ Γ, ∃ P : F[X], P.natDegree ≤ k - 1 ∧
      (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card + 2 = n := by
    intro γ hγ
    rw [hΓ, Finset.mem_filter] at hγ
    exact w2_explainer dom hk hn hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀
      hδn hγ.2
  choose! Pf hPfdeg hPfcard using key
  -- the missing pairs
  set T : F → Finset (Fin n) := fun γ =>
    Finset.univ \ w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ) γ with hT
  have hTcard : ∀ γ ∈ Γ, (T γ).card = 2 := by
    intro γ hγ
    rw [hT]
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, Fintype.card_fin]
    have := hPfcard γ hγ
    omega
  -- pairwise disjointness via the secant forcing
  have hdisj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Disjoint (T γ) (T γ') := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    -- both agreement sets miss i, so they intersect in ≥ n − 3 points
    set A := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ) γ with hA
    set A' := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ') γ' with hA'
    have hiA : i ∉ A := by
      rw [hT] at hi; simp only [Finset.mem_sdiff] at hi; exact hi.2
    have hiA' : i ∉ A' := by
      rw [hT] at hi'; simp only [Finset.mem_sdiff] at hi'; exact hi'.2
    have hunion : (A ∪ A').card ≤ n - 1 := by
      have hsub : A ∪ A' ⊆ Finset.univ.erase i := by
        intro j hj
        rw [Finset.mem_erase]
        refine ⟨fun hji => ?_, Finset.mem_univ _⟩
        subst hji
        rcases Finset.mem_union.mp hj with h | h
        · exact hiA h
        · exact hiA' h
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin] at this
      exact this
    have hIcard : n - 3 ≤ (A ∩ A').card := by
      have h1 := Finset.card_inter_add_card_union A A'
      have h2 := hPfcard γ hγ
      have h3 := hPfcard γ' hγ'
      rw [← hA] at h2
      rw [← hA'] at h3
      omega
    exact hne (w2_shared_forces_eq dom hk hn hℓ₁d hR₁d hℓ₀v hgen₁
      (hPfdeg γ hγ) (hPfdeg γ' hγ') hIcard (fun j hj => by
        have hjA := Finset.mem_of_mem_inter_left hj
        have hjA' := Finset.mem_of_mem_inter_right hj
        rw [hA, w2Agr, Finset.mem_filter] at hjA
        rw [hA', w2Agr, Finset.mem_filter] at hjA'
        exact ⟨hjA.2, hjA'.2⟩))
  -- the disjoint-union count
  have hbiU : (Γ.biUnion T).card = ∑ γ ∈ Γ, (T γ).card :=
    Finset.card_biUnion hdisj
  have hsum : ∑ γ ∈ Γ, (T γ).card = 2 * Γ.card := by
    rw [Finset.sum_congr rfl hTcard, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcap : (Γ.biUnion T).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (Γ.biUnion T))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  omega

end MainCount

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.w2_shared_forces_eq
#print axioms ProximityGap.WBPencil.w2_explainer
#print axioms ProximityGap.WBPencil.w2_bad_card_le
