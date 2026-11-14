/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._W14JacobiWindowMomentEquivalence

/-!
# ZW14 — DISCHARGE of the named open input `MomentsDetermineWindow` (#466)

**Target socket** (`ArkLib/Research/ProximityGap/Frontier/_W14JacobiWindowMomentEquivalence.lean`,
namespace `ArkLib.ProximityGap.Frontier.W14WindowMoment`):

> `MomentsDetermineWindow (N K : ℕ) : Prop` — two Jacobi-normalized (symmetric tridiagonal,
> positive-subdiagonal) `N × N` real matrices with equal `(·^r)₀₀` for all `r ≤ 2K+1` agree
> on the `(K+1) × (K+1)` corner.

**This file PROVES the socket unconditionally** (`momentsDetermineWindow_holds`, stated directly
as `W14WindowMoment.MomentsDetermineWindow N K`): the classical Lanczos / Gram–Schmidt uniqueness
direction, done here as a direct induction on the corner depth `j`:

1. *b-step*: `m_{2j+2} = ∑_k v_k²` with `v = A^{j+1} e₀` supported on `{0,…,j+1}`
   (Krylov support growth).  Off-tip entries of `v` are already determined by the depth-`j`
   corner (corner-agreement propagation), so the moment pins the tip square
   `v_{j+1}² = (b_1 ⋯ b_{j+1})²`; strict positivity of the subdiagonal makes the square root
   unambiguous, and the single-hop recursion `v_{j+1} = b_{j+1} · (A^j e₀)_j` peels off
   `b_{j+1}`.
2. *a-step*: `m_{2j+3} = ∑_k v_k · w_k` with `w = A^{j+2} e₀`.  After the b-step every
   ingredient agrees except the diagonal cell `a_{j+1}`, which enters with coefficient
   `v_{j+1}² > 0`; cancellation pins `a_{j+1}`.

The degenerate regimes (`j + 1 ≥ N`, where the corner saturates the whole matrix, and
`N = 0/1`) are handled inside the induction, so the theorem holds for ALL `N, K` with no side
conditions — exactly the socket's statement.

## Integration

This file imports the W14 file and uses its vocabulary (`IsTridiagonal`, `CornerAgree`,
`PosSubdiag`, `MomentsDetermineWindow`) and its proven support/propagation lemmas
(`pow_firstcol_eq_zero_of_lt`, `pow_firstcol_agree`, `window_determines_moments`) directly; no
copies.  The unconditional consumers at the end instantiate W14's conditional theorems
(`cornerAgree_iff_moments_agree`, `truncation_invariant_is_lowMoment_functional`) with
`momentsDetermineWindow_holds`.

## Honesty contract

NO core / cancellation / completion / moment-saving / anti-concentration / capacity claim.
This discharges the single named classical-OP input of the W14 seam-collapse verdict; the
BGK/Paley wall (`M ≤ C√(n log p)`) remains OPEN and is not touched.  Axiom audit at the
bottom of the file; expected: `[propext, Classical.choice, Quot.sound]` throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000


namespace ArkLib.ProximityGap.Frontier.ZW14MomentsDischarge

open Matrix

variable {N : ℕ}

open ArkLib.ProximityGap.Frontier.W14WindowMoment

/-! ## Local helpers (the W14 versions are `private`) -/

/-- `A^(s+1) = A * A^s` (robust local form, no name dependence on `pow_succ'`). -/
private theorem pow_succ_left (A : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) :
    A ^ (s + 1) = A * A ^ s := by
  conv_lhs => rw [show s + 1 = 1 + s by omega, pow_add, pow_one]

/-- Powers of a symmetric matrix are symmetric. -/
private theorem pow_transpose_eq {A : Matrix (Fin N) (Fin N) ℝ} (hsym : A.IsSymm) (s : ℕ) :
    (A ^ s)ᵀ = A ^ s := by
  rw [Matrix.transpose_pow, hsym.eq]

/-! ## New machinery for the converse -/

/-- Entry-level symmetry. -/
private theorem entry_symm {A : Matrix (Fin N) (Fin N) ℝ} (hsym : A.IsSymm) (i j : Fin N) :
    A i j = A j i :=
  (hsym.apply i j).symm

/-- Entry-level symmetry of powers. -/
private theorem pow_entry_symm {A : Matrix (Fin N) (Fin N) ℝ} (hsym : A.IsSymm) (s : ℕ)
    (i j : Fin N) : (A ^ s) i j = (A ^ s) j i := by
  have h := congrFun (congrFun (pow_transpose_eq hsym s) i) j
  rw [Matrix.transpose_apply] at h
  exact h.symm

/-- **Single-hop tip recursion.** For tridiagonal `A`, the tip entry of the Krylov vector
factors through the last subdiagonal hop: `(A^(t+1))_{t+1,0} = A_{t+1,t} · (A^t)_{t,0}`.
(A length-`(t+1)` walk from `0` reaching coordinate `t+1` must make its final hop from `t`.) -/
theorem pow_firstcol_tip_succ {A : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) {i0 : Fin N} (h0 : (i0 : ℕ) = 0)
    {t : ℕ} {i kt : Fin N} (hi : (i : ℕ) = t + 1) (hkt : (kt : ℕ) = t) :
    (A ^ (t + 1)) i i0 = A i kt * (A ^ t) kt i0 := by
  rw [pow_succ_left, Matrix.mul_apply]
  refine Finset.sum_eq_single_of_mem kt (Finset.mem_univ _) fun b _ hb => ?_
  by_cases hbt : t < (b : ℕ)
  · rw [pow_firstcol_eq_zero_of_lt htri h0 t b hbt, mul_zero]
  · have hbv : (b : ℕ) ≠ t := fun h => hb (Fin.val_injective (by omega))
    have hlt : (b : ℕ) + 1 < (i : ℕ) := by omega
    rw [htri i b (Or.inr hlt), zero_mul]

/-- **Tip positivity.** For a Jacobi-normalized matrix the Krylov tip entry is the product of
subdiagonal entries `b_1 ⋯ b_t`, hence strictly positive: `0 < (A^t)_{t,0}`. -/
theorem pow_firstcol_tip_pos {A : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (hsym : A.IsSymm) (hpos : PosSubdiag A)
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    ∀ (t : ℕ) (i : Fin N), (i : ℕ) = t → 0 < (A ^ t) i i0 := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have hii0 : i = i0 := Fin.val_injective (by omega)
    rw [hii0, pow_zero, Matrix.one_apply_eq]
    exact zero_lt_one
  | succ t ih =>
    intro i hi
    have htN : t < N := by have := i.isLt; omega
    have hkt : ((⟨t, htN⟩ : Fin N) : ℕ) = t := rfl
    rw [pow_firstcol_tip_succ htri h0 hi hkt]
    have h1 : 0 < A i ⟨t, htN⟩ := by
      have h2 : 0 < A ⟨t, htN⟩ i := hpos ⟨t, htN⟩ i (show t + 1 = (i : ℕ) by omega)
      rw [entry_symm hsym i ⟨t, htN⟩]
      exact h2
    exact mul_pos h1 (ih ⟨t, htN⟩ hkt)

/-- **THE INDUCTIVE STEP.**  If the depth-`j` corners agree and the two moments
`m_{2j+2}, m_{2j+3}` agree, then the depth-`(j+1)` corners agree: the even moment pins
`b_{j+1}` (via the Krylov tip square and positivity), the odd moment then pins `a_{j+1}`
(its coefficient is the tip square `> 0`). -/
theorem cornerAgree_succ {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : PosSubdiag A) (hpos' : PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0) {j : ℕ}
    (hm2 : (A ^ (2 * j + 2)) i0 i0 = (A' ^ (2 * j + 2)) i0 i0)
    (hm3 : (A ^ (2 * j + 3)) i0 i0 = (A' ^ (2 * j + 3)) i0 i0)
    (hprev : CornerAgree A A' j) :
    CornerAgree A A' (j + 1) := by
  by_cases hsN : j + 1 < N
  · -- Main case: coordinate `j+1` exists.
    obtain ⟨ks, hks⟩ : ∃ ks : Fin N, (ks : ℕ) = j + 1 := ⟨⟨j + 1, hsN⟩, rfl⟩
    obtain ⟨kj, hkj⟩ : ∃ kj : Fin N, (kj : ℕ) = j := ⟨⟨j, by omega⟩, rfl⟩
    have hkj_ne_ks : kj ≠ ks := fun h => by
      have := congrArg Fin.val h; omega
    -- (B1) off-tip Krylov agreement at exponent j+1
    have hv : ∀ k : Fin N, (k : ℕ) ≤ j →
        (A ^ (j + 1)) k i0 = (A' ^ (j + 1)) k i0 := fun k hk =>
      pow_firstcol_agree htri htri' hprev h0 (j + 1) le_rfl k hk
    -- moment expansions as Krylov quadratic forms
    have hexp2 : ∀ B : Matrix (Fin N) (Fin N) ℝ, B.IsSymm →
        (B ^ (2 * j + 2)) i0 i0
          = ∑ k : Fin N, (B ^ (j + 1)) k i0 * (B ^ (j + 1)) k i0 := by
      intro B hB
      rw [show 2 * j + 2 = (j + 1) + (j + 1) by omega, pow_add B (j + 1) (j + 1),
        Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_entry_symm hB (j + 1) i0 k]
    have hexp3 : ∀ B : Matrix (Fin N) (Fin N) ℝ, B.IsSymm →
        (B ^ (2 * j + 3)) i0 i0
          = ∑ k : Fin N, (B ^ (j + 1)) k i0 * (B ^ (j + 2)) k i0 := by
      intro B hB
      rw [show 2 * j + 3 = (j + 1) + (j + 2) by omega, pow_add B (j + 1) (j + 2),
        Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_entry_symm hB (j + 1) i0 k]
    -- (B2) the even moment pins the Krylov tip
    have hsum2 : ∑ k : Fin N, (A ^ (j + 1)) k i0 * (A ^ (j + 1)) k i0
        = ∑ k : Fin N, (A' ^ (j + 1)) k i0 * (A' ^ (j + 1)) k i0 := by
      rw [← hexp2 A hsym, ← hexp2 A' hsym']; exact hm2
    have hrest2 : ∑ k ∈ Finset.univ.erase ks, (A ^ (j + 1)) k i0 * (A ^ (j + 1)) k i0
        = ∑ k ∈ Finset.univ.erase ks, (A' ^ (j + 1)) k i0 * (A' ^ (j + 1)) k i0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkne : (k : ℕ) ≠ j + 1 := fun h =>
        Finset.ne_of_mem_erase hk (Fin.val_injective (by omega))
      by_cases hkle : (k : ℕ) ≤ j
      · rw [hv k hkle]
      · have hgt : j + 1 < (k : ℕ) := by omega
        rw [pow_firstcol_eq_zero_of_lt htri h0 (j + 1) k hgt,
          pow_firstcol_eq_zero_of_lt htri' h0 (j + 1) k hgt]
    have hpeel2 : (A ^ (j + 1)) ks i0 * (A ^ (j + 1)) ks i0
        + ∑ k ∈ Finset.univ.erase ks, (A ^ (j + 1)) k i0 * (A ^ (j + 1)) k i0
        = ∑ k : Fin N, (A ^ (j + 1)) k i0 * (A ^ (j + 1)) k i0 :=
      Finset.add_sum_erase Finset.univ
        (fun k => (A ^ (j + 1)) k i0 * (A ^ (j + 1)) k i0) (Finset.mem_univ ks)
    have hpeel2' : (A' ^ (j + 1)) ks i0 * (A' ^ (j + 1)) ks i0
        + ∑ k ∈ Finset.univ.erase ks, (A' ^ (j + 1)) k i0 * (A' ^ (j + 1)) k i0
        = ∑ k : Fin N, (A' ^ (j + 1)) k i0 * (A' ^ (j + 1)) k i0 :=
      Finset.add_sum_erase Finset.univ
        (fun k => (A' ^ (j + 1)) k i0 * (A' ^ (j + 1)) k i0) (Finset.mem_univ ks)
    have hsq : (A ^ (j + 1)) ks i0 * (A ^ (j + 1)) ks i0
        = (A' ^ (j + 1)) ks i0 * (A' ^ (j + 1)) ks i0 := by linarith
    have hPpos : 0 < (A ^ (j + 1)) ks i0 :=
      pow_firstcol_tip_pos htri hsym hpos h0 (j + 1) ks hks
    have hPpos' : 0 < (A' ^ (j + 1)) ks i0 :=
      pow_firstcol_tip_pos htri' hsym' hpos' h0 (j + 1) ks hks
    have htip : (A ^ (j + 1)) ks i0 = (A' ^ (j + 1)) ks i0 := by
      have hfac : ((A ^ (j + 1)) ks i0 - (A' ^ (j + 1)) ks i0)
          * ((A ^ (j + 1)) ks i0 + (A' ^ (j + 1)) ks i0) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hfac with hd | hs
      · linarith
      · linarith
    -- (B3) peel off b_{j+1}
    have hb : A ks kj = A' ks kj := by
      have hA1 : (A ^ (j + 1)) ks i0 = A ks kj * (A ^ j) kj i0 :=
        pow_firstcol_tip_succ htri h0 hks hkj
      have hA1' : (A' ^ (j + 1)) ks i0 = A' ks kj * (A' ^ j) kj i0 :=
        pow_firstcol_tip_succ htri' h0 hks hkj
      have hvj : (A ^ j) kj i0 = (A' ^ j) kj i0 :=
        pow_firstcol_agree htri htri' hprev h0 j (by omega) kj (by omega)
      have hQpos' : 0 < (A' ^ j) kj i0 :=
        pow_firstcol_tip_pos htri' hsym' hpos' h0 j kj hkj
      have h := htip
      rw [hA1, hA1', hvj] at h
      exact mul_right_cancel₀ (ne_of_gt hQpos') h
    have hbsymm : A kj ks = A' kj ks := by
      rw [entry_symm hsym kj ks, entry_symm hsym' kj ks]; exact hb
    -- (A1) off-tip Krylov agreement at exponent j+2 (uses the fresh b-agreement)
    have hw : ∀ k : Fin N, (k : ℕ) ≤ j →
        (A ^ (j + 2)) k i0 = (A' ^ (j + 2)) k i0 := by
      intro k hk
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ_left A (j + 1),
        pow_succ_left A' (j + 1), Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl1 : (l : ℕ) ≤ j
      · rw [hprev k l hk hl1, hv l hl1]
      · by_cases hl2 : (l : ℕ) = j + 1
        · have hlks : l = ks := Fin.val_injective (by omega)
          rw [hlks]
          have hAkl : A k ks = A' k ks := by
            by_cases hkj2 : (k : ℕ) = j
            · have hkkj : k = kj := Fin.val_injective (by omega)
              rw [hkkj]; exact hbsymm
            · have hz : (k : ℕ) + 1 < (ks : ℕ) := by omega
              rw [htri k ks (Or.inl hz), htri' k ks (Or.inl hz)]
          rw [hAkl, htip]
        · have hgt : j + 1 < (l : ℕ) := by omega
          rw [pow_firstcol_eq_zero_of_lt htri h0 (j + 1) l hgt,
            pow_firstcol_eq_zero_of_lt htri' h0 (j + 1) l hgt, mul_zero, mul_zero]
    -- (A2) the odd moment pins a_{j+1}
    have hsum3 : ∑ k : Fin N, (A ^ (j + 1)) k i0 * (A ^ (j + 2)) k i0
        = ∑ k : Fin N, (A' ^ (j + 1)) k i0 * (A' ^ (j + 2)) k i0 := by
      rw [← hexp3 A hsym, ← hexp3 A' hsym']; exact hm3
    have hrest3 : ∑ k ∈ Finset.univ.erase ks, (A ^ (j + 1)) k i0 * (A ^ (j + 2)) k i0
        = ∑ k ∈ Finset.univ.erase ks, (A' ^ (j + 1)) k i0 * (A' ^ (j + 2)) k i0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkne : (k : ℕ) ≠ j + 1 := fun h =>
        Finset.ne_of_mem_erase hk (Fin.val_injective (by omega))
      by_cases hkle : (k : ℕ) ≤ j
      · rw [hv k hkle, hw k hkle]
      · have hgt : j + 1 < (k : ℕ) := by omega
        rw [pow_firstcol_eq_zero_of_lt htri h0 (j + 1) k hgt,
          pow_firstcol_eq_zero_of_lt htri' h0 (j + 1) k hgt, zero_mul, zero_mul]
    have hpeel3 : (A ^ (j + 1)) ks i0 * (A ^ (j + 2)) ks i0
        + ∑ k ∈ Finset.univ.erase ks, (A ^ (j + 1)) k i0 * (A ^ (j + 2)) k i0
        = ∑ k : Fin N, (A ^ (j + 1)) k i0 * (A ^ (j + 2)) k i0 :=
      Finset.add_sum_erase Finset.univ
        (fun k => (A ^ (j + 1)) k i0 * (A ^ (j + 2)) k i0) (Finset.mem_univ ks)
    have hpeel3' : (A' ^ (j + 1)) ks i0 * (A' ^ (j + 2)) ks i0
        + ∑ k ∈ Finset.univ.erase ks, (A' ^ (j + 1)) k i0 * (A' ^ (j + 2)) k i0
        = ∑ k : Fin N, (A' ^ (j + 1)) k i0 * (A' ^ (j + 2)) k i0 :=
      Finset.add_sum_erase Finset.univ
        (fun k => (A' ^ (j + 1)) k i0 * (A' ^ (j + 2)) k i0) (Finset.mem_univ ks)
    have htipterm : (A ^ (j + 1)) ks i0 * (A ^ (j + 2)) ks i0
        = (A' ^ (j + 1)) ks i0 * (A' ^ (j + 2)) ks i0 := by linarith
    have hwtip : (A ^ (j + 2)) ks i0 = (A' ^ (j + 2)) ks i0 := by
      rw [htip] at htipterm
      exact mul_left_cancel₀ (ne_of_gt hPpos') htipterm
    -- two-term expansion of the tip of A^{j+2} e₀
    have hexpw : ∀ B : Matrix (Fin N) (Fin N) ℝ, IsTridiagonal B →
        (B ^ (j + 2)) ks i0
          = B ks kj * (B ^ (j + 1)) kj i0 + B ks ks * (B ^ (j + 1)) ks i0 := by
      intro B hB
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ_left B (j + 1), Matrix.mul_apply]
      refine Finset.sum_eq_add_of_mem kj ks (Finset.mem_univ _) (Finset.mem_univ _)
        hkj_ne_ks fun c _ hc => ?_
      by_cases hcle : (c : ℕ) ≤ j
      · have hcj : (c : ℕ) ≠ j := fun h => hc.1 (Fin.val_injective (by omega))
        have hz : (c : ℕ) + 1 < (ks : ℕ) := by omega
        rw [hB ks c (Or.inr hz), zero_mul]
      · have hcs : (c : ℕ) ≠ j + 1 := fun h => hc.2 (Fin.val_injective (by omega))
        have hgt : j + 1 < (c : ℕ) := by omega
        rw [pow_firstcol_eq_zero_of_lt hB h0 (j + 1) c hgt, mul_zero]
    have hvkj : (A ^ (j + 1)) kj i0 = (A' ^ (j + 1)) kj i0 := hv kj (by omega)
    have ha : A ks ks = A' ks ks := by
      rw [hexpw A htri, hexpw A' htri', hb, hvkj, htip] at hwtip
      exact mul_right_cancel₀ (ne_of_gt hPpos') (add_left_cancel hwtip)
    -- assemble the depth-(j+1) corner
    intro i l hi hl
    by_cases hi1 : (i : ℕ) ≤ j
    · by_cases hl1 : (l : ℕ) ≤ j
      · exact hprev i l hi1 hl1
      · have hlks : l = ks := Fin.val_injective (by omega)
        rw [hlks]
        by_cases hij : (i : ℕ) = j
        · have hikj : i = kj := Fin.val_injective (by omega)
          rw [hikj]; exact hbsymm
        · have hz : (i : ℕ) + 1 < (ks : ℕ) := by omega
          rw [htri i ks (Or.inl hz), htri' i ks (Or.inl hz)]
    · have hiks : i = ks := Fin.val_injective (by omega)
      rw [hiks]
      by_cases hl1 : (l : ℕ) ≤ j
      · by_cases hlj : (l : ℕ) = j
        · have hlkj : l = kj := Fin.val_injective (by omega)
          rw [hlkj]; exact hb
        · have hz : (l : ℕ) + 1 < (ks : ℕ) := by omega
          rw [htri ks l (Or.inr hz), htri' ks l (Or.inr hz)]
      · have hlks : l = ks := Fin.val_injective (by omega)
        rw [hlks]; exact ha
  · -- Degenerate case `j + 1 ≥ N`: the depth-(j+1) corner is the depth-j corner.
    intro i l hi hl
    exact hprev i l (by have := i.isLt; omega) (by have := l.isLt; omega)

/-- **MAIN: the socket `MomentsDetermineWindow` HOLDS, for every `N` and `K`,
unconditionally.**  Classical Lanczos / Gram–Schmidt uniqueness: equal moments to order
`2K+1` force equal depth-`K` Jacobi windows. -/
theorem momentsDetermineWindow_holds (N K : ℕ) : MomentsDetermineWindow N K := by
  intro A A' htri htri' hsym hsym' hpos hpos' i0 h0 hmom
  suffices h : ∀ j : ℕ, j ≤ K → CornerAgree A A' j by exact h K le_rfl
  intro j
  induction j with
  | zero =>
    intro _ i l hi hl
    have hii0 : i = i0 := Fin.val_injective (by omega)
    have hli0 : l = i0 := Fin.val_injective (by omega)
    rw [hii0, hli0]
    have h1 := hmom 1 (by omega)
    rwa [pow_one, pow_one] at h1
  | succ j ih =>
    intro hjK
    exact cornerAgree_succ htri htri' hsym hsym' hpos hpos' h0
      (hmom (2 * j + 2) (by omega)) (hmom (2 * j + 3) (by omega)) (ih (by omega))

/-! ## The W14 consumers, now UNCONDITIONAL

W14's conditional theorems instantiated with `momentsDetermineWindow_holds`. -/

/-- **The exact information-content identity, now with NO named input**: for Jacobi-normalized
matrices, depth-`K` corner agreement holds IFF all moments to order `2K+1` agree.  (W14's
`cornerAgree_iff_moments_agree` with the socket discharged.) -/
theorem cornerAgree_iff_moments_agree_unconditional
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : PosSubdiag A) (hpos' : PosSubdiag A')
    {K : ℕ} {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    CornerAgree A A' K ↔
      (∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) :=
  cornerAgree_iff_moments_agree (momentsDetermineWindow_holds N K)
    htri htri' hsym hsym' hpos hpos' h0

/-- **Seam collapse, now with NO named input** (W14's
`truncation_invariant_is_lowMoment_functional` with the socket discharged): every
corner-functional invariant of the Jacobi data at depth `K` is a functional of the moments
`m_0, …, m_{2K+1}` alone. -/
theorem truncation_invariant_is_lowMoment_functional_unconditional
    {X : Type} (Φ : Matrix (Fin N) (Fin N) ℝ → X) {K : ℕ}
    (hΦ : ∀ A A' : Matrix (Fin N) (Fin N) ℝ, CornerAgree A A' K → Φ A = Φ A')
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : PosSubdiag A) (hpos' : PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0)
    (hmom : ∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) :
    Φ A = Φ A' :=
  truncation_invariant_is_lowMoment_functional (momentsDetermineWindow_holds N K)
    Φ hΦ htri htri' hsym hsym' hpos hpos' h0 hmom

#print axioms pow_firstcol_tip_succ
#print axioms pow_firstcol_tip_pos
#print axioms cornerAgree_succ
#print axioms momentsDetermineWindow_holds
#print axioms cornerAgree_iff_moments_agree_unconditional
#print axioms truncation_invariant_is_lowMoment_functional_unconditional

end ArkLib.ProximityGap.Frontier.ZW14MomentsDischarge
