/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowFiberPencil

/-!
# The window division identity and the chain-family kill (#371, G3 ladder)

The parametric engine for ALL window rows (`k = 1`), and the chain theory —
the first rung of the continued-fraction hierarchy behind the deep window:

* `witness_division_identity_window` — at ANY `n`, every bad scalar of a
  reduced-coprime doubly-rational stack yields an agreement set `S`
  (`n − w ≤ |S|`) and a NONZERO multiplier `g` with the graded budget
  `g.natDegree + S.card ≤ 2w` and the exact identity
  `R₀ℓ₁ + γ·R₁ℓ₀ − p·ℓ₀ℓ₁ = g·m_S`.  On the window rows this reads
  `deg g ≤ 3w − n`; above them it is contradictory (ladder-reach zero).
* `key_identity_window` / `witness_cross_dvd` — γ-elimination with polynomial
  multipliers: two witnesses cross-multiply to `ℓ₀ ∣ g₂·m̂₁ − g₁·m̂₂`.
* `chain_pair_factor` — complements sharing a `(w−1)`-core force the
  multiplier factorization `gᵢ = a·(X − τᵢ)` with a COMMON scalar `a`.
* `chain_member_exact` — a cored witness's identity cancels `(X−τ)`:
  `(R₀ℓ₁ + γR₁ℓ₀ − pℓ₀ℓ₁)·m_K = a·m_D` exactly.
* **`cored_gamma_unique`** — any two bad scalars with cored witnesses
  coincide: distinct cores are impossible (mod-`ℓ₀` reduction pins
  `a₁·m_{K₂} = a₂·m_{K₁}`, monicity forces `K₁ = K₂`), and a common core
  cancels to `(γ₁−γ₂)·R₁ = (p₁−p₂)·ℓ₁`, killed by second-row reducedness.
  The ENTIRE chain family carries at most one bad scalar.

Probe record: `probe_slack1_exact.py` (23,11,4): graded fiber = chain (8
members, unique core) + core witness + 2 exotics, exotic complements disjoint
from the core; `probe_wb371_g3_twosided.py`: the two-sided system is sound and
tight on stratum G (0 coverage gaps).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Vanishing polynomial of an inserted point. -/
theorem vanishingPoly_insert (dom : Fin n ↪ F) {K : Finset (Fin n)} {t : Fin n}
    (ht : t ∉ K) :
    vanishingPoly dom (insert t K) = (X - C (dom t)) * vanishingPoly dom K := by
  rw [vanishingPoly, vanishingPoly, Finset.prod_insert ht]

section WindowEngine

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

open Classical in
/-- **The parametric window division identity** (k = 1, every row).  The graded
budget `g.natDegree + S.card ≤ 2w` carries the row structure. -/
theorem witness_division_identity_window
    (hw : 1 ≤ w)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    ∃ (S : Finset (Fin n)) (g : F[X]) (p : F), g ≠ 0 ∧
      (n - w : ℕ) ≤ S.card ∧ g.natDegree + S.card ≤ 2 * w ∧
      (∀ i ∈ S, p = u₀ i + γ * u₁ i) ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = g * vanishingPoly dom S := by
  obtain ⟨S, hsz, ⟨wc, hwc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hwc
  have hPC : P = C (P.coeff 0) := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · refine Polynomial.eq_C_of_natDegree_le_zero ?_
      have hnd : P.natDegree < 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr (by exact_mod_cast hPdeg)
      omega
  set p := P.coeff 0 with hpdef
  have hagree : ∀ i ∈ S, p = u₀ i + γ * u₁ i := by
    intro i hi
    have hwci := hag i hi
    rw [hPC] at hwci
    simpa [smul_eq_mul] using hwci
  have hScard : n - w ≤ S.card := by
    have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
        rw [Nat.cast_tsub]
      have hδ1 : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)
          = (Fintype.card (Fin n) : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
        rw [tsub_mul, one_mul]
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [hδ1, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    exact_mod_cast h1
  set Φ : F[X] := R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) with hΦdef
  have hΦeval : ∀ i ∈ S, Φ.eval (dom i) = 0 := by
    intro i hi
    have h1 := hrel₀ i
    have h2 := hrel₁ i
    have h3 := hagree i hi
    simp only [hΦdef, eval_sub, eval_add, eval_mul, eval_C]
    rw [← h1, ← h2]
    linear_combination (-(ℓ₀.eval (dom i) * ℓ₁.eval (dom i))) * h3
  have hdvd : vanishingPoly dom S ∣ Φ := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hΦeval i hi
  have hℓ₀ne : ℓ₀ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hΦne : Φ ≠ 0 := by
    intro hΦ0
    have h0 : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) = 0 := by
      rw [← hΦdef]
      exact hΦ0
    have hdvd₀ : ℓ₀ ∣ R₀ * ℓ₁ :=
      ⟨C p * ℓ₁ - C γ * R₁, by linear_combination h0⟩
    have hcop : IsCoprime ℓ₀ (R₀ * ℓ₁) := IsCoprime.mul_right hcop₀.symm hcopℓ
    obtain ⟨a, b, hab⟩ := hcop
    have hone : ℓ₀ ∣ 1 := by
      rw [← hab]
      exact dvd_add (Dvd.intro a (mul_comm ℓ₀ a ▸ rfl))
        (Dvd.dvd.mul_left hdvd₀ b)
    have hunit : IsUnit ℓ₀ := isUnit_of_dvd_one hone
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  have hΦdeg : Φ.natDegree ≤ 2 * w := by
    have t1 : (R₀ * ℓ₁).natDegree ≤ 2 * w :=
      le_trans natDegree_mul_le (by omega)
    have t2 : (C γ * (R₁ * ℓ₀)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have h2 : (R₁ * ℓ₀).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      have := natDegree_C γ
      omega
    have t3 : (C p * (ℓ₀ * ℓ₁)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have h2 : (ℓ₀ * ℓ₁).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      have := natDegree_C p
      omega
    rw [hΦdef]
    exact le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (natDegree_add_le _ _) (max_le t1 t2)) t3)
  obtain ⟨cq, hcq⟩ := hdvd
  have hcqne : cq ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcq
    exact hΦne hcq
  have hbudget : cq.natDegree + S.card ≤ 2 * w := by
    have hmul := Polynomial.natDegree_mul (vanishingPoly_ne_zero dom S) hcqne
    rw [← hcq, vanishingPoly_natDegree] at hmul
    omega
  refine ⟨S, cq, p, hcqne, hScard, hbudget, hagree, ?_⟩
  calc R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = vanishingPoly dom S * cq := by rw [← hΦdef]; exact hcq
    _ = cq * vanishingPoly dom S := mul_comm _ _

/-- The complement-multiplied key identity, polynomial-multiplier version. -/
theorem key_identity_window {γ p : F} {g : F[X]} {S : Finset (Fin n)}
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = g * vanishingPoly dom S) :
    R₀ * ℓ₁ * vanishingPoly dom Sᶜ
      = g * vanishingPoly dom Finset.univ
        - ℓ₀ * ((C γ * R₁ - C p * ℓ₁) * vanishingPoly dom Sᶜ) := by
  have hmm := vanishingPoly_mul_compl dom S
  linear_combination (vanishingPoly dom Sᶜ) * hid + g * hmm

/-- **γ-elimination with polynomial multipliers**: cross-multiplying two
witnesses' key identities divides out `A = R₀ℓ₁`. -/
theorem witness_cross_dvd
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hcop₀ : IsCoprime R₀ ℓ₀)
    (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {γ₁ γ₂ p₁ p₂ : F} {g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hid₁ : R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁)
      = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁)
      = g₂ * vanishingPoly dom S₂) :
    ℓ₀ ∣ g₂ * vanishingPoly dom S₁ᶜ - g₁ * vanishingPoly dom S₂ᶜ := by
  have hkey₁ := key_identity_window (dom := dom) hid₁
  have hkey₂ := key_identity_window (dom := dom) hid₂
  have hcross : R₀ * ℓ₁ *
      (g₂ * vanishingPoly dom S₁ᶜ - g₁ * vanishingPoly dom S₂ᶜ)
      = ℓ₀ * (g₁ * ((C γ₂ * R₁ - C p₂ * ℓ₁) * vanishingPoly dom S₂ᶜ)
          - g₂ * ((C γ₁ * R₁ - C p₁ * ℓ₁) * vanishingPoly dom S₁ᶜ)) := by
    linear_combination g₂ * hkey₁ - g₁ * hkey₂
  have hcopRL : IsCoprime ℓ₀ (R₀ * ℓ₁) := IsCoprime.mul_right hcop₀.symm hcopℓ
  refine hcopRL.dvd_of_dvd_mul_left ?_
  exact ⟨g₁ * ((C γ₂ * R₁ - C p₂ * ℓ₁) * vanishingPoly dom S₂ᶜ)
      - g₂ * ((C γ₁ * R₁ - C p₁ * ℓ₁) * vanishingPoly dom S₁ᶜ),
    by linear_combination hcross⟩

/-- **The chain-pair factorization.**  Two witnesses whose complements share a
`(w−1)`-core force `g₁ = a(X−τ₁)`, `g₂ = a(X−τ₂)` with a common scalar. -/
theorem chain_pair_factor
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hdℓ₀ : ℓ₀.natDegree = w) (hw3 : 3 ≤ w)
    {K : Finset (Fin n)} {t₁ t₂ : Fin n} (htne : t₁ ≠ t₂)
    (ht₁ : t₁ ∉ K) (ht₂ : t₂ ∉ K)
    {g₁ g₂ : F[X]} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hdg₁ : g₁.natDegree ≤ 1) (hdg₂ : g₂.natDegree ≤ 1)
    (hcross : ℓ₀ ∣ g₂ * vanishingPoly dom (insert t₁ K)
      - g₁ * vanishingPoly dom (insert t₂ K)) :
    ∃ a : F, a ≠ 0 ∧ g₁ = C a * (X - C (dom t₁))
      ∧ g₂ = C a * (X - C (dom t₂)) := by
  rw [vanishingPoly_insert dom ht₁, vanishingPoly_insert dom ht₂] at hcross
  have hfac : ℓ₀ ∣ (g₂ * (X - C (dom t₁)) - g₁ * (X - C (dom t₂)))
      * vanishingPoly dom K := by
    obtain ⟨c, hc⟩ := hcross
    exact ⟨c, by linear_combination hc⟩
  have hcopK : IsCoprime ℓ₀ (vanishingPoly dom K) :=
    isCoprime_vanishingPoly dom hG₀ K
  have hdvd2 : ℓ₀ ∣ g₂ * (X - C (dom t₁)) - g₁ * (X - C (dom t₂)) :=
    hcopK.dvd_of_dvd_mul_right hfac
  -- degree < w forces exactness
  have hzero : g₂ * (X - C (dom t₁)) - g₁ * (X - C (dom t₂)) = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd2 hne
    have hd : (g₂ * (X - C (dom t₁)) - g₁ * (X - C (dom t₂))).natDegree ≤ 2 := by
      have e1 : (g₂ * (X - C (dom t₁))).natDegree ≤ 2 := by
        refine le_trans natDegree_mul_le ?_
        have := natDegree_X_sub_C (dom t₁)
        omega
      have e2 : (g₁ * (X - C (dom t₂))).natDegree ≤ 2 := by
        refine le_trans natDegree_mul_le ?_
        have := natDegree_X_sub_C (dom t₂)
        omega
      exact le_trans (natDegree_sub_le _ _) (max_le e1 e2)
    omega
  have heq : g₂ * (X - C (dom t₁)) = g₁ * (X - C (dom t₂)) :=
    sub_eq_zero.mp hzero
  -- (X − τ₁) divides g₁
  have hτne : dom t₁ ≠ dom t₂ := fun h => htne (dom.injective h)
  have hdvdX : (X - C (dom t₁)) ∣ g₁ * (X - C (dom t₂)) := ⟨g₂, by
    rw [← heq]
    ring⟩
  have hndvd : ¬ (X - C (dom t₁)) ∣ (X - C (dom t₂)) := by
    rw [Polynomial.dvd_iff_isRoot]
    simp only [IsRoot, eval_sub, eval_X, eval_C]
    exact fun h => hτne (sub_eq_zero.mp h)
  have hdvdg₁ : (X - C (dom t₁)) ∣ g₁ :=
    ((Polynomial.prime_X_sub_C (dom t₁)).dvd_mul.mp hdvdX).resolve_right hndvd
  obtain ⟨q, hq⟩ := hdvdg₁
  have hqC : q = C (q.coeff 0) := by
    refine Polynomial.eq_C_of_natDegree_le_zero ?_
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      exact hg₁ hq
    have hmul := Polynomial.natDegree_mul (X_sub_C_ne_zero (dom t₁)) hqne
    rw [← hq, natDegree_X_sub_C] at hmul
    omega
  set a := q.coeff 0 with hadef
  have hane : a ≠ 0 := by
    intro h0
    apply hg₁
    rw [hq, hqC, h0, map_zero, mul_zero]
  have hg₁eq : g₁ = C a * (X - C (dom t₁)) := by
    rw [hq, hqC]
    ring
  refine ⟨a, hane, hg₁eq, ?_⟩
  -- cancel (X − τ₁) in g₂(X−τ₁) = a(X−τ₁)(X−τ₂)
  have h2 : g₂ * (X - C (dom t₁))
      = (C a * (X - C (dom t₂))) * (X - C (dom t₁)) := by
    rw [heq, hg₁eq]
    ring
  exact mul_right_cancel₀ (X_sub_C_ne_zero (dom t₁)) h2

/-- **The chain cancellation**: a cored witness's identity cancels `(X−τ)`
exactly — `Φ·m_K = a·m_D`. -/
theorem chain_member_exact {γ p a : F} {K : Finset (Fin n)} {t : Fin n}
    (ht : t ∉ K)
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = (C a * (X - C (dom t))) * vanishingPoly dom (insert t K)ᶜ)
    (hcompl : vanishingPoly dom (insert t K) * vanishingPoly dom (insert t K)ᶜ
      = vanishingPoly dom Finset.univ) :
    (R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)) * vanishingPoly dom K
      = C a * vanishingPoly dom Finset.univ := by
  have hins := vanishingPoly_insert dom ht
  have hboth : (R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K * (X - C (dom t))
      = C a * vanishingPoly dom Finset.univ * (X - C (dom t)) := by
    calc (R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁))
        * vanishingPoly dom K * (X - C (dom t))
        = ((C a * (X - C (dom t))) * vanishingPoly dom (insert t K)ᶜ)
          * vanishingPoly dom K * (X - C (dom t)) := by rw [hid]
      _ = C a * (X - C (dom t))
          * ((vanishingPoly dom (insert t K)) * vanishingPoly dom (insert t K)ᶜ) := by
          rw [hins]
          ring
      _ = C a * vanishingPoly dom Finset.univ * (X - C (dom t)) := by
          rw [hcompl]
          ring
  exact mul_right_cancel₀ (X_sub_C_ne_zero (dom t)) hboth

/-- **THE CHAIN-FAMILY KILL**: any two bad scalars whose witnesses are cored
coincide.  Distinct cores are impossible; a common core cancels down to
second-row reducedness. -/
theorem cored_gamma_unique
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hdℓ₀ : 1 ≤ ℓ₀.natDegree)
    (hdℓ₁ : 1 ≤ ℓ₁.natDegree) (hcop₁ : IsCoprime R₁ ℓ₁)
    {γ₁ γ₂ p₁ p₂ a₁ a₂ : F} {K₁ K₂ : Finset (Fin n)}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hKd₁ : K₁.card < ℓ₀.natDegree) (hKd₂ : K₂.card < ℓ₀.natDegree)
    (h₁ : (R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K₁ = C a₁ * vanishingPoly dom Finset.univ)
    (h₂ : (R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K₂ = C a₂ * vanishingPoly dom Finset.univ) :
    γ₁ = γ₂ := by
  have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hℓ₁ne : ℓ₁ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₁
    omega
  -- cross-multiplied subtraction
  have hsub : ((C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁))
      * (vanishingPoly dom K₁ * vanishingPoly dom K₂)
      = (C a₁ * vanishingPoly dom K₂ - C a₂ * vanishingPoly dom K₁)
        * vanishingPoly dom Finset.univ := by
    linear_combination (vanishingPoly dom K₂) * h₁ - (vanishingPoly dom K₁) * h₂
  -- mod ℓ₀ kills the LHS; coprimality with m_D pins the core difference
  have hdvdL : ℓ₀ ∣ (C a₁ * vanishingPoly dom K₂ - C a₂ * vanishingPoly dom K₁)
      * vanishingPoly dom Finset.univ := by
    refine ⟨((C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁)
      * (vanishingPoly dom K₁ * vanishingPoly dom K₂), ?_⟩
    linear_combination -hsub
  have hcopD : IsCoprime ℓ₀ (vanishingPoly dom Finset.univ) :=
    isCoprime_vanishingPoly dom hG₀ _
  have hdvdK : ℓ₀ ∣ C a₁ * vanishingPoly dom K₂ - C a₂ * vanishingPoly dom K₁ :=
    hcopD.dvd_of_dvd_mul_right hdvdL
  have hKzero : C a₁ * vanishingPoly dom K₂ - C a₂ * vanishingPoly dom K₁ = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvdK hne
    have hd : (C a₁ * vanishingPoly dom K₂
        - C a₂ * vanishingPoly dom K₁).natDegree < ℓ₀.natDegree := by
      have e1 : (C a₁ * vanishingPoly dom K₂).natDegree < ℓ₀.natDegree := by
        refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
        rw [vanishingPoly_natDegree]
        exact hKd₂
      have e2 : (C a₂ * vanishingPoly dom K₁).natDegree < ℓ₀.natDegree := by
        refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
        rw [vanishingPoly_natDegree]
        exact hKd₁
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt e1 e2)
    omega
  -- monicity: a₁ = a₂ and K₁ = K₂
  have hKeq : C a₁ * vanishingPoly dom K₂ = C a₂ * vanishingPoly dom K₁ :=
    sub_eq_zero.mp hKzero
  have haeq : a₁ = a₂ := by
    have h := congrArg Polynomial.leadingCoeff hKeq
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
      (vanishingPoly_monic dom K₂).leadingCoeff,
      (vanishingPoly_monic dom K₁).leadingCoeff, mul_one, mul_one] at h
    exact h
  have hKKeq : K₁ = K₂ := by
    have h2 : vanishingPoly dom K₂ = vanishingPoly dom K₁ := by
      have := hKeq
      rw [haeq] at this
      exact mul_left_cancel₀ (C_ne_zero.mpr ha₂) this
    exact (vanishingPoly_inj dom h2).symm
  -- common core: subtract directly and cancel
  subst hKKeq
  have ha : (C a₁ : F[X]) = C a₂ := by rw [haeq]
  have hsub2 : ((C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁))
      * vanishingPoly dom K₁ = 0 := by
    linear_combination h₁ - h₂ + vanishingPoly dom Finset.univ * ha
  have hfac : (C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁) = 0 := by
    rcases mul_eq_zero.mp hsub2 with h | h
    · exact h
    · exact absurd h (vanishingPoly_ne_zero dom K₁)
  have hc : (C γ₁ - C γ₂) * R₁ * ℓ₀ = (C p₁ - C p₂) * ℓ₁ * ℓ₀ := by
    linear_combination hfac
  have hcancel : (C γ₁ - C γ₂) * R₁ = (C p₁ - C p₂) * ℓ₁ :=
    mul_right_cancel₀ hℓ₀ne hc
  have hdvd₁ : ℓ₁ ∣ (C γ₁ - C γ₂) * R₁ :=
    ⟨C p₁ - C p₂, by linear_combination hcancel⟩
  have h3 : ℓ₁ ∣ C γ₁ - C γ₂ := hcop₁.symm.dvd_of_dvd_mul_right hdvd₁
  by_contra hne
  have hCne : (C γ₁ - C γ₂ : F[X]) ≠ 0 := by
    rw [← C_sub]
    exact C_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hdeg := Polynomial.natDegree_le_of_dvd h3 hCne
  have hC0 : (C γ₁ - C γ₂ : F[X]).natDegree = 0 := by
    rw [← C_sub]
    exact natDegree_C _
  omega

end WindowEngine



end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.witness_division_identity_window
#print axioms ProximityGap.WBPencil.witness_cross_dvd
#print axioms ProximityGap.WBPencil.chain_pair_factor
#print axioms ProximityGap.WBPencil.chain_member_exact
#print axioms ProximityGap.WBPencil.cored_gamma_unique
