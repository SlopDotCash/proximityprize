/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAMonomialEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilBelowUDR

/-!
# The Möbius involution is an MCA symmetry of Reed–Solomon codes (#371, S1 brick)

The WB window probes found the below-UDR window adversary concentrated on the
Möbius involution `x ↦ -x⁻¹` (DISPROOF_LOG, `probe_window_mobius_structure.py`:
the `(13,6,1,2)` extremal is σ-invariant; `probe_window_renormalization.py`:
σ-invariant pairs dominate 3:1 at the next scale).  This file upgrades that
probe-grade observation to a theorem chain:

* `negRev N P` — the negated reversal `X^N · P(-1/X)` as a polynomial, with its
  evaluation, degree and nonvanishing laws (the GRS-duality engine);
* `rsCode_mobius_stable` — the twisted substitution
  `(M u)(x) = x^{k-1} · u(-x⁻¹)` stabilizes `rsCode dom k` whenever the
  permutation `τ` realizes `x ↦ -x⁻¹` on the evaluation domain;
* `mcaEvent_rs_mobius` / `badScalars_mobius_eq` — via the in-tree monomial
  equivariance (`mcaEvent_monomial`), the MCA event at EVERY scalar `γ`, hence
  the bad-scalar set itself, is invariant under `M`;
* `wbSolvable_mobius` — `WBSolvable` is `M`-stable (reversal of the
  Welch–Berlekamp locator/numerator pair), so `M` acts on the doubly-rational
  family that carries the below-UDR supremum (`epsMCA_le_max_doublyRational`);
* **`windowRationalBounded_of_halfFamily`** — the capstone: to verify the #371
  residual `WindowRationalBounded` it suffices to check a family containing,
  for every doubly-WB-solvable stack, the stack or its Möbius image — the
  formal search-space halving behind the probes' involution-quotient strategy.

The smooth production domains `μ_{2^a}` (and every even-order subgroup) admit
such a `τ`: `-x⁻¹` has order dividing `n` exactly when `(-1)^n = 1`, and
`exists_mobiusPerm` builds the permutation from closure alone.

This forges the missing link between `MobiusPencilEnergy.lean` (the involution's
orbit combinatorics, previously unconnected to `mcaEvent`) and the monomial
equivariance engine of `MCAMonomialEquivariance.lean`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor ProximityGap.MCAMonomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The negated reversal `X^N · P(-1/X)` -/

/-- The negated reversal of `P` at degree budget `N`:
`negRev N P = Σ_{j ≤ N} P_j (-1)^j X^{N-j}`, i.e. `X^N · P(-1/X)` as a polynomial. -/
noncomputable def negRev (N : ℕ) (P : F[X]) : F[X] :=
  ∑ j ∈ Finset.range (N + 1), C (P.coeff j * (-1) ^ j) * X ^ (N - j)

theorem negRev_natDegree_le (N : ℕ) (P : F[X]) : (negRev N P).natDegree ≤ N := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  calc (C (P.coeff j * (-1) ^ j) * X ^ (N - j)).natDegree
      ≤ (C (P.coeff j * (-1) ^ j)).natDegree + (X ^ (N - j) : F[X]).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + (N - j) := by
        refine Nat.add_le_add (le_of_eq (natDegree_C _)) ?_
        rw [natDegree_X_pow]
    _ ≤ N := by omega

theorem negRev_coeff_of_le {N : ℕ} (P : F[X]) {j₀ : ℕ} (hj₀ : j₀ ≤ N) :
    (negRev N P).coeff (N - j₀) = P.coeff j₀ * (-1) ^ j₀ := by
  rw [negRev, finset_sum_coeff]
  rw [Finset.sum_eq_single j₀]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j hj hne
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj
      omega
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hne (by omega)), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem negRev_ne_zero {N : ℕ} {P : F[X]} (hP : P ≠ 0) (hPd : P.natDegree ≤ N) :
    negRev N P ≠ 0 := by
  intro h
  have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc := negRev_coeff_of_le (F := F) P hPd
  rw [h, coeff_zero] at hc
  rcases mul_eq_zero.mp hc.symm with h1 | h1
  · exact hlc h1
  · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h1

theorem negRev_eval {N : ℕ} {P : F[X]} (hP : P.natDegree ≤ N) {x : F} (hx : x ≠ 0) :
    (negRev N P).eval x = x ^ N * P.eval (-x⁻¹) := by
  have hxj : ∀ j ≤ N, x ^ N * (x⁻¹) ^ j = x ^ (N - j) := by
    intro j hj
    have h1 : x ^ (N - j) * x ^ j = x ^ N := by
      rw [← pow_add]
      congr 1
      omega
    calc x ^ N * (x⁻¹) ^ j = x ^ N * (x ^ j)⁻¹ := by rw [inv_pow]
      _ = (x ^ (N - j) * x ^ j) * (x ^ j)⁻¹ := by rw [h1]
      _ = x ^ (N - j) := by
          rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]
  rw [negRev, eval_finset_sum,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP) (-x⁻¹), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [eval_mul, eval_C, eval_pow, eval_X, neg_pow, ← hxj j hjN]
  ring

/-! ## The Möbius permutation of the domain -/

/-- A domain whose image is closed under `x ↦ -x⁻¹` carries a Möbius permutation. -/
theorem exists_mobiusPerm (dom : Fin n ↪ F)
    (hclosed : ∀ i, ∃ j, dom j = -(dom i)⁻¹) :
    ∃ τ : Equiv.Perm (Fin n), ∀ i, dom (τ i) = -(dom i)⁻¹ := by
  classical
  choose f hf using hclosed
  have hinv : ∀ i, f (f i) = i := by
    intro i
    apply dom.injective
    rw [hf, hf, inv_neg, neg_neg, inv_inv]
  exact ⟨⟨f, f, hinv, hinv⟩, hf⟩

variable {dom : Fin n ↪ F} {τ : Equiv.Perm (Fin n)}

/-- The Möbius permutation squares to the identity. -/
theorem mobiusPerm_invol (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) (i : Fin n) :
    τ (τ i) = i := by
  apply dom.injective
  rw [hτ, hτ, inv_neg, neg_neg, inv_inv]

/-! ## Code stability under the twisted substitution -/

private theorem rsCode_mobius_mem {k : ℕ} (hk : 1 ≤ k) (h0 : ∀ i, dom i ≠ 0)
    (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) {w : Fin n → F}
    (hw : w ∈ rsCode dom k) :
    (fun i => (dom i) ^ (k - 1) • w (τ i)) ∈ rsCode dom k := by
  obtain ⟨P, hPdeg, rfl⟩ := hw
  have hPnd : P.natDegree ≤ k - 1 := by
    rcases eq_or_ne P 0 with h | h
    · simp [h]
    · have h1 : (P.natDegree : WithBot ℕ) < (k : WithBot ℕ) :=
        (degree_eq_natDegree h) ▸ hPdeg
      have h2 : P.natDegree < k := by exact_mod_cast h1
      omega
  refine ⟨negRev (k - 1) P, ?_, ?_⟩
  · rcases eq_or_ne (negRev (k - 1) P) 0 with h | h
    · rw [h, degree_zero]
      exact WithBot.bot_lt_coe k
    · rw [degree_eq_natDegree h]
      have h2 : (negRev (k - 1) P).natDegree < k :=
        lt_of_le_of_lt (negRev_natDegree_le _ _) (by omega)
      exact_mod_cast h2
  · funext i
    rw [smul_eq_mul, negRev_eval hPnd (h0 i), ← hτ i]

/-- **Code stability of the Möbius twist.**  The monomial map
`(M u) i = (dom i)^{k-1} · u (τ i)` (i.e. `u(x) ↦ x^{k-1} u(-x⁻¹)`) maps
`rsCode dom k` to itself, both ways. -/
theorem rsCode_mobius_stable {k : ℕ} (hk : 1 ≤ k) (h0 : ∀ i, dom i ≠ 0)
    (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) (w : Fin n → F) :
    w ∈ rsCode dom k ↔ (fun i => (dom i) ^ (k - 1) • w (τ i)) ∈ rsCode dom k := by
  constructor
  · exact rsCode_mobius_mem hk h0 hτ
  · intro h
    have h2 := rsCode_mobius_mem hk h0 hτ h
    have heq : (fun i => (dom i) ^ (k - 1) •
        (fun j => (dom j) ^ (k - 1) • w (τ j)) (τ i))
        = fun i => ((-1 : F)) ^ (k - 1) * w i := by
      funext i
      simp only [smul_eq_mul, mobiusPerm_invol hτ i]
      rw [← mul_assoc, ← mul_pow, hτ i, mul_neg, mul_inv_cancel₀ (h0 i)]
    rw [heq] at h2
    have hc : ((-1 : F)) ^ (k - 1) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hsm : (fun i => ((-1 : F)) ^ (k - 1) * w i)
        = (((-1 : F)) ^ (k - 1)) • w := by
      funext i
      simp [smul_eq_mul]
    rw [hsm] at h2
    have h3 := (rsCode dom k).smul_mem ((((-1 : F)) ^ (k - 1))⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3

/-! ## MCA-event and bad-set invariance -/

/-- **The Möbius involution is an MCA symmetry of RS codes**: the twisted
substitution preserves the MCA event at EVERY scalar `γ`. -/
theorem mcaEvent_rs_mobius {k : ℕ} (hk : 1 ≤ k) (h0 : ∀ i, dom i ≠ 0)
    (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) (δ : ℝ≥0) (γ : F) (u₀ u₁ : Fin n → F) :
    mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k - 1) • u₀ (τ i))
        (fun i => (dom i) ^ (k - 1) • u₁ (τ i)) γ ↔
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ :=
  mcaEvent_monomial _ δ (τ : Fin n ≃ Fin n) (fun i => (dom i) ^ (k - 1))
    (fun i => pow_ne_zero _ (h0 i)) (rsCode_mobius_stable hk h0 hτ) u₀ u₁ γ

open Classical in
/-- The bad-scalar set is literally Möbius-invariant. -/
theorem badScalars_mobius_eq {k : ℕ} (hk : 1 ≤ k) (h0 : ∀ i, dom i ≠ 0)
    (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) (δ : ℝ≥0) (u₀ u₁ : Fin n → F) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k - 1) • u₀ (τ i))
        (fun i => (dom i) ^ (k - 1) • u₁ (τ i)) γ)
      = Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) := by
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mcaEvent_rs_mobius hk h0 hτ δ γ u₀ u₁

/-! ## `WBSolvable` is Möbius-stable -/

/-- The Welch–Berlekamp relation transports through the Möbius twist: the
locator/numerator pair reverses. -/
theorem wbSolvable_mobius {k w : ℕ} (hk : 1 ≤ k) (h0 : ∀ i, dom i ≠ 0)
    (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) {u : Fin n → F}
    (h : WBSolvable dom k w u) :
    WBSolvable dom k w (fun i => (dom i) ^ (k - 1) • u (τ i)) := by
  obtain ⟨ℓ, R, hℓ0, hℓd, hRd, hrel⟩ := h
  have hRd' : R.natDegree ≤ w + (k - 1) := by omega
  refine ⟨negRev w ℓ, negRev (w + (k - 1)) R, negRev_ne_zero hℓ0 hℓd,
    negRev_natDegree_le _ _, le_trans (negRev_natDegree_le _ _) (by omega), ?_⟩
  intro i
  dsimp only
  rw [smul_eq_mul, negRev_eval hℓd (h0 i), negRev_eval hRd' (h0 i), ← hτ i]
  calc (dom i) ^ w * ℓ.eval (dom (τ i)) * ((dom i) ^ (k - 1) * u (τ i))
      = (dom i) ^ w * (dom i) ^ (k - 1) * (ℓ.eval (dom (τ i)) * u (τ i)) := by ring
    _ = (dom i) ^ (w + (k - 1)) * R.eval (dom (τ i)) := by
        rw [← pow_add, hrel (τ i)]

/-! ## The capstone: Möbius halving of the `WindowRationalBounded` search space -/

open Classical in
/-- **The search-space halving.**  To verify the #371 residual
`WindowRationalBounded`, it suffices to bound the bad-scalar count on any family
`T` that contains, for every doubly-WB-solvable stack, either the stack or its
Möbius image: the Möbius twist preserves both `WBSolvable` (rows) and the
bad-scalar set (count), so the bound transports across each orbit. -/
theorem windowRationalBounded_of_halfFamily {k w : ℕ} (hk : 1 ≤ k)
    (h0 : ∀ i, dom i ≠ 0) (hτ : ∀ i, dom (τ i) = -(dom i)⁻¹) {δ : ℝ≥0}
    (T : Set ((Fin n → F) × (Fin n → F)))
    (hcover : ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
      (u₀, u₁) ∈ T ∨
      ((fun i => (dom i) ^ (k - 1) • u₀ (τ i)),
       (fun i => (dom i) ^ (k - 1) • u₁ (τ i))) ∈ T)
    (hT : ∀ v₀ v₁ : Fin n → F, (v₀, v₁) ∈ T →
      WBSolvable dom k w v₀ → WBSolvable dom k w v₁ →
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        v₀ v₁ γ)).card ≤ w + 3) :
    WindowRationalBounded dom k w δ := by
  intro u₀ u₁ h₀ h₁
  rcases hcover u₀ u₁ h₀ h₁ with hmem | hmem
  · exact hT u₀ u₁ hmem h₀ h₁
  · have hcard := hT _ _ hmem (wbSolvable_mobius hk h0 hτ h₀)
      (wbSolvable_mobius hk h0 hτ h₁)
    refine le_trans (Finset.card_le_card ?_) hcard
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    exact ⟨hγ.1, (mcaEvent_rs_mobius hk h0 hτ δ γ u₀ u₁).mpr hγ.2⟩

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.rsCode_mobius_stable
#print axioms ProximityGap.WBPencil.mcaEvent_rs_mobius
#print axioms ProximityGap.WBPencil.badScalars_mobius_eq
#print axioms ProximityGap.WBPencil.wbSolvable_mobius
#print axioms ProximityGap.WBPencil.windowRationalBounded_of_halfFamily
