/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Character averages with a prescribed first set

Formalizes `docs/research/proximity-gap/paley-character-averages.md`, completely self-contained
on Mathlib and axiom-clean (standard Lean axioms only):

1. **All-order complete character-averaged `2r`-th moment (`sum_mulChar_even_moment_le`)**:
   For every finite field `F` of size `q`, every subset `A ⊆ F` of size `m`, and every `r ≥ 1`,
   `∑_{ψ} ∑_{b : F} ‖W_ψ(b)‖^{2r} ≤ (q - 1) * (r! * q * m^r + (r - 1) * m^{2r})`,
   where `W_ψ(b) = ∑_{a ∈ A} ψ(a + b)` (extended by `ψ(0) = 0`).
2. **Exact nonprincipal complete fourth moment (`sum_nonprincipal_fourth_moment_eq`,
   `sum_nonprincipal_fourth_moment_le`)**:
   For every nonempty `A ⊆ F` of size `m ≥ 1`,
   `∑_{ψ ≠ 1} ∑_{b : F} ‖W_ψ(b)‖^4 = (q - 1) * (q(2m^2 - m) - 4m^3 + 4m^2 - m - E_+(A)) + m(m - 1)(3m^2 - 3m + 1) ≤ (q - 1) * q * (2m^2 - m)`.
3. **Exceptional-character fraction bound (`card_bad_characters_le`)**:
   For every prescribed `A ⊆ F` of size `m ≥ 1`, every `r ≥ 1`, and every `ρ > 0`, the fraction
   of multiplicative characters `ψ` admitting ANY partner `B ⊆ F` (`|B| ≥ m`) with
   `‖∑_{b ∈ B} W_ψ(b)‖ ≥ ρ * m * |B|` is at most `ρ^(-2r) * (r! * q / m^(r+1) + (r - 1) / m)`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace ProximityGap.PaleyCharacterAverages

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Cyclic multiplicative character family and orthogonality -/

/-- The `k`-th complex multiplicative character of `F` associated to a discrete logarithm `dlog`
(with `g ^ dlog u = u`, `dlog u < q - 1`), extended by `0` at `0`. -/
noncomputable def cyclicMulChar (dlog : Fˣ → ℕ) (k : ℕ) (x : F) : ℂ :=
  if hx : x = 0 then 0
  else Complex.exp (2 * Real.pi * Complex.I / ((Fintype.card F - 1 : ℕ) : ℂ)) ^
    (k * dlog (Units.mk0 x hx))

/-- Character shift sum `W_ψ(b) = ∑ a ∈ A, ψ(a + b)`. -/
def charShiftSum (A : Finset F) (ψ : F → ℂ) (b : F) : ℂ :=
  ∑ a ∈ A, ψ (a + b)

/-- Additive energy `E_+(A) = #{(u, v, w, z) ∈ A^4 | u + v = w + z}`. -/
def additiveEnergy (A : Finset F) : ℕ :=
  (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card

private theorem exp_two_pi_div_prim {N : ℕ} (hN : 0 < N) {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ^ r ≠ 1 := by
  intro h1
  rw [← Complex.exp_nat_mul] at h1
  set θ : ℝ := 2 * Real.pi * (r : ℝ) / (N : ℝ)
  have hθ_eq : (r : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = (θ : ℂ) * Complex.I := by
    dsimp [θ]; push_cast; ring
  rw [hθ_eq, Complex.exp_mul_I] at h1
  have hre := congrArg Complex.re h1
  have hcos1 : Real.cos θ = 1 := by
    simpa [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im] using hre
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrNR : (r : ℝ) < N := by exact_mod_cast hrN
  have hθ_pos : 0 < θ := div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hr0R) hNR
  have hθ_lt : θ < 2 * Real.pi := by
    dsimp [θ]; rw [div_lt_iff₀ hNR]; nlinarith [Real.pi_pos]
  have hcos_lt : Real.cos θ < 1 := by
    rcases le_or_gt θ Real.pi with hle | hgt
    · calc Real.cos θ < Real.cos 0 :=
            Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) ⟨hθ_pos.le, hle⟩ hθ_pos
        _ = 1 := Real.cos_zero
    · rw [← Real.cos_two_pi_sub θ]
      calc Real.cos (2 * Real.pi - θ) < Real.cos 0 :=
            Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
              ⟨by linarith, by linarith⟩ (by linarith)
        _ = 1 := Real.cos_zero
  linarith

/-- Existence of a discrete logarithm `dlog : Fˣ → ℕ` relative to a generator of `Fˣ`. -/
theorem exists_dlog :
    ∃ (g : Fˣ) (dlog : Fˣ → ℕ),
      (∀ u : Fˣ, dlog u < Fintype.card F - 1) ∧
      (∀ u : Fˣ, g ^ dlog u = u) ∧
      (∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1)) ∧
      Function.Injective dlog := by
  classical
  set N := Fintype.card F - 1
  have hcard_units : Fintype.card Fˣ = N := by
    rw [Fintype.card_units]
  have hN_pos : 0 < N := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord_g : orderOf g = N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_units]
  have hsurj : ∀ u : Fˣ, ∃ j < N, g ^ j = u := by
    intro u
    obtain ⟨m, hm⟩ := hg u
    refine ⟨(m % (N : ℤ)).toNat, ?_, ?_⟩
    · have h1 := Int.emod_nonneg m (show (N : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos m (show (0 : ℤ) < N by omega)
      omega
    · have hdiv : m = (N : ℤ) * (m / (N : ℤ)) + m % (N : ℤ) := (Int.mul_ediv_add_emod _ _).symm
      have hpowN : g ^ N = 1 := by rw [← hord_g]; exact pow_orderOf_eq_one g
      rw [← hm]
      dsimp only
      conv_rhs =>
        rw [hdiv, zpow_add, zpow_mul, zpow_natCast, hpowN, one_zpow, one_mul,
          ← Int.toNat_of_nonneg (Int.emod_nonneg m (show (N : ℤ) ≠ 0 by omega)), zpow_natCast]
  choose dlog hdlog_lt hdlog_pow using hsurj
  have hpow_inj : ∀ {a b : ℕ}, a < N → b < N → g ^ a = g ^ b → a = b := by
    intro a b ha hb heq
    wlog hle : a ≤ b generalizing a b
    · exact (this hb ha heq.symm (by omega)).symm
    have h1 : g ^ (b - a) = 1 := by
      have : g ^ a * g ^ (b - a) = g ^ a * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, heq]
      exact mul_left_cancel this
    have hdvd : N ∣ b - a := by rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one h1
    rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega
  refine ⟨g, dlog, hdlog_lt, hdlog_pow, ?_, ?_⟩
  · intro u v
    have hmul : g ^ ((dlog u + dlog v) % N) = u * v := by
      have h1 : g ^ (dlog u + dlog v) = u * v := by rw [pow_add, hdlog_pow u, hdlog_pow v]
      rw [← h1]
      conv_rhs => rw [← Nat.div_add_mod (dlog u + dlog v) N]
      rw [pow_add, pow_mul, ← hord_g, pow_orderOf_eq_one, one_pow, one_mul]
    rw [Nat.mod_eq_of_lt (hdlog_lt (u * v))]
    exact hpow_inj (hdlog_lt (u * v)) (Nat.mod_lt _ hN_pos) ((hdlog_pow (u * v)).trans hmul.symm)
  · intro u v huv
    rw [← hdlog_pow u, ← hdlog_pow v, huv]

private theorem cyclicMulChar_mul {dlog : Fˣ → ℕ}
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (k : ℕ) (x y : F) :
    cyclicMulChar dlog k (x * y) = cyclicMulChar dlog k x * cyclicMulChar dlog k y := by
  set N := Fintype.card F - 1
  have hN_pos : 0 < N := by have := Fintype.one_lt_card (α := F); omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hζ_pow_N : ζ ^ N = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by
      field_simp [hne]]
    exact Complex.exp_two_pi_mul_I
  have hζ_mod : ∀ n : ℕ, ζ ^ (n % N) = ζ ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n N]
    rw [pow_add, pow_mul, hζ_pow_N, one_pow, one_mul]
  by_cases hx : x = 0
  · subst hx; simp [cyclicMulChar]
  · by_cases hy : y = 0
    · subst hy; simp [cyclicMulChar]
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [cyclicMulChar, hx, hy, hxy, ↓reduceDIte]
      have hu : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by ext; rfl
      rw [hu, ← pow_add, ← mul_add]
      change ζ ^ (k * dlog (Units.mk0 x hx * Units.mk0 y hy)) =
        ζ ^ (k * (dlog (Units.mk0 x hx) + dlog (Units.mk0 y hy)))
      rw [← hζ_mod (k * dlog _), ← hζ_mod (k * _), Nat.mul_mod, hmul, ← Nat.mul_mod]

private theorem cyclicMulChar_prod {dlog : Fˣ → ℕ}
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (k : ℕ) {ι : Type*} (s : Finset ι) (f : ι → F) :
    cyclicMulChar dlog k (∏ i ∈ s, f i) = ∏ i ∈ s, cyclicMulChar dlog k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, cyclicMulChar, one_ne_zero, ↓reduceDIte]
    -- Show `dlog 1 = 0`:
    have h1 := hmul 1 1
    rw [mul_one] at h1
    set N := Fintype.card F - 1
    have hN_pos : 0 < N := by have := Fintype.one_lt_card (α := F); omega
    have hdvd : N ∣ dlog 1 := by
      set r := dlog 1 % N
      have hr_lt : r < N := Nat.mod_lt _ hN_pos
      have hrr : (r + r) % N = r := by
        dsimp [r]; rw [← Nat.add_mod]; exact h1.symm
      have hr0 : r = 0 := by
        rcases lt_or_ge (r + r) N with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hrr; omega
        · have : (r + r) % N = r + r - N := by
            rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
          omega
      exact Nat.dvd_of_mod_eq_zero hr0
    obtain ⟨t, ht⟩ := hdvd
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
    have hζ_pow_N : ζ ^ N = 1 := by
      dsimp [ζ]
      rw [← Complex.exp_nat_mul]
      have hne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
      rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by
        field_simp [hne]]
      exact Complex.exp_two_pi_mul_I
    have hu1 : Units.mk0 (1 : F) one_ne_zero = 1 := by ext; rfl
    rw [hu1, ht, show k * (N * t) = N * (k * t) by ring, pow_mul, hζ_pow_N, one_pow]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, cyclicMulChar_mul hmul, ih]

private theorem cyclicMulChar_orthogonality {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1) (hinj : Function.Injective dlog)
    (x y : F) :
    ∑ k ∈ Finset.range (Fintype.card F - 1),
        cyclicMulChar dlog k x * starRingEnd ℂ (cyclicMulChar dlog k y) =
      if x = y ∧ x ≠ 0 then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  set N := Fintype.card F - 1
  have hN_pos : 0 < N := by have := Fintype.one_lt_card (α := F); omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hζ_pow_N : ζ ^ N = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by
      field_simp [hne]]
    exact Complex.exp_two_pi_mul_I
  have hζ_conj : starRingEnd ℂ ζ = ζ⁻¹ := by
    have hnorm : ‖ζ‖ = 1 := by
      dsimp [ζ]
      rw [show 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
          ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hmc : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    exact mul_left_cancel₀ hne (hmc.trans (mul_inv_cancel₀ hne).symm)
  by_cases hx : x = 0
  · subst hx; simp [cyclicMulChar]
  · by_cases hy : y = 0
    · subst hy; simp [cyclicMulChar, hx]
    · simp only [cyclicMulChar, hx, hy, ↓reduceDIte, map_pow]
      set a := dlog (Units.mk0 x hx)
      set b := dlog (Units.mk0 y hy)
      have ha : a < N := hlt _
      have hb : b < N := hlt _
      change ∑ k ∈ Finset.range N, ζ ^ (k * a) * (starRingEnd ℂ ζ) ^ (k * b) =
        if x = y ∧ x ≠ 0 then (N : ℂ) else 0
      rw [hζ_conj]
      by_cases hxy : x = y
      · subst hxy
        have hba : b = a := rfl
        rw [hba]
        have hterm : ∀ k ∈ Finset.range N, ζ ^ (k * a) * (ζ⁻¹) ^ (k * a) = 1 := fun k _ => by
          rw [← mul_pow, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_pow]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        simp [hx]
      · simp only [hxy, false_and, ↓reduceIte]
        have hab : a ≠ b := fun h => hxy (congrArg Units.val (hinj h))
        set δ : ℤ := (a : ℤ) - b
        set w : ℂ := ζ ^ δ
        have hterm : ∀ k : ℕ, ζ ^ (k * a) * (ζ⁻¹) ^ (k * b) = w ^ k := fun k => by
          rw [← zpow_natCast, ← zpow_natCast, inv_zpow, ← zpow_neg,
            ← zpow_add₀ (Complex.exp_ne_zero _), ← zpow_natCast, ← zpow_mul]
          congr 1; dsimp [δ]; push_cast; ring
        simp_rw [hterm]
        have hw_pow : w ^ N = 1 := by
          dsimp [w]
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ_pow_N, one_zpow]
        have hw_ne1 : w ≠ 1 := by
          dsimp [w]
          have hrem_pos : 0 < (δ % (N : ℤ)).toNat := by
            have hnn : 0 ≤ δ % (N : ℤ) := Int.emod_nonneg δ (by omega)
            have hndvd : ¬ ((N : ℤ) ∣ δ) := by
              intro ⟨q, hq⟩
              have hq_bounds : q = 0 := by
                have h1 : -(N : ℤ) < (N : ℤ) * q := by dsimp [δ] at hq; omega
                have h2 : (N : ℤ) * q < (N : ℤ) := by dsimp [δ] at hq; omega
                have hge : 0 ≤ q := by
                  by_contra hlt; have : q ≤ -1 := by omega
                  nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℤ) ≤ N by omega)]
                have hle : q ≤ 0 := by
                  by_contra hgt; have : 1 ≤ q := by omega
                  nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℤ) ≤ N by omega)]
                omega
              rw [hq_bounds, mul_zero] at hq
              exact hab (by dsimp [δ] at hq; omega)
            have hnz : δ % (N : ℤ) ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
            omega
          have hrem_lt : (δ % (N : ℤ)).toNat < N := by
            have := Int.emod_lt_of_pos δ (by omega : (0 : ℤ) < N)
            omega
          have hw_eq : ζ ^ δ = ζ ^ (δ % (N : ℤ)).toNat := by
            have hdiv : δ = (N : ℤ) * (δ / (N : ℤ)) + δ % (N : ℤ) := (Int.mul_ediv_add_emod _ _).symm
            have hnn : 0 ≤ δ % (N : ℤ) := Int.emod_nonneg δ (by omega)
            conv_lhs =>
              rw [hdiv, zpow_add₀ (Complex.exp_ne_zero _), zpow_mul, zpow_natCast, hζ_pow_N,
                one_zpow, one_mul, ← Int.toNat_of_nonneg hnn, zpow_natCast]
          rw [hw_eq]
          exact exp_two_pi_div_prim hN_pos hrem_pos hrem_lt
        have hgeom := geom_sum_mul w N
        rw [hw_pow, sub_self] at hgeom
        exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw_ne1)

/-! ## 2. All-order complete character-averaged `2r`-th moment -/

private theorem card_perm_fibers_le {α : Type*} [DecidableEq α] {r : ℕ}
    (u : Fin r → α) :
    ∀ (S : Finset (Fin r → α)),
      (∀ v ∈ S, Multiset.map v Finset.univ.val = Multiset.map u Finset.univ.val) →
      S.card ≤ r.factorial := by
  classical
  intro S hS
  have hsub : S ⊆ Finset.univ.image (fun σ : Equiv.Perm (Fin r) => u ∘ σ) := by
    intro v hv
    rw [Finset.mem_image]
    have hm : Multiset.map v Finset.univ.val = Multiset.map u Finset.univ.val := hS v hv
    have hcard_eq : ∀ a : α, (Finset.univ.filter fun i : Fin r => v i = a).card =
        (Finset.univ.filter fun i : Fin r => u i = a).card := fun a => by
      have hc : ∀ f : Fin r → α, (Finset.univ.filter fun i : Fin r => f i = a).card =
          Multiset.count a (Multiset.map f Finset.univ.val) := fun f => by
        rw [Multiset.count_map]
        change (Multiset.filter (fun i : Fin r => f i = a) Finset.univ.val).card = _
        congr 2; ext i; exact eq_comm
      rw [hc v, hc u, hm]
    -- Piece together bijections on each fiber `v⁻¹(a) ≃ u⁻¹(a)`!
    let eqvFiber : ∀ a : α, {i : Fin r // v i = a} ≃ {i : Fin r // u i = a} := fun a =>
      Fintype.equivOfCardEq (by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact hcard_eq a)
    let f : Fin r → Fin r := fun i => (eqvFiber (v i) ⟨i, rfl⟩).1
    have hf_val : ∀ i : Fin r, u (f i) = v i := fun i => (eqvFiber (v i) ⟨i, rfl⟩).2
    have hf_inj : Function.Injective f := by
      intro i j hij
      have hvu : v i = v j := by rw [← hf_val i, hij, hf_val j]
      have haux : ∀ (a : α) (ha : v i = a) (hb : v j = a),
          (eqvFiber a ⟨i, ha⟩).1 = (eqvFiber a ⟨j, hb⟩).1 → i = j := fun a ha hb h =>
        congrArg Subtype.val ((eqvFiber a).injective (Subtype.ext h))
      refine haux (v i) rfl hvu.symm ?_
      dsimp [f] at hij
      have hrewrite : ∀ (a b : α) (hab : a = b) (hb : v j = b),
          (eqvFiber b ⟨j, hb⟩).1 = (eqvFiber a ⟨j, hb.trans hab.symm⟩).1 := by
        rintro a _ rfl _; rfl
      rw [hij, hrewrite (v i) (v j) hvu rfl]
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
    refine ⟨σ, Finset.mem_univ σ, ?_⟩
    funext i
    exact hf_val i
  calc S.card ≤ (Finset.univ.image (fun σ : Equiv.Perm (Fin r) => u ∘ σ)).card :=
          Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin r))).card := Finset.card_image_le
    _ = Fintype.card (Equiv.Perm (Fin r)) := Finset.card_univ
    _ = r.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

/-- **All-order complete character-averaged `2r`-th moment** (`paley-character-averages.md`, eq. 2):
for every finite field `F`, every `A ⊆ F`, and every `r ≥ 1`,
`∑_{k < |F| - 1} ∑_{b : F} ‖W_{ψ_k}(b)‖^{2r} ≤ (|F| - 1) * (r! * |F| * |A|^r + (r - 1) * |A|^{2r})`. -/
theorem sum_mulChar_even_moment_le {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1)
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (hinj : Function.Injective dlog)
    (A : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (Fintype.card F - 1), ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) ≤
      ((Fintype.card F - 1 : ℕ) : ℝ) *
        ((r.factorial : ℝ) * (Fintype.card F : ℝ) * (A.card : ℝ) ^ r +
          ((r - 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 * r)) := by
  classical
  set N := Fintype.card F - 1
  -- Expand in `ℂ` and apply character orthogonality:
  let Tuples := (Finset.univ : Finset (Fin r → A))
  let P (u : Fin r → A) : F[X] := ∏ i : Fin r, (X + C (u i).1)
  have hP_eval : ∀ (u : Fin r → A) (b : F), (P u).eval b = ∏ i : Fin r, ((u i).1 + b) := fun u b => by
    dsimp [P]
    rw [eval_prod]
    exact Finset.prod_congr rfl fun i _ => by simp [add_comm]
  have hP_monic : ∀ u : Fin r → A, (P u).Monic := fun u =>
    monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _
  have hP_deg : ∀ u : Fin r → A, (P u).natDegree = r := fun u => by
    dsimp [P]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp
  have hpow_expand : ∀ (k : ℕ) (b : F),
      ((‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) : ℝ) : ℂ) =
        ∑ u : Fin r → A, ∑ v : Fin r → A,
          cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) := by
    intro k b
    have hnorm2 : ((‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) : ℝ) : ℂ) =
        (charShiftSum A (cyclicMulChar dlog k) b) ^ r *
          starRingEnd ℂ ((charShiftSum A (cyclicMulChar dlog k) b) ^ r) := by
      rw [pow_mul, Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
        mul_pow, map_pow]
    rw [hnorm2]
    have hsum_pow : (charShiftSum A (cyclicMulChar dlog k) b) ^ r =
        ∑ u : Fin r → A, cyclicMulChar dlog k ((P u).eval b) := by
      unfold charShiftSum
      rw [← A.sum_attach, Finset.attach_eq_univ,
        show (∑ x : A, cyclicMulChar dlog k (x.1 + b)) ^ r =
            ∏ _i : Fin r, ∑ x : A, cyclicMulChar dlog k (x.1 + b) by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
        Fintype.prod_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hP_eval u b, cyclicMulChar_prod hmul]
    rw [hsum_pow, map_sum, Finset.sum_mul_sum]
  have hsumC : ((∑ k ∈ Finset.range N, ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) : ℝ) : ℂ) =
      (N : ℂ) * ((∑ u : Fin r → A, ∑ v : Fin r → A,
        (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card : ℕ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [Complex.ofReal_sum, hpow_expand]
    rw [Finset.sum_comm]
    have hswap1 : ∑ b : F, ∑ k ∈ Finset.range N, ∑ u : Fin r → A, ∑ v : Fin r → A,
          cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) =
        ∑ u : Fin r → A, ∑ v : Fin r → A, ∑ b : F, ∑ k ∈ Finset.range N,
          cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) := by
      calc _ = ∑ b : F, ∑ u : Fin r → A, ∑ k ∈ Finset.range N, ∑ v : Fin r → A,
                cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) :=
              Finset.sum_congr rfl fun b _ => Finset.sum_comm
        _ = ∑ u : Fin r → A, ∑ b : F, ∑ k ∈ Finset.range N, ∑ v : Fin r → A,
              cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) :=
              Finset.sum_comm
        _ = ∑ u : Fin r → A, ∑ b : F, ∑ v : Fin r → A, ∑ k ∈ Finset.range N,
              cyclicMulChar dlog k ((P u).eval b) * starRingEnd ℂ (cyclicMulChar dlog k ((P v).eval b)) :=
              Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun u _ => Finset.sum_comm
    rw [hswap1]
    have horth_eq : ∀ x y : F,
        ∑ k ∈ Finset.range N, cyclicMulChar dlog k x * starRingEnd ℂ (cyclicMulChar dlog k y) =
          if x = y ∧ x ≠ 0 then (N : ℂ) else 0 :=
      cyclicMulChar_orthogonality hlt hinj
    simp_rw [horth_eq]
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsumR : ∑ k ∈ Finset.range N, ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) =
      (N : ℝ) * ((∑ u : Fin r → A, ∑ v : Fin r → A,
        (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card : ℕ) : ℝ) := by
    exact_mod_cast hsumC
  rw [hsumR]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  -- Bound the natural-number count of matching `(u, v, b)` triples!
  suffices hnat : ∑ u : Fin r → A, ∑ v : Fin r → A,
        (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card ≤
      r.factorial * Fintype.card F * A.card ^ r + (r - 1) * A.card ^ (2 * r) by
    exact_mod_cast hnat
  -- Split for each fixed `u` into `P u = P v` vs `P u ≠ P v`:
  have hper_u : ∀ u : Fin r → A,
      ∑ v : Fin r → A,
          (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card ≤
        r.factorial * Fintype.card F + (r - 1) * A.card ^ r := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin r → A)) (fun v => P v = P u)]
    refine Nat.add_le_add ?_ ?_
    · -- Equal polynomials `P v = P u`:
      have hcard_eq : (Finset.univ.filter fun v : Fin r → A => P v = P u).card ≤ r.factorial := by
        refine card_perm_fibers_le u _ fun v hv => ?_
        have hPeq : P v = P u := (Finset.mem_filter.mp hv).2
        have hroots : ∀ w : Fin r → A,
            (P w).roots = Multiset.map (fun i : Fin r => -(w i).1) Finset.univ.val := fun w => by
          dsimp [P]
          have hne : ∏ i : Fin r, (X + C (w i).1) ≠ 0 := (hP_monic w).ne_zero
          rw [Polynomial.roots_prod _ _ hne]
          have hroot1 : ∀ i : Fin r, (X + C (w i).1).roots = {-(w i).1} := fun i => by
            rw [show X + C (w i).1 = X - C (-(w i).1) by simp [sub_neg_eq_add], Polynomial.roots_X_sub_C]
          simp [hroot1, Multiset.bind_singleton]
        have hr_eq : Multiset.map (fun i : Fin r => -(v i).1) Finset.univ.val =
            Multiset.map (fun i : Fin r => -(u i).1) Finset.univ.val := by
          rw [← hroots v, ← hroots u, hPeq]
        have hval_eq : Multiset.map (fun i : Fin r => (v i).1) Finset.univ.val =
            Multiset.map (fun i : Fin r => (u i).1) Finset.univ.val := by
          have := congrArg (Multiset.map Neg.neg) hr_eq
          simpa [Multiset.map_map, Function.comp_def] using this
        -- Lift from `F` to `↥A` using injectivity of `Subtype.val`:
        have hlift : Multiset.map (Subtype.val : A → F) (Multiset.map v Finset.univ.val) =
            Multiset.map (Subtype.val : A → F) (Multiset.map u Finset.univ.val) := by
          simpa [Multiset.map_map, Function.comp_def] using hval_eq
        exact Multiset.map_injective Subtype.val_injective hlift
      calc ∑ v ∈ Finset.univ.filter (fun v : Fin r → A => P v = P u),
              (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card
          ≤ ∑ _v ∈ Finset.univ.filter (fun v : Fin r → A => P v = P u), Fintype.card F :=
            Finset.sum_le_sum fun v _ => (Finset.card_filter_le _ _).trans_eq Finset.card_univ
        _ = (Finset.univ.filter fun v : Fin r → A => P v = P u).card * Fintype.card F := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ r.factorial * Fintype.card F := Nat.mul_le_mul_right _ hcard_eq
    · -- Distinct polynomials `P v ≠ P u`: `(P u - P v)` is nonzero of degree `≤ r - 1`!
      have hterm : ∀ v ∈ Finset.univ.filter (fun v : Fin r → A => ¬ P v = P u),
          (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).card ≤
            r - 1 := by
        intro v hv
        have hne : P u - P v ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hv).2)
        have hdeg_le : (P u - P v).natDegree ≤ r - 1 := by
          have hle_r : (P u - P v).natDegree ≤ r :=
            (natDegree_sub_le _ _).trans (max_le (hP_deg u).le (hP_deg v).le)
          have hcoeff_r : (P u - P v).coeff r = 0 := by
            rw [coeff_sub, ← hP_deg u, show (P u).coeff (P u).natDegree = (P u).leadingCoeff from rfl,
              (hP_monic u).leadingCoeff, hP_deg u, ← hP_deg v,
              show (P v).coeff (P v).natDegree = (P v).leadingCoeff from rfl,
              (hP_monic v).leadingCoeff, sub_self]
          have hne_r : (P u - P v).natDegree ≠ r := fun heq => by
            have hlc : (P u - P v).leadingCoeff = 0 := by rw [leadingCoeff, heq]; exact hcoeff_r
            exact leadingCoeff_ne_zero.mpr hne hlc
          omega
        have hsub : (Finset.univ.filter fun b : F => (P u).eval b = (P v).eval b ∧ (P u).eval b ≠ 0).val ≤
            (P u - P v).roots := by
          rw [Multiset.le_iff_subset (Finset.nodup _)]
          intro b hb
          rw [Finset.mem_val, Finset.mem_filter] at hb
          exact (mem_roots hne).mpr (by rw [IsRoot.def, eval_sub, hb.2.1, sub_self])
        exact (Multiset.card_le_card hsub).trans ((Polynomial.card_roots' _).trans hdeg_le)
      calc _ ≤ ∑ _v ∈ Finset.univ.filter (fun v : Fin r → A => ¬ P v = P u), (r - 1) :=
              Finset.sum_le_sum hterm
        _ = (Finset.univ.filter fun v : Fin r → A => ¬ P v = P u).card * (r - 1) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Fintype.card (Fin r → A) * (r - 1) :=
              Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans_eq Finset.card_univ)
        _ = (r - 1) * A.card ^ r := by
              rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, mul_comm]
  calc _ ≤ ∑ _u : Fin r → A, (r.factorial * Fintype.card F + (r - 1) * A.card ^ r) :=
          Finset.sum_le_sum fun u _ => hper_u u
    _ = Fintype.card (Fin r → A) * (r.factorial * Fintype.card F + (r - 1) * A.card ^ r) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = r.factorial * Fintype.card F * A.card ^ r + (r - 1) * A.card ^ (2 * r) := by
          rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, two_mul, pow_add]; ring

/-! ## 3. Exact nonprincipal complete fourth moment -/

/-- Exact complete fourth moment over all `q - 1` multiplicative characters (including principal):
`∑_{k < q - 1} ∑_{b : F} ‖W_k(b)‖^4 = (q - 1) * ((q - 1) m + 2(q - 2)m(m-1) + m(m-1)^2 + m(m-1)(m-2)^2 - (E_+(A) - (2m^2 - m)))`. -/
theorem sum_all_mulChar_fourth_moment_eq {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1)
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (hinj : Function.Injective dlog)
    (A : Finset F) :
    ∑ k ∈ Finset.range (Fintype.card F - 1), ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 =
      ((Fintype.card F - 1 : ℕ) : ℝ) *
        (((Fintype.card F : ℤ) * (2 * (A.card : ℤ) ^ 2 - A.card) + (A.card : ℤ) ^ 4 -
          4 * (A.card : ℤ) ^ 3 + 4 * (A.card : ℤ) ^ 2 - A.card - (additiveEnergy A : ℤ)) : ℝ) := by
  classical
  set q := Fintype.card F
  set N := q - 1
  set m := A.card
  let Q := (A ×ˢ A) ×ˢ (A ×ˢ A)
  -- Step 1: Express LHS via character orthogonality as `N * ∑_{t ∈ Q} #{b : F | (b+u)(b+v) = (b+w)(b+z) ≠ 0}`!
  have horth : ∑ k ∈ Finset.range N, ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 =
      (N : ℝ) * ((∑ t ∈ Q, (Finset.univ.filter fun b : F =>
        (t.1.1 + b) * (t.1.2 + b) = (t.2.1 + b) * (t.2.2 + b) ∧
          (t.1.1 + b) * (t.1.2 + b) ≠ 0).card : ℕ) : ℝ) := by
    have hC : ((∑ k ∈ Finset.range N, ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 : ℝ) : ℂ) =
        (N : ℂ) * ((∑ t ∈ Q, (Finset.univ.filter fun b : F =>
          (t.1.1 + b) * (t.1.2 + b) = (t.2.1 + b) * (t.2.2 + b) ∧
            (t.1.1 + b) * (t.1.2 + b) ≠ 0).card : ℕ) : ℂ) := by
      have h4 : ∀ (k : ℕ) (b : F),
          ((‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 : ℝ) : ℂ) =
            ∑ t ∈ Q, cyclicMulChar dlog k ((t.1.1 + b) * (t.1.2 + b)) *
              starRingEnd ℂ (cyclicMulChar dlog k ((t.2.1 + b) * (t.2.2 + b))) := fun k b => by
        have h1 : ((‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 : ℝ) : ℂ) =
            (charShiftSum A (cyclicMulChar dlog k) b) ^ 2 *
              starRingEnd ℂ ((charShiftSum A (cyclicMulChar dlog k) b) ^ 2) := by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
            ← Complex.mul_conj, mul_pow, map_pow]
        rw [h1]
        have hsq : (charShiftSum A (cyclicMulChar dlog k) b) ^ 2 =
            ∑ p ∈ A ×ˢ A, cyclicMulChar dlog k ((p.1 + b) * (p.2 + b)) := by
          unfold charShiftSum
          rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
          refine Finset.sum_congr rfl fun p _ => (cyclicMulChar_mul hmul k _ _).symm
        rw [hsq, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
      rw [Complex.ofReal_sum]
      simp_rw [Complex.ofReal_sum, h4]
      rw [Finset.sum_comm]
      have hswap : ∑ b : F, ∑ k ∈ Finset.range N, ∑ t ∈ Q,
            cyclicMulChar dlog k ((t.1.1 + b) * (t.1.2 + b)) *
              starRingEnd ℂ (cyclicMulChar dlog k ((t.2.1 + b) * (t.2.2 + b))) =
          ∑ t ∈ Q, ∑ b : F, ∑ k ∈ Finset.range N,
            cyclicMulChar dlog k ((t.1.1 + b) * (t.1.2 + b)) *
              starRingEnd ℂ (cyclicMulChar dlog k ((t.2.1 + b) * (t.2.2 + b))) := by
        calc _ = ∑ b : F, ∑ t ∈ Q, ∑ k ∈ Finset.range N,
                  cyclicMulChar dlog k ((t.1.1 + b) * (t.1.2 + b)) *
                    starRingEnd ℂ (cyclicMulChar dlog k ((t.2.1 + b) * (t.2.2 + b))) :=
                Finset.sum_congr rfl fun b _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      rw [hswap]
      have horth_eq : ∀ x y : F,
          ∑ k ∈ Finset.range N, cyclicMulChar dlog k x * starRingEnd ℂ (cyclicMulChar dlog k y) =
            if x = y ∧ x ≠ 0 then (N : ℂ) else 0 :=
        cyclicMulChar_orthogonality hlt hinj
      simp_rw [horth_eq]
      rw [Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact_mod_cast hC
  rw [horth]
  congr 1
  -- Step 2: Evaluate the exact integer count over `Q` by classifying quadruples!
  suffices hZ : (∑ t ∈ Q, ((Finset.univ.filter fun b : F =>
        (t.1.1 + b) * (t.1.2 + b) = (t.2.1 + b) * (t.2.2 + b) ∧
          (t.1.1 + b) * (t.1.2 + b) ≠ 0).card : ℤ)) =
      (q : ℤ) * (2 * (m : ℤ) ^ 2 - m) + (m : ℤ) ^ 4 - 4 * (m : ℤ) ^ 3 + 4 * (m : ℤ) ^ 2 - m -
        (additiveEnergy A : ℤ) by
    exact_mod_cast hZ
  -- For each `t = ((u, v), (w, z)) ∈ Q`, compute the exact fiber size:
  have hpt : ∀ t ∈ Q,
      ((Finset.univ.filter fun b : F =>
        (t.1.1 + b) * (t.1.2 + b) = (t.2.1 + b) * (t.2.2 + b) ∧
          (t.1.1 + b) * (t.1.2 + b) ≠ 0).card : ℤ) =
        (if t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2 then (q : ℤ) - 1 else 0) +
        (if t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))
          then (q : ℤ) - 2 else 0) +
        (if t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧
            t.1.1 + t.1.2 ≠ t.2.1 + t.2.2 then 1 else 0) := by
    intro t _
    rcases t with ⟨⟨u, v⟩, ⟨w, z⟩⟩
    dsimp only
    by_cases hmatch : (u = w ∧ v = z) ∨ (u = z ∧ v = w)
    · -- Matching unordered pairs `{u, v} = {w, z}`:
      have hdisj_false : ¬ (u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ u + v ≠ w + z) := by
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      simp only [hdisj_false, ↓reduceIte, add_zero]
      have hprod_eq : ∀ b : F, (u + b) * (v + b) = (w + b) * (z + b) := fun b => by
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
      by_cases huv : u = v
      · subst huv
        have h1 : u = w ∧ u = z := by rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have hfilt : (Finset.univ.filter fun b : F =>
            (u + b) * (u + b) = (w + b) * (z + b) ∧ (u + b) * (u + b) ≠ 0) =
            Finset.univ.erase (-u) := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
            hprod_eq b, mul_ne_zero_iff, and_self]
          exact ⟨fun h hbu => h (by rw [hbu, add_neg_cancel]),
            fun h h0 => h (by linear_combination h0)⟩
        rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        have h12 : w = z := h1.1.symm.trans h1.2
        simp [h1.1, h12]
        have : 1 ≤ q := Fintype.card_pos
        change ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1
        omega
      · have hfilt : (Finset.univ.filter fun b : F =>
            (u + b) * (v + b) = (w + b) * (z + b) ∧ (u + b) * (v + b) ≠ 0) =
            (Finset.univ.erase (-u)).erase (-v) := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
            hprod_eq b, mul_ne_zero_iff]
          constructor
          · rintro ⟨hu0, hv0⟩
            exact ⟨fun h => hv0 (by rw [h, add_neg_cancel]),
              fun h => hu0 (by rw [h, add_neg_cancel])⟩
          · rintro ⟨hvb, hub⟩
            exact ⟨fun h => hub (by linear_combination h), fun h => hvb (by linear_combination h)⟩
        have hmem : -v ∈ Finset.univ.erase (-u) :=
          Finset.mem_erase.mpr ⟨fun h => huv (neg_inj.mp h).symm, Finset.mem_univ _⟩
        rw [hfilt, Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ]
        simp [huv, hmatch]
        have h2 : 2 ≤ q := Fintype.one_lt_card
        change ((q - 1 - 1 : ℕ) : ℤ) = (q : ℤ) - 2
        omega
    · -- Non-matching pairs `{u, v} ≠ {w, z}`:
      have h1 : ¬ (u = v ∧ u = w ∧ u = z) := fun ⟨huv, huw, huz⟩ => hmatch (Or.inl ⟨huw, huv.symm.trans huz⟩)
      have h2 : ¬ (u ≠ v ∧ ((u = w ∧ v = z) ∨ (u = z ∧ v = w))) := fun h => hmatch h.2
      simp only [h1, h2, ↓reduceIte, zero_add]
      by_cases hshare : u = w ∨ u = z ∨ v = w ∨ v = z
      · -- Share a site, yet pairs don't match → ZERO valid shifts!
        have hdisj_false : ¬ (u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ u + v ≠ w + z) := by tauto
        simp only [hdisj_false, ↓reduceIte]
        have hempty : (Finset.univ.filter fun b : F =>
            (u + b) * (v + b) = (w + b) * (z + b) ∧ (u + b) * (v + b) ≠ 0) = ∅ := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            not_and]
          intro heq hnz
          have hu0 : u + b ≠ 0 := left_ne_zero_of_mul hnz
          have hv0 : v + b ≠ 0 := right_ne_zero_of_mul hnz
          rcases hshare with rfl | rfl | rfl | rfl
          · have : v + b = z + b := mul_left_cancel₀ hu0 heq
            exact hmatch (Or.inl ⟨rfl, by linear_combination this⟩)
          · have : v + b = w + b := mul_left_cancel₀ hu0 (by linear_combination heq)
            exact hmatch (Or.inr ⟨rfl, by linear_combination this⟩)
          · have : u + b = z + b := mul_right_cancel₀ hv0 (by linear_combination heq)
            exact hmatch (Or.inr ⟨by linear_combination this, rfl⟩)
          · have : u + b = w + b := mul_right_cancel₀ hv0 heq
            exact hmatch (Or.inl ⟨by linear_combination this, rfl⟩)
        rw [hempty]; simp
      · push Not at hshare
        obtain ⟨huw, huz, hvw, hvz⟩ := hshare
        by_cases hsum : u + v = w + z
        · -- Disjoint pairs with equal sums → ZERO solutions!
          have hdisj_false : ¬ (u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ u + v ≠ w + z) := by tauto
          simp only [hdisj_false, ↓reduceIte]
          have hprod_ne : u * v ≠ w * z := by
            intro hp
            have hfac : (u - w) * (u - z) = 0 := by
              have : (u - w) * (u - z) = u * (u + v - (w + z)) + (w * z - u * v) := by ring
              rw [this, hsum, sub_self, mul_zero, hp, sub_self, add_zero]
            rcases mul_eq_zero.mp hfac with h | h
            · exact huw (sub_eq_zero.mp h)
            · exact huz (sub_eq_zero.mp h)
          have hempty : (Finset.univ.filter fun b : F =>
              (u + b) * (v + b) = (w + b) * (z + b) ∧ (u + b) * (v + b) ≠ 0) = ∅ := by
            ext b
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
              not_and]
            intro heq _
            exact hprod_ne (by linear_combination heq - b * hsum)
          rw [hempty]; simp
        · -- Disjoint pairs with distinct sums → UNIQUE nonzero shift `b₀ = (w*z - u*v) / (u + v - w - z)`!
          simp only [huw, huz, hvw, hvz, hsum, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          set b₀ : F := (w * z - u * v) / (u + v - (w + z))
          have hden : u + v - (w + z) ≠ 0 := sub_ne_zero.mpr hsum
          have hb₀_eq : (u + b₀) * (v + b₀) = (w + b₀) * (z + b₀) := by
            have hmul : (u + v - (w + z)) * b₀ = w * z - u * v := mul_div_cancel₀ _ hden
            linear_combination hmul
          have hb₀_nz : (u + b₀) * (v + b₀) ≠ 0 := by
            intro h0
            have h0' : (w + b₀) * (z + b₀) = 0 := hb₀_eq.symm.trans h0
            rcases mul_eq_zero.mp h0 with hu0 | hv0 <;> rcases mul_eq_zero.mp h0' with hw0 | hz0
            · exact huw (by linear_combination hu0 - hw0)
            · exact huz (by linear_combination hu0 - hz0)
            · exact hvw (by linear_combination hv0 - hw0)
            · exact hvz (by linear_combination hv0 - hz0)
          have hfilt : (Finset.univ.filter fun b : F =>
              (u + b) * (v + b) = (w + b) * (z + b) ∧ (u + b) * (v + b) ≠ 0) = {b₀} := by
            ext b
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨heq, _⟩
              have hlin : (u + v - (w + z)) * b = w * z - u * v := by linear_combination heq
              exact eq_div_of_mul_eq hden (by linear_combination hlin)
            · rintro rfl; exact ⟨hb₀_eq, hb₀_nz⟩
          rw [hfilt]; simp
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Count each of the 3 disjoint families in `Q`:
  -- 1. Constant quadruples (`u = v = w = z`): `m`
  have hc1 : ∑ t ∈ Q, (if t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2 then (q : ℤ) - 1 else 0) =
      (m : ℤ) * ((q : ℤ) - 1) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Q.filter fun t => t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2).card = m :=
      Finset.card_bij (fun t _ => t.1.1)
        (fun t ht => by simp only [Q, mem_filter, mem_product] at ht; exact ht.1.1.1)
        (fun t₁ h₁ t₂ h₂ h => by
          simp only [mem_filter] at h₁ h₂
          exact Prod.ext (Prod.ext h (h₁.2.1.symm.trans (h.trans h₂.2.1)))
            (Prod.ext (h₁.2.2.1.symm.trans (h.trans h₂.2.2.1))
              (h₁.2.2.2.symm.trans (h.trans h₂.2.2.2))))
        (fun u hu => ⟨((u, u), (u, u)), by simp [Q, hu], rfl⟩)
    exact_mod_cast hcard
  -- 2. Non-constant matching pairs (`u ≠ v`, `{u, v} = {w, z}`): `2 * m * (m - 1)`
  have hc2 : ∑ t ∈ Q, (if t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))
        then (q : ℤ) - 2 else 0) =
      2 * (m : ℤ) * ((m : ℤ) - 1) * ((q : ℤ) - 2) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    let P1 := Q.filter fun t => t.1.1 ≠ t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.2 = t.2.2
    let P2 := Q.filter fun t => t.1.1 ≠ t.1.2 ∧ t.1.1 = t.2.2 ∧ t.1.2 = t.2.1
    have hdisj : Disjoint P1 P2 := by
      rw [Finset.disjoint_filter]
      intro t _ h1 h2
      exact h1.1 (h1.2.1.trans h2.2.2.symm)
    have hunion : Q.filter (fun t => t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨
        (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))) = P1 ∪ P2 := by
      ext t; simp only [P1, P2, mem_union, mem_filter]; tauto
    have hcard_pair : ∀ S : Finset ((F × F) × (F × F)),
        (S = P1 ∨ S = P2) → S.card = m * (m - 1) := by
      intro S hS
      let T := A.sigma fun u => A.erase u
      have hT : T.card = m * (m - 1) := by
        rw [Finset.card_sigma, Finset.sum_congr rfl fun u hu => Finset.card_erase_of_mem hu,
          Finset.sum_const, smul_eq_mul]
      rw [← hT]
      rcases hS with rfl | rfl
      · exact Finset.card_bij (fun t _ => ⟨t.1.1, t.1.2⟩)
          (fun t ht => by
            simp only [P1, Q, T, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢
            exact ⟨ht.1.1.1, ht.2.1.symm, ht.1.1.2⟩)
          (fun t₁ h₁ t₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
            simp only [P1, mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 h.2)
              (Prod.ext (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1))
                (h₁.2.2.2.symm.trans (h.2.trans h₂.2.2.2))))
          (fun p hp => by
            simp only [T, mem_sigma, mem_erase] at hp
            exact ⟨((p.1, p.2), (p.1, p.2)), by simp [P1, Q, hp.1, hp.2.1.symm, hp.2.2], rfl⟩)
      · exact Finset.card_bij (fun t _ => ⟨t.1.1, t.1.2⟩)
          (fun t ht => by
            simp only [P2, Q, T, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢
            exact ⟨ht.1.1.1, ht.2.1.symm, ht.1.1.2⟩)
          (fun t₁ h₁ t₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
            simp only [P2, mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 h.2)
              (Prod.ext (h₁.2.2.2.symm.trans (h.2.trans h₂.2.2.2))
                (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1))))
          (fun p hp => by
            simp only [T, mem_sigma, mem_erase] at hp
            exact ⟨((p.1, p.2), (p.2, p.1)), by simp [P2, Q, hp.1, hp.2.1.symm, hp.2.2], rfl⟩)
    rw [hunion, Finset.card_union_of_disjoint hdisj, hcard_pair P1 (Or.inl rfl),
      hcard_pair P2 (Or.inr rfl)]
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · simp [hm0]
    · push_cast [Nat.cast_sub hm_pos]; ring
  -- 3. Disjoint pairs with distinct sums:
  -- Count `Disj = {t ∈ Q | {u, v} ∩ {w, z} = ∅}` AND `DisjEq = {t ∈ Disj | u + v = w + z}`!
  -- Notice `E_+(A) = #{t ∈ Q | u + v = w + z} = (matching pairs: 2m^2 - m) + DisjEq.card`!
  -- (Because if pairs share one site and don't match, `u + v ≠ w + z`!)
  -- And `Disj.card = m(m-1)^2 + m(m-1)(m-2)^2`!
  have hc3 : ∑ t ∈ Q, (if t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧
        t.1.1 + t.1.2 ≠ t.2.1 + t.2.2 then (1 : ℤ) else 0) =
      (m : ℤ) ^ 4 - 4 * (m : ℤ) ^ 3 + 6 * (m : ℤ) ^ 2 - 3 * m -
        ((additiveEnergy A : ℤ) - (2 * (m : ℤ) ^ 2 - m)) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    let Disj := Q.filter fun t => t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2
    let Match := Q.filter fun t => (t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1)
    have hsplit_disj : Disj.card =
        (Q.filter fun t => t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧
          t.1.1 + t.1.2 ≠ t.2.1 + t.2.2).card +
        (Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card := by
      have h1 : (Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card +
          (Disj.filter fun t => ¬ t.1.1 + t.1.2 = t.2.1 + t.2.2).card = Disj.card := by
        simpa using Finset.sum_filter_add_sum_filter_not Disj
          (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2) (fun _ => (1 : ℕ))
      have heq : Disj.filter (fun t => ¬ t.1.1 + t.1.2 = t.2.1 + t.2.2) =
          Q.filter fun t => t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧
            t.1.1 + t.1.2 ≠ t.2.1 + t.2.2 := by
        ext t; simp only [Disj, mem_filter]; tauto
      rw [← heq]; omega
    -- `additiveEnergy A = Match.card + (Disj.filter (u + v = w + z)).card`:
    have hE_split : additiveEnergy A =
        Match.card + (Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card := by
      have hdisj_MD : Disjoint Match (Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2) := by
        rw [Finset.disjoint_left]
        intro t htM htD
        simp only [Match, Disj, mem_filter] at htM htD
        rcases htM.2 with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact htD.1.2.1 h1
        · exact htD.1.2.2.1 h1
      have hunion : Q.filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2) =
          Match ∪ Disj.filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2) := by
        ext t
        simp only [Match, Disj, mem_union, mem_filter]
        constructor
        · rintro ⟨htQ, hsum⟩
          by_cases hM : (t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1)
          · exact Or.inl ⟨htQ, hM⟩
          · refine Or.inr ⟨⟨htQ, ?_, ?_, ?_, ?_⟩, hsum⟩
            · intro h; exact hM (Or.inl ⟨h, by linear_combination hsum - h⟩)
            · intro h; exact hM (Or.inr ⟨h, by linear_combination hsum - h⟩)
            · intro h; exact hM (Or.inr ⟨by linear_combination hsum - h, h⟩)
            · intro h; exact hM (Or.inl ⟨by linear_combination hsum - h, h⟩)
        · rintro (⟨htQ, hM⟩ | ⟨⟨htQ, _⟩, hsum⟩)
          · refine ⟨htQ, ?_⟩
            rcases hM with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
          · exact ⟨htQ, hsum⟩
      unfold additiveEnergy
      rw [← Finset.card_union_of_disjoint hdisj_MD, ← hunion]
    -- `Match.card = 2 * m^2 - m` (in `ℤ`):
    have hMatch_card : (Match.card : ℤ) = 2 * (m : ℤ) ^ 2 - m := by
      have hdisj_M : Disjoint (Q.filter fun t => t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2)
          (Q.filter fun t => t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨
            (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))) := by
        rw [Finset.disjoint_filter]; intro t _ h1 h2; exact h2.1 h1.1
      have hunion_M : Match =
          (Q.filter fun t => t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2) ∪
          (Q.filter fun t => t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨
            (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))) := by
        ext t; simp only [Match, mem_union, mem_filter]
        constructor
        · rintro ⟨htQ, hM⟩
          by_cases huv : t.1.1 = t.1.2
          · refine Or.inl ⟨htQ, huv, ?_⟩
            rcases hM with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1, huv.trans h2⟩
            · exact ⟨huv.trans h2, h1⟩
          · exact Or.inr ⟨htQ, huv, hM⟩
        · rintro (⟨htQ, h1, h2, h3⟩ | ⟨htQ, _, hM⟩)
          · exact ⟨htQ, Or.inl ⟨h2, h1.symm.trans h3⟩⟩
          · exact ⟨htQ, hM⟩
      have hcard1 : (Q.filter fun t => t.1.1 = t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.1 = t.2.2).card = m :=
        Finset.card_bij (fun t _ => t.1.1)
          (fun t ht => by simp only [Q, mem_filter, mem_product] at ht; exact ht.1.1.1)
          (fun t₁ h₁ t₂ h₂ h => by
            simp only [mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h (h₁.2.1.symm.trans (h.trans h₂.2.1)))
              (Prod.ext (h₁.2.2.1.symm.trans (h.trans h₂.2.2.1))
                (h₁.2.2.2.symm.trans (h.trans h₂.2.2.2))))
          (fun u hu => ⟨((u, u), (u, u)), by simp [Q, hu], rfl⟩)
      have hcard2 : ((Q.filter fun t => t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨
          (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))).card : ℤ) = 2 * (m : ℤ) * ((m : ℤ) - 1) := by
        -- Already proved inside `hc2`, derive cleanly:
        let P1 := Q.filter fun t => t.1.1 ≠ t.1.2 ∧ t.1.1 = t.2.1 ∧ t.1.2 = t.2.2
        let P2 := Q.filter fun t => t.1.1 ≠ t.1.2 ∧ t.1.1 = t.2.2 ∧ t.1.2 = t.2.1
        have hd : Disjoint P1 P2 := by
          rw [Finset.disjoint_filter]; intro t _ h1 h2; exact h1.1 (h1.2.1.trans h2.2.2.symm)
        have hu : Q.filter (fun t => t.1.1 ≠ t.1.2 ∧ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨
            (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))) = P1 ∪ P2 := by
          ext t; simp only [P1, P2, mem_union, mem_filter]; tauto
        let T := A.sigma fun u => A.erase u
        have hT : T.card = m * (m - 1) := by
          rw [Finset.card_sigma, Finset.sum_congr rfl fun u hu => Finset.card_erase_of_mem hu,
            Finset.sum_const, smul_eq_mul]
        have hp1 : P1.card = T.card := Finset.card_bij (fun t _ => ⟨t.1.1, t.1.2⟩)
          (fun t ht => by simp only [P1, Q, T, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢; exact ⟨ht.1.1.1, ht.2.1.symm, ht.1.1.2⟩)
          (fun t₁ h₁ t₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; simp only [P1, mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 h.2) (Prod.ext (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1)) (h₁.2.2.2.symm.trans (h.2.trans h₂.2.2.2))))
          (fun p hp => by simp only [T, mem_sigma, mem_erase] at hp; exact ⟨((p.1, p.2), (p.1, p.2)), by simp [P1, Q, hp.1, hp.2.1.symm, hp.2.2], rfl⟩)
        have hp2 : P2.card = T.card := Finset.card_bij (fun t _ => ⟨t.1.1, t.1.2⟩)
          (fun t ht => by simp only [P2, Q, T, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢; exact ⟨ht.1.1.1, ht.2.1.symm, ht.1.1.2⟩)
          (fun t₁ h₁ t₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; simp only [P2, mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 h.2) (Prod.ext (h₁.2.2.2.symm.trans (h.2.trans h₂.2.2.2)) (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1))))
          (fun p hp => by simp only [T, mem_sigma, mem_erase] at hp; exact ⟨((p.1, p.2), (p.2, p.1)), by simp [P2, Q, hp.1, hp.2.1.symm, hp.2.2], rfl⟩)
        rw [hu, Finset.card_union_of_disjoint hd, hp1, hp2, hT]
        rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
        · simp [hm0]
        · push_cast [Nat.cast_sub hm_pos]; ring
      rw [hunion_M, Finset.card_union_of_disjoint hdisj_M, Nat.cast_add, hcard1, hcard2]; ring
    -- `Disj.card = m(m-1)^2 + m(m-1)(m-2)^2 = m^4 - 4m^3 + 6m^2 - 3m` (in `ℤ`):
    have hDisj_card : (Disj.card : ℤ) = (m : ℤ) ^ 4 - 4 * (m : ℤ) ^ 3 + 6 * (m : ℤ) ^ 2 - 3 * m := by
      -- Count by fixing `(u, v) ∈ A ×ˢ A` and choosing `(w, z) ∈ (A \ {u, v})^2`:
      let S := (A ×ˢ A).sigma fun p => ((A.erase p.1).erase p.2) ×ˢ ((A.erase p.1).erase p.2)
      have hbij : Disj.card = S.card :=
        Finset.card_bij (fun t _ => ⟨t.1, t.2⟩)
          (fun t ht => by
            simp only [Disj, Q, S, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢
            exact ⟨ht.1.1, ⟨ht.2.2.2.1.symm, ht.2.1.symm, ht.1.2.1⟩,
              ⟨ht.2.2.2.2.symm, ht.2.2.1.symm, ht.1.2.2⟩⟩)
          (fun _ _ _ _ h => by simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2)
          (fun x hx => by
            simp only [S, mem_sigma, mem_product, mem_erase] at hx
            exact ⟨(x.1, x.2), by
              simp [Disj, Q, hx.1.1, hx.1.2, hx.2.1.1.symm, hx.2.1.2.1.symm, hx.2.1.2.2,
                hx.2.2.1.symm, hx.2.2.2.1.symm, hx.2.2.2.2], rfl⟩)
      rw [hbij, Finset.card_sigma]
      have hper : ∀ p ∈ A ×ˢ A, ((((A.erase p.1).erase p.2) ×ˢ ((A.erase p.1).erase p.2)).card : ℤ) =
          if p.1 = p.2 then ((m : ℤ) - 1) ^ 2 else ((m : ℤ) - 2) ^ 2 := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_product.mp hp
        rw [Finset.card_product, Nat.cast_mul]
        by_cases heq : p.1 = p.2
        · rw [heq, Finset.erase_idem, Finset.card_erase_of_mem hp2]
          simp only [↓reduceIte]
          have hm1 : 1 ≤ m := Finset.card_pos.mpr ⟨p.2, hp2⟩
          rw [show ((A.card - 1 : ℕ) : ℤ) = (m : ℤ) - 1 by dsimp [m]; omega]
          ring
        · have hmem : p.2 ∈ A.erase p.1 := Finset.mem_erase.mpr ⟨Ne.symm heq, hp2⟩
          rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem hp1, Nat.sub_sub]
          simp only [heq, ↓reduceIte]
          have hm2 : 2 ≤ m := Finset.one_lt_card.mpr ⟨p.1, hp1, p.2, hp2, heq⟩
          rw [show ((A.card - (1 + 1) : ℕ) : ℤ) = (m : ℤ) - 2 by dsimp [m]; omega]
          ring
      rw [Nat.cast_sum, Finset.sum_congr rfl hper, Finset.sum_product]
      have hrow : ∀ u ∈ A, ∑ v ∈ A, (if u = v then ((m : ℤ) - 1) ^ 2 else ((m : ℤ) - 2) ^ 2) =
          ((m : ℤ) - 1) ^ 2 + ((m : ℤ) - 1) * ((m : ℤ) - 2) ^ 2 := by
        intro u hu
        rw [← Finset.add_sum_erase A _ hu]
        simp only [↓reduceIte]
        have hrest : ∑ v ∈ A.erase u, (if u = v then ((m : ℤ) - 1) ^ 2 else ((m : ℤ) - 2) ^ 2) =
            ∑ _v ∈ A.erase u, ((m : ℤ) - 2) ^ 2 :=
          Finset.sum_congr rfl fun v hv => by simp [(Finset.mem_erase.mp hv).1.symm]
        rw [hrest, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hu]
        have hm1 : 1 ≤ m := Finset.card_pos.mpr ⟨u, hu⟩
        rw [Nat.cast_sub hm1, Nat.cast_one]
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
      change (m : ℤ) * _ = _
      ring
    have hsplitZ : (Disj.card : ℤ) =
        ((Q.filter fun t => t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧ t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧
          t.1.1 + t.1.2 ≠ t.2.1 + t.2.2).card : ℤ) +
        ((Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card : ℤ) := by
      exact_mod_cast hsplit_disj
    have hEZ : (additiveEnergy A : ℤ) =
        (Match.card : ℤ) + ((Disj.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2).card : ℤ) := by
      exact_mod_cast hE_split
    linarith [hDisj_card, hMatch_card, hsplitZ, hEZ]
  rw [hc1, hc2, hc3]; ring

/-- **Exact complete nonprincipal fourth moment** (`paley-character-averages.md`, eq. 1):
`∑_{ψ ≠ 1} ∑_{b : F} ‖W_ψ(b)‖^4 = (q - 1)(q(2m^2 - m) - 4m^3 + 4m^2 - m - E_+(A)) + m(m-1)(3m^2 - 3m + 1)`. -/
theorem sum_nonprincipal_fourth_moment_eq {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1)
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (hinj : Function.Injective dlog)
    (A : Finset F) :
    ∑ k ∈ (Finset.range (Fintype.card F - 1)).erase 0, ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 =
      ((Fintype.card F - 1 : ℕ) : ℝ) *
        (((Fintype.card F : ℤ) * (2 * (A.card : ℤ) ^ 2 - A.card) -
          4 * (A.card : ℤ) ^ 3 + 4 * (A.card : ℤ) ^ 2 - A.card - (additiveEnergy A : ℤ)) : ℝ) +
      (((A.card : ℤ) * ((A.card : ℤ) - 1) * (3 * (A.card : ℤ) ^ 2 - 3 * A.card + 1)) : ℝ) := by
  classical
  set q := Fintype.card F
  set N := q - 1
  set m := A.card
  have hN_pos : 0 < N := by have := Fintype.one_lt_card (α := F); omega
  have h0_mem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN_pos
  have hall := sum_all_mulChar_fourth_moment_eq hlt hmul hinj A
  rw [← Finset.add_sum_erase _ _ h0_mem] at hall
  -- Principal character `k = 0`: `W_0(b) = m - 1` if `-b ∈ A`, else `m`!
  have hprinc : ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog 0) b‖ ^ 4 =
      (((q : ℤ) - m) * (m : ℤ) ^ 4 + (m : ℤ) * ((m : ℤ) - 1) ^ 4 : ℝ) := by
    have hval : ∀ b : F, ‖charShiftSum A (cyclicMulChar dlog 0) b‖ ^ 4 =
        if -b ∈ A then (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 else ((m : ℤ) : ℝ) ^ 4 := by
      intro b
      have hsum0 : charShiftSum A (cyclicMulChar dlog 0) b =
          (((if -b ∈ A then (m : ℤ) - 1 else (m : ℤ)) : ℤ) : ℂ) := by
        unfold charShiftSum
        have hpt : ∀ a ∈ A, cyclicMulChar dlog 0 (a + b) = if a = -b then 0 else 1 := fun a _ => by
          unfold cyclicMulChar
          by_cases hz : a + b = 0
          · have : a = -b := by linear_combination hz
            simp [this]
          · have : a ≠ -b := fun h => hz (by rw [h, neg_add_cancel])
            simp [hz, this]
        rw [Finset.sum_congr rfl hpt]
        by_cases hmem : -b ∈ A
        · simp only [hmem, ↓reduceIte]
          rw [← Finset.add_sum_erase A _ hmem]
          simp only [↓reduceIte, zero_add]
          have hrest : ∑ a ∈ A.erase (-b), (if a = -b then (0 : ℂ) else 1) =
              ∑ _a ∈ A.erase (-b), (1 : ℂ) :=
            Finset.sum_congr rfl fun a ha => by simp [(Finset.mem_erase.mp ha).1]
          rw [hrest, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hmem]
          have hm1 : 1 ≤ m := Finset.card_pos.mpr ⟨-b, hmem⟩
          change ((m - 1 : ℕ) : ℂ) = (((m : ℤ) - 1 : ℤ) : ℂ)
          push_cast [Nat.cast_sub hm1]; rfl
        · simp only [hmem, ↓reduceIte]
          have hrest : ∑ a ∈ A, (if a = -b then (0 : ℂ) else 1) = ∑ _a ∈ A, (1 : ℂ) :=
            Finset.sum_congr rfl fun a ha => by
              simp [show a ≠ -b from fun h => hmem (h ▸ ha)]
          rw [hrest, Finset.sum_const, nsmul_eq_mul, mul_one]; simp [m]
      rw [hsum0, Complex.norm_intCast]
      split_ifs with hmem
      · have hm1 : 1 ≤ m := Finset.card_pos.mpr ⟨-b, hmem⟩
        have hnn : (0 : ℝ) ≤ ((m : ℤ) - 1 : ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ (m : ℤ) - 1)
        rw [abs_of_nonneg hnn]
      · rw [abs_of_nonneg (by positivity)]
    rw [Finset.sum_congr rfl fun b _ => hval b]
    have hneg_card : (Finset.univ.filter fun b : F => -b ∈ A).card = m := by
      have : (Finset.univ.filter fun b : F => -b ∈ A) = A.image Neg.neg := by
        ext b; simp only [mem_filter, mem_univ, true_and, mem_image]
        exact ⟨fun h => ⟨-b, h, neg_neg b⟩, fun ⟨a, ha, h⟩ => by rw [← h, neg_neg]; exact ha⟩
      rw [this, Finset.card_image_of_injective A neg_injective]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : F => -b ∈ A)]
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : F => -b ∈ A),
          (if -b ∈ A then (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 else ((m : ℤ) : ℝ) ^ 4) =
        (m : ℝ) * (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 := by
      have hcongr : ∑ b ∈ Finset.univ.filter (fun b : F => -b ∈ A),
            (if -b ∈ A then (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 else ((m : ℤ) : ℝ) ^ 4) =
          ∑ _b ∈ Finset.univ.filter (fun b : F => -b ∈ A), (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 :=
        Finset.sum_congr rfl fun b hb => by simp only [(Finset.mem_filter.mp hb).2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, hneg_card, nsmul_eq_mul]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b : F => ¬ -b ∈ A),
          (if -b ∈ A then (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 else ((m : ℤ) : ℝ) ^ 4) =
        (((q : ℤ) - m : ℤ) : ℝ) * ((m : ℤ) : ℝ) ^ 4 := by
      have hcongr : ∑ b ∈ Finset.univ.filter (fun b : F => ¬ -b ∈ A),
            (if -b ∈ A then (((m : ℤ) - 1 : ℤ) : ℝ) ^ 4 else ((m : ℤ) : ℝ) ^ 4) =
          ∑ _b ∈ Finset.univ.filter (fun b : F => ¬ -b ∈ A), ((m : ℤ) : ℝ) ^ 4 :=
        Finset.sum_congr rfl fun b hb => by simp only [(Finset.mem_filter.mp hb).2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul]
      have hcomp : (Finset.univ.filter fun b : F => ¬ -b ∈ A).card = q - m := by
        have htot : (Finset.univ.filter fun b : F => -b ∈ A).card +
            (Finset.univ.filter fun b : F => ¬ -b ∈ A).card = (Finset.univ : Finset F).card := by
          simpa using Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset F)
            (fun b : F => -b ∈ A) (fun _ => (1 : ℕ))
        rw [hneg_card, Finset.card_univ] at htot
        omega
      rw [hcomp, show ((q - m : ℕ) : ℝ) = (((q : ℤ) - m : ℤ) : ℝ) by
        have hmq : m ≤ q := Finset.card_le_univ A
        push_cast [Nat.cast_sub hmq]; rfl]
    rw [h1, h2]
    push_cast; ring
  have hN_eq : ((N : ℕ) : ℝ) = (q : ℝ) - 1 := by
    have : 1 ≤ q := Fintype.card_pos
    rw [Nat.cast_sub this, Nat.cast_one]
  rw [hprinc] at hall
  push_cast at hall ⊢
  rw [hN_eq] at hall ⊢
  linarith

/-- **Nonprincipal fourth moment upper bound**:
`∑_{ψ ≠ 1} ∑_{b : F} ‖W_ψ(b)‖^4 ≤ (q - 1) * q * (2m^2 - m)`. -/
theorem sum_nonprincipal_fourth_moment_le {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1)
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (hinj : Function.Injective dlog)
    (A : Finset F) :
    ∑ k ∈ (Finset.range (Fintype.card F - 1)).erase 0, ∑ b : F,
        ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ 4 ≤
      ((Fintype.card F - 1 : ℕ) : ℝ) * (Fintype.card F : ℝ) *
        (2 * (A.card : ℝ) ^ 2 - A.card) := by
  classical
  rw [sum_nonprincipal_fourth_moment_eq hlt hmul hinj A]
  set q := Fintype.card F
  set m := A.card
  -- Lower bound `E_+(A) ≥ 2m^2 - m` from matching pairs `{u, v} = {w, z}`!
  have hE_ge : 2 * (m : ℤ) ^ 2 - m ≤ (additiveEnergy A : ℤ) := by
    let Q := (A ×ˢ A) ×ˢ (A ×ˢ A)
    let M1 := Q.filter fun t => t.1.1 = t.2.1 ∧ t.1.2 = t.2.2
    let M2 := Q.filter fun t => t.1.1 ≠ t.1.2 ∧ t.1.1 = t.2.2 ∧ t.1.2 = t.2.1
    have hdisj : Disjoint M1 M2 := by
      rw [Finset.disjoint_filter]; intro t _ h1 h2; exact h2.1 (h1.1.trans h2.2.2.symm)
    have hsub : M1 ∪ M2 ⊆ Q.filter fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2 := by
      intro t ht
      simp only [M1, M2, mem_union, mem_filter] at ht ⊢
      rcases ht with ⟨htQ, h1, h2⟩ | ⟨htQ, _, h1, h2⟩
      · exact ⟨htQ, by rw [h1, h2]⟩
      · exact ⟨htQ, by rw [h1, h2]; ring⟩
    have hc1 : M1.card = m * m := by
      have : M1.card = (A ×ˢ A).card := Finset.card_bij (fun t _ => t.1)
        (fun t ht => by simp only [M1, Q, mem_filter, mem_product] at ht; exact mem_product.mpr ht.1.1)
        (fun t₁ h₁ t₂ h₂ h => by
          simp only [M1, mem_filter] at h₁ h₂
          have hu : t₁.1.1 = t₂.1.1 := congrArg Prod.fst h
          have hv : t₁.1.2 = t₂.1.2 := congrArg Prod.snd h
          exact Prod.ext h (Prod.ext (h₁.2.1.symm.trans (hu.trans h₂.2.1))
            (h₁.2.2.symm.trans (hv.trans h₂.2.2))))
        (fun p hp => ⟨(p, p), by simp [M1, Q, hp], rfl⟩)
      rw [this, Finset.card_product]
    have hc2 : M2.card = m * (m - 1) := by
      let T := A.sigma fun u => A.erase u
      have hT : T.card = m * (m - 1) := by
        rw [Finset.card_sigma, Finset.sum_congr rfl fun u hu => Finset.card_erase_of_mem hu,
          Finset.sum_const, smul_eq_mul]
      rw [← hT]
      exact Finset.card_bij (fun t _ => ⟨t.1.1, t.1.2⟩)
        (fun t ht => by
          simp only [M2, Q, T, mem_filter, mem_product, mem_sigma, mem_erase] at ht ⊢
          exact ⟨ht.1.1.1, ht.2.1.symm, ht.1.1.2⟩)
        (fun t₁ h₁ t₂ h₂ h => by
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
          simp only [M2, mem_filter] at h₁ h₂
          exact Prod.ext (Prod.ext h.1 h.2)
            (Prod.ext (h₁.2.2.2.symm.trans (h.2.trans h₂.2.2.2))
              (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1))))
        (fun p hp => by
          simp only [T, mem_sigma, mem_erase] at hp
          exact ⟨((p.1, p.2), (p.2, p.1)), by simp [M2, Q, hp.1, hp.2.1.symm, hp.2.2], rfl⟩)
    have hle : M1.card + M2.card ≤ additiveEnergy A := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    rw [hc1, hc2] at hle
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · simp [hm0]
    · have hleZ : ((m * m + m * (m - 1) : ℕ) : ℤ) ≤ (additiveEnergy A : ℤ) := by exact_mod_cast hle
      push_cast [Nat.cast_sub hm_pos] at hleZ
      linarith
  have hm_le_q : (m : ℝ) ≤ q := by exact_mod_cast Finset.card_le_univ A
  have hN_ge : (m : ℝ) - 1 ≤ ((q - 1 : ℕ) : ℝ) := by
    have : 1 ≤ q := Fintype.card_pos
    rw [Nat.cast_sub this, Nat.cast_one]; linarith
  have hE_geR : 2 * (m : ℝ) ^ 2 - m ≤ (additiveEnergy A : ℝ) := by exact_mod_cast hE_ge
  have hN_nn : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · simp [hm0]; positivity
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
    have hpoly_nn : 0 ≤ (m : ℝ) * (3 * (m : ℝ) ^ 2 - 3 * m + 1) := by nlinarith
    have hstep1 : (m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) ^ 2 - 3 * m + 1) ≤
        ((q - 1 : ℕ) : ℝ) * ((m : ℝ) * (3 * (m : ℝ) ^ 2 - 3 * m + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_right hN_ge hpoly_nn]
    have hstep2 : ((q - 1 : ℕ) : ℝ) * (-(additiveEnergy A : ℝ)) ≤
        ((q - 1 : ℕ) : ℝ) * (-(2 * (m : ℝ) ^ 2 - m)) :=
      mul_le_mul_of_nonneg_left (by linarith) hN_nn
    have hstep3 : 0 ≤ ((q - 1 : ℕ) : ℝ) * ((m : ℝ) ^ 3 + (m : ℝ) ^ 2 - m) :=
      mul_nonneg hN_nn (by nlinarith)
    push_cast
    linarith

/-! ## 4. Exceptional-character fraction bound for prescribed `A` over all partners `|B| ≥ |A|` -/

/-- **Exceptional-character fraction bound** (`paley-character-averages.md`, eq. 3):
for ANY prescribed nonempty `A ⊆ F` (`|A| = m ≥ 1`), ANY `r ≥ 1`, and ANY `ρ > 0`, the fraction of
multiplicative characters `ψ_k` (`k < |F| - 1`) admitting ANY partner `B ⊆ F` with `|B| ≥ m` and
`‖∑_{b ∈ B} W_{ψ_k}(b)‖ ≥ ρ * m * |B|` is at most `ρ^(-2r) * (r! * |F| / m^(r+1) + (r - 1) / m)`. -/
theorem card_bad_characters_le {dlog : Fˣ → ℕ}
    (hlt : ∀ u : Fˣ, dlog u < Fintype.card F - 1)
    (hmul : ∀ u v : Fˣ, dlog (u * v) % (Fintype.card F - 1) = (dlog u + dlog v) % (Fintype.card F - 1))
    (hinj : Function.Injective dlog)
    (A : Finset F) (hA : 0 < A.card) {r : ℕ} (hr : 1 ≤ r) {ρ : ℝ} (hρ : 0 < ρ) :
    let Bad := (Finset.range (Fintype.card F - 1)).filter fun k =>
      ∃ B : Finset F, A.card ≤ B.card ∧
        ρ * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ b ∈ B, charShiftSum A (cyclicMulChar dlog k) b‖
    (Bad.card : ℝ) / ((Fintype.card F - 1 : ℕ) : ℝ) ≤
      (ρ ^ (2 * r))⁻¹ *
        ((r.factorial : ℝ) * (Fintype.card F : ℝ) / (A.card : ℝ) ^ (r + 1) +
          ((r - 1 : ℕ) : ℝ) / (A.card : ℝ)) := by
  classical
  intro Bad
  set N := Fintype.card F - 1
  set m := A.card
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast (by omega : 0 < N)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hA
  have h2r_pos : (0 : ℝ) < (2 * r : ℕ) := by exact_mod_cast (by omega : 0 < 2 * r)
  -- For every `k ∈ Bad`, discrete Hölder implies `ρ^(2r) * m^(2r + 1) ≤ ∑ b : F, ‖W_k(b)‖^(2r)`!
  have hbad_lb : ∀ k ∈ Bad,
      ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1) ≤
        ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) := by
    intro k hk
    obtain ⟨_, B, hB_ge, hB_large⟩ := Finset.mem_filter.mp hk
    have hB_pos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast (lt_of_lt_of_le hA hB_ge)
    have hB_geR : (m : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB_ge
    -- Triangle inequality + convexity of `x ↦ x^(2r)` (Jensen / Hölder on `B`):
    have htri : ‖∑ b ∈ B, charShiftSum A (cyclicMulChar dlog k) b‖ ≤
        ∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖ := norm_sum_le ..
    have hjensen : ((∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖) / (B.card : ℝ)) ^ (2 * r) ≤
        (∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r)) / (B.card : ℝ) := by
      have hmap := Real.pow_arith_mean_le_arith_mean_pow B (fun _ => (B.card : ℝ)⁻¹)
        (fun b => ‖charShiftSum A (cyclicMulChar dlog k) b‖)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hB_pos.ne'])
        (fun _ _ => norm_nonneg _) (2 * r)
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← div_eq_inv_mul, ← div_eq_inv_mul] at hmap
      exact hmap
    have hlb1 : ρ * (m : ℝ) ≤ (∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖) / (B.card : ℝ) := by
      rw [le_div_iff₀ hB_pos]
      exact hB_large.trans htri
    have hlb2 : (ρ * (m : ℝ)) ^ (2 * r) ≤
        (∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r)) / (B.card : ℝ) :=
      (pow_le_pow_left₀ (by positivity) hlb1 (2 * r)).trans hjensen
    have hlb3 : (ρ * (m : ℝ)) ^ (2 * r) * (B.card : ℝ) ≤
        ∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) :=
      (le_div_iff₀ hB_pos).mp hlb2
    have hsub : ∑ b ∈ B, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) ≤
        ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) fun _ _ _ => by positivity
    calc ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1)
        = (ρ * (m : ℝ)) ^ (2 * r) * (m : ℝ) := by rw [mul_pow, pow_succ]; ring
      _ ≤ (ρ * (m : ℝ)) ^ (2 * r) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_left hB_geR (by positivity)
      _ ≤ _ := hlb3.trans hsub
  have hsum_bad : (Bad.card : ℝ) * (ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1)) ≤
      ∑ k ∈ Finset.range N, ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) := by
    calc (Bad.card : ℝ) * (ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1))
        = ∑ _k ∈ Bad, (ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Bad, ∑ b : F, ‖charShiftSum A (cyclicMulChar dlog k) b‖ ^ (2 * r) :=
          Finset.sum_le_sum hbad_lb
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
          fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have htot := hsum_bad.trans (sum_mulChar_even_moment_le hlt hmul hinj A hr)
  have hρ_pow_pos : 0 < ρ ^ (2 * r) := pow_pos hρ _
  have hm_pow_pos : 0 < (m : ℝ) ^ (2 * r + 1) := pow_pos hm_pos _
  rw [div_le_iff₀ hN_pos]
  have hrew : (ρ ^ (2 * r))⁻¹ *
        ((r.factorial : ℝ) * (Fintype.card F : ℝ) / (m : ℝ) ^ (r + 1) +
          ((r - 1 : ℕ) : ℝ) / (m : ℝ)) * (N : ℝ) =
      (N : ℝ) * ((r.factorial : ℝ) * (Fintype.card F : ℝ) * (m : ℝ) ^ r +
          ((r - 1 : ℕ) : ℝ) * (m : ℝ) ^ (2 * r)) / (ρ ^ (2 * r) * (m : ℝ) ^ (2 * r + 1)) := by
    have hpow2r : (m : ℝ) ^ (2 * r) = (m : ℝ) ^ r * (m : ℝ) ^ r := by
      rw [← pow_add, two_mul]
    have hpow2r1 : (m : ℝ) ^ (2 * r + 1) = (m : ℝ) ^ (r + 1) * (m : ℝ) ^ r := by
      rw [← pow_add]; congr 1; omega
    rw [hpow2r1, hpow2r]
    field_simp [hρ_pow_pos.ne', hm_pos.ne']
    rw [pow_succ]
    ring
  rw [hrew, le_div_iff₀ (mul_pos hρ_pow_pos hm_pow_pos)]
  exact htot

end ProximityGap.PaleyCharacterAverages

#print axioms ProximityGap.PaleyCharacterAverages.exists_dlog
#print axioms ProximityGap.PaleyCharacterAverages.sum_mulChar_even_moment_le
#print axioms ProximityGap.PaleyCharacterAverages.sum_all_mulChar_fourth_moment_eq
#print axioms ProximityGap.PaleyCharacterAverages.sum_nonprincipal_fourth_moment_eq
#print axioms ProximityGap.PaleyCharacterAverages.sum_nonprincipal_fourth_moment_le
#print axioms ProximityGap.PaleyCharacterAverages.card_bad_characters_le
