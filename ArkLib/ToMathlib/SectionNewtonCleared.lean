/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.NewtonTailEntry
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The cleared Newton filtration (#304, #138 — the elementary `(A.4)` exponent)

The denominator filtration of the Newton iterate over the localization
`A := Localization.Away ξ̄` of `F[Z]`: every coefficient of the Newton root `γ` clears to a
**polynomial numerator of explicit degree** at the **`(A.4)` exponent `2t − 1`**,

  `Cleared`: `∃ N : F[Z], deg N ≤ clearedBudget … t ∧ 𝔞 N = (𝔞 ξ̄)^(2t−1) · coeff t γ`
  (`gamma_cleared`).

**The `2t − 1` exponent is forced by the truncation structure of the linear Newton iteration
alone** — no partition combinatorics, no Faà-di-Bruno, no `Λ`-weight calculus:

* coefficients `b ≤ t` of `(S t)^i` clear at `2b − 1` (each convolution `(p, q)` either has a
  zero part — exponent exactly `2b − 1` — or two nonzero parts — exponent `2b − 2`;
  `pow_cleared`);
* the **top** coefficient `t + 1` of `(S t)^i` clears at `2t = 2(t+1) − 2`, one better,
  because `S t` is truncated at `t`: a single-part convolution `p = t + 1` *dies*
  (`coeff_S_eq_zero_of_lt`), so every surviving term has two nonzero parts or recurses on the
  top corner itself (`powTop_cleared`);
* the recursion `coeff (t+1) γ = −u⁻¹ · coeff (t+1) (eval (S t) Q)` then spends the saved
  unit on `Ring.inverse`: `2t + 1 = 2(t+1) − 1` (`gamma_cleared`).

This replaces the entire `βHensel`/`B_coeff`/partition apparatus of the legacy lane for the
section-Newton route.  Exit: `coeff_gamma_eq_zero_of_numerator_eq_zero` (unit cancellation)
and `exists_numerator` (the witness pack for per-place counting: the numerator vanishes at
more than `clearedBudget` places ⟹ the coefficient vanishes — the [BCIKS20] Claim 5.8 middle
window by ordinary root counting).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-- The image of `ξ` is a unit in `Localization.Away ξ`. -/
theorem isUnit_xi : IsUnit (𝔞 ξ) :=
  IsLocalization.Away.algebraMap_isUnit ξ

/-! ## The clearing predicate and its calculus -/

/-- `x ∈ Localization.Away ξ` **clears at exponent `e` with degree budget `D`**: some
polynomial numerator `N` of degree at most `D` has `𝔞 N = (𝔞 ξ)^e · x`. -/
def Cleared (x : Localization.Away ξ) (e D : ℕ) : Prop :=
  ∃ N : Polynomial F, N.natDegree ≤ D ∧ 𝔞 N = (𝔞 ξ) ^ e * x

namespace Cleared

variable {ξ}

theorem zero (e D : ℕ) : Cleared ξ (0 : Localization.Away ξ) e D :=
  ⟨0, by simp, by simp⟩

theorem one (D : ℕ) : Cleared ξ (1 : Localization.Away ξ) 0 D :=
  ⟨1, by simp, by simp⟩

theorem of_algebraMap (q : Polynomial F) : Cleared ξ (𝔞 q) 0 q.natDegree :=
  ⟨q, le_refl _, by rw [pow_zero, one_mul]⟩

theorem mono {x : Localization.Away ξ} {e D D' : ℕ} (h : Cleared ξ x e D) (hD : D ≤ D') :
    Cleared ξ x e D' := by
  obtain ⟨N, hdeg, hmap⟩ := h
  exact ⟨N, hdeg.trans hD, hmap⟩

theorem pad {x : Localization.Away ξ} {e e' D : ℕ} (h : Cleared ξ x e D) (he : e ≤ e') :
    Cleared ξ x e' (D + (e' - e) * ξ.natDegree) := by
  obtain ⟨N, hdeg, hmap⟩ := h
  refine ⟨ξ ^ (e' - e) * N, ?_, ?_⟩
  · calc (ξ ^ (e' - e) * N).natDegree ≤ (ξ ^ (e' - e)).natDegree + N.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (e' - e) * ξ.natDegree + D := by
        exact Nat.add_le_add Polynomial.natDegree_pow_le hdeg
      _ = D + (e' - e) * ξ.natDegree := by ring
  · rw [map_mul, map_pow, hmap, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he]

/-- Pad-and-relax in one step. -/
theorem padTo {x : Localization.Away ξ} {e e' D D' : ℕ} (h : Cleared ξ x e D) (he : e ≤ e')
    (hD : D + (e' - e) * ξ.natDegree ≤ D') : Cleared ξ x e' D' :=
  (h.pad he).mono hD

theorem add {x y : Localization.Away ξ} {e D : ℕ} (hx : Cleared ξ x e D)
    (hy : Cleared ξ y e D) : Cleared ξ (x + y) e D := by
  obtain ⟨N, hNdeg, hNmap⟩ := hx
  obtain ⟨M, hMdeg, hMmap⟩ := hy
  refine ⟨N + M, ?_, ?_⟩
  · exact Polynomial.natDegree_add_le_of_degree_le hNdeg hMdeg
  · rw [map_add, hNmap, hMmap, mul_add]

theorem neg {x : Localization.Away ξ} {e D : ℕ} (h : Cleared ξ x e D) :
    Cleared ξ (-x) e D := by
  obtain ⟨N, hdeg, hmap⟩ := h
  exact ⟨-N, by rwa [Polynomial.natDegree_neg], by rw [map_neg, hmap, mul_neg]⟩

theorem mul {x y : Localization.Away ξ} {e e' D D' : ℕ} (hx : Cleared ξ x e D)
    (hy : Cleared ξ y e' D') : Cleared ξ (x * y) (e + e') (D + D') := by
  obtain ⟨N, hNdeg, hNmap⟩ := hx
  obtain ⟨M, hMdeg, hMmap⟩ := hy
  refine ⟨N * M, ?_, ?_⟩
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hNdeg hMdeg)
  · rw [map_mul, hNmap, hMmap, pow_add]
    ring

theorem sum {α : Type*} {s : Finset α} {f : α → Localization.Away ξ} {e D : ℕ}
    (h : ∀ i ∈ s, Cleared ξ (f i) e D) : Cleared ξ (∑ i ∈ s, f i) e D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cleared.zero e D
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Multiplying by `Ring.inverse (𝔞 ξ)` raises the clearing exponent by one, degree-free —
the `(A.4)` unit spend. -/
theorem inverse_xi_mul {x : Localization.Away ξ} {e D : ℕ} (h : Cleared ξ x e D) :
    Cleared ξ (Ring.inverse (𝔞 ξ) * x) (e + 1) D := by
  obtain ⟨N, hdeg, hmap⟩ := h
  refine ⟨N, hdeg, ?_⟩
  rw [pow_succ, mul_assoc, ← mul_assoc (𝔞 ξ), Ring.mul_inverse_cancel _ (isUnit_xi ξ),
    one_mul, hmap]

end Cleared

/-- **Unit cancellation exit**: a vanishing numerator kills the coefficient. -/
theorem eq_zero_of_cleared_witness {x : Localization.Away ξ} {e : ℕ} {N : Polynomial F}
    (hmap : 𝔞 N = (𝔞 ξ) ^ e * x) (hN : N = 0) : x = 0 := by
  rw [hN, map_zero] at hmap
  exact (((isUnit_xi ξ).pow e).mul_right_eq_zero).mp hmap.symm

/-! ## The budget recursion -/

/-- The cleared-numerator degree budget: `dv` at order `0`; one `DZ + d·(budget + 2t·dξ) +
2t·dξ` step per order (quadratic in `t`).  Monotone by construction. -/
def clearedBudget (d dv DZ dξ : ℕ) : ℕ → ℕ
  | 0 => dv
  | (t + 1) => max (clearedBudget d dv DZ dξ t)
      (DZ + d * (clearedBudget d dv DZ dξ t + 2 * t * dξ) + 2 * t * dξ)

theorem clearedBudget_mono (d dv DZ dξ : ℕ) : Monotone (clearedBudget d dv DZ dξ) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [clearedBudget]
  exact le_max_left _ _

/-! ## The power filtration -/

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-- **The power filtration**: coefficients `b ≤ t` of `(S t)^i` clear at the `(A.4)` exponent
`2b − 1`.  Convolution induction on `i`: every `(p, q)`-term either has a zero part (exact
exponent) or two nonzero parts (one to spare). -/
theorem pow_cleared {t G : ℕ}
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1) G) :
    ∀ i, ∀ b ≤ t, Cleared ξ (coeff b ((S QA (𝔞 v) t) ^ i)) (2 * b - 1)
      (i * (G + 2 * t * ξ.natDegree)) := by
  intro i
  induction i with
  | zero =>
      intro b hb
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · rw [pow_zero]
        have h1 : coeff 0 (1 : PowerSeries (Localization.Away ξ)) = 1 := by simp
        rw [h1]
        exact (Cleared.one _).mono (Nat.zero_le _)
      · rw [pow_zero]
        have h0 : coeff b (1 : PowerSeries (Localization.Away ξ)) = 0 := by
          rw [PowerSeries.coeff_one, if_neg (by omega)]
        rw [h0]
        exact Cleared.zero _ _
  | succ i ih =>
      intro b hb
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = b := Finset.mem_antidiagonal.mp hp
      have hp1 : p.1 ≤ t := by omega
      have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
        (coeff_γ_eq_S QA (𝔞 v) hp1).symm
      rw [hSγ]
      have hterm := (hγ p.1 hp1).mul (ih p.2 (by omega))
      have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) ≤ 2 * b - 1 := by omega
      refine hterm.padTo hexp ?_
      have hpadcost : (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) ≤ 2 * t := by omega
      calc G + i * (G + 2 * t * ξ.natDegree)
            + (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
          ≤ G + i * (G + 2 * t * ξ.natDegree) + 2 * t * ξ.natDegree :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hpadcost) _
        _ = (i + 1) * (G + 2 * t * ξ.natDegree) := by ring

/-- **The top-corner filtration**: the `(t+1)`-coefficient of `(S t)^i` clears at `2t`,
**one better** than the generic `2(t+1) − 1` — the single-part convolution dies on the
truncation of `S t`, so every surviving term has two nonzero parts (or recurses on the
corner itself against the exponent-`0` seed). -/
theorem powTop_cleared {t G : ℕ}
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1) G) :
    ∀ i, Cleared ξ (coeff (t + 1) ((S QA (𝔞 v) t) ^ i)) (2 * t)
      (i * (G + 2 * t * ξ.natDegree)) := by
  intro i
  induction i with
  | zero =>
      rw [pow_zero]
      have h0 : coeff (t + 1) (1 : PowerSeries (Localization.Away ξ)) = 0 := by
        rw [PowerSeries.coeff_one, if_neg (by omega)]
      rw [h0]
      exact Cleared.zero _ _
  | succ i ih =>
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
      rcases Nat.lt_or_ge t p.1 with hp1 | hp1
      · -- the single-part corner dies on the truncation
        have hzero : coeff p.1 (S QA (𝔞 v) t) = 0 := coeff_S_eq_zero_of_lt QA (𝔞 v) hp1
        rw [hzero, zero_mul]
        exact Cleared.zero _ _
      · have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
          (coeff_γ_eq_S QA (𝔞 v) hp1).symm
        rw [hSγ]
        rcases Nat.lt_or_ge t p.2 with hp2 | hp2
        · -- the seed-corner: `p.1 = 0`, recurse on the top coefficient
          have hp10 : p.1 = 0 := by omega
          have hp2eq : p.2 = t + 1 := by omega
          rw [hp10, hp2eq]
          have hterm := (hγ 0 (Nat.zero_le t)).mul ih
          have hexp : (2 * 0 - 1) + 2 * t = 2 * t := by omega
          rw [hexp] at hterm
          refine hterm.mono ?_
          calc G + i * (G + 2 * t * ξ.natDegree)
              ≤ (G + 2 * t * ξ.natDegree) + i * (G + 2 * t * ξ.natDegree) :=
                Nat.add_le_add_right (Nat.le_add_right _ _) _
            _ = (i + 1) * (G + 2 * t * ξ.natDegree) := by ring
        · -- two nonzero parts: exponent `2(t+1) − 2 = 2t` exactly
          have hterm := (hγ p.1 hp1).mul (pow_cleared ξ QA v hγ i p.2 hp2)
          have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) ≤ 2 * t := by omega
          refine hterm.padTo hexp ?_
          have hpadcost : (2 * t - ((2 * p.1 - 1) + (2 * p.2 - 1))) ≤ 2 * t := by omega
          calc G + i * (G + 2 * t * ξ.natDegree)
                + (2 * t - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
              ≤ G + i * (G + 2 * t * ξ.natDegree) + 2 * t * ξ.natDegree :=
                Nat.add_le_add_left (Nat.mul_le_mul_right _ hpadcost) _
            _ = (i + 1) * (G + 2 * t * ξ.natDegree) := by ring

/-! ## The main filtration -/

/-- **THE CLEARED NEWTON FILTRATION** (the elementary `(A.4)`): over `Localization.Away ξ̄`,
with polynomial data of degree ≤ `DZ`, seed `v`, and derivative response `𝔞 ξ̄`, every Newton
coefficient clears at exponent `2t − 1` with the explicit quadratic budget. -/
theorem gamma_cleared {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) :
    ∀ t, Cleared ξ (coeff t (γ QA (𝔞 v))) (2 * t - 1)
      (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero =>
        have h0 : coeff 0 (γ QA (𝔞 v)) = 𝔞 v := by
          rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_γ]
        rw [h0]
        have := Cleared.of_algebraMap (ξ := ξ) v
        simpa [clearedBudget] using this
    | succ t =>
        have hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1)
            (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t) :=
          fun j hj => (ih j (by omega)).mono
            (clearedBudget_mono QA.natDegree v.natDegree DZ ξ.natDegree hj)
        -- the inner sum clears at `2t` with budget `DZ + d·X + 2t·dξ`
        have hsum : Cleared ξ (coeff (t + 1) (Polynomial.eval (S QA (𝔞 v) t) QA)) (2 * t)
            (DZ + QA.natDegree * (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t
              + 2 * t * ξ.natDegree) + 2 * t * ξ.natDegree) := by
          rw [coeff_eval_eq_sum_range]
          apply Cleared.sum
          intro i hi
          have hile : i ≤ QA.natDegree := by
            have := Finset.mem_range.mp hi
            omega
          rw [PowerSeries.coeff_mul]
          apply Cleared.sum
          intro p hp
          have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
          obtain ⟨q, hqdeg, hqmap⟩ := hQdeg i p.1
          have hcoeffQ : Cleared ξ (coeff p.1 (QA.coeff i)) 0 DZ := by
            rw [← hqmap]
            exact (Cleared.of_algebraMap q).mono hqdeg
          rcases Nat.lt_or_ge t p.2 with hp2 | hp2
          · -- top corner `p.2 = t + 1`
            have hp2eq : p.2 = t + 1 := by omega
            rw [hp2eq]
            have hterm := hcoeffQ.mul (powTop_cleared ξ QA v hγ i)
            have hexp : 0 + 2 * t = 2 * t := by omega
            rw [hexp] at hterm
            refine hterm.mono ?_
            have hiX : i * (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t
                + 2 * t * ξ.natDegree)
              ≤ QA.natDegree * (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t
                + 2 * t * ξ.natDegree) := Nat.mul_le_mul_right _ hile
            omega
          · -- generic coefficient `p.2 ≤ t`
            have hterm := hcoeffQ.mul (pow_cleared ξ QA v hγ i p.2 hp2)
            have hexp : 0 + (2 * p.2 - 1) ≤ 2 * t := by omega
            refine hterm.padTo hexp ?_
            have hiX : i * (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t
                + 2 * t * ξ.natDegree)
              ≤ QA.natDegree * (clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t
                + 2 * t * ξ.natDegree) := Nat.mul_le_mul_right _ hile
            have hpadcost : (2 * t - (0 + (2 * p.2 - 1))) ≤ 2 * t := by omega
            have hcost : (2 * t - (0 + (2 * p.2 - 1))) * ξ.natDegree
                ≤ 2 * t * ξ.natDegree := Nat.mul_le_mul_right _ hpadcost
            omega
        -- the recursion step spends the unit
        have hrec := coeff_γ_succ_eq QA (𝔞 v) t
        rw [hresp] at hrec
        rw [hrec, neg_mul]
        have hfinal := (hsum.inverse_xi_mul).neg
        have he : 2 * t + 1 = 2 * (t + 1) - 1 := by omega
        rw [he] at hfinal
        refine hfinal.mono ?_
        rw [clearedBudget]
        exact le_max_right _ _

/-! ## The witness pack and the counting exit -/

/-- **The numerator witness pack** for per-place counting: an explicit polynomial numerator
of explicitly bounded degree, with the unit-cancellation exit bundled. -/
theorem exists_numerator {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) (t : ℕ) :
    ∃ N : Polynomial F,
      N.natDegree ≤ clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t ∧
      𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v)) ∧
      (N = 0 → coeff t (γ QA (𝔞 v)) = 0) := by
  obtain ⟨N, hdeg, hmap⟩ := gamma_cleared ξ QA v hQdeg hresp t
  exact ⟨N, hdeg, hmap, fun h0 => eq_zero_of_cleared_witness ξ hmap h0⟩

/-- **The counting exit** ([BCIKS20] Claim 5.8 middle window, elementarily): if every
admissible numerator vanishes at more places than the budget, the Newton coefficient is
zero. -/
theorem coeff_gamma_eq_zero_of_eval_vanish {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t < M.card)
    (hvan : ∀ N : Polynomial F,
      N.natDegree ≤ clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t →
      𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v)) →
      ∀ z ∈ M, N.eval z = 0) :
    coeff t (γ QA (𝔞 v)) = 0 := by
  classical
  obtain ⟨N, hdeg, hmap, hexit⟩ := exists_numerator ξ QA v hQdeg hresp t
  refine hexit ?_
  by_contra hN0
  have hroots : M.card ≤ N.natDegree := by
    have hsub : M ⊆ N.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hN0]
      exact hvan N hdeg hmap z hz
    calc M.card ≤ N.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card N.roots := N.roots.toFinset_card_le
      _ ≤ N.natDegree := N.card_roots'
  omega

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.isUnit_xi
#print axioms ArkLib.SectionNewtonCleared.Cleared.inverse_xi_mul
#print axioms ArkLib.SectionNewtonCleared.eq_zero_of_cleared_witness
#print axioms ArkLib.SectionNewtonCleared.clearedBudget_mono
#print axioms ArkLib.SectionNewtonCleared.pow_cleared
#print axioms ArkLib.SectionNewtonCleared.powTop_cleared
#print axioms ArkLib.SectionNewtonCleared.gamma_cleared
#print axioms ArkLib.SectionNewtonCleared.exists_numerator
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_eval_vanish
