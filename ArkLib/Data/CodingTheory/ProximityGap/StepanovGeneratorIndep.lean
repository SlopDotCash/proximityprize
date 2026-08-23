/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SparseMultiplicity

/-!
# Stepanov generator independence (#389): Shkredov–Vyugin Lemma 3.1, clean route

The non-vanishing of the Garcia–Voloch / Heath-Brown–Konyagin Stepanov auxiliary polynomial (the
named `GVRepBound` input, in the genuine `n ∣ p − 1` split case) is the linear independence of the
generator family `X^{e_j} · (X − α)^{t·β}`.  Shkredov–Vyugin (*On additive shifts of multiplicative
subgroups*, Lemma 3.1) prove it through an `l × l` Wronskian with a bracket induction and the hard
`W = 0 ⟹ dependent` converse (needs a strong characteristic bound, via Cramer's rule).

This file gives a **shorter, self-contained route** that needs neither:

* `eq_zero_of_sum_pow_block` — grouping the generators by their `(X − α)`-power `β` writes a
  dependence as `∑_β (X − α)^{t·β} P_β = 0` with each `P_β` a sparse polynomial in `X`; since each
  nonzero `P_β` vanishes to order `< t` at `α`, the block valuations `tβ + ord_α P_β` lie in
  disjoint length-`t` intervals and the lowest nonzero block cannot cancel.
* `rootMultiplicity_sparse_lt` (`SparseMultiplicity.lean`) — supplies the `ord_α P_β < t` input:
  a sparse polynomial cannot over-vanish.
* `stepanov_generators_linearIndependent` — the assembled statement.

The only hypothesis is the distinctness of the `x`-exponents over `R` (nonzero Vandermonde, e.g.
`char = 0` or `char > max e`) and `n ≤ t` — exactly the Shkredov–Vyugin regime `p ≥ tB`.
-/

open Polynomial Finset Matrix

namespace ArkLib.ProximityGap.Wronskian

variable {R : Type*} [Field R] {n : ℕ}

/-- **Disjoint valuation blocks**: if `∑_β (X−α)^{t·β} P_β = 0` and every nonzero `P_β` vanishes
to order `< t` at `α`, then every `P_β = 0`.  The `(X−α)`-valuation of block `β` lies in
`[tβ, t(β+1))`; these blocks are disjoint, so the lowest nonzero block cannot be cancelled. -/
theorem eq_zero_of_sum_pow_block (α : R) (t : ℕ) (P : Fin n → R[X])
    (hlt : ∀ β, P β ≠ 0 → rootMultiplicity α (P β) < t)
    (hsum : ∑ β : Fin n, (X - C α) ^ (t * (β:ℕ)) * P β = 0) : ∀ β, P β = 0 := by
  classical
  by_contra hcon
  obtain ⟨β', hβ'⟩ := not_forall.mp hcon
  set f : Fin n → R[X] := fun β => (X - C α) ^ (t * (β:ℕ)) * P β with hf
  set S : Finset (Fin n) := Finset.univ.filter (fun β => P β ≠ 0) with hS
  have hSne : S.Nonempty := ⟨β', by rw [hS]; simp [hβ']⟩
  set β₀ := S.min' hSne with hβ₀
  have hβ₀mem : β₀ ∈ S := S.min'_mem hSne
  have hP0 : P β₀ ≠ 0 := by rw [hS, Finset.mem_filter] at hβ₀mem; exact hβ₀mem.2
  have hXne : (X - C α : R[X]) ≠ 0 := X_sub_C_ne_zero α
  set e₀ := t * (β₀:ℕ) + t with he₀
  have hsplit : f β₀ = - ∑ β ∈ Finset.univ.erase β₀, f β := by
    have h := Finset.add_sum_erase Finset.univ f (Finset.mem_univ β₀)
    rw [hsum] at h
    exact eq_neg_of_add_eq_zero_left h
  have hdvderase : (X - C α) ^ e₀ ∣ ∑ β ∈ Finset.univ.erase β₀, f β := by
    refine Finset.dvd_sum (fun β hβ => ?_)
    have hne : β ≠ β₀ := (Finset.mem_erase.mp hβ).1
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · have hnotS : β ∉ S := fun hmem => by
        have := S.min'_le β hmem; rw [← hβ₀] at this
        exact absurd (lt_of_lt_of_le hlt' this) (lt_irrefl _)
      have hPβ : P β = 0 := by by_contra hPβ; exact hnotS (by rw [hS]; simp [hPβ])
      rw [hf]; simp [hPβ]
    · have hexp : e₀ ≤ t * (β:ℕ) := by
        have hb : (β₀:ℕ) + 1 ≤ (β:ℕ) := hgt'
        calc e₀ = t * ((β₀:ℕ) + 1) := by rw [he₀]; ring
          _ ≤ t * (β:ℕ) := Nat.mul_le_mul_left t hb
      rw [hf]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hexp) _
  have hdvdf0 : (X - C α) ^ e₀ ∣ f β₀ := by rw [hsplit]; exact (dvd_neg).mpr hdvderase
  have hcancel : (X - C α) ^ t ∣ P β₀ := by
    rw [hf, he₀, pow_add] at hdvdf0
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hXne)).mp hdvdf0
  have hge : t ≤ rootMultiplicity α (P β₀) := (le_rootMultiplicity_iff hP0).mpr hcancel
  exact absurd hge (not_le.mpr (hlt β₀ hP0))

/-- A combination of monomials with **distinct exponents** that vanishes has zero coefficients. -/
theorem eq_zero_of_sum_monomial_eq_zero {e : Fin n → ℕ} (he : Function.Injective e)
    {c : Fin n → R} (h : ∑ j, C (c j) * X ^ (e j) = 0) : c = 0 := by
  funext j
  have hco := congrArg (fun p : R[X] => p.coeff (e j)) h
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hco
  rw [Finset.sum_eq_single j] at hco
  · simpa using hco
  · intro j' _ hj'
    rw [if_neg (fun heq => hj' (he heq.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Stepanov generator independence (Shkredov–Vyugin Lemma 3.1, clean form)**: for distinct
`x`-exponents `e` (nonzero Vandermonde over `R`, e.g. `char = 0` or `char > max e`) with
`n ≤ t` and `α ≠ 0`, the family `X^{e_j} · (X − α)^{t·β}` (`j < n`, `β < B`) is linearly
independent.  This is the non-vanishing of the Garcia–Voloch / Heath-Brown–Konyagin Stepanov
auxiliary in the genuine `n ∣ p − 1` split case — proved here via the sparse-multiplicity bound
and the disjoint-valuation-block lemma, with **no** bracket induction or `W = 0 ⟹ dependent`
converse. -/
theorem stepanov_generators_linearIndependent (e : Fin n → ℕ) (α : R) (t B : ℕ)
    (hα : α ≠ 0) (hvand : (Matrix.vandermonde (fun j => (e j : R))).det ≠ 0) (hn : n ≤ t) :
    LinearIndependent R (fun (p : Fin B × Fin n) =>
      (X - C α) ^ (t * (p.1:ℕ)) * X ^ (e p.2)) := by
  classical
  have heinj : Function.Injective e := by
    have := Matrix.det_vandermonde_ne_zero_iff.mp hvand
    intro j j' hjj'; exact this (by rw [hjj'] : (e j : R) = (e j'))
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- regroup the vanishing combination by the `(X−α)`-power `β`
  have hrg : ∑ β : Fin B, (X - C α) ^ (t * (β:ℕ)) * (∑ j : Fin n, C (c (β, j)) * X ^ (e j)) = 0 := by
    rw [← hc, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_eq_C_mul]; ring
  -- each block has too low a multiplicity to survive, so it is zero
  have hPzero := eq_zero_of_sum_pow_block α t
    (fun β => ∑ j : Fin n, C (c (β, j)) * X ^ (e j))
    (fun β hPβ => lt_of_lt_of_le
      (rootMultiplicity_sparse_lt e (fun j => c (β, j)) α hα hvand hPβ) hn) hrg
  -- distinct exponents ⟹ all coefficients vanish
  intro p
  have := eq_zero_of_sum_monomial_eq_zero heinj (c := fun j => c (p.1, j)) (hPzero p.1)
  exact congrFun this p.2

end ArkLib.ProximityGap.Wronskian
