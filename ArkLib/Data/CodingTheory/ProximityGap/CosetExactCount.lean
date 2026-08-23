/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Vieta
import ArkLib.Data.CodingTheory.ProximityGap.CosetRigidity

/-!
# Exact count: vanishing-statistic `h`-subsets of `μ_n` are exactly the `n/h` cosets (Issue #232)

Completes the rigidity arc of `CosetRigidity.lean` to an EXACT COUNT (Direction 3). The
vanishing-statistic `h`-subsets of `μ_n` (those `S` with `e_1(S)=...=e_{h-1}(S)=0`) are EXACTLY the
`n/h` cosets of `μ_h`, indexed by their common value `c = x^h ∈ μ_{n/h}` (image of the `h`-th power
map). This makes the coset lower bound `C(n/h,1)=n/h` of `exists_many_vanishing_powersum_subsets`
(at `m=1`) an EQUALITY at agreement level `a=h`, pinning why the coset method cannot push past the
subgroup order. All results sorry-free, axiom-clean.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F]

theorem exists_pow_eq_of_mem {ζ : F} {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    (hζ : IsPrimitiveRoot ζ n) {c : F} (hc : c ^ (n / h) = 1) :
    ∃ x : F, x ^ n = 1 ∧ x ^ h = c := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  have hnh : 0 < n / h := Nat.div_pos (Nat.le_of_dvd hn hdvd) hh
  have hζh : IsPrimitiveRoot (ζ ^ h) (n / h) :=
    IsPrimitiveRoot.pow hn hζ (by rw [Nat.mul_div_cancel' hdvd])
  haveI : NeZero (n / h) := ⟨hnh.ne'⟩
  obtain ⟨i, _, hi⟩ := hζh.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [← pow_mul, mul_comm i h, pow_mul, hi]

variable [DecidableEq F]

noncomputable def fiber (n h : ℕ) (c : F) : Finset F :=
  (nthRootsFinset n (1 : F)).filter (fun x => x ^ h = c)

@[simp] theorem mem_fiber {n h : ℕ} (hn : 0 < n) {c x : F} :
    x ∈ fiber n h c ↔ x ^ n = 1 ∧ x ^ h = c := by
  rw [fiber, Finset.mem_filter, mem_nthRootsFinset hn]

theorem fiber_card_eq {ζ : F} {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n) (hζ : IsPrimitiveRoot ζ n)
    {c g : F} (hgn : g ^ n = 1) (hgc : g ^ h = c) :
    (fiber n h c).card = h := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  have hg0 : g ≠ 0 := by intro h0; rw [h0, zero_pow hn.ne'] at hgn; exact one_ne_zero hgn.symm
  have hηprim : IsPrimitiveRoot (ζ ^ (n / h)) h :=
    IsPrimitiveRoot.pow hn hζ (by rw [Nat.div_mul_cancel hdvd])
  have hcardμh : (nthRootsFinset h (1 : F)).card = h := hηprim.card_nthRootsFinset
  have hbij : (fiber n h c).card = (nthRootsFinset h (1 : F)).card := by
    apply Finset.card_bij' (fun x _ => x / g) (fun y _ => g * y)
    · intro x hx
      rw [mem_fiber hn] at hx
      rw [mem_nthRootsFinset hh, div_pow, hx.2, ← hgc, div_self (pow_ne_zero h hg0)]
    · intro y hy
      rw [mem_nthRootsFinset hh] at hy
      have hyn : y ^ n = 1 := by
        conv_lhs => rw [← Nat.div_mul_cancel hdvd, mul_comm, pow_mul, hy, one_pow]
      rw [mem_fiber hn]
      exact ⟨by rw [mul_pow, hgn, hyn, mul_one], by rw [mul_pow, hgc, hy, mul_one]⟩
    · intro x _; field_simp
    · intro y hy
      rw [mem_nthRootsFinset hh] at hy
      field_simp
  rw [hbij, hcardμh]

theorem prod_X_sub_C_eq_X_pow_sub_C {S : Finset F} {h : ℕ} (hh : 0 < h) (hcard : S.card = h)
    {c : F} (hpow : ∀ x ∈ S, x ^ h = c) :
    (S.val.map (fun t => X - C t)).prod = X ^ h - C c := by
  set P : F[X] := (S.val.map (fun t => X - C t)).prod with hP
  have hPmonic : P.Monic := monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hPdeg : P.natDegree = h := by
    rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]; simpa using hcard
  have hQmonic : (X ^ h - C c : F[X]).Monic := monic_X_pow_sub_C c hh.ne'
  have hQdeg : (X ^ h - C c : F[X]).natDegree = h := natDegree_X_pow_sub_C
  have hQ0 : (X ^ h - C c : F[X]) ≠ 0 := hQmonic.ne_zero
  have hval : S.val ≤ (X ^ h - C c : F[X]).roots := by
    rw [Finset.val_le_iff_val_subset]
    intro x hx
    rw [Polynomial.mem_roots hQ0]
    show (X ^ h - C c : F[X]).eval x = 0
    simp [hpow x hx]
  have hdvd : P ∣ (X ^ h - C c : F[X]) := by
    rw [hP, Multiset.prod_X_sub_C_dvd_iff_le_roots hQ0]; exact hval
  have heq := eq_of_monic_of_dvd_of_natDegree_le hPmonic hQmonic hdvd (by rw [hPdeg, hQdeg])
  rw [hP]; exact heq.symm

theorem esymm_zero_of_pow_eq {S : Finset F} {h : ℕ} (hh : 0 < h) (hcard : S.card = h)
    {c : F} (hpow : ∀ x ∈ S, x ^ h = c) :
    ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0 := by
  have hid := prod_X_sub_C_eq_X_pow_sub_C hh hcard hpow
  intro j hj1 hjh
  have hcs : Multiset.card S.val = h := by simpa using hcard
  set k := h - j with hk
  have hk1 : 1 ≤ k := by omega
  have hkc : k ≤ Multiset.card S.val := by rw [hcs]; omega
  have hcoeff := Multiset.prod_X_sub_C_coeff S.val (k := k) hkc
  rw [hid] at hcoeff
  have hlhs : (X ^ h - C c : F[X]).coeff k = 0 := by
    rw [coeff_sub, coeff_X_pow, coeff_C,
      if_neg (by omega : ¬ k = h), if_neg (by omega : ¬ k = 0), sub_zero]
  rw [hlhs, hcs] at hcoeff
  have hjk : h - k = j := by omega
  rw [hjk] at hcoeff
  have hunit : ((-1 : F) ^ j) ≠ 0 := pow_ne_zero j (neg_ne_zero.2 one_ne_zero)
  rcases mul_eq_zero.1 hcoeff.symm with h1 | h2
  · exact absurd h1 hunit
  · exact h2



open scoped Classical in
noncomputable def vanishingEsymmSubsets (n h : ℕ) : Finset (Finset F) :=
  ((nthRootsFinset n (1 : F)).powersetCard h).filter
    (fun S => ∀ j ∈ Finset.Icc 1 (h - 1), S.val.esymm j = 0)

theorem mem_vanishingEsymmSubsets {n h : ℕ} {S : Finset F} :
    S ∈ vanishingEsymmSubsets n h ↔
      (S ⊆ nthRootsFinset n (1 : F) ∧ S.card = h) ∧
        ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0 := by
  simp only [vanishingEsymmSubsets, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, fun j hj1 hj2 => h3 j ⟨hj1, hj2⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, fun j hj => h3 j hj.1 hj.2⟩

theorem fiber_mem_vanishingEsymmSubsets {ζ : F} {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    (hζ : IsPrimitiveRoot ζ n) {c : F} (hc : c ^ (n / h) = 1) :
    fiber n h c ∈ vanishingEsymmSubsets n h := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  obtain ⟨g, hgn, hgc⟩ := exists_pow_eq_of_mem hn hdvd hζ hc
  have hcard : (fiber n h c).card = h := fiber_card_eq hn hdvd hζ hgn hgc
  have hpow : ∀ x ∈ fiber n h c, x ^ h = c := fun x hx => ((mem_fiber hn).1 hx).2
  rw [mem_vanishingEsymmSubsets]
  refine ⟨⟨fun x hx => ?_, hcard⟩, esymm_zero_of_pow_eq hh hcard hpow⟩
  rw [mem_nthRootsFinset hn]; exact ((mem_fiber hn).1 hx).1

/-- **EXACT COUNT (Issue #232, Direction 3).** For a primitive `n`-th root of unity `ζ ∈ F` and
`h ∣ n`, `0 < h`, the number of `h`-element subsets `S ⊆ μ_n` with `e_1(S)=...=e_{h-1}(S)=0` is
EXACTLY `n / h`. (Bijection `c ↦ fiber c` between `μ_{n/h}` and these subsets.) -/
theorem card_vanishingEsymm_subsets_eq {ζ : F} {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hdvd : h ∣ n)
    (hζ : IsPrimitiveRoot ζ n) :
    (vanishingEsymmSubsets n h : Finset (Finset F)).card = n / h := by
  have hnh : 0 < n / h := Nat.div_pos (Nat.le_of_dvd hn hdvd) hh
  have hζh : IsPrimitiveRoot (ζ ^ h) (n / h) :=
    IsPrimitiveRoot.pow hn hζ (by rw [Nat.mul_div_cancel' hdvd])
  rw [← hζh.card_nthRootsFinset]
  symm
  apply Finset.card_nbij (i := fun c => fiber n h c)
  · intro c hc
    rw [Finset.mem_coe, mem_nthRootsFinset hnh] at hc
    exact Finset.mem_coe.2 (fiber_mem_vanishingEsymmSubsets hn hdvd hζ hc)
  · intro c hc c' hc' heq
    rw [Finset.mem_coe, mem_nthRootsFinset hnh] at hc hc'
    obtain ⟨g, hgn, hgc⟩ := exists_pow_eq_of_mem hn hdvd hζ hc
    have hne : (fiber n h c).Nonempty := by
      rw [← Finset.card_pos, fiber_card_eq hn hdvd hζ hgn hgc]; exact hh
    obtain ⟨x, hx⟩ := hne
    simp only [] at heq
    have hxc : x ^ h = c := ((mem_fiber hn).1 hx).2
    have hx' : x ∈ fiber n h c' := heq ▸ hx
    have hxc' : x ^ h = c' := ((mem_fiber hn).1 hx').2
    rw [← hxc, ← hxc']
  · intro S hS
    rw [Finset.mem_coe, mem_vanishingEsymmSubsets] at hS
    obtain ⟨⟨hSsub, hScard⟩, hSesymm⟩ := hS
    obtain ⟨c, hc⟩ := all_pow_eq_of_esymm_zero hh hScard hSesymm
    have hSne : S.Nonempty := by rw [← Finset.card_pos, hScard]; exact hh
    obtain ⟨x₀, hx₀⟩ := hSne
    have hx₀n : x₀ ^ n = 1 := (mem_nthRootsFinset hn (1:F)).1 (hSsub hx₀)
    have hcμ : c ^ (n / h) = 1 := by
      rw [← hc x₀ hx₀, ← pow_mul, Nat.mul_div_cancel' hdvd, hx₀n]
    refine ⟨c, Finset.mem_coe.2 ((mem_nthRootsFinset hnh (1:F)).2 hcμ), ?_⟩
    have hSsubF : S ⊆ fiber n h c := by
      intro x hx
      rw [mem_fiber hn]
      exact ⟨(mem_nthRootsFinset hn (1:F)).1 (hSsub hx), hc x hx⟩
    obtain ⟨g, hgn, hgc⟩ := exists_pow_eq_of_mem hn hdvd hζ hcμ
    have hFcard : (fiber n h c).card = h := fiber_card_eq hn hdvd hζ hgn hgc
    exact (Finset.eq_of_subset_of_card_le hSsubF (by rw [hFcard, hScard])).symm

end ArkLib.ProximityGap.Rigidity

#print axioms ArkLib.ProximityGap.Rigidity.card_vanishingEsymm_subsets_eq
