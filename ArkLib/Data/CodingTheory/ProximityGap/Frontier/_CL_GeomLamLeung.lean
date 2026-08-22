/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0c_BesselMfoldSymbolic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_LamLeungTwoPowerAntipodalBalan
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvRem_BesselMfold

/-!
# GEOMETRIC closure of STEP-1: μ_n's antipodal directions ARE a HeadDecoupled negPair family

This file discharges the ONE remaining char-0 geometric hypothesis of
`Step1Bessel.bessel_identity_on_energy`: that the `m = n/2` distinct antipodal directions
`{±w_j}` of `μ_n` (`n = 2^μ`) form a `HeadDecoupled` list each with per-direction zero-sum
count `Znp` (the `{1,−1}` central-binomial count).

The closure rests on the in-tree, axiom-clean char-0 Lam–Leung structure theorem
`LamLeungTwoPowerAntipodalBalance.antipodal_balance_root`: a zero-sum tuple of `2^k`-th roots
of unity has, for EVERY value `w`, equally many entries `= w` as `= −w`. From this:

* **`additivelyDecoupled_of_antipodal`** — for two distinct antipodal directions `{±w}`, `{±w'}`
  of roots of unity (`w² ≠ w'²`, `w,w' ≠ 0`), the `separates` field follows DIRECTLY: in any
  zero-sum tuple landing in `{±w} ∪ {±w'}`, the `#(=w)=#(=−w)` balance makes the `{±w}`-block
  sum `w·(#(=w) − #(=−w)) = 0`, and likewise the `{±w'}`-block. No cyclotomic-field linear
  independence beyond the multiset engine is needed.
* **`zeroSumCount_antipodalDir`** — `zeroSumCount {w,−w} = Znp` for `w ≠ 0`, via the scaling
  bijection `c ↦ w·c` from `{1,−1}`-tuples (it is a relabeling, so the count is `Znp`).
* **`headDecoupled_antipodalList`** — assembling the whole list of `m` antipodally-distinct
  directions of `2^k`-roots into a `HeadDecoupled` family.
* **`bessel_identity_muN`** — the composition over an abstract antipodally-distinct root list:
  `E_r^{char0}(union of m antipodal dirs) = Edef r m` unconditionally (char-0).
* **`antipodalDistinct_halfBasis` / `bessel_identity_halfBasis`** — the CONCRETE instantiation for
  the actual prize subgroup `μ_n` (`n = 2^{μ'+1}`): the half-basis `[ζ^0, …, ζ^{2^{μ'}-1}]` of a
  primitive `2^{μ'+1}`-th root is antipodally distinct, so
  `E_r^{char0}(⋃_j {±ζ^j}) = Edef r (2^{μ'})` with NO geometric hypothesis remaining. The full
  char-0 STEP-1 closure on the genuine roots-of-unity energy.

Char-0 ONLY. Does NOT touch the char-`p` excess `W_r` (the open kernel = the prize wall, which a
finite-order method provably cannot cross). Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.NegationClosedWalk (zeroSumCount)
open ArkLib.ProximityGap.Frontier.AvRem (AdditivelyDecoupled)
open ArkLib.ProximityGap.Frontier.Step1Bessel
open ArkLib.ProximityGap.Frontier.AvUC (negPair)

namespace ArkLib.ProximityGap.Frontier.LamLeungGeometric

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- The antipodal direction `{w, −w}` as a `Finset`. -/
def antipodalDir (w : L) : Finset L := {w, -w}

theorem mem_antipodalDir {w x : L} : x ∈ antipodalDir w ↔ x = w ∨ x = -w := by
  unfold antipodalDir; simp [Finset.mem_insert]

/-- For `w ≠ 0`, `{w, −w}` is a genuine 2-element set (`w ≠ −w` since char ≠ 2). -/
theorem antipodalDir_card {w : L} (hw : w ≠ 0) : (antipodalDir w).card = 2 := by
  unfold antipodalDir
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro h
  -- w = -w ⟹ 2w = 0 ⟹ w = 0 (char ≠ 2)
  have : (2 : L) * w = 0 := by rw [two_mul]; linear_combination h
  rcases mul_eq_zero.mp this with h2 | hw0
  · exact absurd h2 (by norm_num)
  · exact hw hw0

/-! ## The scaling bijection: `zeroSumCount {w,−w} = Znp`. -/

/-- `{1,−1}` over a char-0 field `L` as a `Finset` — the local `negPair`. -/
def negPairL : Finset L := {1, -1}

theorem mem_negPairL {x : L} : x ∈ negPairL ↔ x = 1 ∨ x = -1 := by
  unfold negPairL; simp [Finset.mem_insert]

theorem antipodalDir_one : (antipodalDir (1 : L)) = negPairL := by
  unfold antipodalDir negPairL; norm_num

/-- **Scaling bijection.** Over `L`, the zero-sum count of `{w,−w}` (`w ≠ 0`) equals that of
`{1,−1}` at every length, via `c ↦ w⁻¹·c`. -/
theorem zeroSumCount_antipodalDir_eq_negPairL {w : L} (hw : w ≠ 0) (a : ℕ) :
    zeroSumCount (antipodalDir w) a = zeroSumCount (negPairL : Finset L) a := by
  classical
  unfold zeroSumCount
  apply Finset.card_bij'
    (i := fun (c : Fin a → L) (_ : c ∈ _) => fun j => w⁻¹ * c j)
    (j := fun (c : Fin a → L) (_ : c ∈ _) => fun j => w * c j)
  · intro c hc
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
    obtain ⟨hmem, hsum⟩ := hc
    refine ⟨fun j => ?_, ?_⟩
    · have := hmem j
      rw [mem_antipodalDir] at this
      rw [mem_negPairL]
      rcases this with h | h
      · left; rw [h]; field_simp
      · right; rw [h]; field_simp
    · rw [← Finset.mul_sum, hsum, mul_zero]
  · intro c hc
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
    obtain ⟨hmem, hsum⟩ := hc
    refine ⟨fun j => ?_, ?_⟩
    · have := hmem j
      rw [mem_negPairL] at this
      rw [mem_antipodalDir]
      rcases this with h | h
      · left; rw [h, mul_one]
      · right; rw [h]; ring
    · rw [← Finset.mul_sum, hsum, mul_zero]
  · intro c hc
    funext j; field_simp
  · intro c hc
    funext j; field_simp

/-- **`negPairL` central-binomial count over `L`.** Ported from the in-tree ℚ proof
`zeroSum_negPair_eq_centralBinom`; uses only `(1:L) ≠ −1` and char-0 cast injectivity. -/
theorem zeroSumCount_negPairL_eq_centralBinom (r : ℕ) :
    zeroSumCount (negPairL : Finset L) (2 * r) = Nat.centralBinom r := by
  classical
  unfold zeroSumCount
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hone : (1 : L) ≠ -1 := by
    intro h
    have : (2 : L) = 0 := by linear_combination h
    exact absurd this (by norm_num)
  have hcarduniv : ((2 * r).choose r)
      = (Finset.powersetCard r (Finset.univ : Finset (Fin (2 * r)))).card := by
    rw [Finset.card_powersetCard]; simp
  rw [hcarduniv]
  refine Finset.card_nbij'
    (fun c => (Finset.univ.filter (fun i => c i = (1 : L))))
    (fun S => (fun i => if i ∈ S then (1 : L) else -1))
    ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hmem, hsum⟩ := hc
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    set P := Finset.univ.filter (fun i => c i = (1:L)) with hP
    set Nn := Finset.univ.filter (fun i => c i = (-1:L)) with hN
    have hsplit : P.card + Nn.card = 2 * r := by
      have hdj : Disjoint P Nn := by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; rw [h1] at h2; exact hone h2
      have hunion : P ∪ Nn = Finset.univ := by
        apply Finset.eq_univ_of_forall; intro i
        rcases mem_negPairL.mp (hmem i) with h1 | h1
        · exact Finset.mem_union_left _ (by rw [hP]; simp [h1])
        · exact Finset.mem_union_right _ (by rw [hN]; simp [h1])
      have := Finset.card_union_of_disjoint hdj
      rw [hunion] at this
      simp only [Finset.card_univ, Fintype.card_fin] at this; omega
    have hsum2 : (P.card : L) - (Nn.card : L) = 0 := by
      rw [← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = (1:L)) c]
      have hpart1 : ∑ i ∈ P, c i = (P.card : L) := by
        rw [hP, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]; simp
      have hpart2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i = (1:L)), c i = -(Nn.card : L) := by
        rw [hN]
        have hcongr : Finset.univ.filter (fun i => ¬ c i = (1:L))
            = Finset.univ.filter (fun i => c i = (-1:L)) := by
          apply Finset.filter_congr; intro i _
          rcases mem_negPairL.mp (hmem i) with h1 | h1 <;> rw [h1]
          · simp [hone]
          · constructor
            · intro _; rfl
            · intro _ h; exact hone h.symm
        rw [hcongr, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]; simp
      rw [hpart1, hpart2]; ring
    have heq2 : (P.card : L) = (Nn.card : L) := sub_eq_zero.mp hsum2
    have hPN : P.card = Nn.card := by exact_mod_cast heq2
    omega
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    obtain ⟨_, hScard⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · intro i; by_cases h : i ∈ S <;> simp [h, mem_negPairL]
    · have hsub : S ⊆ (Finset.univ : Finset (Fin (2*r))) := Finset.subset_univ S
      have hval : ∑ i, (if i ∈ S then (1 : L) else -1)
          = (S.card : L) - (((Finset.univ : Finset (Fin (2*r))) \ S).card : L) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        have hnot : (Finset.univ.filter (fun i => i ∉ S)) = (Finset.univ : Finset (Fin (2*r))) \ S := by
          ext i; simp [Finset.mem_sdiff]
        rw [hnot]
        simp only [nsmul_eq_mul, mul_one, mul_neg]; ring
      rw [hval, Finset.card_sdiff_of_subset hsub]
      have hcardu : (Finset.univ : Finset (Fin (2*r))).card = 2 * r := by simp
      rw [hcardu, hScard]
      have h2r : (2 * r - r : ℕ) = r := by omega
      rw [h2r]; push_cast; ring
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hmem, _⟩ := hc
    funext i
    have hmemf : (i ∈ Finset.univ.filter (fun j => c j = (1:L))) ↔ c i = 1 := by
      simp [Finset.mem_filter]
    simp only [hmemf]
    by_cases h : c i = (1:L)
    · rw [if_pos h, h]
    · rw [if_neg h]
      rcases mem_negPairL.mp (hmem i) with h1 | h1
      · exact absurd h1 h
      · rw [h1]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i ∈ S
    · simp [h]
    · rw [if_neg h]
      constructor
      · intro hcon; exact absurd hcon.symm hone
      · intro hcon; exact absurd hcon h

/-- **Per-direction count, closed form over `L`.** For `w ≠ 0` in a char-0 field, the zero-sum
count of the antipodal direction `{w, −w}` is `centralBinom (a/2)` for even `a`, `0` for odd `a`
— field-independent (it is the `{1,−1}` central-binomial count). -/
theorem zeroSumCount_antipodalDir_closed {w : L} (hw : w ≠ 0) (a : ℕ) :
    zeroSumCount (antipodalDir w) a
      = if a % 2 = 0 then Nat.centralBinom (a / 2) else 0 := by
  classical
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · have ha2 : a % 2 = 0 := by omega
    rw [if_pos ha2]
    have hak2 : a / 2 = k := by omega
    rw [hak2]
    have hak : a = 2 * k := by omega
    rw [hak, zeroSumCount_antipodalDir_eq_negPairL hw, zeroSumCount_negPairL_eq_centralBinom]
  · -- a odd: sum of an odd number of ±w is ±-combination = w·(#+ − #−); zero ⟹ #+=#− ⟹ a even, ⊥
    have haodd : a % 2 ≠ 0 := by omega
    rw [if_neg haodd]
    unfold zeroSumCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc hcsum
    simp only [Fintype.mem_piFinset] at hc
    set P := Finset.univ.filter (fun i => c i = w) with hP
    set Nn := Finset.univ.filter (fun i => c i = -w) with hN
    have hwne : (w : L) ≠ -w := by
      intro h
      have : (2 : L) * w = 0 := by rw [two_mul]; linear_combination h
      rcases mul_eq_zero.mp this with h2 | h0
      · exact absurd h2 (by norm_num)
      · exact hw h0
    have hdisj : Disjoint P Nn := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; exact hwne (h1 ▸ h2)
    have hunion : P ∪ Nn = Finset.univ := by
      apply Finset.eq_univ_of_forall; intro i
      rcases (mem_antipodalDir).mp (hc i) with h1 | h1
      · exact Finset.mem_union_left _ (by rw [hP]; simp [h1])
      · exact Finset.mem_union_right _ (by rw [hN]; simp [h1])
    have hsplit : P.card + Nn.card = a := by
      have := Finset.card_union_of_disjoint hdisj
      rw [hunion] at this
      simpa [Finset.card_univ, Fintype.card_fin] using this.symm
    have hsumval : ∑ i, c i = (P.card : L) * w - (Nn.card : L) * w := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = w) c]
      have hpart1 : ∑ i ∈ P, c i = (P.card : L) * w := by
        rw [hP, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        rw [Finset.sum_const, nsmul_eq_mul]
      have hpart2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i = w), c i = -((Nn.card : L) * w) := by
        have hcongr : Finset.univ.filter (fun i => ¬ c i = w)
            = Finset.univ.filter (fun i => c i = -w) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases (mem_antipodalDir).mp (hc i) with h1 | h1
          · rw [h1]; constructor
            · intro h; exact absurd rfl h
            · intro h; exact absurd h hwne
          · rw [h1]; constructor
            · intro _; rfl
            · intro _ h; exact hwne h.symm
        rw [hcongr, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        rw [Finset.sum_const, nsmul_eq_mul, hN]; ring
      rw [hpart1, hpart2]; ring
    have hsum0 : (P.card : L) * w - (Nn.card : L) * w = 0 := hsumval ▸ hcsum
    have heq : (P.card : L) = (Nn.card : L) := by
      have hfac : ((P.card : L) - (Nn.card : L)) * w = 0 := by
        rw [sub_mul]; exact hsum0
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw
    have heqn : P.card = Nn.card := by exact_mod_cast heq
    omega

/-- `Znp` form: `zeroSumCount {w,−w} = Znp` as `ℕ→ℕ` functions (for `w ≠ 0`). Field-independent:
both sides are the central-binomial count. -/
theorem zeroSumCount_antipodalDir_eq_Znp {w : L} (hw : w ≠ 0) :
    (fun a => zeroSumCount (antipodalDir w) a) = Znp := by
  funext a
  rw [zeroSumCount_antipodalDir_closed hw, Znp_closed]

/-! ## The decoupling: distinct antipodal directions of roots of unity decouple. -/

/-- The union of a list of antipodal directions consists of `2^k`-th roots of unity, provided
each generating `w` is. (Then `−w` is too, since `(−w)^{2^k} = w^{2^k}` for `k ≥ 1`.) -/
theorem mem_unionFold_root {k : ℕ} (hk : 1 ≤ k) (ws : List L)
    (hroot : ∀ w ∈ ws, w ^ (2 ^ k) = 1) :
    ∀ x ∈ unionFold (ws.map antipodalDir), x ^ (2 ^ k) = 1 := by
  intro x hx
  induction ws with
  | nil => simp [unionFold] at hx
  | cons w ws ih =>
      simp only [List.map_cons, unionFold, Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [mem_antipodalDir] at hx
        rcases hx with h | h
        · rw [h]; exact hroot w (List.mem_cons_self ..)
        · rw [h]
          have : (-w) ^ (2 ^ k) = w ^ (2 ^ k) := by
            rw [neg_pow]
            have : Even (2 ^ k) := by
              have : 2 ^ k = 2 * 2 ^ (k - 1) := by
                rw [← pow_succ']; congr 1; omega
              rw [this]; exact even_two_mul _
            rw [Even.neg_one_pow this, one_mul]
          rw [this]; exact hroot w (List.mem_cons_self ..)
      · exact ih (fun w' hw' => hroot w' (List.mem_cons_of_mem _ hw')) hx

/-- The `{±w}`-block of a zero-sum tuple of `2^k`-roots is itself zero-sum, because
`#(=w) = #(=−w)` (antipodal balance), so the block sum is `w·(#(=w)) + (−w)·(#(=−w)) = 0`. -/
theorem antipodalBlock_sum_zero {k N : ℕ} {w : L} (c : Fin N → L)
    (hcroot : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0)
    (hk : 1 ≤ k) :
    ∑ i ∈ univ.filter (fun i => c i ∈ antipodalDir w), c i = 0 := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- antipodal balance: #(=w) = #(=−w)
  have hbal := LamLeungTwoPowerAntipodalBalance.antipodal_balance_root c hcroot hsum w
  -- split the {±w}-filter into the `=w` part and the `=−w` part
  rcases eq_or_ne w 0 with hw0 | hw0
  · -- degenerate w = 0: antipodalDir 0 = {0}, block sum is a sum of zeros
    subst hw0
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter, mem_antipodalDir] at hi
    rcases hi.2 with h | h
    · exact h
    · rw [h]; ring
  · have hwne : w ≠ -w := by
      intro h
      have : (2 : L) * w = 0 := by rw [two_mul]; linear_combination h
      rcases mul_eq_zero.mp this with h2 | h0
      · exact absurd h2 (by norm_num)
      · exact hw0 h0
    have hsplit : univ.filter (fun i => c i ∈ antipodalDir w)
        = univ.filter (fun i => c i = w) ∪ univ.filter (fun i => c i = -w) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, mem_antipodalDir]
    have hdisj : Disjoint (univ.filter (fun i => c i = w)) (univ.filter (fun i => c i = -w)) := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact hwne (h1 ▸ h2)
    rw [hsplit, Finset.sum_union hdisj]
    have hsw : ∑ i ∈ univ.filter (fun i => c i = w), c i
        = (univ.filter (fun i => c i = w)).card • w := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const]
    have hsnw : ∑ i ∈ univ.filter (fun i => c i = -w), c i
        = (univ.filter (fun i => c i = -w)).card • (-w) := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const]
    rw [hsw, hsnw, hbal, nsmul_eq_mul, nsmul_eq_mul]
    ring

/-- **The key separation, single-direction vs the rest.** Let every element of `{±w} ∪ U` be a
`2^k`-th root of unity (`k ≥ 1`), `w` a `2^k`-root, and `w, −w ∉ U`. Then `AdditivelyDecoupled
{±w} U`. The `separates` field follows from `antipodalBlock_sum_zero`: in any zero-sum tuple, the
`{±w}`-block vanishes; by `∑(block) + ∑(rest) = ∑(all) = 0` the `U`-block vanishes too; the converse
is immediate. -/
theorem additivelyDecoupled_of_antipodal {k : ℕ} (hk : 1 ≤ k) {w : L}
    (hwroot : w ^ (2 ^ k) = 1)
    {U : Finset L} (hUroot : ∀ x ∈ U, x ^ (2 ^ k) = 1)
    (hwU : w ∉ U) (hnwU : -w ∉ U) :
    AdditivelyDecoupled (antipodalDir w) U where
  disjoint := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    rw [mem_antipodalDir] at hx
    rcases hx with h | h
    · exact hwU (h ▸ hxU)
    · exact hnwU (h ▸ hxU)
  separates := by
    intro N c hmem
    classical
    -- `−w` is also a root (k ≥ 1 ⟹ exponent even)
    have hnwroot : (-w) ^ (2 ^ k) = 1 := by
      rw [neg_pow]
      have heven : Even (2 ^ k) := by
        have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        rw [this]; exact even_two_mul _
      rw [Even.neg_one_pow heven, one_mul]; exact hwroot
    -- every entry is a root of unity
    have hcroot : ∀ i, (c i) ^ (2 ^ k) = 1 := by
      intro i
      have := hmem i
      rw [Finset.mem_union, mem_antipodalDir] at this
      rcases this with (h | h) | h
      · rw [h]; exact hwroot
      · rw [h]; exact hnwroot
      · exact hUroot _ h
    -- the {±w}-block sum = sum over `c i ∈ antipodalDir w` (since {±w}∩U = ∅, this filter is the
    -- "lands in G" filter for G = antipodalDir w)
    constructor
    · -- forward: ∑ all = 0 ⟹ both blocks 0
      intro hsum0
      have hG := antipodalBlock_sum_zero (k := k) (w := w) c hcroot hsum0 hk
      refine ⟨hG, ?_⟩
      -- ∑(U-block) = ∑(all) − ∑(G-block) = 0; but need block-partition. Use complementarity:
      -- every i has c i ∈ G or c i ∈ U (exclusively, by disjointness), so the two filters partition.
      have hpart : (univ.filter (fun i => c i ∈ antipodalDir w))
          ∪ (univ.filter (fun i => c i ∈ U)) = univ := by
        apply Finset.eq_univ_of_forall
        intro i
        have := hmem i
        rw [Finset.mem_union] at this ⊢
        rcases this with h | h
        · left; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
        · right; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      have hpdisj : Disjoint (univ.filter (fun i => c i ∈ antipodalDir w))
          (univ.filter (fun i => c i ∈ U)) := by
        rw [Finset.disjoint_filter]
        intro i _ hG' hU'
        exact (Finset.disjoint_left.mp (by
          rw [Finset.disjoint_left]; intro x hx hxU
          rw [mem_antipodalDir] at hx; rcases hx with h | h
          · exact hwU (h ▸ hxU)
          · exact hnwU (h ▸ hxU)) hG') hU'
      have hall : ∑ i ∈ univ.filter (fun i => c i ∈ antipodalDir w), c i
          + ∑ i ∈ univ.filter (fun i => c i ∈ U), c i = 0 := by
        rw [← Finset.sum_union hpdisj, hpart]
        simpa using hsum0
      rw [hG, zero_add] at hall
      exact hall
    · -- backward: both blocks 0 ⟹ ∑ all 0
      rintro ⟨hGblock, hUblock⟩
      have hpart : (univ.filter (fun i => c i ∈ antipodalDir w))
          ∪ (univ.filter (fun i => c i ∈ U)) = univ := by
        apply Finset.eq_univ_of_forall
        intro i
        have := hmem i
        rw [Finset.mem_union] at this ⊢
        rcases this with h | h
        · left; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
        · right; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      have hpdisj : Disjoint (univ.filter (fun i => c i ∈ antipodalDir w))
          (univ.filter (fun i => c i ∈ U)) := by
        rw [Finset.disjoint_filter]
        intro i _ hG' hU'
        exact (Finset.disjoint_left.mp (by
          rw [Finset.disjoint_left]; intro x hx hxU
          rw [mem_antipodalDir] at hx; rcases hx with h | h
          · exact hwU (h ▸ hxU)
          · exact hnwU (h ▸ hxU)) hG') hU'
      calc ∑ i, c i = ∑ i ∈ univ.filter (fun i => c i ∈ antipodalDir w), c i
              + ∑ i ∈ univ.filter (fun i => c i ∈ U), c i := by
            rw [← Finset.sum_union hpdisj, hpart]
        _ = 0 := by rw [hGblock, hUblock, add_zero]

/-! ## List assembly: the whole antipodal family is HeadDecoupled, with per-direction count `Znp`. -/

/-- A list of generators is **antipodally distinct** when no two generators are equal or negatives
of each other (so their antipodal directions are pairwise disjoint, and every direction is a genuine
`{±w}` pair). For `μ_n` this holds for the half-basis `[ζ^0, …, ζ^{m-1}]` (distinct `2^μ`-roots, no
two negatives mod the order). -/
def AntipodalDistinct (ws : List L) : Prop :=
  ws.Pairwise (fun w w' => w ≠ w' ∧ w ≠ -w')

/-- If `w` differs (anti-podally) from every generator in `ws`, then `w ∉ unionFold (ws.map dir)`. -/
theorem notMem_unionFold_of_distinct {w : L} {ws : List L}
    (h : ∀ w' ∈ ws, w ≠ w' ∧ w ≠ -w') :
    w ∉ unionFold (ws.map antipodalDir) := by
  induction ws with
  | nil => simp [unionFold]
  | cons w' ws ih =>
      simp only [List.map_cons, unionFold, Finset.mem_union, not_or]
      refine ⟨?_, ih (fun w'' hw'' => h w'' (List.mem_cons_of_mem _ hw''))⟩
      rw [mem_antipodalDir, not_or]
      obtain ⟨hne, hneg⟩ := h w' (List.mem_cons_self ..)
      exact ⟨hne, hneg⟩

/-- Every element of `unionFold (ws.map dir)` is a `2^k`-root of unity if every generator is. -/
theorem unionFold_root {k : ℕ} (hk : 1 ≤ k) {ws : List L}
    (hroot : ∀ w ∈ ws, w ^ (2 ^ k) = 1) :
    ∀ x ∈ unionFold (ws.map antipodalDir), x ^ (2 ^ k) = 1 :=
  mem_unionFold_root hk ws hroot

/-- **The whole antipodal family is `HeadDecoupled`.** Given antipodally-distinct generators that
are all `2^k`-roots of unity (`k ≥ 1`), the list of their antipodal directions is `HeadDecoupled`:
each head direction additively-decouples from the union of the rest, via
`additivelyDecoupled_of_antipodal`. -/
theorem headDecoupled_antipodalList {k : ℕ} (hk : 1 ≤ k) {ws : List L}
    (hdist : AntipodalDistinct ws) (hroot : ∀ w ∈ ws, w ^ (2 ^ k) = 1) :
    HeadDecoupled (ws.map antipodalDir) := by
  induction ws with
  | nil => exact True.intro
  | cons w ws ih =>
      rw [AntipodalDistinct, List.pairwise_cons] at hdist
      obtain ⟨hhead, htail⟩ := hdist
      simp only [List.map_cons, HeadDecoupled]
      refine ⟨?_, ih htail (fun w' hw' => hroot w' (List.mem_cons_of_mem _ hw'))⟩
      -- head decouples from the rest
      have hwroot : w ^ (2 ^ k) = 1 := hroot w (List.mem_cons_self ..)
      have hUroot := unionFold_root hk
        (fun w' hw' => hroot w' (List.mem_cons_of_mem _ hw'))
      have hwU : w ∉ unionFold (ws.map antipodalDir) :=
        notMem_unionFold_of_distinct hhead
      have hnwU : -w ∉ unionFold (ws.map antipodalDir) := by
        apply notMem_unionFold_of_distinct
        intro w' hw'
        obtain ⟨hne, hneg⟩ := hhead w' hw'
        refine ⟨?_, ?_⟩
        · -- -w ≠ w' : else w' = -w, but hneg says w ≠ -w'  ⟹ contrapose
          intro h; exact hneg (by rw [← h]; ring)
        · -- -w ≠ -w' : else w = w', contradicting hne
          intro h; exact hne (neg_inj.mp h)
      exact additivelyDecoupled_of_antipodal hk hwroot hUroot hwU hnwU

/-- **GEOMETRIC CLOSURE.** For any antipodally-distinct list `ws` of `m` generators that are all
`2^k`-th roots of unity (`k ≥ 1`, all generators `≠ 0`), the char-0 energy of the union of their
antipodal directions equals the Bessel coefficient `Edef r m` on the nose:

  `E_r^{char0}(⋃_{w∈ws} {±w}) = (2r)! · [x^{2r}] I₀(2x)^m`.

This discharges BOTH hypotheses of `bessel_identity_on_energy` for the actual roots-of-unity
energy (no longer the abstract `Finset ℚ` model):
* `HeadDecoupled` — from `headDecoupled_antipodalList` (Lam–Leung antipodal balance);
* per-direction count `= Znp` — from `zeroSumCount_antipodalDir_eq_Znp` (each `{±w}` is a single
  central-binomial direction).

For `μ_n` (`n = 2^μ`, `m = n/2`) take `ws = [ζ^0, …, ζ^{m-1}]`, the half-basis of a primitive
`2^μ`-th root; these are antipodally distinct `2^μ`-roots. The char-0 STEP-1 residual is closed. -/
theorem bessel_identity_muN {k m : ℕ} (hk : 1 ≤ k) {ws : List L}
    (hdist : AntipodalDistinct ws) (hroot : ∀ w ∈ ws, w ^ (2 ^ k) = 1)
    (hne : ∀ w ∈ ws, w ≠ 0) (hlen : ws.length = m) (r : ℕ) :
    ((zeroSumCount (unionFold (ws.map antipodalDir)) (2 * r) : ℕ) : ℚ)
      = ArkLib.ProximityGap.Frontier.AvW0.Edef r m := by
  -- the directions list and its hypotheses, fed to bessel_identity_on_energy.
  -- We must reroute through the ℚ-stated `bessel_identity_on_energy`: but that needs `Finset ℚ`.
  -- Instead we re-derive directly over `L` from the two landed halves (mfold + normalization),
  -- both of which are field-generic in their combinatorial content.
  classical
  set Ds := ws.map antipodalDir with hDs
  have hdec : HeadDecoupled Ds := headDecoupled_antipodalList hk hdist hroot
  -- map of per-direction counts is replicate m Znp
  have hmap : Ds.map (fun D => fun a => zeroSumCount D a) = List.replicate m Znp := by
    rw [hDs, List.map_map]
    apply (List.eq_replicate_iff).mpr
    refine ⟨by rw [List.length_map]; exact hlen, ?_⟩
    intro f hf
    rw [List.mem_map] at hf
    obtain ⟨w, hw, rfl⟩ := hf
    simp only [Function.comp]
    exact zeroSumCount_antipodalDir_eq_Znp (hne w hw)
  -- apply the m-fold decoupling, then the normalization bridge
  rw [zeroSumCount_mfold Ds hdec (2 * r)]
  have hmap2 : Ds.map (fun D => zeroSumCount D) = List.replicate m Znp := hmap
  rw [hmap2, mfoldConv_replicate_negPair m (2 * r)]
  rw [if_pos (by omega : (2 * r) % 2 = 0)]
  have h2r : (2 * r) / 2 = r := by omega
  rw [h2r]
  rfl

/-! ## Concrete `μ_n`: the half-basis `[ζ^0, …, ζ^{2^{μ-1}-1}]` IS an antipodally-distinct
`2^μ`-root family — closing the geometric residual for the ACTUAL prize subgroup. -/

/-- The half-basis generator list `[ζ^0, ζ^1, …, ζ^{2^{μ'}-1}]` of a primitive `2^{μ'+1}`-th root.
Its antipodal directions `{±ζ^j}` are the `m = 2^{μ'}` distinct antipodal directions of the
subgroup `μ_{2^{μ'+1}}`. -/
def halfBasis (ζ : L) (μ' : ℕ) : List L :=
  (List.range (2 ^ μ')).map (fun j => ζ ^ j)

theorem halfBasis_length (ζ : L) (μ' : ℕ) : (halfBasis ζ μ').length = 2 ^ μ' := by
  unfold halfBasis; rw [List.length_map, List.length_range]

/-- Each half-basis element is a `2^{μ'+1}`-th root of unity. -/
theorem halfBasis_root {ζ : L} {μ' : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1))) :
    ∀ w ∈ halfBasis ζ μ', w ^ (2 ^ (μ' + 1)) = 1 := by
  intro w hw
  unfold halfBasis at hw
  rw [List.mem_map] at hw
  obtain ⟨j, _, rfl⟩ := hw
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- Each half-basis element is nonzero. -/
theorem halfBasis_ne_zero {ζ : L} {μ' : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1))) :
    ∀ w ∈ halfBasis ζ μ', w ≠ 0 := by
  intro w hw
  unfold halfBasis at hw
  rw [List.mem_map] at hw
  obtain ⟨j, _, rfl⟩ := hw
  exact pow_ne_zero _ (hζ.ne_zero (by positivity))

/-- **The half-basis is antipodally distinct.** For a primitive `2^{μ'+1}`-th root `ζ`, the powers
`ζ^0, …, ζ^{2^{μ'}-1}` are pairwise `≠` and pairwise non-antipodal: `ζ^i = ζ^j ⟹ i = j` (powers
below the order are distinct) and `ζ^i = −ζ^j ⟺ ζ^{|i−j|} = ζ^{2^{μ'}}` needs index gap `2^{μ'}`,
impossible for `i, j < 2^{μ'}`. -/
theorem antipodalDistinct_halfBasis {ζ : L} {μ' : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1))) :
    AntipodalDistinct (halfBasis ζ μ') := by
  unfold AntipodalDistinct halfBasis
  rw [List.pairwise_map]
  apply List.Nodup.pairwise_of_forall_ne List.nodup_range
  intro a ha b hb hab
  rw [List.mem_range] at ha hb
  -- `−1 = ζ^{2^{μ'}}` (the unique primitive square root of unity).
  have hhalf : ζ ^ (2 ^ μ') = -1 := LamLeungTwoPowerAntipodalBalance.pow_half_eq_neg_one hζ
  -- ζ^a = ζ^b ⟹ a = b (powers below order distinct), so ζ^a ≠ ζ^b.
  have hne : ζ ^ a ≠ ζ ^ b := by
    intro h
    have hord : a < 2 ^ (μ' + 1) := by
      have : (2:ℕ) ^ μ' ≤ 2 ^ (μ' + 1) := by exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hord' : b < 2 ^ (μ' + 1) := by
      have : (2:ℕ) ^ μ' ≤ 2 ^ (μ' + 1) := by exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hab (hζ.pow_inj hord hord' h)
  refine ⟨hne, ?_⟩
  -- ζ^a ≠ −ζ^b : suppose ζ^a = −ζ^b. WLOG a ≥ b; then ζ^{a-b} = −1 = ζ^{2^{μ'}}, forcing
  -- a − b ≡ 2^{μ'} mod 2^{μ'+1}.  But 0 ≤ a−b < 2^{μ'}, contradiction.  (symmetric for a < b).
  intro h
  -- both nonzero
  have hzb : ζ ^ b ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by positivity))
  rcases le_or_gt b a with hba | hba
  · -- a ≥ b : ζ^{a-b} = −1
    have hpow : ζ ^ (a - b) = -1 := by
      have : ζ ^ (a - b) * ζ ^ b = (-1) * ζ ^ b := by
        rw [← pow_add]; rw [Nat.sub_add_cancel hba, h]; ring
      exact mul_right_cancel₀ hzb this
    -- ζ^{a-b} = ζ^{2^{μ'}} and both exponents < 2^{μ'+1} ⟹ a - b = 2^{μ'}; but a - b < 2^{μ'}
    have heq : ζ ^ (a - b) = ζ ^ (2 ^ μ') := by rw [hpow, hhalf]
    have h1 : a - b < 2 ^ (μ' + 1) := by
      have : (2:ℕ) ^ μ' ≤ 2 ^ (μ' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 2 ^ μ' < 2 ^ (μ' + 1) := by
      have : (2:ℕ) ^ (μ' + 1) = 2 ^ μ' * 2 := by ring
      have hp : 0 < (2:ℕ) ^ μ' := pow_pos (by norm_num) _
      omega
    have := hζ.pow_inj h1 h2 heq
    omega
  · -- a < b : ζ^{b-a} = −1 (from ζ^a = −ζ^b ⟹ ζ^b = −ζ^a)
    have h' : ζ ^ b = -ζ ^ a := by rw [h]; ring
    have hza : ζ ^ a ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by positivity))
    have hpow : ζ ^ (b - a) = -1 := by
      have : ζ ^ (b - a) * ζ ^ a = (-1) * ζ ^ a := by
        rw [← pow_add]; rw [Nat.sub_add_cancel (le_of_lt hba), h']; ring
      exact mul_right_cancel₀ hza this
    have heq : ζ ^ (b - a) = ζ ^ (2 ^ μ') := by rw [hpow, hhalf]
    have h1 : b - a < 2 ^ (μ' + 1) := by
      have : (2:ℕ) ^ μ' ≤ 2 ^ (μ' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 2 ^ μ' < 2 ^ (μ' + 1) := by
      have hp : 0 < (2:ℕ) ^ μ' := pow_pos (by norm_num) _
      have : (2:ℕ) ^ (μ' + 1) = 2 ^ μ' * 2 := by ring
      omega
    have := hζ.pow_inj h1 h2 heq
    omega

/-- **GEOMETRIC CLOSURE for the actual prize subgroup `μ_n`, `n = 2^{μ'+1}`.** For a primitive
`2^{μ'+1}`-th root `ζ`, the char-0 energy of the union of the `m = 2^{μ'}` antipodal directions
`{±ζ^j}` of `μ_n` equals the Bessel coefficient `Edef r m = (2r)!·[x^{2r}] I₀(2x)^m`, with NO
geometric hypothesis remaining — the `HeadDecoupled`/antipodal-distinctness/per-direction-count
obligations are all discharged from the in-tree cyclotomic Lam–Leung structure. This is the full
char-0 STEP-1 closure on the genuine roots-of-unity energy. -/
theorem bessel_identity_halfBasis {μ' : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1)))
    (r : ℕ) :
    ((zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * r) : ℕ) : ℚ)
      = ArkLib.ProximityGap.Frontier.AvW0.Edef r (2 ^ μ') := by
  exact bessel_identity_muN (k := μ' + 1) (m := 2 ^ μ') (by omega)
    (antipodalDistinct_halfBasis hζ) (halfBasis_root hζ) (halfBasis_ne_zero hζ)
    (halfBasis_length ζ μ') r

end ArkLib.ProximityGap.Frontier.LamLeungGeometric

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.zeroSumCount_antipodalDir_closed
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.additivelyDecoupled_of_antipodal
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.headDecoupled_antipodalList
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.bessel_identity_muN
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.antipodalDistinct_halfBasis
#print axioms ArkLib.ProximityGap.Frontier.LamLeungGeometric.bessel_identity_halfBasis
