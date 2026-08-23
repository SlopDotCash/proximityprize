/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.A4CensusValue
import ArkLib.Data.CodingTheory.ProximityGap.BalancedFiveLaw

/-!
# The exact `a = 5` census value: the first proven flat-`n` law — census `= n`, no threshold

Campaign #357. The `a = 5` depth-1 census of the adjacent-pair stack — the scalars
`−∑_{i∈A} g^i` over characteristic-zero-qualifying 5-element exponent sets — is computed
exactly at every smooth scale, **with no field-size threshold at all**:

> **`a5Census_card`** — for every prime `p` carrying a primitive `2^m`-th root (`m ≥ 3`):
> `|a5Census| = 2^m = n` — **one full rotation orbit**, the first proven flat-`n` law of
> the depth-1 system.

Mechanism: by the balanced five-set law a qualifying set is a coset of `{0, q, h, q+h}`
plus a free point `v`; the coset cancels **pairwise** in the field
(`g^x + g^(x+h) = 0` and `g^(x+q) + g^(x+q+h) = 0`), so `λ = −g^v` — and every `v` is
realized (the coset based at `v + 1` avoids `v`: the subgroup is even, `n − 1` is odd).
Distinctness of the orbit values needs only the injectivity of `g`-powers below the order:
unlike the `a = 4` census `(n/2 − 1)²` (which needs the pair-sum rigidity threshold
`4^(2^(m−1))`), the flat-`n` law is **unconditional in `p`**.

## References

* Probes `probe_a5_coset_shape.py`, `probe_a58_census_table.py` (census 8/16/32 at
  `n = 8/16/32`); issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

open scoped Classical in
/-- The `a = 5` depth-1 characteristic-zero census. -/
noncomputable def a5Census (p : ℕ) [Fact p.Prime] (m : ℕ) (g : ZMod p) :
    Finset (ZMod p) :=
  (((Finset.range (2 ^ m)).powersetCard 5).filter (fun A => e2Folded m A = 0)).image
    (fun A => -∑ i ∈ A, g ^ i)

/-- Five-element multisets are quintuples. -/
theorem multiset_card_eq_five {α : Type*} {M : Multiset α} (hM : Multiset.card M = 5) :
    ∃ a b c d e, M = {a, b, c, d, e} := by
  classical
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < Multiset.card M by omega)
  obtain ⟨b, c, d, e, hM'⟩ := Multiset.card_eq_four.mp
    (show Multiset.card (M.erase a) = 4 by rw [Multiset.card_erase_of_mem ha, hM]; rfl)
  exact ⟨a, b, c, d, e, by rw [← Multiset.cons_erase ha, hM']; rfl⟩

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}

/-- The field-level collapse for the five-shape: both coset pairs cancel. -/
theorem sum_pow_of_coset_shape (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {A : Finset ℕ} {x v : ZMod (2 ^ m)}
    (hM : A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
      = {x, x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)),
          x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
          x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
          v}) :
    ∑ i ∈ A, g ^ i = g ^ v.val := by
  have h1 : ∑ i ∈ A, g ^ i
      = ((A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))).map (fun w => g ^ w.val)).sum := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (pow_val_cast hg i).symm
  rw [h1, hM]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  rw [pow_val_add_half hm hg x, pow_val_add_half hm hg
    (x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)))]
  ring

/-- **The census set is the full negated orbit.** -/
theorem a5Census_eq (hm : 3 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m)) :
    a5Census p m g = (Finset.range (2 ^ m)).image (fun w => -(g ^ w)) := by
  classical
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hQQ : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega] at h
    omega
  have hQQ' : ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
      = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [← Nat.cast_add, hQQ]
  ext lam
  simp only [a5Census, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨A, ⟨⟨hsub, hcard⟩, hzero⟩, rfl⟩
    -- qualifying ⟹ balanced ⟹ coset shape ⟹ the sum collapses to the free point
    have hbal := (e2Folded_eq_zero_iff_balanced_cast hm1 A).mp hzero
    have hcard5 : Multiset.card (A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))) = 5 := by
      simp [hcard]
    obtain ⟨a, b, c, d, e, hM⟩ := multiset_card_eq_five hcard5
    -- distinctness from injectivity of the reduction on the range
    have hnd : ({a, b, c, d, e} : Multiset (ZMod (2 ^ m))).Nodup := by
      rw [← hM]
      refine Multiset.Nodup.map_on ?_ A.nodup
      intro i hi j hj hij
      have hi' : i < 2 ^ m := Finset.mem_range.mp (hsub hi)
      have hj' : j < 2 ^ m := Finset.mem_range.mp (hsub hj)
      have := congrArg ZMod.val hij
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi',
        Nat.mod_eq_of_lt hj'] at this
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, not_or] at hnd
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, -⟩ := hnd
    rw [hM] at hbal
    obtain ⟨x, v, hshape⟩ := (balanced_five_iff_zmod hm2 hab hac had hae hbc hbd hbe
      hcd hce hde).mp hbal
    have hsum := sum_pow_of_coset_shape hm1 hg (hM.trans hshape)
    exact ⟨v.val, Finset.mem_range.mpr (ZMod.val_lt v), by rw [hsum]⟩
  · rintro ⟨w, hw, rfl⟩
    have hw' : w < 2 ^ m := Finset.mem_range.mp hw
    -- the coset based at w + 1 avoids w (the subgroup is even, −1 is odd)
    set Q : ℕ := 2 ^ (m - 2) with hQdef
    set H : ℕ := 2 ^ (m - 1) with hHdef
    set x₀ : ℕ := (w + 1) % 2 ^ m with hx₀
    set c₂ : ℕ := (x₀ + Q) % 2 ^ m with hc₂
    set c₃ : ℕ := (x₀ + H) % 2 ^ m with hc₃
    set c₄ : ℕ := (x₀ + Q + H) % 2 ^ m with hc₄
    have hbound : x₀ < 2 ^ m ∧ c₂ < 2 ^ m ∧ c₃ < 2 ^ m ∧ c₄ < 2 ^ m :=
      ⟨Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity),
        Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩
    obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbound
    -- the reductions
    have castinj : ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
        ((i : ℕ) : ZMod (2 ^ m)) = ((j : ℕ) : ZMod (2 ^ m)) → i = j := by
      intro i j hi hj hij
      have := congrArg ZMod.val hij
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi,
        Nat.mod_eq_of_lt hj] at this
    have castne : ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m → i ≠ j →
        ((i : ℕ) : ZMod (2 ^ m)) ≠ ((j : ℕ) : ZMod (2 ^ m)) :=
      fun i j hi hj hne hc => hne (castinj i j hi hj hc)
    set X : ZMod (2 ^ m) := ((x₀ : ℕ) : ZMod (2 ^ m)) with hX
    have hXw : X = ((w : ℕ) : ZMod (2 ^ m)) + 1 := by
      rw [hX, hx₀, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
    have hcast₂ : ((c₂ : ℕ) : ZMod (2 ^ m)) = X + ((Q : ℕ) : ZMod (2 ^ m)) := by
      rw [hc₂, ZMod.natCast_mod, Nat.cast_add, hX, hx₀, ZMod.natCast_mod]
    have hcast₃ : ((c₃ : ℕ) : ZMod (2 ^ m)) = X + ((H : ℕ) : ZMod (2 ^ m)) := by
      rw [hc₃, ZMod.natCast_mod, Nat.cast_add, hX, hx₀, ZMod.natCast_mod]
    have hcast₄ : ((c₄ : ℕ) : ZMod (2 ^ m))
        = X + ((Q : ℕ) : ZMod (2 ^ m)) + ((H : ℕ) : ZMod (2 ^ m)) := by
      rw [hc₄, ZMod.natCast_mod, Nat.cast_add, Nat.cast_add, hX, hx₀, ZMod.natCast_mod]
    -- ℕ-level distinctness via the reductions
    have hQH : Q < H ∧ H + H = 2 ^ m ∧ 0 < Q := by
      refine ⟨Nat.pow_lt_pow_right (by norm_num) (by omega), ?_, pow_pos (by norm_num) _⟩
      have h := pow_succ 2 (m - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
      omega
    obtain ⟨hQltH, hHH, hQpos⟩ := hQH
    have hQ2 : 2 ≤ Q := by
      calc (2 : ℕ) = 2 ^ 1 := rfl
        _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hQQ2 : Q + Q = H := by
      have h := pow_succ 2 (m - 2)
      rw [show m - 2 + 1 = m - 1 by omega] at h
      omega
    -- distinct offsets in ZMod: nonzero casts of small nonzero naturals
    have hne0 : ∀ k : ℕ, 0 < k → k < 2 ^ m → ((k : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
      intro k h0 hk hc
      have := castinj k 0 hk (by positivity) (by simpa using hc)
      omega
    -- the five entries are pairwise distinct as naturals
    have hd₁₂ : x₀ ≠ c₂ := fun hc => hne0 Q hQpos (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [← hX, hcast₂] at this
          linear_combination -this)
    have hd₁₃ : x₀ ≠ c₃ := fun hc => hne0 H (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [← hX, hcast₃] at this
          linear_combination -this)
    have hd₁₄ : x₀ ≠ c₄ := fun hc => hne0 (Q + H) (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [← hX, hcast₄] at this
          push_cast
          linear_combination -this)
    have hd₂₃ : c₂ ≠ c₃ := fun hc => hne0 (H - Q) (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₂, hcast₃] at this
          have hsub : ((H - Q : ℕ) : ZMod (2 ^ m))
              = ((H : ℕ) : ZMod (2 ^ m)) - ((Q : ℕ) : ZMod (2 ^ m)) := by
            have : Q + (H - Q) = H := by omega
            have hc' := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) this
            push_cast at hc'
            linear_combination hc'
          rw [hsub]
          linear_combination -this)
    have hd₂₄ : c₂ ≠ c₄ := fun hc => hne0 H (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₂, hcast₄] at this
          linear_combination -this)
    have hd₃₄ : c₃ ≠ c₄ := fun hc => hne0 Q hQpos (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₃, hcast₄] at this
          linear_combination -this)
    -- w avoids the coset: 1 + s ≠ 0 for the four subgroup offsets
    have hw₁ : w ≠ x₀ := fun hc => hne0 1 (by norm_num) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [← hX, hXw] at this
          push_cast at this ⊢
          linear_combination -this)
    have hw₂ : w ≠ c₂ := fun hc => hne0 (1 + Q) (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₂, hXw] at this
          push_cast at this ⊢
          linear_combination -this)
    have hw₃ : w ≠ c₃ := fun hc => hne0 (1 + H) (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₃, hXw] at this
          push_cast at this ⊢
          linear_combination -this)
    have hw₄ : w ≠ c₄ := fun hc => hne0 (1 + Q + H) (by omega) (by omega)
      (by have := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
          rw [hcast₄, hXw] at this
          push_cast at this ⊢
          linear_combination -this)
    -- assemble the witness set
    refine ⟨{x₀, c₂, c₃, c₄, w}, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> (rw [Finset.mem_range]; omega)
    · rw [Finset.card_insert_of_notMem (by simp [hd₁₂, hd₁₃, hd₁₄, Ne.symm hw₁]),
        Finset.card_insert_of_notMem (by simp [hd₂₃, hd₂₄, Ne.symm hw₂]),
        Finset.card_insert_of_notMem (by simp [hd₃₄, Ne.symm hw₃]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hw₄]),
        Finset.card_singleton]
    · -- qualifies: the reduction is the coset shape, which is balanced
      refine (e2Folded_eq_zero_iff_balanced_cast (by omega) _).mpr ?_
      have hval : ({x₀, c₂, c₃, c₄, w} : Finset ℕ).val.map
            (Nat.cast : ℕ → ZMod (2 ^ m))
          = {X, X + ((Q : ℕ) : ZMod (2 ^ m)), X + ((H : ℕ) : ZMod (2 ^ m)),
              X + ((Q : ℕ) : ZMod (2 ^ m)) + ((H : ℕ) : ZMod (2 ^ m)),
              ((w : ℕ) : ZMod (2 ^ m))} := by
        rw [Finset.insert_val_of_notMem (by simp [hd₁₂, hd₁₃, hd₁₄, Ne.symm hw₁]),
          Finset.insert_val_of_notMem (by simp [hd₂₃, hd₂₄, Ne.symm hw₂]),
          Finset.insert_val_of_notMem (by simp [hd₃₄, Ne.symm hw₃]),
          Finset.insert_val_of_notMem (by simp [Ne.symm hw₄])]
        simp only [Finset.singleton_val, Multiset.insert_eq_cons, Multiset.map_cons,
          Multiset.map_singleton]
        rw [hcast₂, hcast₃, hcast₄, ← hX]
      rw [hval]
      have hQQ' : ((Q : ℕ) : ZMod (2 ^ m)) + ((Q : ℕ) : ZMod (2 ^ m))
          = ((H : ℕ) : ZMod (2 ^ m)) := by
        rw [← Nat.cast_add, hQQ2]
      exact balanced_of_coset_shape (zmod_half_add_half (by omega)) hQQ' X _
    · -- the census value is −g^w
      have hval : ({x₀, c₂, c₃, c₄, w} : Finset ℕ).val.map
            (Nat.cast : ℕ → ZMod (2 ^ m))
          = {X, X + ((Q : ℕ) : ZMod (2 ^ m)), X + ((H : ℕ) : ZMod (2 ^ m)),
              X + ((Q : ℕ) : ZMod (2 ^ m)) + ((H : ℕ) : ZMod (2 ^ m)),
              ((w : ℕ) : ZMod (2 ^ m))} := by
        rw [Finset.insert_val_of_notMem (by simp [hd₁₂, hd₁₃, hd₁₄, Ne.symm hw₁]),
          Finset.insert_val_of_notMem (by simp [hd₂₃, hd₂₄, Ne.symm hw₂]),
          Finset.insert_val_of_notMem (by simp [hd₃₄, Ne.symm hw₃]),
          Finset.insert_val_of_notMem (by simp [Ne.symm hw₄])]
        simp only [Finset.singleton_val, Multiset.insert_eq_cons, Multiset.map_cons,
          Multiset.map_singleton]
        rw [hcast₂, hcast₃, hcast₄, ← hX]
      rw [sum_pow_of_coset_shape (by omega) hg hval, pow_val_cast hg]

/-- **THE FLAT-`n` LAW (the exact `a = 5` census value).** For every prime carrying a
primitive `2^m`-th root, `m ≥ 3`: the `a = 5` depth-1 census is one full rotation orbit —
**exactly `2^m = n` values, with no field-size threshold**. -/
theorem a5Census_card (hm : 3 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m)) :
    (a5Census p m g).card = 2 ^ m := by
  rw [a5Census_eq hm hg, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hi' : i < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hi)
  have hj' : j < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hj)
  exact hg.pow_inj hi' hj' (by linear_combination -hij)

/-! ## Source audit -/

#print axioms multiset_card_eq_five
#print axioms sum_pow_of_coset_shape
#print axioms a5Census_eq
#print axioms a5Census_card

end ArkLib.ProximityGap.WindowTwoLayer
