/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairSumsWiring
import ArkLib.Data.CodingTheory.ProximityGap.PairSumRigidityModP

/-!
# The exact `a = 4` census value: `(2^(m−1) − 1)²` at every smooth scale

Campaign #357. The depth-1 census of the adjacent-pair stack at `a = 4` — the set of
scalars `λ = −∑_{i∈A} g^i` over characteristic-zero-qualifying 4-element exponent sets
(`e2Folded m A = 0`), the right-hand side of the two-sided dictionary
`depthOne_badScalar_iff_char0` — is computed **exactly, in closed form, at every smooth
scale simultaneously**:

> **`a4Census_card`** — for `p > 4^(2^(m−1))`:
> `|a4Census| = (2^(m−1) − 1)²` — a perfect square: `n²/4 − n + 1` at `n = 2^m`.

The mechanism, layer by layer (all landed):
1. the structure law (`e2Folded_eq_zero_iff_structured`): qualifying sets are
   `{x, x+h, y, 2x−y}`;
2. **the field-level collapse** (`sum_pow_of_structured`): the antipodal pair cancels —
   `g^x + g^(x+h) = 0` — so `λ = −(g^y + g^z)` depends only on the symmetric couple;
3. the census set is exactly `{0} ∪ {−(g^y + g^z)}` over same-parity non-antipodal pairs
   (`a4Census_eq`): the `0` comes from the doubly-antipodal configurations, every
   admissible couple is realized, and nothing else appears;
4. distinctness of the values is the landed pair-sum rigidity (`pair_sums_ne_modp`,
   threshold `4^(2^(m−1))`), and the pair count is `n²/4 − n` by the
   difference-reindexed Gauss sum.

Probe ground truth (`probe_a4_census_value.py`, exact `ℤ[ζ]`): 1, 9, 49, 225 at
`n = 4, 8, 16, 32` — including the previously-unexplained `9` of O143's `(8,2)` row.

## Honest scope

This counts the **characteristic-zero census** — the right side of the dictionary; via
`depthOne_badScalar_iff_char0` it equals the bad-scalar count of the explicit stack for
every `p` above the *dictionary's* threshold, while the count itself is valid already
above the (smaller) rigidity threshold. The row sits at `δ = 1 − 4/n`, strictly above
Johnson for `n > 8`: this is the first exact in-window census value uniform in the scale.

## References

* Probes O143/O145, `probe_a4_census_value.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PairSumRigidityModP

namespace ArkLib.ProximityGap.WindowTwoLayer

/-! ## The census objects -/

open scoped Classical in
/-- The `a = 4` depth-1 characteristic-zero census: all scalars `−∑_{i∈A} g^i` over
qualifying 4-element exponent subsets of the smooth scale. -/
noncomputable def a4Census (p : ℕ) [Fact p.Prime] (m : ℕ) (g : ZMod p) :
    Finset (ZMod p) :=
  (((Finset.range (2 ^ m)).powersetCard 4).filter (fun A => e2Folded m A = 0)).image
    (fun A => -∑ i ∈ A, g ^ i)

/-- The canonical parameter set: ordered same-parity non-antipodal exponent pairs. -/
def a4Pairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2 ^ m)) ×ˢ (Finset.range (2 ^ m))).filter
    (fun q => q.1 < q.2 ∧ (q.1 + q.2) % 2 = 0 ∧ q.2 ≠ q.1 + 2 ^ (m - 1))

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}

/-! ## Power bookkeeping -/

theorem pow_mod_order (hg : IsPrimitiveRoot g (2 ^ m)) (i : ℕ) :
    g ^ (i % 2 ^ m) = g ^ i := by
  conv_rhs => rw [← Nat.div_add_mod i (2 ^ m)]
  rw [pow_add, pow_mul, hg.pow_eq_one, one_pow, one_mul]

theorem pow_val_cast (hg : IsPrimitiveRoot g (2 ^ m)) (i : ℕ) :
    g ^ ((i : ZMod (2 ^ m))).val = g ^ i := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [ZMod.val_natCast, pow_mod_order hg]

theorem pow_val_add_half (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    (w : ZMod (2 ^ m)) :
    g ^ ((w + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))).val) = -(g ^ w.val) := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h1 : w + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      = ((w.val + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast, pow_mod_order hg, pow_add, pow_half_eq_neg_one hm hg,
    mul_neg_one]

/-- A sum of two `g`-powers with exponents below the order vanishes **iff** the exponents
are antipodal. -/
theorem two_pow_sum_eq_zero_iff (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m) (hij : i < j) :
    g ^ i + g ^ j = 0 ↔ j = i + 2 ^ (m - 1) := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  constructor
  · intro h0
    have hneg : g ^ j = g ^ (i + 2 ^ (m - 1)) := by
      rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg_one]
      exact (add_eq_zero_iff_neg_eq.mp h0).symm
    by_cases hcase : i + 2 ^ (m - 1) < 2 ^ m
    · exact hg.pow_inj hj hcase hneg
    · exfalso
      have hmod : g ^ (i + 2 ^ (m - 1)) = g ^ ((i + 2 ^ (m - 1)) % 2 ^ m) :=
        (pow_mod_order hg _).symm
      have hlt : (i + 2 ^ (m - 1)) % 2 ^ m = i + 2 ^ (m - 1) - 2 ^ m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have hj' := hg.pow_inj hj
        (show i + 2 ^ (m - 1) - 2 ^ m < 2 ^ m by omega)
        (by rw [hneg, hmod, hlt])
      omega
  · rintro rfl
    rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg_one]
    ring

/-! ## The field-level collapse -/

/-- **The antipodal pair cancels in the field**: for a structured exponent set the census
scalar depends only on the symmetric couple. -/
theorem sum_pow_of_structured (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {A : Finset ℕ} {x y z : ZMod (2 ^ m)}
    (hM : A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
      = {x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), y, z}) :
    ∑ i ∈ A, g ^ i = g ^ y.val + g ^ z.val := by
  have h1 : ∑ i ∈ A, g ^ i
      = ((A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))).map (fun w => g ^ w.val)).sum := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (pow_val_cast hg i).symm
  rw [h1, hM]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  rw [pow_val_add_half hm hg x]
  ring

/-- The reduction of a subset of the scale is duplicate-free, so the structured form has
four pairwise distinct entries. -/
theorem structured_nodup {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m))
    {x y z : ZMod (2 ^ m)}
    (hM : A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
      = {x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), y, z}) :
    ({x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), y, z} : Multiset (ZMod (2 ^ m))).Nodup := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [← hM]
  refine Multiset.Nodup.map_on ?_ A.nodup
  intro i hi j hj hij
  have hi' : i < 2 ^ m := Finset.mem_range.mp (hsub hi)
  have hj' : j < 2 ^ m := Finset.mem_range.mp (hsub hj)
  have := congrArg ZMod.val hij
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi',
    Nat.mod_eq_of_lt hj'] at this

/-! ## The witnesses -/

/-- The doubly-antipodal witness `{0, Q, 2Q, 3Q}`, `Q = 2^(m−2)` — the qualifying set
realizing the census value `0`. -/
def doubleAntipodalWitness (m : ℕ) : Finset ℕ :=
  {0, 2 ^ (m - 2), 2 ^ (m - 1), 2 ^ (m - 2) + 2 ^ (m - 1)}

section Witnesses

variable (hm : 2 ≤ m)

private theorem witness_facts (hm : 2 ≤ m) :
    0 < 2 ^ (m - 2) ∧ 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1)
      ∧ 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m :=
  ⟨pow_pos (by norm_num) _,
    by rw [← two_mul, ← pow_succ']; congr 1; omega,
    by rw [← two_mul, ← pow_succ']; congr 1; omega⟩

theorem doubleAntipodalWitness_subset (hm : 2 ≤ m) :
    doubleAntipodalWitness m ⊆ Finset.range (2 ^ m) := by
  obtain ⟨h1, h2, h3⟩ := witness_facts hm
  intro i hi
  simp only [doubleAntipodalWitness, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> (rw [Finset.mem_range]; omega)

theorem doubleAntipodalWitness_card (hm : 2 ≤ m) :
    (doubleAntipodalWitness m).card = 4 := by
  obtain ⟨h1, h2, h3⟩ := witness_facts hm
  rw [doubleAntipodalWitness,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega),
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
    Finset.card_singleton]

theorem doubleAntipodalWitness_val (hm : 2 ≤ m) :
    (doubleAntipodalWitness m).val
      = ({0, 2 ^ (m - 2), 2 ^ (m - 1), 2 ^ (m - 2) + 2 ^ (m - 1)} : Multiset ℕ) := by
  obtain ⟨h1, h2, h3⟩ := witness_facts hm
  rw [doubleAntipodalWitness,
    Finset.insert_val_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega),
    Finset.insert_val_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega),
    Finset.insert_val_of_notMem (by simp only [Finset.mem_singleton]; omega)]
  rfl

theorem doubleAntipodalWitness_structured (hm : 2 ≤ m) :
    (doubleAntipodalWitness m).val.map (Nat.cast : ℕ → ZMod (2 ^ m))
      = {0, 0 + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
          ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)),
          ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))} := by
  rw [doubleAntipodalWitness_val hm]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Nat.cast_zero, Nat.cast_add, zero_add]
  exact congrArg (0 ::ₘ ·) (Multiset.cons_swap _ _ _)

theorem doubleAntipodalWitness_qualifies (hm : 2 ≤ m) :
    e2Folded m (doubleAntipodalWitness m) = 0 := by
  obtain ⟨h1, h2, h3⟩ := witness_facts hm
  refine (e2Folded_eq_zero_iff_structured (by omega) _
    (doubleAntipodalWitness_card hm)).mpr
    ⟨0, ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)),
      ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
      doubleAntipodalWitness_structured hm, ?_⟩
  rw [← add_assoc, ← Nat.cast_add, ← Nat.cast_add, h2, h3, ZMod.natCast_self]
  ring

/-- Every same-parity couple is realized by a qualifying witness: midpoint plus its
antipode. -/
theorem pairWitness_exists (hm : 2 ≤ m) {y₀ z₀ : ℕ} (hy : y₀ < 2 ^ m) (hz : z₀ < 2 ^ m)
    (hlt : y₀ < z₀) (hpar : (y₀ + z₀) % 2 = 0) :
    ∃ (A : Finset ℕ) (x : ZMod (2 ^ m)),
      A ⊆ Finset.range (2 ^ m) ∧ A.card = 4 ∧
      A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
        = {x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
            ((y₀ : ℕ) : ZMod (2 ^ m)), ((z₀ : ℕ) : ZMod (2 ^ m))} ∧
      ((y₀ : ℕ) : ZMod (2 ^ m)) + ((z₀ : ℕ) : ZMod (2 ^ m)) = x + x := by
  obtain ⟨-, -, h3⟩ := witness_facts hm
  set x₀ : ℕ := (y₀ + z₀) / 2 with hx₀
  have h2x : 2 * x₀ = y₀ + z₀ := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hpar) |>.symm
    ▸ (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hpar))
  set w₀ : ℕ := (x₀ + 2 ^ (m - 1)) % 2 ^ m with hw₀
  have hxlt : x₀ < 2 ^ m := by omega
  have hwlt : w₀ < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hw : w₀ = x₀ + 2 ^ (m - 1) ∨ (2 ^ (m - 1) ≤ x₀ ∧ w₀ + 2 ^ m = x₀ + 2 ^ (m - 1)) := by
    by_cases hc : x₀ + 2 ^ (m - 1) < 2 ^ m
    · left
      rw [hw₀, Nat.mod_eq_of_lt hc]
    · right
      refine ⟨by omega, ?_⟩
      rw [hw₀, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  -- all four entries pairwise distinct
  have hne : x₀ ≠ w₀ ∧ x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ w₀ ≠ y₀ ∧ w₀ ≠ z₀ ∧ y₀ ≠ z₀ := by
    rcases hw with hw | ⟨hge, hw⟩ <;>
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨ne1, ne2, ne3, ne4, ne5, ne6⟩ := hne
  refine ⟨{x₀, w₀, y₀, z₀}, ((x₀ : ℕ) : ZMod (2 ^ m)), ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> (rw [Finset.mem_range]; omega)
  · rw [Finset.card_insert_of_notMem (by simp [ne1, ne2, ne3]),
      Finset.card_insert_of_notMem (by simp [ne4, ne5]),
      Finset.card_insert_of_notMem (by simp [ne6]),
      Finset.card_singleton]
  · rw [Finset.insert_val_of_notMem (by simp [ne1, ne2, ne3]),
      Finset.insert_val_of_notMem (by simp [ne4, ne5]),
      Finset.insert_val_of_notMem (by simp [ne6])]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 2
    -- the antipode entry casts to x + h
    rw [hw₀, ZMod.natCast_mod, Nat.cast_add]
  · rw [← Nat.cast_add, ← Nat.cast_add, show y₀ + z₀ = x₀ + x₀ from by omega]

end Witnesses

/-! ## The census set equality -/

/-- **The census is `{0}` plus the symmetric-couple values.** -/
theorem a4Census_eq (hm : 2 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m)) :
    a4Census p m g
      = insert 0 ((a4Pairs m).image (fun q => -(g ^ q.1 + g ^ q.2))) := by
  classical
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hm1 : 1 ≤ m := by omega
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm1] at h
    omega
  have hchch : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      = 0 := zmod_half_add_half hm1
  ext lam
  simp only [a4Census, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.mem_insert]
  constructor
  · rintro ⟨A, ⟨⟨hsub, hcard⟩, hzero⟩, rfl⟩
    obtain ⟨x, y, z, hM, hyz⟩ :=
      (e2Folded_eq_zero_iff_structured hm1 A hcard).mp hzero
    have hsum := sum_pow_of_structured hm1 hg hM
    have hnd := structured_nodup hsub hM
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton] at hnd
    simp only [not_or] at hnd
    obtain ⟨⟨hx1, hx2, hx3⟩, ⟨hh1, hh2⟩, hyz', _⟩ := hnd
    by_cases hanti : z = y + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
    · -- doubly-antipodal: the census value is 0
      left
      rw [hsum, hanti, pow_val_add_half hm1 hg y]
      ring
    · -- generic: a same-parity non-antipodal couple
      right
      have hyz0 : y.val ≠ z.val := fun hc => hyz' (ZMod.val_injective _ hc)
      -- parity of the value pair
      have hpar : (y.val + z.val) % 2 = 0 := by
        have hv := congrArg ZMod.val hyz
        rw [ZMod.val_add, ZMod.val_add] at hv
        have h2n : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        have e1 : (y.val + z.val) % 2 = (x.val + x.val) % 2 := by
          have l1 := Nat.mod_mod_of_dvd (y.val + z.val) h2n
          have l2 := Nat.mod_mod_of_dvd (x.val + x.val) h2n
          omega
        omega
      -- non-antipodality of the value pair, both orientations
      have hna : ∀ {u v : ZMod (2 ^ m)}, v ≠ u + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) →
          v.val ≠ u.val + 2 ^ (m - 1) := by
        intro u v hne hc
        apply hne
        have : ((v.val : ℕ) : ZMod (2 ^ m)) = ((u.val + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
          rw [hc]
        rwa [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val] at this
      have hanti' : y ≠ z + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        intro hc
        apply hanti
        rw [hc, add_assoc, hchch, add_zero]
      rcases Nat.lt_or_ge y.val z.val with hlt | hge
      · exact ⟨(y.val, z.val), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt y),
            Finset.mem_range.mpr (ZMod.val_lt z)⟩,
            hlt, hpar, hna hanti⟩, by rw [hsum]⟩
      · have hlt' : z.val < y.val := by omega
        exact ⟨(z.val, y.val), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt z),
            Finset.mem_range.mpr (ZMod.val_lt y)⟩,
            hlt', by omega, hna hanti'⟩, by rw [hsum]; ring⟩
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · -- 0 is realized by the doubly-antipodal witness {0, Q, 2Q, 3Q}
      refine ⟨doubleAntipodalWitness m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact doubleAntipodalWitness_subset hm
      · exact doubleAntipodalWitness_card hm
      · exact doubleAntipodalWitness_qualifies hm
      · have hM := doubleAntipodalWitness_structured (m := m) hm
        rw [sum_pow_of_structured hm1 hg hM, pow_val_add_half hm1 hg]
        ring
    · -- every admissible couple is realized
      obtain ⟨hmem, hlt, hpar, hna⟩ := Finset.mem_filter.mp hq
      obtain ⟨hy, hz⟩ := Finset.mem_product.mp hmem
      obtain ⟨A, x, hsub, hcard, hM, hyzsum⟩ :=
        pairWitness_exists hm (Finset.mem_range.mp hy) (Finset.mem_range.mp hz)
          hlt hpar
      refine ⟨A, ⟨⟨hsub, hcard⟩, ?_⟩, ?_⟩
      · exact (e2Folded_eq_zero_iff_structured hm1 A hcard).mpr
          ⟨_, _, _, hM, hyzsum⟩
      · rw [sum_pow_of_structured hm1 hg hM, pow_val_cast hg, pow_val_cast hg]

/-! ## The count -/

/-- The parameter set counted by the difference reindex: `n²/4 − n`. -/
theorem a4Pairs_card (hm : 2 ≤ m) :
    (a4Pairs m).card = 2 ^ (m - 1) * 2 ^ (m - 1) - 2 ^ m := by
  classical
  obtain ⟨hQ, hQQ, hsplit⟩ := witness_facts hm
  set M : ℕ := 2 ^ (m - 1) with hM
  set Q : ℕ := 2 ^ (m - 2) with hQdef
  -- the difference reindex
  have hbi : a4Pairs m
      = ((Finset.range M).filter (fun i => 0 < i ∧ i ≠ Q)).biUnion
          (fun i => (Finset.range (2 ^ m - 2 * i)).image (fun y => (y, y + 2 * i))) := by
    ext q
    simp only [a4Pairs, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hlt, hpar, hna⟩
      refine ⟨(q.2 - q.1) / 2, ⟨by omega, by omega, by omega⟩, q.1, by omega, ?_⟩
      have : 2 * ((q.2 - q.1) / 2) = q.2 - q.1 := by omega
      rw [this]
      exact Prod.ext rfl (by omega)
    · rintro ⟨i, ⟨hiM, hi0, hiQ⟩, y, hy, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩
  rw [hbi, Finset.card_biUnion]
  · -- evaluate the sum of fiber sizes
    have hcards : ∀ i ∈ (Finset.range M).filter (fun i => 0 < i ∧ i ≠ Q),
        ((Finset.range (2 ^ m - 2 * i)).image (fun y => (y, y + 2 * i))).card
          = 2 ^ m - 2 * i := by
      intro i _
      rw [Finset.card_image_of_injective _ (fun a b hab => by
        simpa using (Prod.ext_iff.mp hab).1), Finset.card_range]
    rw [Finset.sum_congr rfl hcards]
    -- split off the excluded indices 0 and Q
    have hfe : (Finset.range M).filter (fun i => 0 < i ∧ i ≠ Q)
        = ((Finset.range M).erase 0).erase Q := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
      omega
    have hQmem : Q ∈ (Finset.range M).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    have h0mem : (0 : ℕ) ∈ Finset.range M := by
      simp only [Finset.mem_range]
      omega
    have e1 := Finset.sum_erase_add _ (fun i => 2 ^ m - 2 * i) hQmem
    have e2 := Finset.sum_erase_add _ (fun i => 2 ^ m - 2 * i) h0mem
    -- Gauss
    have e3 : (∑ i ∈ Finset.range M, (2 ^ m - 2 * i)) + 2 * ∑ i ∈ Finset.range M, i
        = M * 2 ^ m := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i hi => by
        have := Finset.mem_range.mp hi
        omega : ∀ i ∈ Finset.range M, (2 ^ m - 2 * i) + 2 * i = 2 ^ m)]
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have e4 := Finset.sum_range_id_mul_two M
    -- assemble
    rw [hfe]
    simp only at e1 e2
    have ha : M * 2 ^ m = 2 * (M * M) := by
      rw [show (2 : ℕ) ^ m = M + M from hsplit.symm]
      ring
    have hb : M * (M - 1) + M = M * M := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    -- atomize the products so the linear arithmetic can link everything
    obtain ⟨MN, hMN⟩ : ∃ t, M * 2 ^ m = t := ⟨_, rfl⟩
    obtain ⟨MM, hMM⟩ : ∃ t, M * M = t := ⟨_, rfl⟩
    obtain ⟨ML, hML⟩ : ∃ t, M * (M - 1) = t := ⟨_, rfl⟩
    rw [hMN] at e3 ha
    rw [hMM] at ha hb ⊢
    rw [hML] at e4 hb
    omega
  · -- the fibers are pairwise disjoint (the difference is determined)
    intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro q ⟨y, hy, rfl⟩ ⟨y', hy', hq⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hq
    simp only at h1 h2
    omega

/-- **THE EXACT `a = 4` CENSUS VALUE**: a perfect square, at every smooth scale, for every
prime above the rigidity threshold. -/
theorem a4Census_card (hm : 2 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : 4 ^ 2 ^ (m - 1) < p) :
    (a4Census p m g).card = (2 ^ (m - 1) - 1) * (2 ^ (m - 1) - 1) := by
  classical
  obtain ⟨hQ, hQQ, hsplit⟩ := witness_facts hm
  have hm1 : 1 ≤ m := by omega
  rw [a4Census_eq hm hg]
  -- 0 is not among the couple values
  have h0not : (0 : ZMod p) ∉ (a4Pairs m).image (fun q => -(g ^ q.1 + g ^ q.2)) := by
    simp only [Finset.mem_image, not_exists, not_and]
    rintro q hq hzero
    obtain ⟨hmem, hlt, _, hna⟩ := Finset.mem_filter.mp hq
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hmem
    have hsum : g ^ q.1 + g ^ q.2 = 0 := by
      have := congrArg Neg.neg hzero
      simpa using this
    exact hna ((two_pow_sum_eq_zero_iff hm1 hg (Finset.mem_range.mp hy)
      (Finset.mem_range.mp hz) hlt).mp hsum)
  rw [Finset.card_insert_of_notMem h0not]
  -- the couple values are pairwise distinct (the landed rigidity)
  rw [Finset.card_image_of_injOn ?inj]
  case inj =>
    intro q hq q' hq' heq
    obtain ⟨hmem, hlt, _, hna⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hmem
    obtain ⟨hmem', hlt', _, hna'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
    obtain ⟨hy', hz'⟩ := Finset.mem_product.mp hmem'
    have hy := Finset.mem_range.mp hy
    have hz := Finset.mem_range.mp hz
    have hy' := Finset.mem_range.mp hy'
    have hz' := Finset.mem_range.mp hz'
    have hsum : g ^ q.1 + g ^ q.2 = g ^ q'.1 + g ^ q'.2 := by
      have := congrArg Neg.neg heq
      simpa using this
    have hnaij : q.2 ≠ (q.1 + 2 ^ (m - 1)) % 2 ^ m := by
      by_cases hc : q.1 + 2 ^ (m - 1) < 2 ^ m
      · rw [Nat.mod_eq_of_lt hc]
        exact hna
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    rcases pair_sum_rigidity_modp hm1 hg hy hz hy' hz' (by omega) (by omega)
      hnaij hp hsum with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1 e2
    · exfalso
      omega
  -- numerics
  rw [a4Pairs_card hm]
  have hM1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have hsq : (2 ^ (m - 1) - 1) * (2 ^ (m - 1) - 1) + 2 * 2 ^ (m - 1)
      = 2 ^ (m - 1) * 2 ^ (m - 1) + 1 := by
    obtain ⟨N, hN⟩ : ∃ N, 2 ^ (m - 1) = N + 1 := ⟨2 ^ (m - 1) - 1, by omega⟩
    rw [hN, Nat.add_sub_cancel]
    ring
  have hM2 : 2 ≤ 2 ^ (m - 1) := by omega
  have hMM2 : 2 * 2 ^ (m - 1) ≤ 2 ^ (m - 1) * 2 ^ (m - 1) :=
    Nat.mul_le_mul_right _ hM2
  obtain ⟨SQ, hSQ⟩ : ∃ t, (2 ^ (m - 1) - 1) * (2 ^ (m - 1) - 1) = t := ⟨_, rfl⟩
  obtain ⟨MM, hMM⟩ : ∃ t, 2 ^ (m - 1) * 2 ^ (m - 1) = t := ⟨_, rfl⟩
  rw [hSQ, hMM] at hsq ⊢
  rw [hMM] at hMM2
  rw [← hsplit]
  obtain ⟨H, hH⟩ : ∃ t, 2 ^ (m - 1) = t := ⟨_, rfl⟩
  rw [hH] at hsq hMM2 ⊢
  omega

/-! ## Source audit -/

#print axioms sum_pow_of_structured
#print axioms a4Census_eq
#print axioms a4Pairs_card
#print axioms a4Census_card

end ArkLib.ProximityGap.WindowTwoLayer
