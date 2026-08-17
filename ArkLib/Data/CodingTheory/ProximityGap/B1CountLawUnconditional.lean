/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ArkLib.Data.CodingTheory.ProximityGap.B1TopDirectionCountLaw

/-!
# B1CountLawUnconditional

Module docstring for `B1CountLawUnconditional.lean`.
-/


open Finset

namespace SubsetSurj

/-- The minimal `m`-subset sum of `range n`: `0+1+…+(m-1)`. -/
def minSum (m : ℕ) : ℕ := ∑ i ∈ range m, i

/-- The maximal `m`-subset sum of `range n`: `(n-m)+…+(n-1)`. -/
def maxSum (n m : ℕ) : ℕ := ∑ i ∈ Ico (n - m) n, i

theorem two_mul_minSum (m : ℕ) : 2 * minSum m = m * (m - 1) := by
  rw [minSum, mul_comm, Finset.sum_range_id_mul_two]

@[simp] theorem maxSum_zero (n : ℕ) : maxSum n 0 = 0 := by
  simp [maxSum]

@[simp] theorem minSum_zero : minSum 0 = 0 := by
  simp [minSum]

theorem maxSum_add (n m : ℕ) (hm : m ≤ n) : maxSum n m + minSum (n - m) = minSum n := by
  rw [maxSum, minSum, minSum, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n m), add_comm]

theorem two_mul_maxSum (n m : ℕ) (hm : m ≤ n) :
    2 * maxSum n m = n * (n - 1) - (n - m) * (n - m - 1) := by
  have h := maxSum_add n m hm
  have h2 : 2 * (maxSum n m + minSum (n - m)) = 2 * minSum n := by rw [h]
  rw [Nat.mul_add, two_mul_minSum, two_mul_minSum] at h2
  omega

/-- Superadditivity of triangular numbers: `T_a + T_b ≤ T_{a+b}`. -/
theorem minSum_superadd (a b : ℕ) : minSum a + minSum b ≤ minSum (a + b) := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0; simp
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · subst hb0; simp
  have ha := two_mul_minSum a
  have hb := two_mul_minSum b
  have hab := two_mul_minSum (a + b)
  -- with a,b ≥ 1: (a+b)(a+b-1) = a(a-1)+b(b-1)+2ab
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0.ne'
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0.ne'
  simp only [Nat.succ_eq_add_one] at ha hb hab ⊢
  have hexp : (a' + 1 + (b' + 1)) * (a' + 1 + (b' + 1) - 1)
      = (a' + 1) * (a' + 1 - 1) + (b' + 1) * (b' + 1 - 1) + 2 * ((a' + 1) * (b' + 1)) := by
    have e1 : a' + 1 - 1 = a' := by omega
    have e2 : b' + 1 - 1 = b' := by omega
    have e3 : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
    rw [e1, e2, e3]; ring
  omega

/-- Peeling the top element off the maximal `m`-window: `maxSum (n+1) m = maxSum n (m-1) + n`. -/
theorem maxSum_succ_left (n m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n + 1) :
    maxSum (n + 1) m = maxSum n (m - 1) + n := by
  have hidx : n + 1 - m = n - (m - 1) := by omega
  have hle : n - (m - 1) ≤ n := Nat.sub_le _ _
  rw [maxSum, hidx, Finset.sum_Ico_succ_top hle, maxSum]

/-- **Contiguity.** Every integer `T ∈ [minSum m, maxSum n m]` is realized as the sum of some
`m`-element subset of `range n` (with `m ≤ n`). Proof by induction on `n`. -/
theorem exists_subset_sum (n : ℕ) :
    ∀ (m T : ℕ), m ≤ n → minSum m ≤ T → T ≤ maxSum n m →
      ∃ R ⊆ range n, R.card = m ∧ ∑ i ∈ R, i = T := by
  induction n with
  | zero =>
    intro m T hm hmin hmax
    interval_cases m
    refine ⟨∅, by simp, by simp, ?_⟩
    rw [maxSum_zero] at hmax
    rw [Finset.sum_empty]; omega
  | succ n ih =>
    intro m T hm hmin hmax
    -- m = 0 case: T = 0, R = ∅
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      refine ⟨∅, by simp, by simp, ?_⟩
      rw [maxSum_zero] at hmax
      rw [Finset.sum_empty]; omega
    -- m ≥ 1.  Decide whether we can avoid the top element n.
    by_cases hcase : m ≤ n ∧ T ≤ maxSum n m
    · -- don't use n: apply IH on range n
      obtain ⟨hmn, hTmax⟩ := hcase
      obtain ⟨R, hRsub, hRcard, hRsum⟩ := ih m T hmn hmin hTmax
      refine ⟨R, hRsub.trans ?_, hRcard, hRsum⟩
      exact Finset.range_subset_range.mpr (Nat.le_succ n)
    · -- must use n: build insert n R' with R' an (m-1)-subset of range n
      -- arithmetic: need minSum (m-1) ≤ T - n ≤ maxSum n (m-1) and m-1 ≤ n
      have hmaxn1 : m - 1 ≤ n := by omega
      -- the peel-off identity: maxSum (n+1) m = maxSum n (m-1) + n
      have hpeel : maxSum (n + 1) m = maxSum n (m - 1) + n :=
        maxSum_succ_left n m hmpos hm
      -- minSum recursion: minSum m = minSum (m-1) + (m-1)
      have hminrec : minSum m = minSum (m - 1) + (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        rw [minSum, minSum, Finset.sum_range_succ]
      -- derive: minSum (m-1) + n ≤ T
      have hlow : minSum (m - 1) + n ≤ T := by
        rcases Nat.lt_or_ge n m with hlt | hge
        · -- m = n+1: only the full set; minSum m ≤ T, and minSum m = minSum(m-1)+n
          have hmeq : m = n + 1 := by omega
          have : minSum m = minSum (m - 1) + n := by
            rw [hminrec]; omega
          omega
        · -- m ≤ n and ¬(T ≤ maxSum n m), so T > maxSum n m
          have hTgt : maxSum n m < T := by
            by_contra hcon
            exact hcase ⟨hge, by omega⟩
          -- overlap: minSum (m-1) + n ≤ maxSum n m + 1, via superadditivity
          have hoverlap : minSum (m - 1) + n ≤ maxSum n m + 1 := by
            have hadd := maxSum_add n m hge
            have hsup := minSum_superadd (m - 1) (n - m)
            have heqn : (m - 1) + (n - m) = n - 1 := by omega
            have hminn : minSum n = minSum (n - 1) + (n - 1) := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega]
              rw [minSum, minSum, Finset.sum_range_succ]
            rw [heqn] at hsup
            omega
          omega
      -- upper bound: T ≤ maxSum n (m-1) + n
      have hup : T ≤ maxSum n (m - 1) + n := by rw [← hpeel]; exact hmax
      -- now build the subset via IH for (m-1, T-n) on range n
      obtain ⟨R', hR'sub, hR'card, hR'sum⟩ :=
        ih (m - 1) (T - n) hmaxn1 (by omega) (by omega)
      -- n ∉ R' since R' ⊆ range n
      have hnnotin : n ∉ R' := fun h => by simpa using hR'sub h
      refine ⟨insert n R', ?_, ?_, ?_⟩
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · simp
        · exact (Finset.range_subset_range.mpr (Nat.le_succ n)) (hR'sub hx)
      · rw [Finset.card_insert_of_notMem hnnotin, hR'card]; omega
      · rw [sum_insert hnnotin, hR'sum]; omega

/-- The additive law for triangular numbers: `T_{a+b} = T_a + a*b + T_b`. -/
theorem minSum_add_eq (a b : ℕ) : minSum (a + b) = minSum a + a * b + minSum b := by
  induction b with
  | zero => simp [minSum]
  | succ b ih =>
    have h1 : a + (b + 1) = (a + b) + 1 := by ring
    rw [h1, minSum, Finset.sum_range_succ, ← minSum, ih]
    -- minSum (a+b) + (a+b) = minSum a + a*b + minSum b + (a+b)
    have h2 : minSum (b + 1) = minSum b + b := by
      rw [minSum, Finset.sum_range_succ, ← minSum]
    rw [h2]; ring

/-- The window length: `maxSum n m = minSum m + m*(n-m)` for `m ≤ n`. -/
theorem maxSum_eq_minSum_add (n m : ℕ) (hm : m ≤ n) :
    maxSum n m = minSum m + m * (n - m) := by
  have hadd := maxSum_add n m hm
  -- minSum n = minSum (m + (n-m)) = minSum m + m*(n-m) + minSum (n-m)
  have hsplit : minSum n = minSum m + m * (n - m) + minSum (n - m) := by
    conv_lhs => rw [show n = m + (n - m) from by omega]
    rw [minSum_add_eq]
  omega

/-- **Subset-sum surjectivity mod `n`.** For `2 ≤ n` and `1 ≤ m ≤ n-1`, the `m`-subset sums of
`{0,…,n-1}` hit every residue mod `n`. -/
theorem subset_sum_surj_zmod (n m : ℕ) (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hm2 : m ≤ n - 1)
    (t : ZMod n) :
    ∃ R ⊆ range n, R.card = m ∧ ((∑ i ∈ R, i : ℕ) : ZMod n) = t := by
  have hmn : m ≤ n := by omega
  -- run of n consecutive sums [minSum m, minSum m + (n-1)] is inside [minSum m, maxSum n m]
  have hlen : minSum m + (n - 1) ≤ maxSum n m := by
    rw [maxSum_eq_minSum_add n m hmn]
    have hmlb : n - 1 ≤ m * (n - m) := by
      -- m*(n-m) = (m-1)*(n-m-1) + (n-1)
      have hkey : m * (n - m) = (m - 1) * (n - m - 1) + (n - 1) := by
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hnm : 1 ≤ n - (m' + 1) := by omega
        obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - (m' + 1) ≠ 0)
        rw [hc]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        have hn1 : n - 1 = m' + (c + 1) := by omega
        rw [hn1]; ring
      omega
    omega
  have hnpos : 0 < n := by omega
  have hNZ : NeZero n := ⟨by omega⟩
  set s := minSum m with hs
  -- pick u with (u : ZMod n) = t - s, then i = u % n < n, and (s + i : ZMod n) = t.
  obtain ⟨u, hu⟩ := ZMod.natCast_zmod_surjective (t - (s : ZMod n))
  set i := u % n with hi
  have hilt : i < n := Nat.mod_lt _ hnpos
  obtain ⟨R, hRsub, hRcard, hRsum⟩ := exists_subset_sum n m (s + i) hmn (by omega) (by omega)
  refine ⟨R, hRsub, hRcard, ?_⟩
  rw [hRsum]
  -- (s + i : ZMod n) = s + u = s + (t - s) = t
  have hicast : (i : ZMod n) = (u : ZMod n) := by rw [hi, ZMod.natCast_mod]
  push_cast
  rw [hicast, hu]
  ring

/-! ## Part B: transport to subset-products over `μ_n`, discharging `SubsetProductSurjectsMu`. -/

open Polynomial in
/-- `nthRootsFinset n 1` is the `(ζ ^ ·)`-image of `range n` for a primitive `n`-th root `ζ`. -/
theorem nthRootsFinset_eq_image_pow {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    nthRootsFinset n (1 : F) = (range n).image (ζ ^ ·) := by
  have hsub : (range n).image (ζ ^ ·) ⊆ nthRootsFinset n (1 : F) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hζ.injOn_pow, Finset.card_range]

open Polynomial in
/-- **The subset-product surjectivity over `μ_n` (PROVED).**  For a primitive `n`-th root `ζ`
in a field `F`, with `2 ≤ n` and `1 ≤ k+1 ≤ n-1`, the `(k+1)`-subset products of `nthRootsFinset n 1`
realize *all* of `nthRootsFinset n 1`. This discharges `B1CountLaw.SubsetProductSurjectsMu` for
`nodes = nthRootsFinset n 1`, `v = id`. -/
theorem subsetProducts_id_eq_nthRoots {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k + 1) (hk2 : k + 1 ≤ n - 1) :
    ProximityGap.B1CountLaw.subsetProducts (nthRootsFinset n (1 : F)) id k
      = nthRootsFinset n (1 : F) := by
  have hnpos : 0 < n := by omega
  have horder : orderOf ζ = n := hζ.eq_orderOf.symm
  apply Finset.Subset.antisymm
  · -- products of nth-roots are nth-roots
    have := ProximityGap.B1CountLaw.subsetProducts_subset_nthRoots
      (nthRootsFinset n (1 : F)) id n k hnpos
      (fun i hi => by simpa using (Polynomial.mem_nthRootsFinset hnpos (1 : F)).mp hi)
    simpa using this
  · -- every nth-root is realized
    intro y hy
    -- write y = ζ ^ t with t < n
    rw [nthRootsFinset_eq_image_pow hζ hnpos, Finset.mem_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    -- surjectivity gives an exponent set S of size k+1 with sum ≡ t mod n
    obtain ⟨S, hSsub, hScard, hSsum⟩ :=
      subset_sum_surj_zmod n (k + 1) hn hk1 hk2 (t : ZMod n)
    -- R := image of S under ζ^·, inside nthRootsFinset
    rw [ProximityGap.B1CountLaw.subsetProducts, Finset.mem_image]
    refine ⟨S.image (ζ ^ ·), ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      have hSinjOn : Set.InjOn (ζ ^ ·) (S : Set ℕ) :=
        hζ.injOn_pow.mono (by exact_mod_cast hSsub)
      refine ⟨?_, ?_⟩
      · rw [nthRootsFinset_eq_image_pow hζ hnpos]
        exact Finset.image_subset_image hSsub
      · rw [Finset.card_image_of_injOn hSinjOn, hScard]
    · -- ∏_{x ∈ S.image (ζ^·)} x = ζ ^ (∑ S) = ζ ^ t
      have hSinjOn : Set.InjOn (ζ ^ ·) (S : Set ℕ) :=
        hζ.injOn_pow.mono (by exact_mod_cast hSsub)
      rw [Finset.prod_image (fun a ha b hb => hSinjOn ha hb)]
      simp only [id_eq]
      rw [Finset.prod_pow_eq_pow_sum]
      -- ζ ^ (∑ S) = ζ ^ t  since ∑ S ≡ t mod n and ζ^n = 1
      have hmod : (∑ i ∈ S, i) ≡ t [MOD n] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        exact hSsum
      exact pow_eq_pow_of_modEq hmod hζ.pow_eq_one

open Polynomial in
/-- **`SubsetProductSurjectsMu` DISCHARGED** for the canonical `μ_n` instance (a field `F` with a
primitive `n`-th root `ζ`, `nodes = nthRootsFinset n 1`, `v = id`). -/
theorem subsetProductSurjectsMu_holds {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    ProximityGap.B1CountLaw.SubsetProductSurjectsMu (nthRootsFinset n (1 : F)) id n k :=
  subsetProducts_id_eq_nthRoots hζ hn k (by omega) (by omega)

open Polynomial in
/-- **B1 TOP-DIRECTION COUNT LAW, UNCONDITIONAL `= n`.**
For a field `F` carrying a primitive `n`-th root `ζ` (`2 ≤ n`) and `1 ≤ k ≤ n-2`, the number of
distinct B1 top-direction divided-difference readouts over `(k+1)`-subsets of `μ_n = nthRootsFinset n 1`
is **exactly `n`** — no residual. This combines the proven `≤ n` collapse with the now-discharged
subset-product surjectivity `subsetProducts_id_eq_nthRoots`. -/
theorem topReadouts_card_eq_n_unconditional {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    (ProximityGap.B1CountLaw.topReadouts (nthRootsFinset n (1 : F)) id n k).card = n := by
  have hnpos : 0 < n := by omega
  refine ProximityGap.B1CountLaw.topReadouts_card_eq_n_of_surjects
    (nthRootsFinset n (1 : F)) id n k hnpos (by omega) ?_ ?_ ?_ ?_
  · -- InjOn id
    exact Set.injOn_id _
  · -- nodes are nth roots
    intro i hi
    simpa using (Polynomial.mem_nthRootsFinset hnpos (1 : F)).mp hi
  · -- surjectivity (the discharged residual)
    exact subsetProductSurjectsMu_holds hζ hn k hk1 hk2
  · -- full root group has card n
    exact hζ.card_nthRootsFinset

end SubsetSurj

set_option linter.style.longLine false in
#print axioms SubsetSurj.exists_subset_sum
set_option linter.style.longLine false in
#print axioms SubsetSurj.subset_sum_surj_zmod
set_option linter.style.longLine false in
#print axioms SubsetSurj.subsetProducts_id_eq_nthRoots
set_option linter.style.longLine false in
#print axioms SubsetSurj.subsetProductSurjectsMu_holds
set_option linter.style.longLine false in
#print axioms SubsetSurj.topReadouts_card_eq_n_unconditional
