/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeightedPrimePowerPacket
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Issue #232 — multiset antipodal balance over 2-power roots of unity

The O108 census layer consumes "2-power Lam–Leung in multiset form": a finite
multiset of `2^k`-th roots of unity (char 0) sums to zero **iff** its counting
function is antipodally balanced — `count z = count (-z)` for every `z`.  The
in-tree set-form lemmas (`LamLeungUnconditionalGeneral.antipodal_of_sum_zero`)
state this for subsets; this file lands the multiset upgrade, the named O108
Lean follow-up.

* `count_antipodal_of_sum_eq_zero` — **the forward direction**: a vanishing
  multiset sum over `μ_{2^k}` forces `count z = count (-z)` for all `z`.
  Route: the subgroup `rootsOfUnity (2^k) L` is finite cyclic of order `2^j`
  (`j ≥ 1` since `-1` is a `2^k`-th root for `k ≥ 1`); a generator `ζ` is a
  primitive `2^j`-th root, every multiset element is a power `ζ^e`, and the
  counting function transported to `ZMod (2^j)` satisfies the O96 weighted
  prime-power packet theorem
  (`WeightedPrimePowerPacket.debruijn_prime_power_weighted` at `p = 2`), whose
  half-period shift `e ↦ e + 2^(j-1)` is exactly negation (`ζ^(2^(j-1)) = -1`).
* `sum_eq_zero_of_count_antipodal` — the converse: antipodal balance kills the
  sum by the fixed-point-free pairing `z ↦ -z` (`Finset.sum_involution`); only
  `0 ∉ M` is needed, no root-of-unity structure.
* `multiset_antipodal_iff` — the iff, hypotheses exactly as the O108 layer
  uses them (`∀ z ∈ M, z ^ 2^k = 1`).

Teeth at `ℂ`: `{I, I, -I, -I}` vanishes by the converse (genuine multiplicity
2); the forward direction refutes `{1, I}` (it would force
`count 1 = count (-1)`, i.e. `1 = 0`).
-/

namespace LamLeungMultisetAntipodal

open Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- Powers of an `n`-torsion element only see exponents mod `n`. -/
private lemma pow_mod_eq {ζ : L} {n : ℕ} (hζ : ζ ^ n = 1) (a : ℕ) :
    ζ ^ (a % n) = ζ ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, hζ, one_pow, mul_one]

omit [CharZero L] in
/-- `ζ^((e+c).val) = ζ^(e.val) * ζ^(c.val)` for `n`-torsion `ζ` and
`e c : ZMod n`. -/
private lemma pow_val_add {ζ : L} {n : ℕ} [NeZero n] (hζ : ζ ^ n = 1)
    (e c : ZMod n) : ζ ^ (e + c).val = ζ ^ e.val * ζ ^ c.val := by
  rw [ZMod.val_add, pow_mod_eq hζ, pow_add]

variable [DecidableEq L]

omit [CharZero L] in
/-- Multiset sum as a count-weighted finset sum. -/
private lemma sum_eq_count_sum (M : Multiset L) :
    M.sum = ∑ z ∈ M.toFinset, M.count z • z := by
  conv_lhs => rw [← Multiset.map_id M]
  rw [Finset.sum_multiset_map_count]
  rfl

/-- **The converse (pairing)**: an antipodally balanced multiset avoiding `0`
sums to zero — no root-of-unity structure needed. -/
theorem sum_eq_zero_of_count_antipodal {M : Multiset L} (h0 : (0 : L) ∉ M)
    (hbal : ∀ z : L, M.count z = M.count (-z)) : M.sum = 0 := by
  rw [sum_eq_count_sum]
  refine Finset.sum_involution (g := fun z _ => -z) ?_ ?_ ?_ ?_
  · intro a _
    rw [← hbal a, smul_neg, add_neg_cancel]
  · intro a ha _ hcontra
    have haM : a ∈ M := Multiset.mem_toFinset.mp ha
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ haM)
    exact ha0 (add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp hcontra))
  · intro a ha
    have haM : a ∈ M := Multiset.mem_toFinset.mp ha
    have hpos : 0 < M.count a := Multiset.count_pos.mpr haM
    have hpos' : 0 < M.count (-a) := hbal a ▸ hpos
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hpos')
  · intro a _
    exact neg_neg a

omit [DecidableEq L] in
/-- The structural core: for `k ≥ 1` there is a primitive `2^j`-th root
`ζ ∈ L` (`j ≥ 1`) whose powers exhaust the `2^k`-th roots of unity of `L`. -/
private lemma exists_primitive_generator {k : ℕ} (hk : 1 ≤ k) :
    ∃ (j : ℕ) (ζ : L), 1 ≤ j ∧ IsPrimitiveRoot ζ (2 ^ j) ∧
      ∀ z : L, z ^ (2 ^ k) = 1 → ∃ e, e < 2 ^ j ∧ z = ζ ^ e := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity (2 ^ k) L)
  set ζ : L := ((g : Lˣ) : L) with hζdef
  have hgpow : ζ ^ (2 ^ k) = 1 := by
    have hmem := g.2
    rw [mem_rootsOfUnity'] at hmem
    exact hmem
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one hgpow)
  have horderG : orderOf g = orderOf ζ := by
    rw [hζdef, orderOf_units]
    exact (orderOf_injective (rootsOfUnity (2 ^ k) L).subtype
      Subtype.coe_injective g).symm
  -- `-1` is a `2^k`-th root of unity, of order 2, dividing `orderOf g = 2^j`
  have hneg1 : (-1 : Lˣ) ∈ rootsOfUnity (2 ^ k) L := by
    rw [mem_rootsOfUnity]
    refine Even.neg_one_pow ⟨2 ^ (k - 1), ?_⟩
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hj1 : 1 ≤ j := by
    by_contra hj0
    have hj0' : j = 0 := by omega
    have hord2 : orderOf (⟨-1, hneg1⟩ : rootsOfUnity (2 ^ k) L) ∣ orderOf g :=
      orderOf_dvd_of_mem_zpowers (hg _)
    have hcoe : orderOf (⟨-1, hneg1⟩ : rootsOfUnity (2 ^ k) L)
        = orderOf (-1 : Lˣ) :=
      (orderOf_injective (rootsOfUnity (2 ^ k) L).subtype
        Subtype.coe_injective ⟨-1, hneg1⟩).symm
    have hLneg : orderOf (-1 : Lˣ) = orderOf (-1 : L) := by
      conv_rhs => rw [show (-1 : L) = ((-1 : Lˣ) : L) by simp]
      rw [orderOf_units]
    have hchar : ringChar L ≠ 2 := by
      rw [ringChar.eq_zero (R := L)]
      omega
    have hord_neg : orderOf (-1 : L) = 2 := by
      rw [orderOf_neg_one, if_neg hchar]
    rw [hcoe, hLneg, hord_neg, horderG, hj, hj0', pow_zero] at hord2
    omega
  refine ⟨j, ζ, hj1, hj ▸ IsPrimitiveRoot.orderOf ζ, ?_⟩
  intro z hz1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hz1
    exact zero_ne_one hz1
  have hzu : IsUnit z := IsUnit.mk0 z hz0
  have hzG : hzu.unit ∈ rootsOfUnity (2 ^ k) L := by
    rw [mem_rootsOfUnity']
    rw [IsUnit.unit_spec]
    exact hz1
  obtain ⟨m, hm⟩ := hg ⟨hzu.unit, hzG⟩
  have horder_pos : 0 < orderOf g := orderOf_pos g
  set e : ℕ := (m % (orderOf g : ℤ)).toNat with he
  have hmod_nonneg : 0 ≤ m % (orderOf g : ℤ) :=
    Int.emod_nonneg m (by exact_mod_cast horder_pos.ne')
  have hge : g ^ e = g ^ m := by
    rw [he, ← zpow_natCast, Int.toNat_of_nonneg hmod_nonneg, zpow_mod_orderOf]
  refine ⟨e, ?_, ?_⟩
  · have hlt : (e : ℤ) < (orderOf g : ℤ) := by
      rw [he, Int.toNat_of_nonneg hmod_nonneg]
      exact Int.emod_lt_of_pos m (by exact_mod_cast horder_pos)
    have : e < orderOf g := by exact_mod_cast hlt
    rwa [horderG, hj] at this
  · have hcoe := congrArg
      (fun x : rootsOfUnity (2 ^ k) L => ((x : Lˣ) : L)) (hge.trans hm)
    simpa [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec, hζdef] using hcoe.symm

/-- **The forward direction (the O108 multiset upgrade)**: a vanishing multiset
sum of `2^k`-th roots of unity in characteristic zero is antipodally balanced:
`count z = count (-z)` for every `z`. -/
theorem count_antipodal_of_sum_eq_zero {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hsum : M.sum = 0) :
    ∀ z : L, M.count z = M.count (-z) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: every element is `1`, so the sum is the cast cardinality.
    have hone : ∀ z ∈ M, z = (1 : L) := by
      intro z hz
      simpa using hM z hz
    have hrep : M = Multiset.replicate (Multiset.card M) (1 : L) :=
      Multiset.eq_replicate_card.mpr hone
    have hcard : ((Multiset.card M : ℕ) : L) = 0 := by
      calc ((Multiset.card M : ℕ) : L)
          = (Multiset.replicate (Multiset.card M) (1 : L)).sum := by
            rw [Multiset.sum_replicate, nsmul_eq_mul, mul_one]
        _ = M.sum := by rw [← hrep]
        _ = 0 := hsum
    have hM0 : M = 0 := by
      have : Multiset.card M = 0 := by exact_mod_cast hcard
      exact Multiset.card_eq_zero.mp this
    simp [hM0]
  obtain ⟨j, ζ, hj1, hζprim, hpow⟩ := exists_primitive_generator (L := L) hk
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hζtor : ζ ^ (2 ^ (j' + 1)) = 1 := hζprim.pow_eq_one
  haveI : NeZero (2 ^ (j' + 1)) := ⟨by positivity⟩
  set w : ZMod (2 ^ (j' + 1)) → ℕ := fun e => M.count (ζ ^ e.val) with hw
  have hmem_pow : ∀ z ∈ M, ∃ e, e < 2 ^ (j' + 1) ∧ z = ζ ^ e :=
    fun z hz => hpow z (hM z hz)
  have hφinj : Function.Injective
      (fun e : ZMod (2 ^ (j' + 1)) => ζ ^ e.val) := by
    intro e e' hee
    exact ZMod.val_injective _
      (hζprim.pow_inj (ZMod.val_lt e) (ZMod.val_lt e') hee)
  -- transport the vanishing sum to the `ZMod` weight surface
  have htrans : ∑ e : ZMod (2 ^ (j' + 1)), (w e : L) * ζ ^ e.val = M.sum := by
    have himg : M.toFinset ⊆
        Finset.univ.image (fun e : ZMod (2 ^ (j' + 1)) => ζ ^ e.val) := by
      intro z hz
      obtain ⟨e, helt, rfl⟩ := hmem_pow z (Multiset.mem_toFinset.mp hz)
      exact Finset.mem_image.mpr ⟨(e : ZMod (2 ^ (j' + 1))),
        Finset.mem_univ _, by rw [ZMod.val_cast_of_lt helt]⟩
    calc ∑ e : ZMod (2 ^ (j' + 1)), (w e : L) * ζ ^ e.val
        = ∑ e : ZMod (2 ^ (j' + 1)), M.count (ζ ^ e.val) • ζ ^ e.val :=
          Finset.sum_congr rfl fun e _ => by rw [hw, nsmul_eq_mul]
      _ = ∑ z ∈ Finset.univ.image
            (fun e : ZMod (2 ^ (j' + 1)) => ζ ^ e.val), M.count z • z := by
          rw [Finset.sum_image (fun e _ e' _ h => hφinj h)]
      _ = ∑ z ∈ M.toFinset, M.count z • z := by
          refine (Finset.sum_subset himg fun z _ hz => ?_).symm
          rw [Multiset.count_eq_zero_of_notMem
            (fun hmem => hz (Multiset.mem_toFinset.mpr hmem)), zero_smul]
      _ = M.sum := (sum_eq_count_sum M).symm
  -- O96 at `p = 2`, `a = j'`
  have hO96 := (WeightedPrimePowerPacket.debruijn_prime_power_weighted
    (p := 2) (a := j') Nat.prime_two hζprim (w := w)).mp
    (by rw [htrans]; exact hsum)
  -- the half-period power is `-1`
  have hhalf : ζ ^ (2 ^ j') = -1 := by
    have hsq : (ζ ^ (2 ^ j')) * (ζ ^ (2 ^ j')) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hζtor
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have hdvd : orderOf ζ ∣ 2 ^ j' := orderOf_dvd_of_pow_eq_one h1
      have hord : orderOf ζ = 2 ^ (j' + 1) := hζprim.eq_orderOf.symm
      rw [hord] at hdvd
      have hle := Nat.le_of_dvd (by positivity) hdvd
      have hlt : (2 : ℕ) ^ j' < 2 ^ (j' + 1) := by
        rw [pow_succ]
        have : 0 < (2 : ℕ) ^ j' := by positivity
        omega
      omega
    · exact h1
  have h2pos : 0 < (2 : ℕ) ^ j' := by positivity
  have hcval : ((2 ^ j' : ℕ) : ZMod (2 ^ (j' + 1))).val = 2 ^ j' := by
    apply ZMod.val_cast_of_lt
    rw [pow_succ]
    omega
  -- antipodal balance on the powers of `ζ`
  have hbal_pow : ∀ e : ZMod (2 ^ (j' + 1)),
      M.count (ζ ^ e.val) = M.count (-(ζ ^ e.val)) := by
    intro e
    have hexp : ζ ^ (e + ((2 ^ j' : ℕ) : ZMod (2 ^ (j' + 1)))).val
        = -(ζ ^ e.val) := by
      rw [pow_val_add hζtor, hcval, hhalf, mul_neg_one]
    calc M.count (ζ ^ e.val)
        = w e := rfl
      _ = w (e + ((2 ^ j' : ℕ) : ZMod (2 ^ (j' + 1)))) := (hO96 e).symm
      _ = M.count (-(ζ ^ e.val)) := by rw [hw]; simp only []; rw [hexp]
  -- conclude for arbitrary `z`
  intro z
  by_cases hzim : ∃ e : ZMod (2 ^ (j' + 1)), z = ζ ^ e.val
  · obtain ⟨e, rfl⟩ := hzim
    exact hbal_pow e
  · have hz0 : M.count z = 0 := by
      rw [Multiset.count_eq_zero]
      intro hzM
      obtain ⟨e, helt, rfl⟩ := hmem_pow z hzM
      exact hzim ⟨(e : ZMod (2 ^ (j' + 1))), by rw [ZMod.val_cast_of_lt helt]⟩
    have hz0' : M.count (-z) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hzM
      obtain ⟨e, helt, hze⟩ := hmem_pow (-z) hzM
      apply hzim
      refine ⟨(e : ZMod (2 ^ (j' + 1)))
        + ((2 ^ j' : ℕ) : ZMod (2 ^ (j' + 1))), ?_⟩
      rw [pow_val_add hζtor, ZMod.val_cast_of_lt helt, hcval, hhalf,
        mul_neg_one, ← hze, neg_neg]
    rw [hz0, hz0']

/-- **The multiset antipodal iff** (the O108 census-layer form): a finite
multiset of `2^k`-th roots of unity in characteristic zero sums to zero iff its
counting function is antipodally balanced. -/
theorem multiset_antipodal_iff {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) :
    M.sum = 0 ↔ ∀ z : L, M.count z = M.count (-z) := by
  refine ⟨count_antipodal_of_sum_eq_zero hM, fun hbal =>
    sum_eq_zero_of_count_antipodal (fun h0 => ?_) hbal⟩
  have h1 := hM 0 h0
  rw [zero_pow (by positivity)] at h1
  exact zero_ne_one h1

/-! ## Teeth (fired at `ℂ`, genuine multiplicity) -/

/-- The converse manufactures the genuinely weighted vanishing
`I + I + (-I) + (-I) = 0` (multiplicity 2 on each antipode). -/
example : ({Complex.I, Complex.I, -Complex.I, -Complex.I} :
    Multiset ℂ).sum = 0 := by
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons,
    Multiset.sum_singleton]
  ring

/-- The forward direction refutes `{1, I}`: its vanishing would force
`count 1 = count (-1)`, i.e. `1 = 0`. -/
example : ({1, Complex.I} : Multiset ℂ).sum ≠ 0 := by
  intro hsum
  have hM : ∀ z ∈ ({1, Complex.I} : Multiset ℂ), z ^ (2 ^ 2) = 1 := by
    intro z hz
    rw [Multiset.insert_eq_cons] at hz
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · norm_num
    · rw [Multiset.mem_singleton.mp hz]
      norm_num [show (2:ℕ)^2 = 4 from rfl, show (4:ℕ) = 2 * 2 from rfl,
        pow_mul, Complex.I_sq]
  have hbal := count_antipodal_of_sum_eq_zero hM hsum 1
  have hI1 : Complex.I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hI1' : Complex.I ≠ -1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hneg : (-1 : ℂ) ≠ 1 := by norm_num
  rw [Multiset.insert_eq_cons, Multiset.count_cons_self,
    Multiset.count_singleton, if_neg hI1.symm.elim, Multiset.count_cons,
    if_neg (by norm_num : (-1 : ℂ) ≠ 1), Multiset.count_singleton,
    if_neg fun h => hI1' (by rw [h])] at hbal
  · simp at hbal

end LamLeungMultisetAntipodal
