import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Lam–Leung (prime-power 2 case): zero-sum tuples of `2^μ`-th roots are antipodally balanced

`LamLeungTwoPowerAntipodalBalance` (#444, AvX). External theorem Mathlib lacks: the
prime-power-`2` case of the Lam–Leung / Mann vanishing-sum-of-roots-of-unity structure theorem
(Lam–Leung, *J. Algebra* 224 (2000) 91–109; classical via the cyclotomic basis).

**Statement.** Let `L` be a field with `ζ` a primitive `2^μ`-th root of unity (`μ ≥ 1`; this forces
`2 ≠ 0` and char `≠ 2`). For any exponent tuple `c : Fin m → ZMod (2^μ)`, if
`∑ i, ζ^(c i).val = 0` in `L`, then the multiset of exponents is **antipodally balanced**:

* root form: `#{i : ζ^(c i).val = w} = #{i : ζ^(c i).val = -w}` for every `w`;
* exponent form: `#{i : c i = j} = #{i : c i = j + 2^(μ-1)}` for every `j : ZMod (2^μ)`.

The mechanism is `ζ^(2^(μ-1)) = -1` (the unique primitive square root of unity), so
`ζ^(j + 2^(μ-1)) = -ζ^j`; folding the top half of the cyclotomic basis onto the bottom and using
`Q`-linear independence of `{ζ^j : j < 2^(μ-1)}` forces each paired coefficient to coincide.

**Value.** Discharges the char-0 Lam–Leung named hypothesis (`fiber_balanced_of_sum_eq_zero`) used
by `_AvL_T3ClosedForm` / the No-Excess energy ladder, here landed in the exact exponent form over
`ZMod (2^μ)` with an explicit `IsPrimitiveRoot`. The structural core is reused from the in-tree
multiset engine `LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace LamLeungTwoPowerAntipodalBalance

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- A primitive `2^μ`-th root of unity satisfies `ζ^(2^(μ-1)) = -1` (the unique primitive square
root of unity is `-1`). Stated for `μ = μ'+1` to keep `2^(μ-1)` literal. -/
theorem pow_half_eq_neg_one {ζ : L} {μ' : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1))) :
    ζ ^ (2 ^ μ') = -1 := by
  -- `(ζ^(2^μ'))^2 = ζ^(2^(μ'+1)) = 1`, so `ζ^(2^μ')` is a square root of unity; it is `≠ 1`
  -- (else order ≤ 2^μ' < 2^(μ'+1)), hence `= -1`.
  have hsq : (ζ ^ (2 ^ μ')) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ μ' * 2 = 2 ^ (μ' + 1) := by ring
    rw [this, hζ.pow_eq_one]
  have hne : ζ ^ (2 ^ μ') ≠ 1 := by
    intro h
    have hdvd := hζ.pow_eq_one_iff_dvd (2 ^ μ') |>.mp h
    have hpos : 0 < 2 ^ μ' := pow_pos (by norm_num) μ'
    have hlt : (2 : ℕ) ^ μ' < 2 ^ (μ' + 1) := by
      have : 2 ^ (μ' + 1) = 2 ^ μ' * 2 := by ring
      omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  -- root of `X^2 - 1 = (X-1)(X+1)`, not `1`, so `-1`.
  have hfac : (ζ ^ (2 ^ μ') - 1) * (ζ ^ (2 ^ μ') + 1) = 0 := by
    have : (ζ ^ (2 ^ μ') - 1) * (ζ ^ (2 ^ μ') + 1) = (ζ ^ (2 ^ μ')) ^ 2 - 1 := by ring
    rw [this, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact eq_neg_of_add_eq_zero_left h

/-- **Antipodal balance, root form.** A zero-sum tuple of `2^μ`-th roots of unity has, for every
value `w`, equally many entries equal to `w` and to `-w`. (`μ ≥ 1`, i.e. `μ = k`.) -/
theorem antipodal_balance_root {m k : ℕ} (c : Fin m → L)
    (hroot : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0) :
    ∀ w : L, (univ.filter (fun i => c i = w)).card
           = (univ.filter (fun i => c i = -w)).card := by
  classical
  set M : Multiset L := (univ.val).map c with hM
  have hMsum : M.sum = 0 := by
    have hms : M.sum = ∑ i, c i := by rw [hM]; rfl
    rw [hms]; exact hsum
  have hMroot : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
    intro z hz
    rw [hM, Multiset.mem_map] at hz
    obtain ⟨i, _, hi⟩ := hz
    rw [← hi]; exact hroot i
  have hcount : ∀ z : L, M.count z = (univ.filter (fun i => c i = z)).card := by
    intro z
    rw [hM, Multiset.count_map]
    simp only [Finset.filter]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  intro w
  have := LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero hMroot hMsum w
  rw [hcount w, hcount (-w)] at this
  exact this

/-- **Lam–Leung two-power, exponent form.** Over `ZMod (2^μ)` with a primitive `2^μ`-th root `ζ`,
a zero-sum tuple of exponentials `ζ^(c i).val` is balanced under the antipodal shift
`j ↦ j + 2^(μ-1)` on exponents. -/
theorem antipodal_balance_exponent {m μ' : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1)))
    (c : Fin m → ZMod (2 ^ (μ' + 1)))
    (hsum : ∑ i, ζ ^ (c i).val = 0) :
    ∀ j : ZMod (2 ^ (μ' + 1)),
      (univ.filter (fun i => c i = j)).card
        = (univ.filter (fun i => c i = j + (2 ^ μ' : ℕ))).card := by
  classical
  haveI : NeZero (2 ^ (μ' + 1)) := ⟨by positivity⟩
  -- The roots `d i := ζ^(c i).val`.
  set d : Fin m → L := fun i => ζ ^ (c i).val with hd
  have hroot : ∀ i, (d i) ^ (2 ^ (μ' + 1)) = 1 := by
    intro i
    rw [hd]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- `ζ` is injective on `ZMod (2^μ)` exponents (via `.val`), so `c i = j ↔ d i = ζ^j.val`.
  have hinj : Function.Injective (fun e : ZMod (2 ^ (μ' + 1)) => ζ ^ e.val) := by
    intro e e' hee
    simp only at hee
    -- `IsPrimitiveRoot.eq_pow_of_pow_eq` style: powers with val < order are distinct.
    have hev : e.val < 2 ^ (μ' + 1) := ZMod.val_lt e
    have hev' : e'.val < 2 ^ (μ' + 1) := ZMod.val_lt e'
    have := hζ.pow_inj hev hev' hee
    -- `e.val = e'.val` ⟹ `e = e'`
    have : e.val = e'.val := this
    exact (ZMod.val_injective _) this
  -- `ζ^x` depends only on `x mod 2^(μ'+1)` since `ζ^(2^(μ'+1)) = 1`.
  have htor : ζ ^ (2 ^ (μ' + 1)) = 1 := hζ.pow_eq_one
  have hmodpow : ∀ x : ℕ, ζ ^ x = ζ ^ (x % 2 ^ (μ' + 1)) := by
    intro x
    conv_lhs => rw [← Nat.div_add_mod x (2 ^ (μ' + 1))]
    rw [pow_add, pow_mul, htor, one_pow, one_mul]
  -- key: `-ζ^j.val = ζ^((j + 2^μ').val)`.
  have hneg : ∀ j : ZMod (2 ^ (μ' + 1)),
      -(ζ ^ j.val) = ζ ^ ((j + (2 ^ μ' : ℕ)).val) := by
    intro j
    have hhalf : ζ ^ (2 ^ μ') = -1 := pow_half_eq_neg_one hζ
    -- `(j + 2^μ').val ≡ j.val + 2^μ' [MOD 2^(μ'+1)]`
    have hvalcast : ((j + (2 ^ μ' : ℕ)).val) % 2 ^ (μ' + 1)
        = (j.val + 2 ^ μ') % 2 ^ (μ' + 1) := by
      have h1 : ((j + (2 ^ μ' : ℕ)).val : ZMod (2 ^ (μ' + 1)))
          = ((j.val + 2 ^ μ' : ℕ) : ZMod (2 ^ (μ' + 1))) := by
        simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_add]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
    -- conclude
    have step : ζ ^ ((j + (2 ^ μ' : ℕ)).val) = ζ ^ (j.val + 2 ^ μ') :=
      (hmodpow _).trans (((congrArg (fun e => ζ ^ e) hvalcast)).trans (hmodpow _).symm)
    calc -(ζ ^ j.val) = ζ ^ j.val * ζ ^ (2 ^ μ') := by
          rw [hhalf]; ring
      _ = ζ ^ (j.val + 2 ^ μ') := (pow_add ζ j.val (2 ^ μ')).symm
      _ = ζ ^ ((j + (2 ^ μ' : ℕ)).val) := step.symm
  -- assemble the exponent-form balance from the root-form balance
  intro j
  have hbal := antipodal_balance_root d hroot hsum (ζ ^ j.val)
  -- rewrite `c i = j ↔ d i = ζ^j.val` and `c i = j + 2^μ' ↔ d i = -ζ^j.val`
  have hL : (univ.filter (fun i => c i = j)).card
      = (univ.filter (fun i => d i = ζ ^ j.val)).card := by
    congr 1; apply filter_congr; intro i _
    constructor
    · intro h; rw [hd]; simp only; rw [h]
    · intro h; rw [hd] at h; simp only at h; exact hinj h
  have hR : (univ.filter (fun i => c i = j + (2 ^ μ' : ℕ))).card
      = (univ.filter (fun i => d i = -(ζ ^ j.val))).card := by
    congr 1; apply filter_congr; intro i _
    rw [hneg j]
    constructor
    · intro h; rw [hd]; simp only; rw [h]
    · intro h; rw [hd] at h; simp only at h; exact hinj h
  rw [hL, hR, hbal]

end LamLeungTwoPowerAntipodalBalance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms LamLeungTwoPowerAntipodalBalance.pow_half_eq_neg_one
#print axioms LamLeungTwoPowerAntipodalBalance.antipodal_balance_root
#print axioms LamLeungTwoPowerAntipodalBalance.antipodal_balance_exponent
