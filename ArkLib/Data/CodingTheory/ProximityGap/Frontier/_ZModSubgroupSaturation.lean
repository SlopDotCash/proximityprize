/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDonohoStark
import Mathlib.Algebra.Field.GeomSum

/-!
# Subgroup saturation of Donoho–Stark on `ZMod N` (#407)

`_ZModDonohoStark.lean` lands the *inequality* `Φ ≠ 0 ⟹ |supp Φ| · |supp 𝓕Φ| ≥ N`. This
file lands the matching *tightness*: the indicator of an order-`d` subgroup of `ZMod N`
**saturates** the principle with equality.

For `d ∣ N` let `m := N / d` and let `H_d := {0, m, 2m, …, (d−1)m}` be the order-`d` subgroup
(multiples of `m = N/d`). With `Φ = 1_{H_d}`:

> `|supp Φ| = d`,  `|supp 𝓕Φ| = N/d`,  and  `|supp Φ| · |supp 𝓕Φ| = N`.

The DFT is itself the indicator of the dual subgroup, scaled by `d`:
`𝓕Φ k = d` if `(N/d)·k = 0` and `0` otherwise (geometric sum of a `d`-th root of unity).

**Why it matters for #407.** Donoho–Stark has *equality* exactly on subgroup indicators, and
`μ_{2^μ}` is a subgroup — so `2`-power groups sit at the worst (saturating) constant of the
discrete uncertainty principle, with no slack to exploit. This is the structural reason the prize
floor on `μ_{2^μ}` is hard. Axiom-clean. Issue #407.
-/

set_option autoImplicit false

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark

namespace ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- The kernel of multiplication by a divisor `c ∣ N`, as a `Finset (ZMod N)`. It will be both the
support of a subgroup indicator (`c = d`) and the support of its DFT (`c = N/d`). -/
noncomputable def kernel (c : ℕ) : Finset (ZMod N) := univ.filter (fun k => (c : ZMod N) * k = 0)

/-- Membership in `kernel c` for a divisor `c ∣ N` is "being a multiple of `N/c`": for `k` we have
`(c : ZMod N) * k = 0 ↔ ∃ i < c, k = (i : ZMod N) * (N / c)`. -/
theorem mul_eq_zero_iff_mem_multiples {c : ℕ} (hc : c ∣ N) (k : ZMod N) :
    (c : ZMod N) * k = 0 ↔ ∃ i < c, k = (i : ZMod N) * ((N / c : ℕ) : ZMod N) := by
  obtain ⟨m, hm⟩ := hc
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcpos : 0 < c := by
    refine Nat.pos_of_ne_zero (fun h => ?_); rw [h, zero_mul] at hm; omega
  have hmpos : 0 < m := by
    refine Nat.pos_of_ne_zero (fun h => ?_); rw [h, mul_zero] at hm; omega
  have hNdivc : N / c = m := by rw [hm]; exact Nat.mul_div_cancel_left m hcpos
  constructor
  · intro hk
    -- pass to `val`: `N ∣ c * k.val`, and `N = c * m`, so `m ∣ k.val`.
    have hval : (N : ℕ) ∣ c * k.val := by
      have hz : ((c * k.val : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_mul, natCast_zmod_val]; exact hk
      exact (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hmk : m ∣ k.val := by
      have : c * m ∣ c * k.val := by rw [← hm]; exact hval
      exact (mul_dvd_mul_iff_left (by positivity : (c : ℕ) ≠ 0)).mp this
    obtain ⟨i, hi⟩ := hmk      -- `hi : k.val = m * i`
    refine ⟨i, ?_, ?_⟩
    · -- `i < c`  since  `m * i = k.val < N = c * m`
      have hkval : k.val < N := ZMod.val_lt k
      rw [hi, hm] at hkval
      -- `m * i < m * c`
      have : m * i < m * c := by rw [mul_comm c m] at hkval; exact hkval
      exact (Nat.mul_lt_mul_left hmpos).mp this
    · rw [hNdivc]
      have hcast : (k.val : ZMod N) = ((m * i : ℕ) : ZMod N) := by rw [hi]
      rw [natCast_zmod_val] at hcast
      rw [hcast]; push_cast; ring
  · rintro ⟨i, _, rfl⟩
    rw [hNdivc]
    have hrw : (c : ZMod N) * ((i : ZMod N) * (m : ZMod N))
        = (i : ZMod N) * ((c * m : ℕ) : ZMod N) := by push_cast; ring
    rw [hrw, ← hm, natCast_self, mul_zero]

/-- For a divisor `c ∣ N`, the kernel of multiplication by `c` is the image of `range c` under
`i ↦ i · (N/c)`. -/
theorem kernel_eq_image {c : ℕ} (hc : c ∣ N) :
    (kernel c : Finset (ZMod N))
      = (range c).image (fun i : ℕ => (i : ZMod N) * ((N / c : ℕ) : ZMod N)) := by
  ext k
  simp only [kernel, mem_filter, mem_univ, true_and, mem_image, mem_range]
  rw [mul_eq_zero_iff_mem_multiples hc]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, hki⟩; exact ⟨i, hi, hki.symm⟩

/-- The map `i ↦ i · (N/c)` is injective on `range c` when `c ∣ N`. -/
theorem injOn_multiples {c : ℕ} (hc : c ∣ N) :
    Set.InjOn (fun i : ℕ => (i : ZMod N) * ((N / c : ℕ) : ZMod N)) (range c : Finset ℕ) := by
  obtain ⟨m, hm⟩ := hc
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcpos : 0 < c := by
    refine Nat.pos_of_ne_zero (fun h => ?_); rw [h, zero_mul] at hm; omega
  have hmpos : 0 < m := by
    refine Nat.pos_of_ne_zero (fun h => ?_); rw [h, mul_zero] at hm; omega
  have hNdivc : N / c = m := by rw [hm]; exact Nat.mul_div_cancel_left m hcpos
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  -- `(i*m : ZMod N) = (j*m : ZMod N)`  with  `i,j < c = N/m`  forces  `i = j`.
  rw [hNdivc] at hij
  have e1 : ((i * m : ℕ) : ZMod N) = ((j * m : ℕ) : ZMod N) := by push_cast; exact hij
  rw [ZMod.natCast_eq_natCast_iff] at e1
  have him : i * m < N := by rw [hm]; exact (Nat.mul_lt_mul_right hmpos).mpr hi
  have hjm : j * m < N := by rw [hm]; exact (Nat.mul_lt_mul_right hmpos).mpr hj
  have heq : i * m = j * m := by
    have ht := e1
    rw [Nat.ModEq, Nat.mod_eq_of_lt him, Nat.mod_eq_of_lt hjm] at ht
    exact ht
  exact Nat.eq_of_mul_eq_mul_right hmpos heq

/-- **Kernel cardinality:** for `c ∣ N`, `#{k : ZMod N | (c : ZMod N)·k = 0} = c`. -/
theorem kernel_card {c : ℕ} (hc : c ∣ N) : (kernel c : Finset (ZMod N)).card = c := by
  rw [kernel_eq_image hc, Finset.card_image_of_injOn (injOn_multiples hc), card_range]

/-- The order-`d` subgroup indicator: `1` on `{0, N/d, 2·(N/d), …}`, `0` elsewhere. Equivalently
the indicator of `kernel d` (the multiples of `N/d`). -/
noncomputable def subgroupIndicator (d : ℕ) : ZMod N → ℂ :=
  fun j => if (d : ZMod N) * j = 0 then 1 else 0

/-- Its support is `kernel d`. -/
theorem supp_subgroupIndicator (d : ℕ) : supp (subgroupIndicator (N := N) d) = kernel d := by
  ext k
  simp only [supp, subgroupIndicator, kernel, mem_filter, mem_univ, true_and]
  by_cases h : (d : ZMod N) * k = 0 <;> simp [h]

/-- `|supp Φ| = d` for the order-`d` subgroup indicator (`d ∣ N`). -/
theorem supp_subgroupIndicator_card {d : ℕ} (hd : d ∣ N) :
    (supp (subgroupIndicator (N := N) d)).card = d := by
  rw [supp_subgroupIndicator, kernel_card hd]

/-- The DFT of the order-`d` subgroup indicator is a geometric sum of the `d`-th root of unity
`z := stdAddChar(−(N/d)·k)`, namely `d` when `z = 1` and `0` otherwise. -/
theorem dft_subgroupIndicator {d : ℕ} (hd : d ∣ N) (k : ZMod N) :
    𝓕 (subgroupIndicator (N := N) d) k
      = if stdAddChar (-(((N / d : ℕ) : ZMod N)) * k) = 1 then (d : ℂ) else 0 := by
  set m : ZMod N := ((N / d : ℕ) : ZMod N) with hmdef
  set z : ℂ := stdAddChar (-(m) * k) with hzdef
  have hcpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · obtain ⟨e, he⟩ := hd; rw [h, zero_mul] at he; exact absurd he (NeZero.ne N)
    · exact h
  -- `(d : ZMod N) * m = 0` since `d * (N/d) = N ≡ 0`.
  have hdm : (d : ZMod N) * m = 0 := by
    rw [hmdef]
    have hcast : (d : ZMod N) * ((N / d : ℕ) : ZMod N) = ((d * (N / d) : ℕ) : ZMod N) := by
      push_cast; ring
    rw [hcast, Nat.mul_div_cancel' hd, natCast_self]
  -- `z ^ d = 1`  since  `d • (-(m)*k) = -(d * m)*k = 0`.
  have hzd : z ^ d = 1 := by
    rw [hzdef, ← AddChar.map_nsmul_eq_pow]
    have hsmul : (d : ℕ) • (-(m) * k) = 0 := by
      rw [nsmul_eq_mul]
      have : ((d : ℕ) : ZMod N) * (-(m) * k) = -((d : ZMod N) * m) * k := by ring
      rw [this, hdm, neg_zero, zero_mul]
    rw [hsmul, AddChar.map_zero_eq_one]
  -- Expand the DFT and collapse to a sum over the kernel.
  rw [dft_apply]
  have hsum : (∑ j : ZMod N, stdAddChar (-(j * k)) • subgroupIndicator (N := N) d j)
      = ∑ j ∈ kernel d, stdAddChar (-(j * k)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => (d : ZMod N) * j = 0)]
    have hzero : (∑ j ∈ univ.filter (fun j => ¬ (d : ZMod N) * j = 0),
        stdAddChar (-(j * k)) • subgroupIndicator (N := N) d j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      simp only [subgroupIndicator, if_neg hj, smul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr ?_ ?_
    · simp only [kernel]
    · intro j hj
      simp only [kernel, mem_filter, mem_univ, true_and] at hj
      simp only [subgroupIndicator, if_pos hj, smul_eq_mul, mul_one]
  rw [hsum]
  -- reindex the kernel sum as `∑ i ∈ range d, z ^ i`.
  have hinj : ∀ i ∈ range d, ∀ j ∈ range d,
      (i : ZMod N) * ((N / d : ℕ) : ZMod N)
        = (j : ZMod N) * ((N / d : ℕ) : ZMod N) → i = j := fun i hi j hj h =>
    injOn_multiples hd (by simpa using hi) (by simpa using hj) h
  have hreindex : (∑ j ∈ kernel d, stdAddChar (-(j * k)))
      = ∑ i ∈ range d, z ^ i := by
    rw [kernel_eq_image hd, Finset.sum_image hinj]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hzdef, ← AddChar.map_nsmul_eq_pow]
    congr 1
    rw [nsmul_eq_mul]
    ring
  rw [hreindex]
  -- geometric sum.
  by_cases hz1 : z = 1
  · simp [hz1, Finset.sum_const, card_range]
  · rw [if_neg hz1, geom_sum_eq hz1, hzd, sub_self, zero_div]

/-- The DFT support is exactly `kernel (N/d)` (where `z = 1`). -/
theorem supp_dft_subgroupIndicator {d : ℕ} (hd : d ∣ N) :
    supp (𝓕 (subgroupIndicator (N := N) d)) = kernel (N / d) := by
  have hcpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · obtain ⟨e, he⟩ := hd; rw [h, zero_mul] at he; exact absurd he (NeZero.ne N)
    · exact h
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  ext k
  simp only [supp, kernel, mem_filter, mem_univ, true_and]
  rw [dft_subgroupIndicator hd k]
  -- `z = 1 ⟺ -(N/d)*k = 0 ⟺ (N/d)*k = 0` via injectivity of `stdAddChar`.
  have hz1 : stdAddChar (-(((N / d : ℕ) : ZMod N)) * k) = 1
      ↔ ((N / d : ℕ) : ZMod N) * k = 0 := by
    rw [← AddChar.map_zero_eq_one (stdAddChar (N := N)),
      (ZMod.injective_stdAddChar (N := N)).eq_iff, neg_mul, neg_eq_zero]
  by_cases h : ((N / d : ℕ) : ZMod N) * k = 0
  · rw [if_pos (hz1.mpr h)]; simp only [h, iff_true]; exact hdC
  · rw [if_neg (fun hc => h (hz1.mp hc))]; simp [h]

/-- `|supp 𝓕Φ| = N/d` for the order-`d` subgroup indicator (`d ∣ N`). -/
theorem supp_dft_subgroupIndicator_card {d : ℕ} (hd : d ∣ N) :
    (supp (𝓕 (subgroupIndicator (N := N) d))).card = N / d := by
  rw [supp_dft_subgroupIndicator hd, kernel_card (Nat.div_dvd_of_dvd hd)]

omit [NeZero N] in
/-- The subgroup indicator is nonzero (it is `1` at `0`). -/
theorem subgroupIndicator_ne_zero (d : ℕ) :
    subgroupIndicator (N := N) d ≠ 0 := by
  intro hzero
  have hv : subgroupIndicator (N := N) d 0 = 0 := by rw [hzero]; rfl
  simp only [subgroupIndicator, mul_zero] at hv
  exact one_ne_zero hv

/-- **Subgroup saturation of Donoho–Stark.** For `d ∣ N`, the order-`d` subgroup indicator
saturates the support uncertainty principle:
`|supp Φ| · |supp 𝓕Φ| = N`, with `|supp Φ| = d` and `|supp 𝓕Φ| = N/d`. -/
theorem subgroup_saturates_donoho_stark {d : ℕ} (hd : d ∣ N) :
    (supp (subgroupIndicator (N := N) d)).card = d
      ∧ (supp (𝓕 (subgroupIndicator (N := N) d))).card = N / d
      ∧ (supp (subgroupIndicator (N := N) d)).card
          * (supp (𝓕 (subgroupIndicator (N := N) d))).card = N := by
  refine ⟨supp_subgroupIndicator_card hd, supp_dft_subgroupIndicator_card hd, ?_⟩
  rw [supp_subgroupIndicator_card hd, supp_dft_subgroupIndicator_card hd,
    Nat.mul_div_cancel' hd]

/-- The real-valued product form matching `donoho_stark`'s conclusion: subgroup indicators turn
the Donoho–Stark inequality `≥ N` into an equality `= N`. -/
theorem subgroup_saturates_donoho_stark_real {d : ℕ} (hd : d ∣ N) :
    ((supp (subgroupIndicator (N := N) d)).card : ℝ)
        * (supp (𝓕 (subgroupIndicator (N := N) d))).card = N := by
  have h := (subgroup_saturates_donoho_stark hd).2.2
  exact_mod_cast h

/-- **The Donoho–Stark inequality is tight at every divisor subgroup.** The substrate bound
`donoho_stark` gives `|supp Φ|·|supp 𝓕Φ| ≥ N` for any `Φ ≠ 0`; here the order-`d` subgroup
indicator (`d ∣ N`) attains equality. Hence the discrete uncertainty constant cannot be
improved, and (since `μ_{2^μ}` is such a subgroup) the prize floor on `μ_{2^μ}` has no slack. -/
theorem donoho_stark_tight_at_subgroup {d : ℕ} (hd : d ∣ N) :
    subgroupIndicator (N := N) d ≠ 0
      ∧ (N : ℝ) ≤ (supp (subgroupIndicator (N := N) d)).card
            * (supp (𝓕 (subgroupIndicator (N := N) d))).card
      ∧ ((supp (subgroupIndicator (N := N) d)).card : ℝ)
            * (supp (𝓕 (subgroupIndicator (N := N) d))).card = N :=
  ⟨subgroupIndicator_ne_zero d,
   donoho_stark _ (subgroupIndicator_ne_zero d),
   subgroup_saturates_donoho_stark_real hd⟩

end ProximityGap.Frontier.ZModSubgroupSaturation

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ZModSubgroupSaturation.kernel_card
#print axioms ProximityGap.Frontier.ZModSubgroupSaturation.dft_subgroupIndicator
#print axioms ProximityGap.Frontier.ZModSubgroupSaturation.subgroup_saturates_donoho_stark
#print axioms ProximityGap.Frontier.ZModSubgroupSaturation.subgroup_saturates_donoho_stark_real
#print axioms ProximityGap.Frontier.ZModSubgroupSaturation.donoho_stark_tight_at_subgroup
