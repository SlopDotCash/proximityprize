/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25DualFamilyInstantiation

/-!
# LANE B2 (#466 round 26): the discrete log EXISTS — the round 19–25 Jacobi chain is now
  fully unconditional for every finite field

Round 25 reduced the dual-family packages to one input: `DiscreteLogTo G m dl`.  This brick
constructs `dl` from cyclicity of `F*` and proves every field of the package, for
`G = μ_n = {a : aⁿ = 1}` and `m·n = q − 1`:

* `dl a := (dlogNat a : ℤ/m)` where `dlogNat` is a choice of exponent for a fixed generator;
* `map_mul` — exponent addition, transported through `orderOf g = q−1` and `m ∣ q−1`;
* `vanish_iff` — `aⁿ = 1 ⟺ (q−1) ∣ k·n ⟺ m ∣ k`;
* `fiber_card` — the fibers of `dl` are multiplicative translates of the kernel
  (`a ↦ g^{c}·a` is a bijection `fiber(0) → fiber(c)`), hence equal-size; `m` equal numbers
  partitioning `q−1` units are each `(q−1)/m`.

With `dualFam_isSubgroupDualFamily`/`dualFam_groupLaw` (round 25), the ENTIRE Jacobi
normal-form chain (rounds 19–24: expansion, Parseval, quartic/sextic collapses, the
`TripleConvEnergyBound` consumer chain, the involution no-go) now holds UNCONDITIONALLY for
every finite field and every divisor pair `m·n = q−1`.  No hypothesis packages remain: the
open core is exactly `TripleConvEnergyBound` and its deep-depth iterates.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 26, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R26DiscreteLogExists

open ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) Generator and discrete log. -/

/-- A fixed generator of the cyclic group `F*`. -/
noncomputable def gen (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Fˣ :=
  (IsCyclic.exists_generator (α := Fˣ)).choose

theorem gen_spec (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    ∀ x : Fˣ, x ∈ Subgroup.zpowers (gen F) :=
  (IsCyclic.exists_generator (α := Fˣ)).choose_spec

theorem orderOf_gen (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    orderOf (gen F) = Fintype.card F - 1 := by
  have h := orderOf_eq_card_of_forall_mem_zpowers (gen_spec F)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_units]

/-- A choice of exponent: `gen^(dlogNat x) = x`. -/
noncomputable def dlogNat (x : Fˣ) : ℕ :=
  Classical.choose ((mem_powers_iff_mem_zpowers).mpr (gen_spec F x))

theorem dlogNat_spec (x : Fˣ) : gen F ^ dlogNat x = x :=
  Classical.choose_spec ((mem_powers_iff_mem_zpowers).mpr (gen_spec F x))

/-- The discrete log to `ℤ/m`. -/
noncomputable def dl (m : ℕ) [NeZero m] : F → ZMod m :=
  fun a => if h : a = 0 then 0 else ((dlogNat (Units.mk0 a h) : ℕ) : ZMod m)

/-! ### (1) The package fields. -/

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- Exponent congruence transported to `ℤ/m` (uses `m ∣ q−1`). -/
theorem dlog_congr (hmn : m * n = Fintype.card F - 1) {i j : ℕ}
    (h : gen F ^ i = (gen F : Fˣ) ^ j) : ((i : ZMod m) : ZMod m) = (j : ZMod m) := by
  have horder := pow_eq_pow_iff_modEq.mp h
  rw [orderOf_gen F] at horder
  have hdvd : m ∣ Fintype.card F - 1 := ⟨n, hmn.symm⟩
  have hm : i ≡ j [MOD m] := horder.of_dvd hdvd
  exact_mod_cast (ZMod.natCast_eq_natCast_iff i j m).mpr hm

theorem dl_map_mul (hmn : m * n = Fintype.card F - 1) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    dl m (a * b) = dl m a + dl m b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [dl, dif_neg ha, dif_neg hb, dif_neg hab]
  have hunits : Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  have hpow : gen F ^ dlogNat (Units.mk0 (a*b) hab)
      = gen F ^ (dlogNat (Units.mk0 a ha) + dlogNat (Units.mk0 b hb)) := by
    rw [pow_add, dlogNat_spec, dlogNat_spec, dlogNat_spec, hunits]
  have := dlog_congr (F := F) (n := n) hmn hpow
  push_cast at this ⊢
  rw [this]

/-- `μ_n` as a Finset. -/
def muN (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) : Finset F :=
  Finset.univ.filter (fun a => a ^ n = 1)

theorem zero_notMem_muN (n : ℕ) [NeZero n] : (0 : F) ∉ muN F n := by
  simp only [muN, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [zero_pow (NeZero.ne n)]
  exact zero_ne_one

theorem dl_vanish_iff (hmn : m * n = Fintype.card F - 1) (a : F) (ha : a ≠ 0) :
    (dl m a = 0 ↔ a ∈ muN F n) := by
  simp only [dl, dif_neg ha, muN, Finset.mem_filter, Finset.mem_univ, true_and]
  set k := dlogNat (Units.mk0 a ha) with hk
  have hga : (gen F : Fˣ) ^ k = Units.mk0 a ha := dlogNat_spec _
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  constructor
  · -- m ∣ k ⟹ aⁿ = 1
    intro h0
    have hmk : m ∣ k := by
      have := (ZMod.natCast_eq_zero_iff k m).mp h0
      exact this
    obtain ⟨t, ht⟩ := hmk
    have hpow : (Units.mk0 a ha) ^ n = 1 := by
      rw [← hga, ← pow_mul, ht]
      have : m * t * n = (Fintype.card F - 1) * t := by
        rw [← hmn]; ring
      rw [this, pow_mul, ← orderOf_gen F, pow_orderOf_eq_one, one_pow]
    have : a ^ n = 1 := by
      have := congrArg (Units.val) hpow
      simpa using this
    exact this
  · -- aⁿ = 1 ⟹ m ∣ k
    intro hn
    have hupow : (Units.mk0 a ha) ^ n = 1 := by
      ext; simpa using hn
    have hgkn : (gen F) ^ (k * n) = 1 := by
      rw [pow_mul, hga, hupow]
    have hdvd : (Fintype.card F - 1) ∣ k * n := by
      rw [← orderOf_gen F]
      exact orderOf_dvd_of_pow_eq_one hgkn
    rw [← hmn] at hdvd
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hmk : m ∣ k := by
      rcases hdvd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have h2 : k * n = m * u * n := by rw [hu]; ring
      exact Nat.eq_of_mul_eq_mul_right hn0 h2
    exact (ZMod.natCast_eq_zero_iff k m).mpr hmk

/-- `dl 1 = 0`. -/
theorem dl_one (hmn : m * n = Fintype.card F - 1) : dl m (1 : F) = 0 := by
  simp only [dl, dif_neg (one_ne_zero (α := F))]
  have hpow : gen F ^ dlogNat (Units.mk0 (1:F) one_ne_zero) = gen F ^ (0 : ℕ) := by
    rw [dlogNat_spec, pow_zero]
    ext; simp
  have := dlog_congr (F := F) (n := n) hmn hpow
  simpa using this

/-- The fibers of `dl` on the punctured field are multiplicative translates of each other,
hence equal-size; `m` of them partition `q−1` elements. -/
theorem dl_fiber_card (hmn : m * n = Fintype.card F - 1) (c : ZMod m) :
    (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c)).card
      = (Fintype.card F - 1) / m := by
  classical
  -- Step 1: any two fibers have equal card (translate by u with dl u = c₂ − c₁).
  have hdl_of_unit : ∀ e : ℕ, dl m (((gen F : Fˣ) ^ e : Fˣ) : F) = (e : ZMod m) := by
    intro e
    have hu0 : (((gen F : Fˣ) ^ e : Fˣ) : F) ≠ 0 := Units.ne_zero _
    simp only [dl, dif_neg hu0]
    have hmk : Units.mk0 (((gen F : Fˣ) ^ e : Fˣ) : F) hu0 = (gen F) ^ e := by
      ext; simp
    have hpow : gen F ^ dlogNat (Units.mk0 (((gen F : Fˣ) ^ e : Fˣ) : F) hu0)
        = gen F ^ e := by
      rw [dlogNat_spec, hmk]
    exact dlog_congr (F := F) (n := n) hmn hpow
  have htrans : ∀ c₁ c₂ : ZMod m,
      (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c₁)).card
        = (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c₂)).card := by
    intro c₁ c₂
    set e : ℕ := (c₂ - c₁).val with he
    set u : F := (((gen F : Fˣ) ^ e : Fˣ) : F) with hu
    have hu0 : u ≠ 0 := Units.ne_zero _
    have hdlu : dl m u = c₂ - c₁ := by
      rw [hu, hdl_of_unit e, he]
      simp [ZMod.natCast_val, ZMod.cast_id]
    -- inverse translator
    set v : F := ((((gen F : Fˣ) ^ e : Fˣ)⁻¹ : Fˣ) : F) with hv
    have hv0 : v ≠ 0 := Units.ne_zero _
    have huv : u * v = 1 := by
      rw [hu, hv]
      norm_cast
      simp
    have hdlv : dl m v = -(c₂ - c₁) := by
      have h1 : dl m (u * v) = dl m u + dl m v := dl_map_mul (n := n) hmn u v hu0 hv0
      rw [huv, dl_one (n := n) hmn, hdlu] at h1
      linear_combination -h1
    refine Finset.card_bij' (fun a _ => u * a) (fun b _ => v * b) ?_ ?_ ?_ ?_
    · intro a ha
      have h2 := Finset.mem_filter.mp ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp h2.1).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨mul_ne_zero hu0 ha0,
        Finset.mem_univ _⟩, ?_⟩
      rw [dl_map_mul (n := n) hmn u a hu0 ha0, hdlu, h2.2]
      ring
    · intro b hb
      have h2 := Finset.mem_filter.mp hb
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp h2.1).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨mul_ne_zero hv0 hb0,
        Finset.mem_univ _⟩, ?_⟩
      rw [dl_map_mul (n := n) hmn v b hv0 hb0, hdlv, h2.2]
      ring
    · intro a _
      dsimp only
      rw [← mul_assoc]
      rw [show v * u = 1 from by rw [mul_comm]; exact huv, one_mul]
    · intro b _
      dsimp only
      rw [← mul_assoc]
      rw [huv, one_mul]
  -- Step 2: the m equal fibers partition the q−1 nonzero elements.
  have hpart : ∑ c' : ZMod m,
      (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c')).card
      = Fintype.card F - 1 := by
    have h1 := Finset.sum_fiberwise ((Finset.univ : Finset F).erase 0)
      (fun a => dl m a) (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hconst : ∑ c' : ZMod m,
      (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c')).card
      = m * (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c)).card := by
    rw [Finset.sum_congr rfl (fun c' _ => htrans c' c), Finset.sum_const,
      smul_eq_mul, Finset.card_univ, ZMod.card]
  have hfin : m * (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c)).card
      = Fintype.card F - 1 := by rw [← hconst, hpart]
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hfin' : Fintype.card F - 1
      = (((Finset.univ : Finset F).erase 0).filter (fun a => dl m a = c)).card * m := by
    rw [← hfin]; ring
  exact (Nat.div_eq_of_eq_mul_left hm0 hfin').symm

/-- **THE EXISTENCE THEOREM: the discrete-log package holds for `μ_n`** — hence (round 25)
the full dual-family packages, hence (rounds 19–24) the entire Jacobi normal-form chain,
unconditionally for every finite field and divisor pair `m·n = q−1`. -/
theorem discreteLogTo_muN (hmn : m * n = Fintype.card F - 1) :
    DiscreteLogTo (muN F n) m (dl m) where
  zero_notMem := zero_notMem_muN n
  map_mul := fun a b => dl_map_mul (n := n) hmn a b
  vanish_iff := fun a => dl_vanish_iff (n := n) hmn a
  fiber_card := fun c => dl_fiber_card (n := n) hmn c

end ArkLib.ProximityGap.Frontier.R26DiscreteLogExists

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R26DiscreteLogExists.dl_map_mul
#print axioms ArkLib.ProximityGap.Frontier.R26DiscreteLogExists.dl_vanish_iff
#print axioms ArkLib.ProximityGap.Frontier.R26DiscreteLogExists.dl_fiber_card
#print axioms ArkLib.ProximityGap.Frontier.R26DiscreteLogExists.discreteLogTo_muN
