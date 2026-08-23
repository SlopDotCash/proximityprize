/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The monomial γ-coset fibration: `badSet = c·badSet` for monomial stacks, every radius (#371)

For the monomial stack `(u₀, u₁) = (Xᵃ|_{⟨g⟩}, Xᵇ|_{⟨g⟩})` on the smooth domain of order `n`,
the smooth rotation `x ↦ gx` scales the rows by `(gᵃ, gᵇ)`, and the in-tree equivariance
engine (`mcaEvent_rs_rotate` + `mcaEvent_smul_both` + `mcaEvent_smul_right`) converts the
row-scaling into a *scalar* reparametrization:

> **`mcaEvent_monoStack_gamma_mul`** — `γ` is MCA-bad for the monomial stack iff `γ·c` is,
> where `c = gᵇ⁻ᵃ` (as the field element `gᵇ·(gᵃ)⁻¹`) — at EVERY radius `δ`, every code
> degree `d`, unconditionally.

So the bad-scalar set fibers over `γ ↦ c·γ`: its nonzero part is a disjoint union of free
`⟨c⟩`-orbits, hence

> **`orderOf_dvd_card_badScalars_erase_zero`** — `ord(c) ∣ #(badSet ∖ {0})`, and for the
> adjacent-pair family (`b = a + 1`, the KKH26 ceiling stacks) **`n ∣ #(badSet ∖ {0})`**
> (`n_dvd_card_badScalars_adjacent`).

## Why this matters (#371)

1. **It explains the spectrum laws' arithmetic.**  Every landed exact ceiling count obeys it:
   `N(3,3) = 40 = 5·8`, `N(4,4) = 1233 = 77·16 + 1` (the `+1` is `γ = 0`), the probe value
   `24 = 3·8` at `(97, 8)` — the `TwoPowerSubsetSumSpectrum` counts are forced into residue
   `#bad ≡ [0 ∈ badSet] (mod n)` by symmetry alone, a structural constraint any future
   spectrum formula must satisfy.
2. **It cuts every monomial census by a factor `ord(c)`.**  The boundary-slice residual-ratio
   image (`BoundarySliceExact` / the unconditional law) of a monomial stack is `⟨c⟩`-invariant,
   so the collision census only needs the orbit-class count — at adjacent pairs, a factor-`n`
   reduction (probe section D: e.g. `|B∖0| = 24 = 3 orbits × 8` at `(97, 8, d = 1)`).
3. **It is a γ-space fibration, not a stack-space one**: `mcaEvent_monomial`
   (`MCAMonomialEquivariance`) and the rotation/translation engine transport badness between
   *stacks* at the same `γ`; this brick is the first in-tree statement that moves the
   *scalar* while fixing the stack — the structure the bad-set censuses actually quotient by.

Probe: `scripts/probes/probe_monomial_gamma_fibration.py` (pre-registered, exit 0) —
invariance `badSet = c·badSet` and `ord(c)`-divisibility at `(p, n) ∈ {(17,8), (97,8),
(97,16)}`, `d ≤ 2`, five monomial pairs, every witness threshold up to `d+5`; the spectrum
cross-check at the ceiling radius; the orbit-freeness of the fibration (all orbits full size).

Honest scope: the fibration constrains and quotients the monomial bad-set censuses; it does
not by itself produce new bounds (the orbit-class counts remain the census content).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26RegimeSplit ProximityGap.MCAEquivariance

namespace ArkLib.ProximityGap.MonomialGammaFibration

/-! ## The monomial words and the rotation transport -/

/-- The monomial word `Xᵃ` evaluated on the smooth domain `i ↦ gⁱ`. -/
def monoWord {p : ℕ} (g : ZMod p) {n : ℕ} (a : ℕ) : Fin n → ZMod p :=
  fun i => (g ^ (i : ℕ)) ^ a

/-- The smooth rotation advances the power domain by one step: `g^{σ(i)} = g · gⁱ`. -/
theorem pow_finRotate {p : ℕ} {g : ZMod p} {m : ℕ} (hg : orderOf g = m + 1)
    (i : Fin (m + 1)) :
    g ^ ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) = g * g ^ (i : ℕ) := by
  rw [finRotate_succ_apply]
  by_cases hlast : i = Fin.last m
  · subst hlast
    have hval : ((Fin.last m + 1 : Fin (m + 1)) : ℕ) = 0 := by
      rw [Fin.last_add_one, Fin.val_zero]
    rw [hval]
    have hcycle : g * g ^ ((Fin.last m : Fin (m + 1)) : ℕ) = g ^ (m + 1) := by
      rw [Fin.val_last, pow_succ']
    rw [hcycle, ← hg, pow_orderOf_eq_one]
    simp
  · have hval : ((i + 1 : Fin (m + 1)) : ℕ) = (i : ℕ) + 1 := by
      rw [Fin.val_add_one]
      simp [hlast]
    rw [hval, pow_succ']

/-- Precomposing the monomial word with the rotation scales it by `gᵃ`. -/
theorem monoWord_comp_rotate {p : ℕ} {g : ZMod p} {m : ℕ} (hg : orderOf g = m + 1)
    (a : ℕ) :
    monoWord g (n := m + 1) a ∘ ⇑(finRotate (m + 1)) = (g ^ a) • monoWord g (n := m + 1) a := by
  funext i
  show (g ^ ((finRotate (m + 1) i : Fin (m + 1)) : ℕ)) ^ a = (g ^ a) * (g ^ (i : ℕ)) ^ a
  rw [pow_finRotate hg i, mul_pow]

/-! ## The fibration: badness at `γ` is badness at `γ·c` -/

open Classical in
/-- **The monomial γ-coset fibration.**  For the monomial stack `(Xᵃ, Xᵇ)` on the smooth
domain `⟨g⟩` of order `n`, the MCA event at scalar `γ` is equivalent to the MCA event at
`γ·c`, `c = gᵇ·(gᵃ)⁻¹` — at every radius, every code degree, unconditionally.  The smooth
rotation scales the stack rows by `(gᵃ, gᵇ)`, and the row-scaling re-parametrizes the
scalar. -/
theorem mcaEvent_monoStack_gamma_mul {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0) (d a b : ℕ) (δ : ℝ≥0) (γ : ZMod p) :
    mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g b) γ ↔
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g b) (γ * (g ^ b * (g ^ a)⁻¹)) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [evalCode_eq_reedSolomon g hg hg0 d]
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hc0 : g ^ b * (g ^ a)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hg0) (inv_ne_zero hga)
  have hdomrot : ∀ i : Fin (m + 1),
      powDomain g hg hg0 (finRotate (m + 1) i) = g * powDomain g hg hg0 i := by
    intro i
    show g ^ ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) = g * g ^ (i : ℕ)
    exact pow_finRotate hg i
  have hrot := mcaEvent_rs_rotate (powDomain g hg hg0) (d + 1)
    (finRotate (m + 1)) g hg0 hdomrot δ γ (monoWord g a) (monoWord g b)
  rw [monoWord_comp_rotate hg a, monoWord_comp_rotate hg b] at hrot
  have hsplit : (g ^ b : ZMod p) • monoWord g (n := m + 1) b
      = (g ^ a) • ((g ^ b * (g ^ a)⁻¹) • monoWord g (n := m + 1) b) := by
    rw [smul_smul, ← mul_assoc, mul_comm ((g : ZMod p) ^ a) (g ^ b), mul_assoc,
      mul_inv_cancel₀ hga, mul_one]
  rw [hsplit] at hrot
  have hboth := mcaEvent_smul_both
    (C := ReedSolomon.code (powDomain g hg hg0) (d + 1)) (δ := δ)
    (u₀ := monoWord g a) (u₁ := (g ^ b * (g ^ a)⁻¹) • monoWord g b) hga γ
  have hright := mcaEvent_smul_right
    (C := ReedSolomon.code (powDomain g hg hg0) (d + 1)) (δ := δ)
    (u₀ := monoWord g a) (u₁ := monoWord g b) hc0 γ
  constructor
  · intro h
    exact hright.mp (hboth.mp (hrot.mpr h))
  · intro h
    exact hrot.mp (hboth.mpr (hright.mpr h))

open Classical in
/-- Finset form of the monomial γ-coset fibration: the MCA-bad scalar set is fixed by
right-multiplication by `c = gᵇ·(gᵃ)⁻¹`.  This is the literal `badSet = badSet·c`
API used by orbit quotients and exact-count consumers. -/
theorem badScalars_image_mul_eq {p : ℕ} [Fact p.Prime] {g : ZMod p}
    {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0) (d a b : ℕ) (δ : ℝ≥0) :
    (Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g b) γ)).image
      (fun γ => γ * (g ^ b * (g ^ a)⁻¹)) =
    Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g b) γ) := by
  classical
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hc0 : g ^ b * (g ^ a)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hg0) (inv_ne_zero hga)
  ext γ
  constructor
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨γ₀, hγ₀, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ₀ ⊢
    exact (mcaEvent_monoStack_gamma_mul hg hg0 d a b δ γ₀).mp hγ₀
  · intro hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
    refine Finset.mem_image.mpr ⟨γ * (g ^ b * (g ^ a)⁻¹)⁻¹, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmul : (γ * (g ^ b * (g ^ a)⁻¹)⁻¹) * (g ^ b * (g ^ a)⁻¹) = γ := by
        rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      have hiff := mcaEvent_monoStack_gamma_mul hg hg0 d a b δ
        (γ * (g ^ b * (g ^ a)⁻¹)⁻¹)
      have htarget : mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g b)
          ((γ * (g ^ b * (g ^ a)⁻¹)⁻¹) * (g ^ b * (g ^ a)⁻¹)) := by
        rw [hmul]
        exact hγ
      exact hiff.mpr htarget
    · rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]

/-! ## The orbit-peeling divisibility engine -/

/-- **Divisibility from multiplicative invariance** (generic): a finite set of nonzero field
elements invariant under `γ ↦ γ·c` (`c` of finite multiplicative order) has cardinality
divisible by `ord(c)` — peel free `⟨c⟩`-orbits one at a time. -/
theorem card_dvd_of_mul_invariant {F : Type*} [Field F] [DecidableEq F] {c : F}
    (hc : IsOfFinOrder c) :
    ∀ N : ℕ, ∀ S : Finset F, S.card ≤ N → (0 : F) ∉ S →
      (∀ γ, γ ∈ S ↔ γ * c ∈ S) → orderOf c ∣ S.card := by
  have hm : 0 < orderOf c := hc.orderOf_pos
  have hcpow : c ^ orderOf c = 1 := pow_orderOf_eq_one c
  intro N
  induction N with
  | zero =>
    intro S hS _ _
    rw [Nat.le_zero.mp hS]
    exact dvd_zero _
  | succ N ih =>
    intro S hS h0 hinv
    rcases S.eq_empty_or_nonempty with rfl | ⟨γ, hγ⟩
    · simp
    have hγ0 : γ ≠ 0 := fun h => h0 (h ▸ hγ)
    -- the full ⟨c⟩-orbit of γ
    set O := (Finset.range (orderOf c)).image (fun k => γ * c ^ k) with hOdef
    have horbmem : ∀ k : ℕ, γ * c ^ k ∈ S := by
      intro k
      induction k with
      | zero => simpa using hγ
      | succ k ihk =>
        have := (hinv (γ * c ^ k)).mp ihk
        rwa [mul_assoc, ← pow_succ] at this
    have hOsub : O ⊆ S := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact horbmem k
    have hinjOn : Set.InjOn (fun k => γ * c ^ k) ↑(Finset.range (orderOf c)) := by
      intro i hi j hj hij
      have hipow : c ^ i = c ^ j := mul_left_cancel₀ hγ0 hij
      exact pow_injOn_Iio_orderOf
        (by simpa using Finset.mem_range.mp (Finset.mem_coe.mp hi))
        (by simpa using Finset.mem_range.mp (Finset.mem_coe.mp hj)) hipow
    have hOcard : O.card = orderOf c := by
      rw [hOdef, Finset.card_image_of_injOn hinjOn, Finset.card_range]
    -- the orbit is itself invariant under `· * c` (both directions)
    have hOinv : ∀ x, x ∈ O ↔ x * c ∈ O := by
      intro x
      constructor
      · rintro hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        refine Finset.mem_image.mpr ⟨(k + 1) % orderOf c, Finset.mem_range.mpr
          (Nat.mod_lt _ hm), ?_⟩
        rw [pow_mod_orderOf, pow_succ, mul_assoc]
      · rintro hx
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hx
        -- x·c = γ·cᵏ  ⟹  x = γ·c^{k + ord − 1}
        have hx2 : x = γ * c ^ ((k + (orderOf c - 1)) % orderOf c) := by
          rw [pow_mod_orderOf, pow_add]
          have hxc : x * (c * c ^ (orderOf c - 1)) = γ * c ^ k * c ^ (orderOf c - 1) := by
            rw [← mul_assoc, hk]
          rw [← pow_succ', show (orderOf c - 1) + 1 = orderOf c from by omega, hcpow,
            mul_one] at hxc
          rw [hxc, mul_assoc]
        rw [hx2]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ hm), rfl⟩
    -- peel: S ∖ O is smaller, still invariant, still 0-free
    have hsdiff_inv : ∀ γ', γ' ∈ S \ O ↔ γ' * c ∈ S \ O := by
      intro γ'
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨hS', hO'⟩
        exact ⟨(hinv γ').mp hS', fun h => hO' ((hOinv γ').mpr h)⟩
      · rintro ⟨hS', hO'⟩
        exact ⟨(hinv γ').mpr hS', fun h => hO' ((hOinv γ').mp h)⟩
    have hcard_sdiff : (S \ O).card = S.card - orderOf c := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hOsub, hOcard]
    have hOle : orderOf c ≤ S.card := hOcard ▸ Finset.card_le_card hOsub
    have hrec := ih (S \ O) (by omega) (fun h => h0 (Finset.mem_sdiff.mp h).1) hsdiff_inv
    rw [hcard_sdiff] at hrec
    have hsum : S.card = (S.card - orderOf c) + orderOf c := (Nat.sub_add_cancel hOle).symm
    rw [hsum]
    exact Nat.dvd_add hrec dvd_rfl

/-! ## The headline divisibilities -/

open Classical in
/-- **The fibration divisibility.**  The nonzero MCA-bad scalars of a monomial stack are a
union of free `⟨c⟩`-orbits, `c = gᵇ·(gᵃ)⁻¹`: their count is divisible by `ord(c)`. -/
theorem orderOf_dvd_card_badScalars_erase_zero {p : ℕ} [Fact p.Prime] {g : ZMod p}
    {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0) (d a b : ℕ) (δ : ℝ≥0) :
    orderOf (g ^ b * (g ^ a)⁻¹) ∣
      ((Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g b) γ)).erase 0).card := by
  classical
  have npos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hc0 : g ^ b * (g ^ a)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hg0) (inv_ne_zero hga)
  have hcfin : IsOfFinOrder (g ^ b * (g ^ a)⁻¹) := by
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, ?_⟩
    have hgn : g ^ n = 1 := hg ▸ pow_orderOf_eq_one g
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm b n, mul_comm a n, pow_mul,
      pow_mul, hgn, one_pow, one_pow, inv_one, mul_one]
  refine card_dvd_of_mul_invariant hcfin _ _ le_rfl (by simp) ?_
  intro γ
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hγ0, hbad⟩
    exact ⟨mul_ne_zero hγ0 hc0,
      (mcaEvent_monoStack_gamma_mul hg hg0 d a b δ γ).mp hbad⟩
  · rintro ⟨hγc0, hbad⟩
    refine ⟨fun h => hγc0 (by rw [h, zero_mul]), ?_⟩
    exact (mcaEvent_monoStack_gamma_mul hg hg0 d a b δ γ).mpr hbad

open Classical in
/-- Total-count form of the fibration divisibility: the full monomial bad-scalar count is
an `ord(c)`-multiple plus the possible fixed zero scalar.  This packages
`orderOf_dvd_card_badScalars_erase_zero` in the form used by spectrum exactness checks:
`#bad = ord(c)·q + [0 ∈ badSet]`. -/
theorem badScalars_card_eq_order_mul_add_zero {p : ℕ} [Fact p.Prime]
    {g : ZMod p} {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0)
    (d a b : ℕ) (δ : ℝ≥0) :
    ∃ q : ℕ,
      (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g b) γ)).card =
        orderOf (g ^ b * (g ^ a)⁻¹) * q +
          if mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
              (monoWord g a) (monoWord g b) 0 then 1 else 0 := by
  classical
  let B : Finset (ZMod p) := Finset.univ.filter (fun γ : ZMod p =>
    mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      (monoWord g a) (monoWord g b) γ)
  have hdvd : orderOf (g ^ b * (g ^ a)⁻¹) ∣ (B.erase 0).card := by
    simpa [B] using orderOf_dvd_card_badScalars_erase_zero hg hg0 d a b δ
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  change B.card =
    orderOf (g ^ b * (g ^ a)⁻¹) * q +
      if mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g b) 0 then 1 else 0
  by_cases h0 : mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      (monoWord g a) (monoWord g b) 0
  · have h0B : (0 : ZMod p) ∈ B := by
      simp [B, h0]
    have hcard : (B.erase 0).card + 1 = B.card := Finset.card_erase_add_one h0B
    simp only [h0, if_true]
    rw [hq] at hcard
    exact hcard.symm
  · have h0B : (0 : ZMod p) ∉ B := by
      simp [B, h0]
    have hcard : (B.erase 0).card = B.card := by
      rw [Finset.erase_eq_of_notMem h0B]
    simp only [h0, if_false, add_zero]
    rw [hcard] at hq
    exact hq

open Classical in
/-- **The adjacent-pair divisibility** (`b = a + 1`, the KKH26 ceiling family): the
multiplier is `g` itself, so the nonzero bad count is divisible by the full domain size
`n` at every radius — the structural constraint behind the spectrum laws' arithmetic
(`N(3,3) = 40 = 5·8`; `N(4,4) = 1233 = 77·16 + 1`, the `+1` being `γ = 0`). -/
theorem n_dvd_card_badScalars_adjacent {p : ℕ} [Fact p.Prime] {g : ZMod p}
    {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0) (d a : ℕ) (δ : ℝ≥0) :
    n ∣ ((Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g (a + 1)) γ)).erase 0).card := by
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hmul : g ^ (a + 1) * (g ^ a)⁻¹ = g := by
    rw [pow_succ', mul_assoc, mul_inv_cancel₀ hga, mul_one]
  have h := orderOf_dvd_card_badScalars_erase_zero hg hg0 d a (a + 1) δ
  rwa [hmul, hg] at h

open Classical in
/-- Adjacent-pair total-count form: for the KKH26 ceiling stacks `(Xᵃ, Xᵃ⁺¹)`, the full
bad-scalar count is `n·q + [0 ∈ badSet]` at every radius. -/
theorem adjacent_card_eq_n_mul_add_zero {p : ℕ} [Fact p.Prime]
    {g : ZMod p} {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0)
    (d a : ℕ) (δ : ℝ≥0) :
    ∃ q : ℕ,
      (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g (a + 1)) γ)).card =
        n * q +
          if mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
              (monoWord g a) (monoWord g (a + 1)) 0 then 1 else 0 := by
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hmul : g ^ (a + 1) * (g ^ a)⁻¹ = g := by
    rw [pow_succ', mul_assoc, mul_inv_cancel₀ hga, mul_one]
  simpa [hmul, hg] using
    badScalars_card_eq_order_mul_add_zero hg hg0 d a (a + 1) δ

open Classical in
/-- **One seed gives one full orbit.**  If a nonzero scalar is bad for a monomial stack, then
the nonzero bad set contains its complete `⟨gᵇ·(gᵃ)⁻¹⟩`-orbit, hence has size at least the
orbit order.  This is the lower-bound counterpart to
`orderOf_dvd_card_badScalars_erase_zero`. -/
theorem orderOf_le_card_badScalars_erase_zero_of_nonzero_bad {p : ℕ} [Fact p.Prime]
    {g : ZMod p} {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0)
    (d a b : ℕ) (δ : ℝ≥0) {γ : ZMod p} (hγ0 : γ ≠ 0)
    (hγbad : mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      (monoWord g a) (monoWord g b) γ) :
    orderOf (g ^ b * (g ^ a)⁻¹) ≤
      ((Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          (monoWord g a) (monoWord g b) γ)).erase 0).card := by
  classical
  set c : ZMod p := g ^ b * (g ^ a)⁻¹ with hcdef
  set Bad := (Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g b) γ)).erase 0 with hBaddef
  set O := (Finset.range (orderOf c)).image (fun k => γ * c ^ k) with hOdef
  have npos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (pow_ne_zero _ hg0) (inv_ne_zero hga)
  have hcfin : IsOfFinOrder c := by
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, ?_⟩
    have hgn : g ^ n = 1 := hg ▸ pow_orderOf_eq_one g
    rw [hcdef, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm b n, mul_comm a n, pow_mul,
      pow_mul, hgn, one_pow, one_pow, inv_one, mul_one]
  have horbmem : ∀ k : ℕ, γ * c ^ k ∈ Bad := by
    intro k
    induction k with
    | zero =>
        rw [hBaddef]
        simp [hγ0, hγbad]
    | succ k ih =>
        have hbadk : mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            (monoWord g a) (monoWord g b) (γ * c ^ k) := by
          simpa [hBaddef] using (Finset.mem_erase.mp ih).2
        have hbadnext :
            mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
              (monoWord g a) (monoWord g b) ((γ * c ^ k) * c) := by
          simpa [c] using (mcaEvent_monoStack_gamma_mul hg hg0 d a b δ (γ * c ^ k)).mp hbadk
        rw [hBaddef]
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · exact mul_ne_zero hγ0 (pow_ne_zero _ hc0)
        · simpa [pow_succ, mul_assoc] using hbadnext
  have hOsub : O ⊆ Bad := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact horbmem k
  have hinjOn : Set.InjOn (fun k => γ * c ^ k) ↑(Finset.range (orderOf c)) := by
    intro i hi j hj hij
    have hipow : c ^ i = c ^ j := mul_left_cancel₀ hγ0 hij
    exact pow_injOn_Iio_orderOf
      (by simpa using Finset.mem_range.mp (Finset.mem_coe.mp hi))
      (by simpa using Finset.mem_range.mp (Finset.mem_coe.mp hj)) hipow
  have hOcard : O.card = orderOf c := by
    rw [hOdef, Finset.card_image_of_injOn hinjOn, Finset.card_range]
  rw [← hOcard]
  exact Finset.card_le_card hOsub

open Classical in
/-- Adjacent-pair one-orbit lower bound: one nonzero bad scalar forces at least `n` nonzero
bad scalars. -/
theorem n_le_card_badScalars_adjacent_erase_zero_of_nonzero_bad {p : ℕ} [Fact p.Prime]
    {g : ZMod p} {n : ℕ} [NeZero n] (hg : orderOf g = n) (hg0 : g ≠ 0)
    (d a : ℕ) (δ : ℝ≥0) {γ : ZMod p} (hγ0 : γ ≠ 0)
    (hγbad : mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      (monoWord g a) (monoWord g (a + 1)) γ) :
    n ≤ ((Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (monoWord g a) (monoWord g (a + 1)) γ)).erase 0).card := by
  have hga : (g : ZMod p) ^ a ≠ 0 := pow_ne_zero _ hg0
  have hmul : g ^ (a + 1) * (g ^ a)⁻¹ = g := by
    rw [pow_succ', mul_assoc, mul_inv_cancel₀ hga, mul_one]
  have h := orderOf_le_card_badScalars_erase_zero_of_nonzero_bad hg hg0 d a (a + 1) δ
    hγ0 hγbad
  rwa [hmul, hg] at h

end ArkLib.ProximityGap.MonomialGammaFibration

#print axioms ArkLib.ProximityGap.MonomialGammaFibration.mcaEvent_monoStack_gamma_mul
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.badScalars_image_mul_eq
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.card_dvd_of_mul_invariant
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.orderOf_dvd_card_badScalars_erase_zero
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.n_dvd_card_badScalars_adjacent
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.badScalars_card_eq_order_mul_add_zero
#print axioms ArkLib.ProximityGap.MonomialGammaFibration.adjacent_card_eq_n_mul_add_zero
