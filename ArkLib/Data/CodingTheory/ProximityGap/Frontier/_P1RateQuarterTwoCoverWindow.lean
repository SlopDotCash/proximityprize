/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit

/-!
# The two-cover window is REALIZED at the literal P1 predecessor: three dense pencils exist

`three_heavy_twoCover_window` (the minimal open statement left by the layer-cake file) asked
whether three distinct near-threshold-aligned joint pairs through one base codeword can have
aligned regions this dense: each aligned on `≥ T − 1 = 592794965` coordinates of `N = 2^30`
while every pairwise aligned-region overlap stays `< k = 2^28`.  **This file constructs such a
triple at the literal canonical domain** (the order-`2^30` power domain of the certified prize
prime `P`), kernel-checked and generator-symbolic.

**The construction.**  A cyclotomic Davenport triple: with `w = gen^(2^26)` (a primitive 16-th
root of unity, so `w^8 = −1`), the degree-3 identity

  `(y−1)(y−w)(y−w^8) + (−w^2)·(y−w^2)(y−w^9)(y−w^10) = μ·(y−w^3)(y−w^5)(y−w^7)`

holds *in `ℤ[w]/(w^8+1)`* — three fully split cubics on `μ_16` with disjoint roots summing to
zero (an exact `char-0` identity, hence valid at every prime with a 16-th root of unity; the
probe found it by exhaustive search and the cofactors `Q_r` below certify it by
`linear_combination`).  Substituting `y = X^(2^26)` and multiplying by the common split factor
`E(X) = (X^(2^23) − z^15)(X^(2^24) − s^14)(X^(2^25) − v^12)` (fresh roots at levels
`μ_128, μ_64, μ_32`) produces three codeword *differences* of degree
`31·2^23 = 260046848 < k`, each vanishing on `31` full residue classes mod `128` of the power
enumeration, with exactly `7` common (triple) classes.  The three second-row codewords are
`P₁ = Df`, `P₂ = 0`, `P₃ = −Dg`; all pairs share the base witness codeword `1` (first row),
and the stack is `u₀ = 1` with `u₁` the mod-128-periodic selection table.

**What is proved** (all axiom-clean, no `sorry`/`axiom`):

* each aligned region contains `71` full residue classes: `71·2^23 = 595591168 ≥ T − 1`
  (`aligned₁_card_ge` etc. — in fact `≥ T`, one class above the predecessor level; the window
  demands only `≥ T − 1`);
* the three pairs are pairwise distinct (`pairs_distinct`), so every pairwise aligned-region
  overlap is `≤ k − 1 < k` by the in-tree `alignedSet_inter_card_lt_k`;
* consequently the weighted two-cover surplus — the quantity actually forced by over-budget,
  `Σᵢ|Aᵢ| − |A₁∪A₂∪A₃| = e₂ + 2e₃` — is `≥ 3(T−1) − N = 704643071`
  (`twoCover_surplus`), i.e. **the `87.5%`-saturated packing window is occupied**.

**Verdict.**  The two-cover window is REALIZED, not excluded: no RS-rigidity theorem at this
window can rescue the counting route to the predecessor pin.  Honest scope notes: (i) the
realized configuration has plain two-cover count `3·24+7 = 79` classes (`662700032`); the
`704643071` figure of the window prose is the *weighted* overlap mass (they coincide only at
`t = 0`), and the weighted form is what union-in-`N` forces; a plain-count-saturating triple
would additionally need a `t = 0` full-cap Davenport base on `μ_32`, left open and irrelevant
to the exclusion question; (ii) this does NOT construct bad scalars/riders and does NOT refute
`#bad ≤ N` — it kills the last counting-side obstruction, leaving the structured-floor route
(`PredecessorStructuredFloorResidual`) as the predecessor branch.

Executable certificates: `scripts/probes/probe_rate_quarter_p1_twocover_frustration.py`,
`scripts/probes/probe_rate_quarter_p1_twocover_realization.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterTwoCoverWindow

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open _root_.ProximityGap.KKH26RegimeSplit

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩

/-! ## The window arithmetic (restated) -/

/-- The window: demand `3(T−1) − N = 704643071` of cap `3(k−1) = 805306365`; the realized
class counts: `71·2^23 = 595591168 ≥ T − 1` and `3·595591168 − N ≥ 704643071`. -/
theorem window_numbers :
    3 * (predecessorThreshold - 1) - N = 704643071 ∧
    3 * (k - 1) = 805306365 ∧
    predecessorThreshold - 1 ≤ 71 * 2 ^ 23 ∧
    704643071 + N ≤ 3 * (71 * 2 ^ 23) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-! ## Residue classes mod 128 of the power enumeration -/

/-- The union of the residue-`I` classes mod `128` of the index enumeration. -/
def residueSet128 (I : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun e => (e : ℕ) % 128 ∈ I)

theorem mem_residueSet128_iff (I : Finset ℕ) (e : Fin N) :
    e ∈ residueSet128 I ↔ (e : ℕ) % 128 ∈ I := by
  rw [residueSet128, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem fin_N_lt (e : Fin N) : (e : ℕ) < 1073741824 := by
  have := e.isLt
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Each single residue class mod `128` has exactly `2^23` coordinates. -/
theorem card_singleResidue128 (r : ℕ) (hr : r < 128) :
    (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 128 = r)).card = 2 ^ 23 := by
  have hcard : (Finset.univ : Finset (Fin (2 ^ 23))).card = 2 ^ 23 := by
    simp
  rw [← hcard]
  apply Finset.card_nbij'
    (fun e : Fin N => (⟨(e : ℕ) / 128, by
      have := fin_N_lt e
      omega⟩ : Fin (2 ^ 23)))
    (fun s : Fin (2 ^ 23) => (⟨128 * (s : ℕ) + r, by
      have := s.isLt
      have h23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
      have hN : N = 1073741824 := by norm_num [N]
      omega⟩ : Fin N))
  · intro e he
    simp
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    omega
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at he
    apply Fin.ext
    simp only
    omega
  · intro s hs
    apply Fin.ext
    simp only
    omega

/-- **Coset counting mod 128**: a union of residue classes below `128` has cardinality
`(number of classes) · 2^23`. -/
theorem residueSet128_card (I : Finset ℕ) (hI : ∀ r ∈ I, r < 128) :
    (residueSet128 I).card = I.card * 2 ^ 23 := by
  classical
  have hsplit : residueSet128 I =
      I.biUnion (fun r => Finset.univ.filter (fun e : Fin N => (e : ℕ) % 128 = r)) := by
    ext e
    rw [mem_residueSet128_iff, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨(e : ℕ) % 128, h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · rintro ⟨r, hr, he⟩
      rw [Finset.mem_filter] at he
      rw [he.2]
      exact hr
  rw [hsplit, Finset.card_biUnion]
  · have hsum : ∑ r ∈ I,
        (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 128 = r)).card
          = ∑ _r ∈ I, 2 ^ 23 :=
      Finset.sum_congr rfl (fun r hr => card_singleResidue128 r (hI r hr))
    rw [hsum, Finset.sum_const, smul_eq_mul]
  · intro r hr r' hr' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    exact hne (he.2.symm.trans he'.2)

/-! ## The fold generators and exponent folding -/

section Symbolic

variable (gen : F)

/-- `ω₁₆ = gen^(2^26)`, the 16-th-root level. -/
noncomputable def w16 : F := gen ^ ((2 : ℕ) ^ 26)

/-- `ω₃₂ = gen^(2^25)`. -/
noncomputable def w32 : F := gen ^ ((2 : ℕ) ^ 25)

/-- `ω₆₄ = gen^(2^24)`. -/
noncomputable def w64 : F := gen ^ ((2 : ℕ) ^ 24)

/-- `ω₁₂₈ = gen^(2^23)`. -/
noncomputable def w128 : F := gen ^ ((2 : ℕ) ^ 23)

theorem pow_fold16 (hg : orderOf gen = 2 ^ 30) (e : ℕ) : (gen ^ e) ^ ((2 : ℕ) ^ 26) = w16 gen ^ (e % 16) := by
  have h1 : gen ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]; exact pow_orderOf_eq_one gen
  have hdecomp : e * 2 ^ 26 = 2 ^ 30 * (e / 16) + 2 ^ 26 * (e % 16) := by
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
    omega
  calc
    (gen ^ e) ^ ((2 : ℕ) ^ 26) = gen ^ (e * 2 ^ 26) := by rw [← pow_mul]
    _ = (gen ^ ((2 : ℕ) ^ 30)) ^ (e / 16) * (gen ^ ((2 : ℕ) ^ 26)) ^ (e % 16) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, hdecomp]
    _ = w16 gen ^ (e % 16) := by rw [h1, one_pow, one_mul, w16]

theorem pow_fold32 (hg : orderOf gen = 2 ^ 30) (e : ℕ) : (gen ^ e) ^ ((2 : ℕ) ^ 25) = w32 gen ^ (e % 32) := by
  have h1 : gen ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]; exact pow_orderOf_eq_one gen
  have hdecomp : e * 2 ^ 25 = 2 ^ 30 * (e / 32) + 2 ^ 25 * (e % 32) := by
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have h25 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
    omega
  calc
    (gen ^ e) ^ ((2 : ℕ) ^ 25) = gen ^ (e * 2 ^ 25) := by rw [← pow_mul]
    _ = (gen ^ ((2 : ℕ) ^ 30)) ^ (e / 32) * (gen ^ ((2 : ℕ) ^ 25)) ^ (e % 32) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, hdecomp]
    _ = w32 gen ^ (e % 32) := by rw [h1, one_pow, one_mul, w32]

theorem pow_fold64 (hg : orderOf gen = 2 ^ 30) (e : ℕ) : (gen ^ e) ^ ((2 : ℕ) ^ 24) = w64 gen ^ (e % 64) := by
  have h1 : gen ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]; exact pow_orderOf_eq_one gen
  have hdecomp : e * 2 ^ 24 = 2 ^ 30 * (e / 64) + 2 ^ 24 * (e % 64) := by
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    omega
  calc
    (gen ^ e) ^ ((2 : ℕ) ^ 24) = gen ^ (e * 2 ^ 24) := by rw [← pow_mul]
    _ = (gen ^ ((2 : ℕ) ^ 30)) ^ (e / 64) * (gen ^ ((2 : ℕ) ^ 24)) ^ (e % 64) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, hdecomp]
    _ = w64 gen ^ (e % 64) := by rw [h1, one_pow, one_mul, w64]

theorem pow_fold128 (hg : orderOf gen = 2 ^ 30) (e : ℕ) : (gen ^ e) ^ ((2 : ℕ) ^ 23) = w128 gen ^ (e % 128) := by
  have h1 : gen ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]; exact pow_orderOf_eq_one gen
  have hdecomp : e * 2 ^ 23 = 2 ^ 30 * (e / 128) + 2 ^ 23 * (e % 128) := by
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have h23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
    omega
  calc
    (gen ^ e) ^ ((2 : ℕ) ^ 23) = gen ^ (e * 2 ^ 23) := by rw [← pow_mul]
    _ = (gen ^ ((2 : ℕ) ^ 30)) ^ (e / 128) * (gen ^ ((2 : ℕ) ^ 23)) ^ (e % 128) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, hdecomp]
    _ = w128 gen ^ (e % 128) := by rw [h1, one_pow, one_mul, w128]

/-! ### Distinct powers at each level -/

theorem w16_pow_ne_one (hg : orderOf gen = 2 ^ 30) {t : ℕ} (ht : 0 < t) (ht' : t < 16) : w16 gen ^ t ≠ 1 := by
  intro h
  rw [w16, ← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
  omega

theorem w32_pow_ne_one (hg : orderOf gen = 2 ^ 30) {t : ℕ} (ht : 0 < t) (ht' : t < 32) : w32 gen ^ t ≠ 1 := by
  intro h
  rw [w32, ← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have h25 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  omega

theorem w64_pow_ne_one (hg : orderOf gen = 2 ^ 30) {t : ℕ} (ht : 0 < t) (ht' : t < 64) : w64 gen ^ t ≠ 1 := by
  intro h
  rw [w64, ← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem w128_pow_ne_one (hg : orderOf gen = 2 ^ 30) {t : ℕ} (ht : 0 < t) (ht' : t < 128) : w128 gen ^ t ≠ 1 := by
  intro h
  rw [w128, ← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have h23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
  omega

/-- Generic distinct-power helper. -/
theorem pow_ne_pow_of_lt {x : F} (hx0 : x ≠ 0) {M a b : ℕ}
    (hord : ∀ t, 0 < t → t < M → x ^ t ≠ 1) (hab : a < b) (hbM : b < M) :
    x ^ a ≠ x ^ b := by
  intro h
  have hxa : x ^ a ≠ 0 := pow_ne_zero _ hx0
  have hsplit : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  have hone : x ^ (b - a) = 1 := by
    apply mul_left_cancel₀ hxa
    rw [mul_one, ← hsplit]
    exact h.symm
  exact hord (b - a) (by omega) (by omega) hone

theorem w16_ne_zero (hg0 : gen ≠ 0) : w16 gen ≠ 0 := pow_ne_zero _ hg0
theorem w32_ne_zero (hg0 : gen ≠ 0) : w32 gen ≠ 0 := pow_ne_zero _ hg0
theorem w64_ne_zero (hg0 : gen ≠ 0) : w64 gen ≠ 0 := pow_ne_zero _ hg0
theorem w128_ne_zero (hg0 : gen ≠ 0) : w128 gen ≠ 0 := pow_ne_zero _ hg0

/-- The half-order relation: `ω₁₆^8 = −1` (primitive 16-th root in a field). -/
theorem w16_pow_eight (hg : orderOf gen = 2 ^ 30) : w16 gen ^ 8 = -1 := by
  have h16 : w16 gen ^ 16 = 1 := by
    rw [w16, ← pow_mul]
    have : (2 : ℕ) ^ 26 * 16 = 2 ^ 30 := by norm_num
    rw [this, ← hg]
    exact pow_orderOf_eq_one gen
  have hfact : (w16 gen ^ 8 - 1) * (w16 gen ^ 8 + 1) = 0 := by
    linear_combination h16
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd (sub_eq_zero.mp h) (w16_pow_ne_one gen hg (by norm_num) (by norm_num))
  · exact eq_neg_of_add_eq_zero_left h

/-! ## The residue tables -/

/-- Root residues (mod 16) of the three base cubics. -/
def A16F : Finset ℕ := {0, 1, 8}
def B16F : Finset ℕ := {2, 9, 10}
def C16F : Finset ℕ := {3, 5, 7}

/-- The seven common (triple) classes mod 128: roots of the shared split factor `E`. -/
def COMF : Finset ℕ := {12, 14, 15, 44, 76, 78, 108}

/-- Classes where `u₁` copies `P₁ = Df` (the 24 `C`-classes plus 16 private classes). -/
def U1DF : Finset ℕ :=
  {3, 4, 5, 6, 7, 11, 13, 19, 20, 21, 22, 23, 27, 28, 29, 30, 31, 35, 36, 37, 38, 39,
   43, 45, 46, 51, 53, 55, 67, 69, 71, 83, 85, 87, 99, 101, 103, 115, 117, 119}

/-- Classes where `u₁` copies `P₃ = −Dg` (16 private classes). -/
def U1NG : Finset ℕ :=
  {92, 93, 94, 95, 100, 102, 107, 109, 110, 111, 116, 118, 123, 124, 125, 126}

/-- The 71 aligned classes of pencil 1 (`A`-classes ∪ `C`-classes ∪ common ∪ 16 private). -/
def S1F : Finset ℕ :=
  {0, 1, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 27, 28,
   29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 43, 44, 45, 46, 48, 49, 51, 53, 55, 56,
   64, 65, 67, 69, 71, 72, 76, 78, 80, 81, 83, 85, 87, 88, 96, 97, 99, 101, 103, 104,
   108, 112, 113, 115, 117, 119, 120}

/-- The 71 aligned classes of pencil 2. -/
def S2F : Finset ℕ :=
  {0, 1, 2, 8, 9, 10, 12, 14, 15, 16, 17, 18, 24, 25, 26, 32, 33, 34, 40, 41, 42, 44,
   47, 48, 49, 50, 52, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 72, 73,
   74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 86, 88, 89, 90, 91, 96, 97, 98, 104, 105,
   106, 108, 112, 113, 114, 120, 121, 122}

/-- The 71 aligned classes of pencil 3. -/
def S3F : Finset ℕ :=
  {2, 3, 5, 7, 9, 10, 12, 14, 15, 18, 19, 21, 23, 25, 26, 34, 35, 37, 39, 41, 42, 44,
   50, 51, 53, 55, 57, 58, 66, 67, 69, 71, 73, 74, 76, 78, 82, 83, 85, 87, 89, 90, 92,
   93, 94, 95, 98, 99, 100, 101, 102, 103, 105, 106, 107, 108, 109, 110, 111, 114, 115,
   116, 117, 118, 119, 121, 122, 123, 124, 125, 126}

theorem S1F_card : S1F.card = 71 := by decide
theorem S2F_card : S2F.card = 71 := by decide
theorem S3F_card : S3F.card = 71 := by decide
theorem S1F_lt : ∀ r ∈ S1F, r < 128 := by decide
theorem S2F_lt : ∀ r ∈ S2F, r < 128 := by decide
theorem S3F_lt : ∀ r ∈ S3F, r < 128 := by decide

/-- Case split for pencil 1's aligned classes. -/
theorem split1 : ∀ r < 128, r ∈ S1F →
    r ∈ U1DF ∨ (r ∉ U1DF ∧ r ∉ U1NG ∧ (r % 16 ∈ A16F ∨ r ∈ COMF)) := by decide

/-- Case split for pencil 2's aligned classes: `u₁` vanishes there. -/
theorem split2 : ∀ r < 128, r ∈ S2F → r ∉ U1DF ∧ r ∉ U1NG := by decide

/-- Case split for pencil 3's aligned classes. -/
theorem split3 : ∀ r < 128, r ∈ S3F →
    (r ∉ U1DF ∧ r ∈ U1NG) ∨ (r ∉ U1DF ∧ r ∉ U1NG ∧ (r % 16 ∈ B16F ∨ r ∈ COMF)) ∨
    (r ∈ U1DF ∧ r % 16 ∈ C16F) := by decide

/-! ## The construction: shared split factor, base cubics, differences -/

/-- The shared fresh split factor `E` (evaluated, mod form). -/
noncomputable def Efun : Fin N → F := fun e =>
  (w128 gen ^ ((e : ℕ) % 128) - w128 gen ^ 15) *
    ((w64 gen ^ ((e : ℕ) % 64) - w64 gen ^ 14) *
      (w32 gen ^ ((e : ℕ) % 32) - w32 gen ^ 12))

/-- The base `A`-cubic evaluated at the fold of `e`. -/
noncomputable def Aprd : Fin N → F := fun e =>
  (w16 gen ^ ((e : ℕ) % 16) - 1) *
    ((w16 gen ^ ((e : ℕ) % 16) - w16 gen) * (w16 gen ^ ((e : ℕ) % 16) - w16 gen ^ 8))

/-- The base `B`-cubic evaluated at the fold of `e`. -/
noncomputable def Bprd : Fin N → F := fun e =>
  (w16 gen ^ ((e : ℕ) % 16) - w16 gen ^ 2) *
    ((w16 gen ^ ((e : ℕ) % 16) - w16 gen ^ 9) * (w16 gen ^ ((e : ℕ) % 16) - w16 gen ^ 10))

/-- The first codeword difference `Df = E·A`. -/
noncomputable def Dffun : Fin N → F := fun e => Efun gen e * Aprd gen e

/-- The second codeword difference `Dg = (−ω₁₆²)·E·B`. -/
noncomputable def Dgfun : Fin N → F := fun e =>
  -(w16 gen ^ 2) * (Efun gen e * Bprd gen e)

/-- The received second row: the mod-128-periodic selection table. -/
noncomputable def u1fun : Fin N → F := fun e =>
  if (e : ℕ) % 128 ∈ U1DF then Dffun gen e
  else if (e : ℕ) % 128 ∈ U1NG then -(Dgfun gen e)
  else 0

/-- The shared base row (and base witness codeword): the constant `1`. -/
noncomputable def basefun : Fin N → F := fun _ => 1

/-! ### Category vanishing lemmas -/

/-- On the common classes the shared factor `E` vanishes. -/
theorem Efun_zero_of_common (e : Fin N) (h : (e : ℕ) % 128 ∈ COMF) :
    Efun gen e = 0 := by
  have h' : (e : ℕ) % 128 = 12 ∨ (e : ℕ) % 128 = 14 ∨ (e : ℕ) % 128 = 15 ∨
      (e : ℕ) % 128 = 44 ∨ (e : ℕ) % 128 = 76 ∨ (e : ℕ) % 128 = 78 ∨
      (e : ℕ) % 128 = 108 := by
    simpa [COMF] using h
  rcases h' with h' | h' | h' | h' | h' | h' | h'
  · rw [Efun, show (e : ℕ) % 32 = 12 by omega]
    simp
  · rw [Efun, show (e : ℕ) % 64 = 14 by omega]
    simp
  · rw [Efun, h']
    simp
  · rw [Efun, show (e : ℕ) % 32 = 12 by omega]
    simp
  · rw [Efun, show (e : ℕ) % 32 = 12 by omega]
    simp
  · rw [Efun, show (e : ℕ) % 64 = 14 by omega]
    simp
  · rw [Efun, show (e : ℕ) % 32 = 12 by omega]
    simp

/-- On the `A`-residues the `A`-cubic vanishes. -/
theorem Aprd_zero_of_res (e : Fin N) (h : (e : ℕ) % 16 ∈ A16F) :
    Aprd gen e = 0 := by
  have h' : (e : ℕ) % 16 = 0 ∨ (e : ℕ) % 16 = 1 ∨ (e : ℕ) % 16 = 8 := by
    simpa [A16F] using h
  rcases h' with h' | h' | h'
  · rw [Aprd, h']
    simp
  · rw [Aprd, h']
    simp
  · rw [Aprd, h']
    simp

/-- On the `B`-residues the `B`-cubic vanishes. -/
theorem Bprd_zero_of_res (e : Fin N) (h : (e : ℕ) % 16 ∈ B16F) :
    Bprd gen e = 0 := by
  have h' : (e : ℕ) % 16 = 2 ∨ (e : ℕ) % 16 = 9 ∨ (e : ℕ) % 16 = 10 := by
    simpa [B16F] using h
  rcases h' with h' | h' | h'
  · rw [Bprd, h']
    simp
  · rw [Bprd, h']
    simp
  · rw [Bprd, h']
    simp

/-- **The cyclotomic Davenport identity** on the `C`-residues:
`A(ω^r) + (−ω²)·B(ω^r) = 0` for `r ∈ {3,5,7}`, via the explicit `ℤ[w]`-cofactors of
`w^8 + 1`. -/
theorem base_sum_zero_of_res (hg : orderOf gen = 2 ^ 30) (e : Fin N) (h : (e : ℕ) % 16 ∈ C16F) :
    Aprd gen e + -(w16 gen ^ 2) * Bprd gen e = 0 := by
  have h8 : w16 gen ^ 8 + 1 = 0 := by
    rw [w16_pow_eight gen hg]
    ring
  have h' : (e : ℕ) % 16 = 3 ∨ (e : ℕ) % 16 = 5 ∨ (e : ℕ) % 16 = 7 := by
    simpa [C16F] using h
  rcases h' with h' | h' | h'
  · rw [Aprd, Bprd, h']
    linear_combination (w16 gen ^ 4 - w16 gen ^ 6 - w16 gen ^ 7 + w16 gen ^ 10 +
      w16 gen ^ 15 - w16 gen ^ 16) * h8
  · rw [Aprd, Bprd, h']
    linear_combination (w16 gen ^ 6 - w16 gen ^ 9 - w16 gen ^ 10 - w16 gen ^ 11 +
      w16 gen ^ 13 + w16 gen ^ 14 + w16 gen ^ 15 - w16 gen ^ 18) * h8
  · rw [Aprd, Bprd, h']
    linear_combination (w16 gen ^ 8 - w16 gen ^ 9 - w16 gen ^ 14 + w16 gen ^ 17 +
      w16 gen ^ 18 - w16 gen ^ 20) * h8

/-- The nonvanishing witness class `r = 11`: `A(ω^11) + (−ω²)·B(ω^11) = 4·ω₁₆`. -/
theorem base_sum_at_eleven (hg : orderOf gen = 2 ^ 30) (e : Fin N) (h : (e : ℕ) % 16 = 11) :
    Aprd gen e + -(w16 gen ^ 2) * Bprd gen e = 4 * w16 gen := by
  have h8 : w16 gen ^ 8 + 1 = 0 := by
    rw [w16_pow_eight gen hg]
    ring
  rw [Aprd, Bprd, h]
  linear_combination (-4 * w16 gen + 3 * w16 gen ^ 9 + w16 gen ^ 12 - 3 * w16 gen ^ 17 +
    w16 gen ^ 19 - w16 gen ^ 22 - w16 gen ^ 24 + 2 * w16 gen ^ 25 + w16 gen ^ 26 -
    w16 gen ^ 27) * h8

/-! ### Codeword membership -/

/-- **RS membership of `Df`**: the sparse product polynomial has degree
`2^23 + 2^24 + 2^25 + 3·2^26 = 31·2^23 < k = 2^28`. -/
theorem Dffun_mem (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) :
    Dffun gen ∈ predecessorCode (powDomain gen hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 23) - Polynomial.C (w128 gen ^ 15)) *
      (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 24) - Polynomial.C (w64 gen ^ 14)) *
        ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 25) - Polynomial.C (w32 gen ^ 12))) *
      (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C 1) *
        (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C (w16 gen)) *
          ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C (w16 gen ^ 8)))))
    ?_ ?_
  · rw [degree_mul, degree_mul, degree_mul, degree_mul, degree_mul,
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 23) (w128 gen ^ 15),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 24) (w64 gen ^ 14),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 25) (w32 gen ^ 12),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (1 : F),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (w16 gen),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (w16 gen ^ 8)]
    exact_mod_cast (by norm_num [k] :
      (2 : ℕ) ^ 23 + (2 ^ 24 + 2 ^ 25) + (2 ^ 26 + (2 ^ 26 + 2 ^ 26)) < k)
  · intro i
    have hdom : (powDomain gen hg hg0) i = gen ^ ((i : Fin N) : ℕ) := rfl
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hdom]
    rw [pow_fold16 gen hg, pow_fold32 gen hg, pow_fold64 gen hg, pow_fold128 gen hg]
    simp only [Dffun, Efun, Aprd]

/-- **RS membership of `Dg`.** -/
theorem Dgfun_mem (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) :
    Dgfun gen ∈ predecessorCode (powDomain gen hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (Polynomial.C (-(w16 gen ^ 2)) *
      (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 23) - Polynomial.C (w128 gen ^ 15)) *
        (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 24) - Polynomial.C (w64 gen ^ 14)) *
          ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 25) - Polynomial.C (w32 gen ^ 12))) *
        (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C (w16 gen ^ 2)) *
          (((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C (w16 gen ^ 9)) *
            ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) - Polynomial.C (w16 gen ^ 10))))))
    ?_ ?_
  · have hlam : (-(w16 gen ^ 2) : F) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (w16_ne_zero gen hg0))
    rw [degree_mul, degree_mul, degree_mul, degree_mul, degree_mul, degree_mul,
      Polynomial.degree_C hlam,
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 23) (w128 gen ^ 15),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 24) (w64 gen ^ 14),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 25) (w32 gen ^ 12),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (w16 gen ^ 2),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (w16 gen ^ 9),
      degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ) ^ 26) (w16 gen ^ 10)]
    rw [zero_add]
    exact_mod_cast (by norm_num [k] :
      (2 : ℕ) ^ 23 + (2 ^ 24 + 2 ^ 25) + (2 ^ 26 + (2 ^ 26 + 2 ^ 26)) < k)
  · intro i
    have hdom : (powDomain gen hg hg0) i = gen ^ ((i : Fin N) : ℕ) := rfl
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hdom]
    rw [pow_fold16 gen hg, pow_fold32 gen hg, pow_fold64 gen hg, pow_fold128 gen hg]
    simp only [Dgfun, Efun, Bprd]

theorem neg_Dgfun_mem (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) :
    (fun e => -(Dgfun gen e)) ∈ predecessorCode (powDomain gen hg hg0) := by
  exact Submodule.neg_mem _ (Dgfun_mem gen hg hg0)

theorem basefun_mem (dom : Fin N ↪ F) : basefun ∈ predecessorCode dom := by
  apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval (Polynomial.C 1)
  · calc (Polynomial.C (1 : F)).degree ≤ 0 := Polynomial.degree_C_le
      _ < (k : ℕ) := by exact_mod_cast (by norm_num [k] : (0 : ℕ) < k)
  · intro i
    simp [basefun]

theorem zerofun_mem (dom : Fin N ↪ F) :
    (fun _ : Fin N => (0 : F)) ∈ predecessorCode dom :=
  Submodule.zero_mem _

/-! ### The aligned regions contain 71 residue classes each -/

theorem mod16_eq (e : Fin N) : (e : ℕ) % 128 % 16 = (e : ℕ) % 16 :=
  Nat.mod_mod_of_dvd _ (by norm_num)

/-- Pencil 1 (`w₁ = Df`) is aligned on all of `residueSet128 S1F`. -/
theorem aligned₁_superset :
    residueSet128 S1F ⊆ alignedSet basefun (u1fun gen) basefun (Dffun gen) := by
  intro e he
  rw [mem_residueSet128_iff] at he
  rw [mem_alignedSet_iff]
  refine ⟨rfl, ?_⟩
  rcases split1 ((e : ℕ) % 128) (Nat.mod_lt _ (by norm_num)) he with hin | ⟨h1, h2, hcat⟩
  · rw [u1fun, if_pos hin]
  · rw [u1fun, if_neg h1, if_neg h2]
    rcases hcat with hA | hC
    · rw [Dffun, Aprd_zero_of_res gen e (by rwa [mod16_eq] at hA), mul_zero]
    · rw [Dffun, Efun_zero_of_common gen e hC, zero_mul]

/-- Pencil 2 (`w₁ = 0`) is aligned on all of `residueSet128 S2F`. -/
theorem aligned₂_superset :
    residueSet128 S2F ⊆
      alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F)) := by
  intro e he
  rw [mem_residueSet128_iff] at he
  rw [mem_alignedSet_iff]
  refine ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := split2 ((e : ℕ) % 128) (Nat.mod_lt _ (by norm_num)) he
  rw [u1fun, if_neg h1, if_neg h2]

/-- Pencil 3 (`w₁ = −Dg`) is aligned on all of `residueSet128 S3F`. -/
theorem aligned₃_superset (hg : orderOf gen = 2 ^ 30) :
    residueSet128 S3F ⊆
      alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e)) := by
  intro e he
  rw [mem_residueSet128_iff] at he
  rw [mem_alignedSet_iff]
  refine ⟨rfl, ?_⟩
  rcases split3 ((e : ℕ) % 128) (Nat.mod_lt _ (by norm_num)) he with
    ⟨h1, h2⟩ | ⟨h1, h2, hcat⟩ | ⟨h1, hC⟩
  · rw [u1fun, if_neg h1, if_pos h2]
  · rw [u1fun, if_neg h1, if_neg h2]
    rcases hcat with hB | hcom
    · rw [Dgfun, Bprd_zero_of_res gen e (by rwa [mod16_eq] at hB), mul_zero, mul_zero,
        neg_zero]
    · rw [Dgfun, Efun_zero_of_common gen e hcom, zero_mul, mul_zero, neg_zero]
  · rw [u1fun, if_pos h1]
    have hsum : Dffun gen e + Dgfun gen e =
        Efun gen e * (Aprd gen e + -(w16 gen ^ 2) * Bprd gen e) := by
      rw [Dffun, Dgfun]
      ring
    rw [base_sum_zero_of_res gen hg e (by rwa [mod16_eq] at hC), mul_zero] at hsum
    linear_combination -hsum

/-- Each aligned region has at least `71·2^23 = 595591168` coordinates. -/
theorem aligned₁_card_ge :
    71 * 2 ^ 23 ≤ (alignedSet basefun (u1fun gen) basefun (Dffun gen)).card := by
  calc 71 * 2 ^ 23 = (residueSet128 S1F).card := by
        rw [residueSet128_card S1F S1F_lt, S1F_card]
    _ ≤ _ := Finset.card_le_card (aligned₁_superset gen)

theorem aligned₂_card_ge :
    71 * 2 ^ 23 ≤
      (alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F))).card := by
  calc 71 * 2 ^ 23 = (residueSet128 S2F).card := by
        rw [residueSet128_card S2F S2F_lt, S2F_card]
    _ ≤ _ := Finset.card_le_card (aligned₂_superset gen)

theorem aligned₃_card_ge (hg : orderOf gen = 2 ^ 30) :
    71 * 2 ^ 23 ≤
      (alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card := by
  calc 71 * 2 ^ 23 = (residueSet128 S3F).card := by
        rw [residueSet128_card S3F S3F_lt, S3F_card]
    _ ≤ _ := Finset.card_le_card (aligned₃_superset gen hg)

/-! ### The three second rows are pairwise distinct -/

/-- The witness coordinate `e₀ = 11`: all factors of `E`, `A`, `B` are nonzero there. -/
def e11 : Fin N := ⟨11, by norm_num [N]⟩

theorem Efun_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Efun gen e11 ≠ 0 := by
  have h128 : ((e11 : ℕ) % 128) = 11 := by norm_num [e11]
  have h64 : ((e11 : ℕ) % 64) = 11 := by norm_num [e11]
  have h32 : ((e11 : ℕ) % 32) = 11 := by norm_num [e11]
  rw [Efun, h128, h64, h32]
  refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
  · exact sub_ne_zero.mpr (pow_ne_pow_of_lt (w128_ne_zero gen hg0)
      (fun t ht ht' => w128_pow_ne_one gen hg ht ht') (by norm_num) (by norm_num))
  · exact sub_ne_zero.mpr (pow_ne_pow_of_lt (w64_ne_zero gen hg0)
      (fun t ht ht' => w64_pow_ne_one gen hg ht ht') (by norm_num) (by norm_num))
  · exact sub_ne_zero.mpr (pow_ne_pow_of_lt (w32_ne_zero gen hg0)
      (fun t ht ht' => w32_pow_ne_one gen hg ht ht') (by norm_num) (by norm_num))

theorem Aprd_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Aprd gen e11 ≠ 0 := by
  have h16 : ((e11 : ℕ) % 16) = 11 := by norm_num [e11]
  rw [Aprd, h16]
  have hne : ∀ t, 0 < t → t < 16 → w16 gen ^ t ≠ 1 :=
    fun t ht ht' => w16_pow_ne_one gen hg ht ht'
  refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
  · have := pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 0 < 11 by norm_num) (show 11 < 16 by norm_num)
    rw [pow_zero] at this
    exact sub_ne_zero.mpr (Ne.symm this)
  · have := pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 1 < 11 by norm_num) (show 11 < 16 by norm_num)
    rw [pow_one] at this
    exact sub_ne_zero.mpr this.symm
  · exact sub_ne_zero.mpr (Ne.symm (pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 8 < 11 by norm_num) (show 11 < 16 by norm_num)))

theorem Bprd_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Bprd gen e11 ≠ 0 := by
  have h16 : ((e11 : ℕ) % 16) = 11 := by norm_num [e11]
  rw [Bprd, h16]
  have hne : ∀ t, 0 < t → t < 16 → w16 gen ^ t ≠ 1 :=
    fun t ht ht' => w16_pow_ne_one gen hg ht ht'
  refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
  · exact sub_ne_zero.mpr (Ne.symm (pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 2 < 11 by norm_num) (show 11 < 16 by norm_num)))
  · exact sub_ne_zero.mpr (Ne.symm (pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 9 < 11 by norm_num) (show 11 < 16 by norm_num)))
  · exact sub_ne_zero.mpr (Ne.symm (pow_ne_pow_of_lt (w16_ne_zero gen hg0) hne
      (show 10 < 11 by norm_num) (show 11 < 16 by norm_num)))

theorem four_ne_zero : (4 : F) ≠ 0 := by decide

theorem Dffun_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Dffun gen e11 ≠ 0 :=
  mul_ne_zero (Efun_ne_zero_at11 gen hg hg0) (Aprd_ne_zero_at11 gen hg hg0)

theorem Dgfun_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Dgfun gen e11 ≠ 0 := by
  rw [Dgfun]
  exact mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero _ (w16_ne_zero gen hg0)))
    (mul_ne_zero (Efun_ne_zero_at11 gen hg hg0) (Bprd_ne_zero_at11 gen hg hg0))

/-- `Df + Dg` is nonzero at `e₀ = 11`: its base part equals `4·ω₁₆ ≠ 0`. -/
theorem sum_ne_zero_at11 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Dffun gen e11 + Dgfun gen e11 ≠ 0 := by
  have h16 : ((e11 : ℕ) % 16) = 11 := by norm_num [e11]
  have hsum : Dffun gen e11 + Dgfun gen e11 =
      Efun gen e11 * (Aprd gen e11 + -(w16 gen ^ 2) * Bprd gen e11) := by
    rw [Dffun, Dgfun]
    ring
  rw [hsum, base_sum_at_eleven gen hg e11 h16]
  exact mul_ne_zero (Efun_ne_zero_at11 gen hg hg0)
    (mul_ne_zero four_ne_zero (w16_ne_zero gen hg0))

theorem P1_ne_P2 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Dffun gen ≠ (fun _ : Fin N => (0 : F)) := by
  intro h
  exact Dffun_ne_zero_at11 gen hg hg0 (congrFun h e11)

theorem P3_ne_P2 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : (fun e => -(Dgfun gen e)) ≠ (fun _ : Fin N => (0 : F)) := by
  intro h
  have := congrFun h e11
  simp only [neg_eq_zero] at this
  exact Dgfun_ne_zero_at11 gen hg hg0 this

theorem P1_ne_P3 (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) : Dffun gen ≠ (fun e => -(Dgfun gen e)) := by
  intro h
  have h11 := congrFun h e11
  apply sum_ne_zero_at11 gen hg hg0
  linear_combination h11

/-! ## The main theorem: the window is realized at the literal P1 predecessor -/

/-- **The two-cover window is REALIZED.**  On the canonical order-`2^30` power domain of the
prize field there exist a stack `(u₀, u₁)` and three pairwise-distinct pencil pairs, all with
the same base witness codeword `1` in the first row, such that every pencil is aligned with
the stack on at least `T − 1 = 592794965` coordinates (indeed on `595591168 ≥ T`), every
pairwise aligned-region overlap is `≤ k − 1 < k = 2^28`, and the weighted two-cover surplus
meets the window demand: `704643071 + |A₁ ∪ A₂ ∪ A₃| ≤ |A₁| + |A₂| + |A₃|`. -/
theorem three_heavy_twoCover_window_realized (gen : F)
    (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0) :
    ∃ (u₀ u₁ : Fin N → F) (π₁ π₂ π₃ : (Fin N → F) × (Fin N → F)),
      -- all through one base witness codeword
      π₁.1 = π₂.1 ∧ π₂.1 = π₃.1 ∧
      -- membership: all six components are codewords of the predecessor code
      π₁.1 ∈ predecessorCode (powDomain gen hg hg0) ∧
      π₁.2 ∈ predecessorCode (powDomain gen hg hg0) ∧
      π₂.2 ∈ predecessorCode (powDomain gen hg hg0) ∧
      π₃.2 ∈ predecessorCode (powDomain gen hg hg0) ∧
      -- pairwise distinct pairs
      π₁ ≠ π₂ ∧ π₁ ≠ π₃ ∧ π₂ ≠ π₃ ∧
      -- near-threshold alignment (the window level `T − 1`)
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₁.1 π₁.2).card ∧
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₂.1 π₂.2).card ∧
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₃.1 π₃.2).card ∧
      -- pairwise overlaps strictly below `k`
      (alignedSet u₀ u₁ π₁.1 π₁.2 ∩ alignedSet u₀ u₁ π₂.1 π₂.2).card ≤ k - 1 ∧
      (alignedSet u₀ u₁ π₁.1 π₁.2 ∩ alignedSet u₀ u₁ π₃.1 π₃.2).card ≤ k - 1 ∧
      (alignedSet u₀ u₁ π₂.1 π₂.2 ∩ alignedSet u₀ u₁ π₃.1 π₃.2).card ≤ k - 1 ∧
      -- the weighted two-cover surplus meets the window demand
      704643071 +
          (alignedSet u₀ u₁ π₁.1 π₁.2 ∪ alignedSet u₀ u₁ π₂.1 π₂.2 ∪
            alignedSet u₀ u₁ π₃.1 π₃.2).card ≤
        (alignedSet u₀ u₁ π₁.1 π₁.2).card + (alignedSet u₀ u₁ π₂.1 π₂.2).card +
          (alignedSet u₀ u₁ π₃.1 π₃.2).card := by
  classical
  refine ⟨basefun, u1fun gen, (basefun, Dffun gen),
    (basefun, fun _ : Fin N => (0 : F)), (basefun, fun e => -(Dgfun gen e)),
    rfl, rfl,
    basefun_mem _, Dffun_mem gen hg hg0, zerofun_mem _, neg_Dgfun_mem gen hg hg0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Prod.mk.injEq] at h
    exact P1_ne_P2 gen hg hg0 h.2
  · intro h
    rw [Prod.mk.injEq] at h
    exact P1_ne_P3 gen hg hg0 h.2
  · intro h
    rw [Prod.mk.injEq] at h
    exact P3_ne_P2 gen hg hg0 h.2.symm
  · show predecessorThreshold - 1 ≤
      (alignedSet basefun (u1fun gen) basefun (Dffun gen)).card
    have := aligned₁_card_ge gen
    have hT := predecessorThreshold_eq
    omega
  · show predecessorThreshold - 1 ≤
      (alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F))).card
    have := aligned₂_card_ge gen
    have hT := predecessorThreshold_eq
    omega
  · show predecessorThreshold - 1 ≤
      (alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card
    have := aligned₃_card_ge gen hg
    have hT := predecessorThreshold_eq
    omega
  · show (alignedSet basefun (u1fun gen) basefun (Dffun gen) ∩
        alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F))).card ≤ k - 1
    exact alignedSet_inter_card_lt_k (powDomain gen hg hg0) basefun (u1fun gen)
      (basefun_mem _) (Dffun_mem gen hg hg0) (basefun_mem _) (zerofun_mem _)
      (fun h => P1_ne_P2 gen hg hg0 (by rw [Prod.mk.injEq] at h; exact h.2))
  · show (alignedSet basefun (u1fun gen) basefun (Dffun gen) ∩
        alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card ≤ k - 1
    exact alignedSet_inter_card_lt_k (powDomain gen hg hg0) basefun (u1fun gen)
      (basefun_mem _) (Dffun_mem gen hg hg0) (basefun_mem _) (neg_Dgfun_mem gen hg hg0)
      (fun h => P1_ne_P3 gen hg hg0 (by rw [Prod.mk.injEq] at h; exact h.2))
  · show (alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F)) ∩
        alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card ≤ k - 1
    exact alignedSet_inter_card_lt_k (powDomain gen hg hg0) basefun (u1fun gen)
      (basefun_mem _) (zerofun_mem _) (basefun_mem _) (neg_Dgfun_mem gen hg hg0)
      (fun h => P3_ne_P2 gen hg hg0 (by rw [Prod.mk.injEq] at h; exact h.2.symm))
  · show 704643071 +
        (alignedSet basefun (u1fun gen) basefun (Dffun gen) ∪
          alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F)) ∪
          alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card ≤
      (alignedSet basefun (u1fun gen) basefun (Dffun gen)).card +
        (alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F))).card +
        (alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card
    have h1 := aligned₁_card_ge gen
    have h2 := aligned₂_card_ge gen
    have h3 := aligned₃_card_ge gen hg
    have hu : (alignedSet basefun (u1fun gen) basefun (Dffun gen) ∪
        alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F)) ∪
        alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e))).card ≤ N := by
      have := Finset.card_le_univ (alignedSet basefun (u1fun gen) basefun (Dffun gen) ∪
        alignedSet basefun (u1fun gen) basefun (fun _ : Fin N => (0 : F)) ∪
        alignedSet basefun (u1fun gen) basefun (fun e => -(Dgfun gen e)))
      simpa using this
    have hN : N = 1073741824 := by norm_num [N]
    omega

/-- The realization at the certified literal generator of the prize field. -/
theorem three_heavy_twoCover_window_realized_literal :
    ∃ (gen : F) (hg : orderOf gen = 2 ^ 30) (hg0 : gen ≠ 0)
      (u₀ u₁ : Fin N → F) (π₁ π₂ π₃ : (Fin N → F) × (Fin N → F)),
      π₁.1 = π₂.1 ∧ π₂.1 = π₃.1 ∧
      π₁.1 ∈ predecessorCode (powDomain gen hg hg0) ∧
      π₁ ≠ π₂ ∧ π₁ ≠ π₃ ∧ π₂ ≠ π₃ ∧
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₁.1 π₁.2).card ∧
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₂.1 π₂.2).card ∧
      predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ π₃.1 π₃.2).card ∧
      (alignedSet u₀ u₁ π₁.1 π₁.2 ∩ alignedSet u₀ u₁ π₂.1 π₂.2).card ≤ k - 1 ∧
      (alignedSet u₀ u₁ π₁.1 π₁.2 ∩ alignedSet u₀ u₁ π₃.1 π₃.2).card ≤ k - 1 ∧
      (alignedSet u₀ u₁ π₂.1 π₂.2 ∩ alignedSet u₀ u₁ π₃.1 π₃.2).card ≤ k - 1 := by
  have hg : orderOf ArkLib.ProximityGap.PrizeShapePrimeP30.g = 2 ^ 30 := orderOf_g
  have hg0 : ArkLib.ProximityGap.PrizeShapePrimeP30.g ≠ 0 := by
    intro h
    rw [h] at hg
    have h1 : ¬ IsOfFinOrder (0 : F) := by
      rw [isOfFinOrder_iff_pow_eq_one]
      rintro ⟨t, ht, hpow⟩
      rw [zero_pow ht.ne'] at hpow
      exact zero_ne_one hpow
    rw [orderOf_eq_zero h1] at hg
    norm_num at hg
  obtain ⟨u₀, u₁, π₁, π₂, π₃, hb1, hb2, hm, _, _, _, hne1, hne2, hne3,
    ha1, ha2, ha3, ho1, ho2, ho3, _⟩ :=
    three_heavy_twoCover_window_realized ArkLib.ProximityGap.PrizeShapePrimeP30.g hg hg0
  exact ⟨_, hg, hg0, u₀, u₁, π₁, π₂, π₃, hb1, hb2, hm, hne1, hne2, hne3,
    ha1, ha2, ha3, ho1, ho2, ho3⟩

end Symbolic

end ArkLib.ProximityGap.Frontier.P1RateQuarterTwoCoverWindow

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterTwoCoverWindow

#print axioms window_numbers
#print axioms residueSet128_card
#print axioms w16_pow_eight
#print axioms base_sum_zero_of_res
#print axioms base_sum_at_eleven
#print axioms Dffun_mem
#print axioms aligned₁_card_ge
#print axioms aligned₃_card_ge
#print axioms three_heavy_twoCover_window_realized
#print axioms three_heavy_twoCover_window_realized_literal
