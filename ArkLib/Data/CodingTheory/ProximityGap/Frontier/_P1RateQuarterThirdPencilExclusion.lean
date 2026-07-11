/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge

/-!
# The third pencil through a base scalar: exclusion fails at literal P1

Successor of `_P1RateQuarterPencilCountCharge.lean`.  That file reduced the predecessor
budget to `BasePencilImageCap`: at most two divided-difference pencils through a base scalar.
This file settles the question both ways.

**Characterization (proved):** the base witness's pairwise intersections are absorbed into
the pencils' aligned regions (`base_pair_inter_subset_aligned`), so for two *distinct*
pencils through the base the triple overlap `S₀ ∩ S_i ∩ S_j` has at most `k - 1` coordinates
(`base_triple_overlap_card_le`).  These are the exact structural constraints a third pencil
must satisfy — and they are satisfiable.

**Refutation (kernel-checked, literal P1):** `BasePencilImageCap` is FALSE at the canonical
P1 domain.  The partners-collinear construction puts three partners on the single pencil
`σ = (x^(2m), 1)` (`m = 2^25`, folding `μ_{2^30}` onto `μ_32`):

* `p_j = x^(2m) + γ_j` for partners `γ_j = 3, 4, 5`; base `p₀ = x^(2m) + x^m` OFF `σ` with
  `γ₀ = 2`, so the three pair pencils are pairwise distinct automatically:
  `dir_j = (γ_j - x^m)/(γ_j - γ₀)` and `dir_i - dir_j ∝ x^m - γ₀ ≠ 0`, because
  `x^m ∈ μ_32` while `2^32 ≠ 1` in `F_P`;
* classes (`e mod 32`): `B = {0..13}` carries `u = (x^(2m), 1)` (σ-aligned, `14·2^25 ≥ k`),
  `P₁ = {14..23}` carries the `π₁` pencil values (`10·2^25 ≥ k`), `P₂ = {24..27}` and
  `P₃ = {28..31}` carry `π₂, π₃` values;
* witnesses: `S₀ = P₁∪P₂∪P₃`, `S_j = B ∪ (four classes of P_j)` — all `18·2^25 ≥ T`;
* non-jointness by pinning: the partners' second row is pinned to the constant `1` on `B`
  and mismatches on `P_j` (`dir_j = 1` would force `x^m = γ₀`); the base's second row is
  pinned to `dir₁` on `P₁` and mismatches on `P₂` (`dir₁ = dir₂` forces the common value `1`
  and then `x^m = γ₀`).

Hence a genuine bad family with THREE distinct pencils through the base exists at literal P1
(`basePencilImageCap_canonicalDomain_refuted`), and the crude cap-2 consumer is dead.  The
class budget also fits `P = 4`; no finite `P`-cap with `1 + P·(N−T) ≤ N` survives (`P ≤ 2`
was required).  The surviving object is the **weighted/layered budget**: per-fiber
`fiber·(T − A_π) ≤ N − T` (already proved as `riders_pred_mul_le`), the ten-rider Johnson
crossover for the heavy layer, and the open question of summing the light layers — this is
recorded as the lane successor, not as a named cap residual, since every finite uniform cap
of the above shape is now refuted or insufficient.

Executable certificate: `scripts/probes/probe_rate_quarter_p1_third_pencil.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterThirdPencilExclusion

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ProximityGap.SharedFreshPencil
open _root_.ProximityGap.KKH26RegimeSplit

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Structural caps on a third pencil (the characterization half) -/

/-- The base-partner witness intersection is absorbed into the pair pencil's aligned
region. -/
theorem base_pair_inter_subset_aligned
    {γ₀ γj : F} (hγ : γ₀ ≠ γj) {S₀ Sj : Finset (Fin N)} {u₀ u₁ p₀ pj : Fin N → F}
    (h₀ : ∀ i ∈ S₀, p₀ i = u₀ i + γ₀ * u₁ i)
    (hj : ∀ i ∈ Sj, pj i = u₀ i + γj * u₁ i) :
    S₀ ∩ Sj ⊆ alignedSet u₀ u₁ (pencilBase γ₀ γj p₀ pj) (pencilDir γ₀ γj p₀ pj) := by
  intro x hx
  rw [mem_alignedSet_iff]
  have h₀' : ∀ i ∈ S₀, p₀ i = u₀ i + γ₀ • u₁ i := by
    intro i hi
    rw [smul_eq_mul]
    exact h₀ i hi
  have hj' : ∀ i ∈ Sj, pj i = u₀ i + γj • u₁ i := by
    intro i hi
    rw [smul_eq_mul]
    exact hj i hi
  exact pencil_agrees_on_inter hγ h₀' hj' x hx

/-- **Base-triple cap.**  For two distinct pencils through the base, the triple overlap of
the base witness with the two partner witnesses has fewer than `k` coordinates. -/
theorem base_triple_overlap_card_le (dom : Fin N ↪ F)
    {γ₀ γi γj : F} (hγi : γ₀ ≠ γi) (hγj : γ₀ ≠ γj)
    {S₀ Si Sj : Finset (Fin N)} {u₀ u₁ p₀ pi pj : Fin N → F}
    (hp₀ : p₀ ∈ predecessorCode dom) (hpi : pi ∈ predecessorCode dom)
    (hpj : pj ∈ predecessorCode dom)
    (h₀ : ∀ x ∈ S₀, p₀ x = u₀ x + γ₀ * u₁ x)
    (hi : ∀ x ∈ Si, pi x = u₀ x + γi * u₁ x)
    (hj : ∀ x ∈ Sj, pj x = u₀ x + γj * u₁ x)
    (hne : (pencilBase γ₀ γi p₀ pi, pencilDir γ₀ γi p₀ pi) ≠
      (pencilBase γ₀ γj p₀ pj, pencilDir γ₀ γj p₀ pj)) :
    (S₀ ∩ Si ∩ Sj).card ≤ k - 1 := by
  have hsub : S₀ ∩ Si ∩ Sj ⊆
      alignedSet u₀ u₁ (pencilBase γ₀ γi p₀ pi) (pencilDir γ₀ γi p₀ pi) ∩
      alignedSet u₀ u₁ (pencilBase γ₀ γj p₀ pj) (pencilDir γ₀ γj p₀ pj) := by
    intro x hx
    obtain ⟨hx0i, hxj⟩ := Finset.mem_inter.mp hx
    obtain ⟨hx0, hxi⟩ := Finset.mem_inter.mp hx0i
    exact Finset.mem_inter.mpr
      ⟨base_pair_inter_subset_aligned hγi h₀ hi (Finset.mem_inter.mpr ⟨hx0, hxi⟩),
        base_pair_inter_subset_aligned hγj h₀ hj (Finset.mem_inter.mpr ⟨hx0, hxj⟩)⟩
  exact (Finset.card_le_card hsub).trans
    (alignedSet_inter_card_lt_k dom u₀ u₁
      (pencilBase_mem _ hp₀ hpi) (pencilDir_mem _ hp₀ hpi)
      (pencilBase_mem _ hp₀ hpj) (pencilDir_mem _ hp₀ hpj) hne)

/-! ## Residue-32 cosets of the power enumeration -/

def residue32Set (I : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun e => (e : ℕ) % 32 ∈ I)

theorem mem_residue32Set_iff (I : Finset ℕ) (e : Fin N) :
    e ∈ residue32Set I ↔ (e : ℕ) % 32 ∈ I := by
  rw [residue32Set, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem residue32Set_mono {I I' : Finset ℕ} (h : I ⊆ I') :
    residue32Set I ⊆ residue32Set I' := by
  intro e he
  rw [mem_residue32Set_iff] at he ⊢
  exact h he

theorem card_singleResidue32 (r : ℕ) (hr : r < 32) :
    (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 32 = r)).card = 2 ^ 25 := by
  have hcard : (Finset.univ : Finset (Fin (2 ^ 25))).card = 2 ^ 25 := by simp
  rw [← hcard]
  apply Finset.card_nbij'
    (fun e : Fin N => (⟨(e : ℕ) / 32, by
      have he := e.isLt
      have hN : N = 1073741824 := by norm_num [N]
      omega⟩ : Fin (2 ^ 25)))
    (fun s : Fin (2 ^ 25) => (⟨32 * (s : ℕ) + r, by
      have := s.isLt
      have h25 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
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

theorem residue32Set_card (I : Finset ℕ) (hI : ∀ r ∈ I, r < 32) :
    (residue32Set I).card = I.card * 2 ^ 25 := by
  classical
  have hsplit : residue32Set I =
      I.biUnion (fun r => Finset.univ.filter (fun e : Fin N => (e : ℕ) % 32 = r)) := by
    ext e
    rw [mem_residue32Set_iff, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨(e : ℕ) % 32, h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · rintro ⟨r, hr, he⟩
      rw [Finset.mem_filter] at he
      rw [he.2]
      exact hr
  rw [hsplit, Finset.card_biUnion]
  · have hsum : ∑ r ∈ I,
        (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 32 = r)).card
          = ∑ _r ∈ I, 2 ^ 25 :=
      Finset.sum_congr rfl (fun r hr => card_singleResidue32 r (hI r hr))
    rw [hsum, Finset.sum_const, smul_eq_mul]
  · intro r hr r' hr' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    exact hne (he.2.symm.trans he'.2)

/-! ## Small numerals are honest in `F_P` -/

theorem natCast_ne_zero_of_lt_P {c : ℕ} (h0 : 0 < c) (hcP : c < P) :
    ((c : ℕ) : F) ≠ 0 := by
  intro h
  have hdvd : P ∣ c := (ZMod.natCast_eq_zero_iff c P).mp h
  have hle := Nat.le_of_dvd h0 hdvd
  omega

theorem lt_P_of_le_pow32 {c : ℕ} (hc : c ≤ 4294967295) : c < P := by
  have hbig : (4294967295 : ℕ) <
      365375409332725729550921208179070755120141565953 := by norm_num
  have hP : P = 365375409332725729550921208179070755120141565953 := rfl
  omega

theorem one_ne_zero_F : (1 : F) ≠ 0 := one_ne_zero

theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  have := natCast_ne_zero_of_lt_P (c := 2) (by norm_num)
    (lt_P_of_le_pow32 (by norm_num))
  simpa using this

theorem three_ne_zero_F : (3 : F) ≠ 0 := by
  have := natCast_ne_zero_of_lt_P (c := 3) (by norm_num)
    (lt_P_of_le_pow32 (by norm_num))
  simpa using this

theorem two_ne_three : (2 : F) ≠ 3 := by
  intro h
  apply one_ne_zero_F
  linear_combination -h

theorem two_ne_four : (2 : F) ≠ 4 := by
  intro h
  apply two_ne_zero_F
  linear_combination -h

theorem two_ne_five : (2 : F) ≠ 5 := by
  intro h
  apply three_ne_zero_F
  linear_combination -h

theorem three_ne_four : (3 : F) ≠ 4 := by
  intro h
  apply one_ne_zero_F
  linear_combination -h

theorem three_ne_five : (3 : F) ≠ 5 := by
  intro h
  apply two_ne_zero_F
  linear_combination -h

theorem four_ne_five : (4 : F) ≠ 5 := by
  intro h
  apply one_ne_zero_F
  linear_combination -h

/-- `γ₀ = 2` is not a 32nd root of unity in `F_P`. -/
theorem two_pow_32_ne_one : (2 : F) ^ 32 ≠ 1 := by
  intro h
  apply natCast_ne_zero_of_lt_P (c := 4294967295) (by norm_num)
    (lt_P_of_le_pow32 le_rfl)
  push_cast
  linear_combination h

/-! ## The construction -/

section Construction

variable (g : F)

/-- The canonical fold atom `x^m = (g^e)^(2^25)`.  Every construction formula is phrased in
terms of `xm g e`, so all ring reasoning shares one elaboration of the big power. -/
noncomputable def xm : Fin N → F := fun e => (g ^ (e : ℕ)) ^ ((2 : ℕ) ^ 25)

/-- Fold values never hit `γ₀ = 2`. -/
theorem xm_ne_two (hg : orderOf g = 2 ^ 30) (e : Fin N) : xm g e ≠ 2 := by
  intro h
  apply two_pow_32_ne_one
  have hxm : xm g e = (g ^ ((e : Fin N) : ℕ)) ^ ((2 : ℕ) ^ 25) := rfl
  rw [← h, hxm, ← pow_mul, ← pow_mul]
  have h1 : g ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hexp : ((e : Fin N) : ℕ) * (2 ^ 25 * 32) = 2 ^ 30 * ((e : Fin N) : ℕ) := by
    have h25 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    omega
  rw [hexp, pow_mul, h1, one_pow]

/-- The four bad scalars: base `2`, partners `3, 4, 5`. -/
def gamP : Fin 3 → F := ![3, 4, 5]

theorem gamP_sub_ne_zero (j : Fin 3) : gamP j - 2 ≠ 0 := by
  fin_cases j
  · show (3 : F) - 2 ≠ 0
    intro h
    exact one_ne_zero_F (by linear_combination h)
  · show (4 : F) - 2 ≠ 0
    intro h
    exact two_ne_zero_F (by linear_combination h)
  · show (5 : F) - 2 ≠ 0
    intro h
    exact three_ne_zero_F (by linear_combination h)

theorem gamP_pairwise_ne :
    gamP 0 ≠ gamP 1 ∧ gamP 0 ≠ gamP 2 ∧ gamP 1 ≠ gamP 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show (3 : F) ≠ 4
    exact three_ne_four
  · show (3 : F) ≠ 5
    exact three_ne_five
  · show (4 : F) ≠ 5
    exact four_ne_five

/-- The base witness codeword `p₀ = x^(2m) + x^m` (off the partners' pencil). -/
noncomputable def p0fun : Fin N → F := fun e => xm g e ^ 2 + xm g e

/-- The partner witness codewords `p_j = x^(2m) + γ_j` (all on `σ = (x^(2m), 1)`). -/
noncomputable def pPfun (j : Fin 3) : Fin N → F := fun e => xm g e ^ 2 + gamP j

/-- The witness-codeword selector of the bad family. -/
noncomputable def pf : F → Fin N → F := fun γ =>
  if γ = 3 then pPfun g 0
  else if γ = 4 then pPfun g 1
  else if γ = 5 then pPfun g 2
  else p0fun g

theorem pf_two : pf g 2 = p0fun g := by
  rw [pf, if_neg two_ne_three, if_neg two_ne_four, if_neg two_ne_five]

theorem pf_three : pf g 3 = pPfun g 0 := by
  rw [pf, if_pos rfl]

theorem pf_four : pf g 4 = pPfun g 1 := by
  rw [pf, if_neg (fun h => three_ne_four h.symm), if_pos rfl]

theorem pf_five : pf g 5 = pPfun g 2 := by
  rw [pf, if_neg (fun h => three_ne_five h.symm),
    if_neg (fun h => four_ne_five h.symm), if_pos rfl]

theorem pf_gamP (j : Fin 3) : pf g (gamP j) = pPfun g j := by
  fin_cases j
  · exact pf_three g
  · exact pf_four g
  · exact pf_five g

/-- The pair pencils through the base, as produced by the fiber machinery. -/
noncomputable def dirF (j : Fin 3) : Fin N → F := (pencilOf (pf g) 2 (gamP j)).2

noncomputable def baseF (j : Fin 3) : Fin N → F := (pencilOf (pf g) 2 (gamP j)).1

theorem pencilOf_eq (j : Fin 3) :
    pencilOf (pf g) 2 (gamP j) = (baseF g j, dirF g j) := rfl

theorem dirF_eq_pencilDir (j : Fin 3) :
    dirF g j = pencilDir (2 : F) (gamP j) (p0fun g) (pPfun g j) := by
  rw [dirF, pencilOf, pf_two, pf_gamP]

theorem baseF_eq_pencilBase (j : Fin 3) :
    baseF g j = pencilBase (2 : F) (gamP j) (p0fun g) (pPfun g j) := by
  rw [baseF, pencilOf, pf_two, pf_gamP]

theorem dirF_apply (j : Fin 3) (e : Fin N) :
    dirF g j e = (gamP j - 2)⁻¹ * (gamP j - xm g e) := by
  rw [dirF_eq_pencilDir, pencilDir]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hsub : pPfun g j e - p0fun g e = gamP j - xm g e := by
    show (xm g e ^ 2 + gamP j) - (xm g e ^ 2 + xm g e) = _
    rw [add_sub_add_left_eq_sub]
  rw [hsub]

theorem baseF_apply (j : Fin 3) (e : Fin N) :
    baseF g j e = p0fun g e - 2 * dirF g j e := by
  rw [baseF_eq_pencilBase, pencilBase]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← dirF_eq_pencilDir]

/-- The scaled direction identity `(γ_j − 2)·dir_j = γ_j − x^m`. -/
theorem dirF_scaled (j : Fin 3) (e : Fin N) :
    (gamP j - 2) * dirF g j e = gamP j - xm g e := by
  rw [dirF_apply, ← mul_assoc, mul_inv_cancel₀ (gamP_sub_ne_zero j), one_mul]

/-- Distinct partners give distinct directions (evaluated anywhere). -/
theorem dirF_ne (hg : orderOf g = 2 ^ 30) {i j : Fin 3} (hij : gamP i ≠ gamP j)
    (e : Fin N) : dirF g i e ≠ dirF g j e := by
  intro h
  have hi := dirF_scaled g i e
  have hj := dirF_scaled g j e
  rw [h] at hi
  have hd : dirF g j e = 1 := by
    have hsub : (gamP i - gamP j) * dirF g j e = gamP i - gamP j := by
      linear_combination hi - hj
    have hne : gamP i - gamP j ≠ 0 := sub_ne_zero_of_ne hij
    have hcancel : (gamP i - gamP j) * (dirF g j e - 1) = 0 := by
      linear_combination hsub
    rcases mul_eq_zero.mp hcancel with h' | h'
    · exact absurd h' hne
    · linear_combination h'
  apply xm_ne_two g hg e
  rw [hd, mul_one] at hj
  linear_combination hj

/-- A direction is never `1` (it would force `x^m = 2`). -/
theorem dirF_ne_one (hg : orderOf g = 2 ^ 30) (j : Fin 3) (e : Fin N) :
    dirF g j e ≠ 1 := by
  intro h
  have hs := dirF_scaled g j e
  rw [h, mul_one] at hs
  exact xm_ne_two g hg e (by linear_combination hs)

/-! ### Class layout -/

def BIdx : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}
def P1Idx : Finset ℕ := {14, 15, 16, 17, 18, 19, 20, 21, 22, 23}
def P2Idx : Finset ℕ := {24, 25, 26, 27}
def P3Idx : Finset ℕ := {28, 29, 30, 31}

def S0Idx : Finset ℕ := P1Idx ∪ P2Idx ∪ P3Idx

def SPIdx : Fin 3 → Finset ℕ := ![
  BIdx ∪ {14, 15, 16, 17}, BIdx ∪ P2Idx, BIdx ∪ P3Idx]

/-- First received row. -/
noncomputable def u0 : Fin N → F := fun e =>
  if (e : ℕ) % 32 ∈ BIdx then xm g e ^ 2
  else if (e : ℕ) % 32 ∈ P1Idx then baseF g 0 e
  else if (e : ℕ) % 32 ∈ P2Idx then baseF g 1 e
  else baseF g 2 e

/-- Second received row. -/
noncomputable def u1 : Fin N → F := fun e =>
  if (e : ℕ) % 32 ∈ BIdx then 1
  else if (e : ℕ) % 32 ∈ P1Idx then dirF g 0 e
  else if (e : ℕ) % 32 ∈ P2Idx then dirF g 1 e
  else dirF g 2 e

def Sset0 : Finset (Fin N) := residue32Set S0Idx

def SsetP (j : Fin 3) : Finset (Fin N) := residue32Set (SPIdx j)

/-- The witness-set selector of the bad family. -/
noncomputable def Sf : F → Finset (Fin N) := fun γ =>
  if γ = 3 then SsetP 0
  else if γ = 4 then SsetP 1
  else if γ = 5 then SsetP 2
  else Sset0

theorem Sf_two : Sf 2 = Sset0 := by
  rw [Sf, if_neg two_ne_three, if_neg two_ne_four, if_neg two_ne_five]

theorem Sf_three : Sf 3 = SsetP 0 := by
  rw [Sf, if_pos rfl]

theorem Sf_four : Sf 4 = SsetP 1 := by
  rw [Sf, if_neg (fun h => three_ne_four h.symm), if_pos rfl]

theorem Sf_five : Sf 5 = SsetP 2 := by
  rw [Sf, if_neg (fun h => three_ne_five h.symm),
    if_neg (fun h => four_ne_five h.symm), if_pos rfl]

/-! ### Cardinalities -/

theorem Sset0_card_ge : predecessorThreshold ≤ Sset0.card := by
  rw [Sset0, residue32Set_card S0Idx (by decide), predecessorThreshold_eq]
  have h : S0Idx.card = 18 := by decide
  rw [h]
  norm_num

theorem SsetP_card_ge (j : Fin 3) : predecessorThreshold ≤ (SsetP j).card := by
  rw [SsetP, predecessorThreshold_eq]
  fin_cases j <;>
    · rw [residue32Set_card _ (by decide)]
      norm_num
      decide

/-! ### Line agreements -/

/-- The base witness rides all three pencils: agreement on `S₀`. -/
theorem agree_base : ∀ e ∈ Sset0, p0fun g e = u0 g e + 2 * u1 g e := by
  intro e he
  have hres := (mem_residue32Set_iff S0Idx e).mp he
  have hB : (e : ℕ) % 32 ∉ BIdx := by
    have hstep : ∀ r ∈ S0Idx, r ∉ BIdx := by decide
    exact hstep _ hres
  by_cases h1 : (e : ℕ) % 32 ∈ P1Idx
  · simp only [u0, u1, if_neg hB, if_pos h1, baseF_apply]
    ring
  · by_cases h2 : (e : ℕ) % 32 ∈ P2Idx
    · simp only [u0, u1, if_neg hB, if_neg h1, if_pos h2, baseF_apply]
      ring
    · simp only [u0, u1, if_neg hB, if_neg h1, if_neg h2, baseF_apply]
      ring

/-- The pencil identity consumer: aligned pencil values satisfy the partner's line. -/
theorem partner_line_of_pencil_values (j : Fin 3) (e : Fin N)
    (h0 : u0 g e = baseF g j e) (h1 : u1 g e = dirF g j e) :
    pPfun g j e = u0 g e + gamP j * u1 g e := by
  rw [h0, h1, baseF_apply]
  have hs := dirF_scaled g j e
  have hp : pPfun g j e - p0fun g e = gamP j - xm g e := by
    show (xm g e ^ 2 + gamP j) - (xm g e ^ 2 + xm g e) = _
    rw [add_sub_add_left_eq_sub]
  linear_combination hp - hs

/-- Each partner witness agreement: `σ` on `B`, its own pencil on its `P`-block. -/
theorem agree_partner (j : Fin 3) :
    ∀ e ∈ SsetP j, pPfun g j e = u0 g e + gamP j * u1 g e := by
  intro e he
  have hres := (mem_residue32Set_iff (SPIdx j) e).mp he
  by_cases hB : (e : ℕ) % 32 ∈ BIdx
  · simp only [u0, u1, if_pos hB, pPfun, mul_one]
  · apply partner_line_of_pencil_values
    · fin_cases j
      · have h1 : (e : ℕ) % 32 ∈ P1Idx := by
          have hstep : ∀ r ∈ SPIdx 0, r ∉ BIdx → r ∈ P1Idx := by decide
          exact hstep _ hres hB
        simp [u0, hB, h1]
      · have h2 : (e : ℕ) % 32 ∈ P2Idx := by
          have hstep : ∀ r ∈ SPIdx 1, r ∉ BIdx → r ∈ P2Idx := by decide
          exact hstep _ hres hB
        have hnot1 : (e : ℕ) % 32 ∉ P1Idx := by
          have hstep : ∀ r ∈ P2Idx, r ∉ P1Idx := by decide
          exact hstep _ h2
        simp [u0, hB, hnot1, h2]
      · have h3 : (e : ℕ) % 32 ∈ P3Idx := by
          have hstep : ∀ r ∈ SPIdx 2, r ∉ BIdx → r ∈ P3Idx := by decide
          exact hstep _ hres hB
        have hnot1 : (e : ℕ) % 32 ∉ P1Idx := by
          have hstep : ∀ r ∈ P3Idx, r ∉ P1Idx := by decide
          exact hstep _ h3
        have hnot2 : (e : ℕ) % 32 ∉ P2Idx := by
          have hstep : ∀ r ∈ P3Idx, r ∉ P2Idx := by decide
          exact hstep _ h3
        simp [u0, hB, hnot1, hnot2]
    · fin_cases j
      · have h1 : (e : ℕ) % 32 ∈ P1Idx := by
          have hstep : ∀ r ∈ SPIdx 0, r ∉ BIdx → r ∈ P1Idx := by decide
          exact hstep _ hres hB
        simp [u1, hB, h1]
      · have h2 : (e : ℕ) % 32 ∈ P2Idx := by
          have hstep : ∀ r ∈ SPIdx 1, r ∉ BIdx → r ∈ P2Idx := by decide
          exact hstep _ hres hB
        have hnot1 : (e : ℕ) % 32 ∉ P1Idx := by
          have hstep : ∀ r ∈ P2Idx, r ∉ P1Idx := by decide
          exact hstep _ h2
        simp [u1, hB, hnot1, h2]
      · have h3 : (e : ℕ) % 32 ∈ P3Idx := by
          have hstep : ∀ r ∈ SPIdx 2, r ∉ BIdx → r ∈ P3Idx := by decide
          exact hstep _ hres hB
        have hnot1 : (e : ℕ) % 32 ∉ P1Idx := by
          have hstep : ∀ r ∈ P3Idx, r ∉ P1Idx := by decide
          exact hstep _ h3
        have hnot2 : (e : ℕ) % 32 ∉ P2Idx := by
          have hstep : ∀ r ∈ P3Idx, r ∉ P2Idx := by decide
          exact hstep _ h3
        simp [u1, hB, hnot1, hnot2]

/-! ### Codeword memberships -/

theorem p0fun_mem (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    p0fun g ∈ predecessorCode (powDomain g hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) + (Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 25))
    ?_ ?_
  · have hnd : ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) +
        (Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 25)).natDegree ≤ 2 ^ 26 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le
        (Polynomial.natDegree_X_pow_le _)
        ((Polynomial.natDegree_X_pow_le _).trans (by norm_num)))
    by_cases hzero : ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) +
        (Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 25)) = 0
    · rw [hzero, Polynomial.degree_zero]
      exact_mod_cast WithBot.bot_lt_coe k
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
      have hk : (2 : ℕ) ^ 26 < k := by norm_num [k]
      omega
  · intro i
    have hxm : xm g i = (g ^ ((i : Fin N) : ℕ)) ^ ((2 : ℕ) ^ 25) := rfl
    show xm g i ^ 2 + xm g i = _
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_pow,
      Polynomial.eval_X, hxm, ← pow_mul,
      show (2 : ℕ) ^ 25 * 2 = 2 ^ 26 by norm_num]
    rfl

theorem pPfun_mem (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) (j : Fin 3) :
    pPfun g j ∈ predecessorCode (powDomain g hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) + Polynomial.C (gamP j)) ?_ ?_
  · have hnd : ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) +
        Polynomial.C (gamP j)).natDegree ≤ 2 ^ 26 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le
        (Polynomial.natDegree_X_pow_le _)
        ((Polynomial.natDegree_C _).le.trans (by norm_num)))
    by_cases hzero : ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 26) +
        Polynomial.C (gamP j)) = 0
    · rw [hzero, Polynomial.degree_zero]
      exact_mod_cast WithBot.bot_lt_coe k
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
      have hk : (2 : ℕ) ^ 26 < k := by norm_num [k]
      omega
  · intro i
    have hxm : xm g i = (g ^ ((i : Fin N) : ℕ)) ^ ((2 : ℕ) ^ 25) := rfl
    show xm g i ^ 2 + gamP j = _
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hxm, ← pow_mul,
      show (2 : ℕ) ^ 25 * 2 = 2 ^ 26 by norm_num]
    rfl

theorem onefun_mem (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    (fun _ : Fin N => (1 : F)) ∈ predecessorCode (powDomain g hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (Polynomial.C (1 : F)) ?_ ?_
  · calc (Polynomial.C (1 : F)).degree ≤ 0 := Polynomial.degree_C_le
      _ < (k : WithBot ℕ) := by
        exact_mod_cast (by norm_num [k] : (0 : ℕ) < k)
  · intro i
    simp

theorem dirF_mem (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) (j : Fin 3) :
    dirF g j ∈ predecessorCode (powDomain g hg hg0) := by
  rw [dirF_eq_pencilDir]
  exact pencilDir_mem _ (p0fun_mem g hg hg0) (pPfun_mem g hg hg0 j)

/-! ### Non-jointness by pinning -/

theorem BIdx_subset_SPIdx (j : Fin 3) : BIdx ⊆ SPIdx j := by
  fin_cases j <;> decide

theorem P1Idx_subset_S0Idx : P1Idx ⊆ S0Idx := by decide

theorem Bpart_card_ge : k ≤ (residue32Set BIdx).card := by
  rw [residue32Set_card BIdx (by decide)]
  have h : BIdx.card = 14 := by decide
  rw [h]
  norm_num [k]

theorem P1part_card_ge : k ≤ (residue32Set P1Idx).card := by
  rw [residue32Set_card P1Idx (by decide)]
  have h : P1Idx.card = 10 := by decide
  rw [h]
  norm_num [k]

/-- Anchor coordinates inside each partner's `P`-block and inside `P₂` for the base. -/
def anchorP : Fin 3 → Fin N := ![
  ⟨14, by norm_num [N]⟩, ⟨24, by norm_num [N]⟩, ⟨28, by norm_num [N]⟩]

def anchor0 : Fin N := ⟨24, by norm_num [N]⟩

theorem anchorP_mem (j : Fin 3) : anchorP j ∈ SsetP j := by
  rw [SsetP, mem_residue32Set_iff]
  fin_cases j <;> decide

theorem anchor0_mem : anchor0 ∈ Sset0 := by
  rw [Sset0, mem_residue32Set_iff]
  decide

theorem u1_on_Bpart (e : Fin N) (he : e ∈ residue32Set BIdx) : u1 g e = 1 := by
  have hres := (mem_residue32Set_iff BIdx e).mp he
  simp [u1, hres]

theorem u1_on_P1part (e : Fin N) (he : e ∈ residue32Set P1Idx) :
    u1 g e = dirF g 0 e := by
  have hres := (mem_residue32Set_iff P1Idx e).mp he
  have hB : (e : ℕ) % 32 ∉ BIdx := by
    have hstep : ∀ r ∈ P1Idx, r ∉ BIdx := by decide
    exact hstep _ hres
  simp [u1, hB, hres]

theorem u1_on_P2part (e : Fin N) (he : e ∈ residue32Set P2Idx) :
    u1 g e = dirF g 1 e := by
  have hres := (mem_residue32Set_iff P2Idx e).mp he
  have hB : (e : ℕ) % 32 ∉ BIdx := by
    have hstep : ∀ r ∈ P2Idx, r ∉ BIdx := by decide
    exact hstep _ hres
  have h1 : (e : ℕ) % 32 ∉ P1Idx := by
    have hstep : ∀ r ∈ P2Idx, r ∉ P1Idx := by decide
    exact hstep _ hres
  simp [u1, hB, h1, hres]

theorem u1_on_P3part (e : Fin N) (he : e ∈ residue32Set P3Idx) :
    u1 g e = dirF g 2 e := by
  have hres := (mem_residue32Set_iff P3Idx e).mp he
  have hB : (e : ℕ) % 32 ∉ BIdx := by
    have hstep : ∀ r ∈ P3Idx, r ∉ BIdx := by decide
    exact hstep _ hres
  have h1 : (e : ℕ) % 32 ∉ P1Idx := by
    have hstep : ∀ r ∈ P3Idx, r ∉ P1Idx := by decide
    exact hstep _ hres
  have h2 : (e : ℕ) % 32 ∉ P2Idx := by
    have hstep : ∀ r ∈ P3Idx, r ∉ P2Idx := by decide
    exact hstep _ hres
  simp [u1, hB, h1, h2]

theorem u1_at_anchorP (j : Fin 3) : u1 g (anchorP j) = dirF g j (anchorP j) := by
  fin_cases j
  · exact u1_on_P1part g _ (by rw [mem_residue32Set_iff]; decide)
  · exact u1_on_P2part g _ (by rw [mem_residue32Set_iff]; decide)
  · exact u1_on_P3part g _ (by rw [mem_residue32Set_iff]; decide)

theorem u1_at_anchor0 : u1 g anchor0 = dirF g 1 anchor0 :=
  u1_on_P2part g _ (by rw [mem_residue32Set_iff]; decide)

/-- Partners' non-jointness: the second row is pinned to `1` on `B`, mismatching on the
`P_j` anchor. -/
theorem not_joint_partner (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) (j : Fin 3) :
    ¬ pairJointAgreesOn
      (predecessorCode (powDomain g hg hg0) : Set (Fin N → F)) (SsetP j) (u0 g) (u1 g) := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  have hBsub : residue32Set BIdx ⊆ SsetP j :=
    residue32Set_mono (BIdx_subset_SPIdx j)
  have hv1eq : v1 = fun _ : Fin N => (1 : F) := by
    apply predecessor_sep (powDomain g hg hg0) v1 hv1 _
      (onefun_mem g hg hg0) (residue32Set BIdx) Bpart_card_ge
    intro x hx
    rw [(hagree x (hBsub hx)).2, u1_on_Bpart g x hx]
  have hanch := (hagree (anchorP j) (anchorP_mem j)).2
  rw [hv1eq, u1_at_anchorP] at hanch
  exact dirF_ne_one g hg j (anchorP j) hanch.symm

/-- Base non-jointness: the second row is pinned to `dir₁` on `P₁`, mismatching on `P₂`. -/
theorem not_joint_base (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    ¬ pairJointAgreesOn
      (predecessorCode (powDomain g hg hg0) : Set (Fin N → F)) Sset0 (u0 g) (u1 g) := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  have hP1sub : residue32Set P1Idx ⊆ Sset0 :=
    residue32Set_mono P1Idx_subset_S0Idx
  have hv1eq : v1 = dirF g 0 := by
    apply predecessor_sep (powDomain g hg hg0) v1 hv1 _
      (dirF_mem g hg hg0 0) (residue32Set P1Idx) P1part_card_ge
    intro x hx
    rw [(hagree x (hP1sub hx)).2, u1_on_P1part g x hx]
  have hanch := (hagree anchor0 anchor0_mem).2
  rw [hv1eq, u1_at_anchor0] at hanch
  exact dirF_ne g hg gamP_pairwise_ne.1 anchor0 hanch

/-! ### The bad family and its three pencils -/

/-- The four bad scalars. -/
noncomputable def Gset : Finset F := {2, 3, 4, 5}

theorem two_mem_Gset : (2 : F) ∈ Gset := by
  rw [Gset]
  exact Finset.mem_insert_self _ _

theorem hdata (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    BadFamilyData (powDomain g hg hg0) (u0 g) (u1 g) Gset Sf (pf g) := by
  intro γ hγ
  have hmem : γ = 2 ∨ γ = 3 ∨ γ = 4 ∨ γ = 5 := by
    simpa [Gset, Finset.mem_insert] using hγ
  rcases hmem with rfl | rfl | rfl | rfl
  · rw [Sf_two, pf_two]
    exact ⟨Sset0_card_ge, p0fun_mem g hg hg0, agree_base g, not_joint_base g hg hg0⟩
  · rw [Sf_three, pf_three]
    exact ⟨SsetP_card_ge 0, pPfun_mem g hg hg0 0, agree_partner g 0,
      not_joint_partner g hg hg0 0⟩
  · rw [Sf_four, pf_four]
    exact ⟨SsetP_card_ge 1, pPfun_mem g hg hg0 1, agree_partner g 1,
      not_joint_partner g hg hg0 1⟩
  · rw [Sf_five, pf_five]
    exact ⟨SsetP_card_ge 2, pPfun_mem g hg hg0 2, agree_partner g 2,
      not_joint_partner g hg hg0 2⟩

theorem pencilOf_pairwise_ne (hg : orderOf g = 2 ^ 30) {i j : Fin 3}
    (hij : gamP i ≠ gamP j) :
    pencilOf (pf g) 2 (gamP i) ≠ pencilOf (pf g) 2 (gamP j) := by
  rw [pencilOf_eq, pencilOf_eq]
  intro h
  have hsnd := congrArg Prod.snd h
  simp only at hsnd
  exact dirF_ne g hg hij ⟨0, by norm_num [N]⟩ (congrFun hsnd _)

theorem Gset_erase_two : Gset.erase 2 = {3, 4, 5} := by
  rw [Gset, Finset.erase_insert]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact ⟨two_ne_three, two_ne_four, two_ne_five⟩

/-- **Three distinct pencils through the base.** -/
theorem pencilImage_card_eq_three :
    ∀ (hg : orderOf g = 2 ^ 30),
    ((Gset.erase 2).image (pencilOf (pf g) 2)).card = 3 := by
  intro hg
  rw [Gset_erase_two]
  rw [show ({3, 4, 5} : Finset F) =
    insert (gamP 0) (insert (gamP 1) {gamP 2}) from rfl]
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · rw [Finset.mem_singleton]
    exact pencilOf_pairwise_ne g hg gamP_pairwise_ne.2.2
  · rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨pencilOf_pairwise_ne g hg gamP_pairwise_ne.1,
      pencilOf_pairwise_ne g hg gamP_pairwise_ne.2.1⟩

/-! ### The refutation -/

/-- **`BasePencilImageCap` is false on every order-`2^30` power domain of `F_P`.** -/
theorem basePencilImageCap_refuted (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    ¬ BasePencilImageCap (powDomain g hg hg0) := by
  intro hcap
  have h := hcap (u0 g) (u1 g) Gset Sf (pf g) (hdata g hg hg0) 2 two_mem_Gset
  rw [pencilImage_card_eq_three g hg] at h
  omega

end Construction

/-- **The cap is false at the canonical P1 domain**: the pencil-count consumer with the
uniform cap `≤ 2` is dead, exactly like the shared-fresh charge before it. -/
theorem basePencilImageCap_canonicalDomain_refuted :
    ¬ BasePencilImageCap
      ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge.canonicalDomain :=
  basePencilImageCap_refuted g orderOf_g
    ArkLib.ProximityGap.Frontier.P1RateQuarterScaleConstruction.g_ne_zero

end ArkLib.ProximityGap.Frontier.P1RateQuarterThirdPencilExclusion

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterThirdPencilExclusion

#print axioms base_pair_inter_subset_aligned
#print axioms base_triple_overlap_card_le
#print axioms residue32Set_card
#print axioms two_pow_32_ne_one
#print axioms xm_ne_two
#print axioms dirF_ne
#print axioms agree_base
#print axioms agree_partner
#print axioms not_joint_partner
#print axioms not_joint_base
#print axioms hdata
#print axioms pencilImage_card_eq_three
#print axioms basePencilImageCap_refuted
#print axioms basePencilImageCap_canonicalDomain_refuted
