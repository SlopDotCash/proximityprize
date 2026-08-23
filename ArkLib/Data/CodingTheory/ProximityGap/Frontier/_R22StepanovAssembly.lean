/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20StepanovScaffold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20MobiusDischarge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovS2

/-!
# LANE S3 (#466 round 22): the Stepanov ASSEMBLY — count-to-charsum pipeline,
# generic-constant Hasse chain, small-`q` closure

This file works AGAINST the S2 interface: the moment S2 (dimension-count existence +
Hasse-derivative Leibniz vanishing) lands, everything downstream to the r=2 rung fires
automatically, WITHOUT requiring the sharp Hasse constant.

## The constant question, RESOLVED (task (a) of the lane brief)

The round-19/20 chain was pinned at the sharp Hasse constant: `LegendreCubicHasse` is
`S² ≤ 4p`, and `legendreCubicHasse_of_stepanovUpper` demands `B² ≤ 4p`.  But the
elementary Stepanov method does NOT generally reach `2√q` one-sided — classical
elementary treatments give `N⁺ ≤ q/2 + A√q` with `A` in the `2–4` range, i.e.
`S ≤ C√q` with `C = 2A` up to `4–8`.  **Audit of the actual consumer chain** (verified
by grep, 2026-07-07):

* `FourthMomentTwistBound G X Cw` (`_R17QuadrupleWeilRung.lean:202`) carries the
  constant `Cw` as a PARAMETER;
* every downstream consumer (`_R18SigmaGate`, `_R18SigmaEquidistribution` — 15 rung
  theorems —, `_R19ExplicitCharacterRung`, `_R19DepletedConstant`) quantifies over
  generic `Cw`;
* only the ADAPTERS hard-code constants: `QuarticWeilInput` pins `3√p`
  (`_R18FourthMomentTwist.lean:137`) and `LegendreCubicHasse` pins `4p`
  (`_R19HasseAudit.lean:191`).

**Conclusion: the campaign does NOT need the sharp Hasse constant anywhere.**  This
file therefore provides the whole chain with a generic constant:

```
S2Output m Dtot  (the named S2 interface Prop, this file)
  ⟹ (charSum_eq_two_nplus + hasseDeriv_stepanov_degree_count, THE FINAL COUNT)
CubicStepanovUpper F B          for any B with 2·Dtot + 3m ≤ m(B + q)
  ⟹ (legendreCubicHasseC_of_stepanovUpper, generic K; twist-halving reused)
LegendreCubicHasseC F K         (S² ≤ K·p; K = 4 ⟺ the round-19 LegendreCubicHasse)
  ⟹ (quartic_even_bound_of_cubicHasseC, K = k² ⟹ (k+1)²p)
  ⟹ (quarticWeilInputC_of_cubicHasseC, Möbius discharge reused verbatim)
QuarticWeilInputC (quadCharC F) G (k+1)     (generic-constant quartic face)
  ⟹ (fourthMoment_le_of_quarticWeilInputC, parametric round-18 reduction)
∑_s ‖T_{χ₂}(s)‖⁴ ≤ (k+4)·|G|²·p             (the r=2 rung quadratic face, Cw = k+4)
```

So an elementary Stepanov constant `C` (one-sided `S ≤ C√q`) propagates to
`Cw = C + 4` at the rung — finite for every `C`; the rung tolerates ANY constant.
At the sharp `C = 2` this recovers exactly the round-18 `Cw = 6`.

## Small `q` (task (b))

Stepanov needs `q ≥ q₀` (the S1 budget `2D + 3 < q` plus S2's dimension count).  For
`q ≤ K` the TRIVIAL bound closes the target: `S ≤ q` always
(`cubicStepanovUpper_trivial`), and `q² ≤ K·q` when `q ≤ K`
(`legendreCubicHasseC_of_card_le`).  So with achievable `K = C²` (e.g. `C = 8 ⟹
K = 64`) every field with `q ≤ K` is closed by arithmetic, and S2 only ever needs to
operate at `q > K`.  ⚠️ HONEST FLAG: if S2's actual `q₀` exceeds `K + 1`, a finite gap
`q ∈ (K, q₀)` remains and needs per-field finite verification; this cannot be settled
until S2 fixes its parameters.  The case split is packaged as
`legendreCubicHasseC_cases : q ≤ K ∨ S2OutputSized F K → LegendreCubicHasseC F K`.

## What this file PROVES (axiom-clean, real locked build)

1. **The final count** (task (a) core): `S = 2·#N⁺ + 3 − q` EXACTLY
   (`charSum_eq_two_nplus`), via the trichotomy partition `q = #N⁺ + #N⁻ + 3`
   (`card_nplus_add_nminus`, reusing `cubic_zero_count`); then
   `S2Output → m·#N⁺ ≤ deg P ≤ Dtot` (`nplus_card_le_of_s2output`, reusing the
   in-tree `hasseDeriv_stepanov_degree_count`) gives `CubicStepanovUpper F B` for
   every admissible `B` (`cubicStepanovUpper_of_s2output`).
2. **The generic-constant Hasse chain**: `LegendreCubicHasseC F K` with
   `LegendreCubicHasseC F 4 ⟺ LegendreCubicHasse F` (defeq), one-sided⟹two-sided at
   generic `K` (`legendreCubicHasseC_of_stepanovUpper`), the `(k+1)²` quartic transfer,
   the generic-constant Möbius'd quartic face, and the parametric fourth-moment rung.
3. **Small-`q` closure** and the assembled case-split pipeline
   (`fourthMoment_quadChar_of_s2output_pipeline`): from
   `q ≤ k² ∨ S2OutputSized F k²` all the way to the rung bound `(k+4)|G|²p`.
4. **Sharp-constant wiring kept alive**: `legendreCubicHasse_of_s2output_sharp` —
   IF S2 delivers `B² ≤ 4q`, the original round-19/20 chain fires unchanged.

## What remains OPEN (honest scope)

`S2Output F m Dtot` is THE named open input: the dimension-count existence of the
auxiliary polynomial + the Hasse-derivative Leibniz vanishing bookkeeping on `N⁺`
(S2 lane).  Nothing here discharges it.  The higher-order-χ faces of the rung also
remain open (round-21 `TripleLinearHasse` covers them under ITS named input).
No closure claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R22StepanovAssembly

open ArkLib.ProximityGap.Frontier.R19HasseAudit
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge
open ArkLib.ProximityGap.Frontier.R20MobiusDischarge
open ArkLib.ProximityGap.Frontier.R21StepanovS1
open ArkLib.ProximityGap.Frontier.R22StepanovS2

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The Stepanov set `N⁺` and THE FINAL COUNT `S = 2·#N⁺ + 3 − q` -/

/-- The Stepanov positive set: points where the Legendre cubic is a nonzero square.
This is exactly the set S2's auxiliary polynomial vanishes on to order `m`. -/
def NPlus (u v : F) : Finset F :=
  univ.filter fun s => quadraticChar F (s * ((s - u) * (s - v))) = 1

/-- The negative set (χ = −1). -/
def NMinus (u v : F) : Finset F :=
  univ.filter fun s => quadraticChar F (s * ((s - u) * (s - v))) = -1

/-- The char sum is exactly `#N⁺ − #N⁻` (value trichotomy, zero fibers drop). -/
theorem charSum_eq_card_sub_card (u v : F) :
    (∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) : ℤ)
      = ((NPlus u v).card : ℤ) - ((NMinus u v).card : ℤ) := by
  classical
  have hpt : ∀ s : F, (quadraticChar F (s * ((s - u) * (s - v))) : ℤ)
      = (if s ∈ NPlus u v then (1 : ℤ) else 0)
        - (if s ∈ NMinus u v then (1 : ℤ) else 0) := by
    intro s
    rcases (quadraticChar_isQuadratic F) (s * ((s - u) * (s - v))) with h | h | h <;>
      · rw [h]
        simp only [NPlus, NMinus, mem_filter, mem_univ, true_and, h]
        norm_num
  rw [Finset.sum_congr rfl fun s _ => hpt s, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  · rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The trichotomy partition**: `#N⁺ + #N⁻ + 3 = q` for `0, u, v` distinct — the 3
zero fibers are `cubic_zero_count`'s 2-torsion points, everything else is `χ = ±1`. -/
theorem card_nplus_add_nminus {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (NPlus u v).card + (NMinus u v).card + 3 = Fintype.card F := by
  classical
  set Z : Finset F := univ.filter fun s : F => s * ((s - u) * (s - v)) = 0 with hZ
  have hZ3 : Z.card = 3 := cubic_zero_count hu hv huv
  have hunion : NPlus u v ∪ (NMinus u v ∪ Z) = univ := by
    ext s
    simp only [NPlus, NMinus, hZ, mem_union, mem_filter, mem_univ, true_and, iff_true]
    rcases (quadraticChar_isQuadratic F) (s * ((s - u) * (s - v))) with h | h | h
    · exact Or.inr (Or.inr (quadraticChar_eq_zero_iff.mp h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hdisj2 : Disjoint (NMinus u v) Z := by
    rw [Finset.disjoint_left]
    intro s hsM hsZ
    simp only [NMinus, mem_filter, mem_univ, true_and] at hsM
    simp only [hZ, mem_filter, mem_univ, true_and] at hsZ
    rw [hsZ] at hsM
    simp at hsM
  have hdisj1 : Disjoint (NPlus u v) (NMinus u v ∪ Z) := by
    rw [Finset.disjoint_left]
    intro s hsP hsMZ
    simp only [NPlus, mem_filter, mem_univ, true_and] at hsP
    rcases Finset.mem_union.mp hsMZ with hsM | hsZ
    · simp only [NMinus, mem_filter, mem_univ, true_and] at hsM
      rw [hsP] at hsM
      norm_num at hsM
    · simp only [hZ, mem_filter, mem_univ, true_and] at hsZ
      rw [hsZ] at hsP
      simp at hsP
  have hcard : (NPlus u v ∪ (NMinus u v ∪ Z)).card
      = (NPlus u v).card + ((NMinus u v).card + Z.card) := by
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2]
  rw [hunion, Finset.card_univ] at hcard
  omega

/-- **THE FINAL COUNT** (the count-to-charsum bridge, task (a)):
`S = 2·#N⁺ + 3 − q` EXACTLY.  A bound on `#N⁺` IS a one-sided bound on `S`. -/
theorem charSum_eq_two_nplus {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) : ℤ)
      = 2 * ((NPlus u v).card : ℤ) + 3 - (Fintype.card F : ℤ) := by
  have h1 := charSum_eq_card_sub_card u v
  have h2 : ((NPlus u v).card : ℤ) + ((NMinus u v).card : ℤ) + 3
      = (Fintype.card F : ℤ) := by exact_mod_cast card_nplus_add_nminus hu hv huv
  omega

/-! ## 2. The S2 interface Prop and the count-side discharge -/

/-- **THE NAMED S2 INTERFACE** (open input, the S2 lane's contract): for each family
member, a NONZERO auxiliary polynomial vanishing to Hasse-order `m` on `N⁺` with total
degree at most `Dtot`.  S2 produces this from `cubic_aux_ne_zero` (S1's nonvanishing,
`_R21StepanovS1.lean`) + its own dimension count + Leibniz bookkeeping; the classical
shape is `Dtot = q·J + 3(q−1)/2 + D` (`cubic_aux_natDegree_le`). -/
def S2Output (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m Dtot : ℕ) : Prop :=
  ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
    ∃ P : F[X], P ≠ 0 ∧
      (∀ a ∈ NPlus u v, ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) ∧
      P.natDegree ≤ Dtot

/-- `S2Output ⟹ m·#N⁺ ≤ Dtot` — the in-tree Stepanov engine
(`hasseDeriv_stepanov_degree_count`) applied verbatim to the S2 output. -/
theorem nplus_card_le_of_s2output {m Dtot : ℕ} (hS : S2Output F m Dtot)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    m * (NPlus u v).card ≤ Dtot := by
  obtain ⟨P, hP0, hvan, hdeg⟩ := hS u v hu hv huv
  exact le_trans (hasseDeriv_stepanov_degree_count hP0 hvan) hdeg

/-- Concrete S2 (`_R22StepanovS2.cubic_stepanov_S2`) packaged into the assembly
interface `S2Output`.  The only extra bridge is Euler's criterion:
`quadraticChar f = 1` on `NPlus` implies `f^((q-1)/2)=1`, which is the vanishing set
used by the auxiliary polynomial theorem. -/
theorem s2Output_of_cubic_stepanov_S2 (hF : ringChar F ≠ 2)
    (hq_odd : Odd (Fintype.card F))
    {m J D : ℕ} (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1))) :
    S2Output F m
      (3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1)) := by
  intro u v hu hv huv
  obtain ⟨P, hP0, hPdeg, hPvan⟩ :=
    cubic_stepanov_S2 hq_odd hu hv huv hJ hme hD hcount
  refine ⟨P, hP0, ?_, hPdeg⟩
  intro a ha k hk
  have hχ : quadraticChar F (a * ((a - u) * (a - v))) = 1 := by
    simpa [NPlus] using ha
  have hcast : ((quadraticChar F (a * ((a - u) * (a - v))) : ℤ) : F) = 1 := by
    rw [hχ]
    norm_num
  have hpow_card : (a * ((a - u) * (a - v))) ^ (Fintype.card F / 2) = 1 := by
    simpa using (by
      rw [quadraticChar_eq_pow_of_char_ne_two' hF (a * ((a - u) * (a - v)))] at hcast
      exact hcast)
  have hexp : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rcases hq_odd with ⟨t, ht⟩
    omega
  have hpow :
      ((cubic u v).eval a) ^ ((Fintype.card F - 1) / 2) = 1 := by
    rw [cubic_eval, ← hexp]
    exact hpow_card
  exact hPvan a hpow k hk

/-- **S2 ⟹ the one-sided Stepanov bound**: any budget `B` with
`2·Dtot + 3m ≤ m·(B + q)` (i.e. `B ≥ 2·Dtot/m + 3 − q`) gives `CubicStepanovUpper F B`.
With the classical parameters (`m ≈ √q`, `Dtot ≈ m·q/2 + O(m√q)`) this yields
`B = C√q` with `C` determined by S2's dimension count. -/
theorem cubicStepanovUpper_of_s2output {m Dtot : ℕ} {B : ℤ}
    (hm : 0 < m) (hS : S2Output F m Dtot)
    (harith : 2 * (Dtot : ℤ) + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ))) :
    CubicStepanovUpper F B := by
  intro u v hu hv huv
  have hcount : ((m : ℤ)) * ((NPlus u v).card : ℤ) ≤ (Dtot : ℤ) := by
    exact_mod_cast nplus_card_le_of_s2output hS hu hv huv
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  rw [charSum_eq_two_nplus hu hv huv]
  have hmul : (m : ℤ) * (2 * ((NPlus u v).card : ℤ) + 3 - (Fintype.card F : ℤ))
      ≤ (m : ℤ) * B := by nlinarith
  exact le_of_mul_le_mul_left hmul hm'

/-! ## 3. Small `q`: the trivial bound (task (b)) -/

/-- The trivial one-sided bound `S ≤ q` — each character value is at most 1. -/
theorem cubicStepanovUpper_trivial : CubicStepanovUpper F (Fintype.card F : ℤ) := by
  intro u v _ _ _
  have h1 : ∀ s : F, (quadraticChar F (s * ((s - u) * (s - v))) : ℤ) ≤ 1 := by
    intro s
    rcases (quadraticChar_isQuadratic F) (s * ((s - u) * (s - v))) with h | h | h <;>
      rw [h] <;> norm_num
  calc (∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) : ℤ)
      ≤ ∑ _s : F, (1 : ℤ) := Finset.sum_le_sum fun s _ => h1 s
    _ = (Fintype.card F : ℤ) := by simp

/-! ## 4. The generic-constant Hasse chain -/

/-- `LegendreCubicHasse` with a GENERIC constant: `S² ≤ K·q` uniformly over the
family.  `K = 4` is the sharp Hasse value; elementary Stepanov reaches some `K = C²`
with `C` possibly `> 2`, and (this file's point) every consumer tolerates that. -/
def LegendreCubicHasseC (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (K : ℤ) : Prop :=
  ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
    (∑ s : F, quadraticChar F (s * ((s - u) * (s - v)))) ^ 2
      ≤ K * (Fintype.card F : ℤ)

/-- At the sharp constant the generic Prop IS the round-19 residual (definitional). -/
theorem legendreCubicHasseC_four_iff :
    LegendreCubicHasseC F 4 ↔ LegendreCubicHasse F :=
  Iff.rfl

/-- **One-sided ⟹ two-sided at generic `K`** (twist-negation halving reused from the
round-20 scaffold): `B ≥ 0`, `B² ≤ K·q`, and the uniform upper bound give
`LegendreCubicHasseC F K`. -/
theorem legendreCubicHasseC_of_stepanovUpper (hF : ringChar F ≠ 2) {K B : ℤ}
    (_hB0 : 0 ≤ B) (hB : B ^ 2 ≤ K * (Fintype.card F : ℤ))
    (hU : CubicStepanovUpper F B) :
    LegendreCubicHasseC F K := by
  intro u v hu hv huv
  obtain ⟨g, hgχ⟩ := quadraticChar_exists_neg_one hF
  have hg : g ≠ 0 := by
    intro h; rw [h] at hgχ; simp at hgχ
  set S : ℤ := ∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) with hS
  have hupper : S ≤ B := hU u v hu hv huv
  have hlower : -B ≤ S := by
    have htw := twist_negation hg u v
    have hU' : ∑ s : F, quadraticChar F (s * ((s - g * u) * (s - g * v))) ≤ B :=
      hU (g * u) (g * v) (mul_ne_zero hg hu) (mul_ne_zero hg hv)
        (fun h => huv (mul_left_cancel₀ hg h))
    rw [htw, hgχ] at hU'
    linarith
  calc S ^ 2 ≤ B ^ 2 := sq_le_sq' hlower hupper
    _ ≤ K * (Fintype.card F : ℤ) := hB

/-- **Small-`q` closure**: for `q ≤ K` the trivial bound already gives
`LegendreCubicHasseC F K` — the Stepanov regime restriction `q ≥ q₀` costs nothing
below `K`. -/
theorem legendreCubicHasseC_of_card_le (hF : ringChar F ≠ 2) {K : ℤ}
    (hq : (Fintype.card F : ℤ) ≤ K) :
    LegendreCubicHasseC F K := by
  have hc0 : (0 : ℤ) ≤ (Fintype.card F : ℤ) := Int.natCast_nonneg _
  refine legendreCubicHasseC_of_stepanovUpper hF hc0 ?_ cubicStepanovUpper_trivial
  nlinarith

/-! ## 5. The packaged S2 supply and the case-split assembly -/

/-- **The sized S2 supply**: S2's parameters `(m, Dtot)` together with an admissible
budget `B` hitting `B² ≤ K·q`.  This is the exact shape the S2 lane must produce at
large `q`; the arithmetic side conditions are the ones proven sufficient below. -/
def S2OutputSized (F : Type*) [Field F] [Fintype F] [DecidableEq F] (K : ℤ) : Prop :=
  ∃ (m Dtot : ℕ) (B : ℤ), 0 < m ∧ 0 ≤ B ∧
    B ^ 2 ≤ K * (Fintype.card F : ℤ) ∧
    2 * (Dtot : ℤ) + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ)) ∧
    S2Output F m Dtot

/-- Concrete S2 parameters packaged into `S2OutputSized`.  This is the existential adapter
from the raw auxiliary-polynomial theorem to the generic-constant Hasse pipeline; only the
remaining scalar arithmetic (`B² ≤ Kq` and the count budget) is left explicit. -/
theorem s2OutputSized_of_cubic_stepanov_params (hF : ringChar F ≠ 2)
    (hq_odd : Odd (Fintype.card F))
    {m J D : ℕ} (hm : 0 < m) (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1)))
    {K B : ℤ} (hB0 : 0 ≤ B) (hBK : B ^ 2 ≤ K * (Fintype.card F : ℤ))
    (harith :
      2 * ((3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) : ℕ) : ℤ)
        + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ))) :
    S2OutputSized F K := by
  refine ⟨m,
    3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1),
    B, hm, hB0, hBK, harith, ?_⟩
  exact s2Output_of_cubic_stepanov_S2 hF hq_odd hJ hme hD hcount

/-- Sized S2 supply ⟹ the generic-constant Hasse bound. -/
theorem legendreCubicHasseC_of_s2outputSized (hF : ringChar F ≠ 2) {K : ℤ}
    (h : S2OutputSized F K) :
    LegendreCubicHasseC F K := by
  obtain ⟨m, Dtot, B, hm, hB0, hBK, harith, hS⟩ := h
  exact legendreCubicHasseC_of_stepanovUpper hF hB0 hBK
    (cubicStepanovUpper_of_s2output hm hS harith)

/-- **THE ASSEMBLED CASE SPLIT** (tasks (a)+(b) wired): small fields by the trivial
bound, large fields by S2 — `LegendreCubicHasseC F K` either way. -/
theorem legendreCubicHasseC_cases (hF : ringChar F ≠ 2) {K : ℤ}
    (h : (Fintype.card F : ℤ) ≤ K ∨ S2OutputSized F K) :
    LegendreCubicHasseC F K := by
  rcases h with hq | hS
  · exact legendreCubicHasseC_of_card_le hF hq
  · exact legendreCubicHasseC_of_s2outputSized hF hS

/-- **Sharp-constant wiring kept alive**: IF S2 reaches the Hasse-sharp budget
(`B² ≤ 4q`), the ORIGINAL round-19 `LegendreCubicHasse` fires and the whole
round-20 chain (`quarticWeilInput_of_legendreCubicHasse` → `Cw = 6`) is unchanged. -/
theorem legendreCubicHasse_of_s2output_sharp (hF : ringChar F ≠ 2)
    (h : (Fintype.card F : ℤ) ≤ 4 ∨ S2OutputSized F 4) :
    LegendreCubicHasse F :=
  legendreCubicHasseC_four_iff.mp (legendreCubicHasseC_cases hF h)

/-! ## 6. The generic-constant quartic transfer `(k+1)²` -/

/-- **Generic-constant quartic transfer**: `S² ≤ k²·q` for the cubic gives
`Q² ≤ (k+1)²·q` for the ±-paired quartic (integer-clean; generalizes the round-19
`4 → 9` step, which is the case `k = 2`). -/
theorem quartic_even_bound_of_cubicHasseC (hF : ringChar F ≠ 2) {k : ℤ} (hk : 0 ≤ k)
    (hH : LegendreCubicHasseC F (k ^ 2))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (∑ t : F, quadraticChar F ((t ^ 2 - u) * (t ^ 2 - v))) ^ 2
      ≤ (k + 1) ^ 2 * (Fintype.card F : ℤ) := by
  have hsplit := quartic_even_split hF huv
  set C : ℤ := ∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) with hC
  have hHC : C ^ 2 ≤ k ^ 2 * (Fintype.card F : ℤ) := hH u v hu hv huv
  have hcard : (2 : ℤ) ≤ (Fintype.card F : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hsq : C ^ 2 ≤ (k * (Fintype.card F : ℤ)) ^ 2 := by nlinarith
  have habs := abs_le_of_sq_le_sq' hsq
    (mul_nonneg hk (Int.natCast_nonneg _))
  rw [hsplit]
  nlinarith [habs.1, habs.2]

/-! ## 7. The generic-constant quartic Weil face (Möbius discharge reused) -/

/-- `QuarticWeilInput` with a GENERIC constant `Cq` in place of the hard-coded `3`. -/
def QuarticWeilInputC (χ : MulChar F ℂ) (G : Finset F) (Cq : ℝ) : Prop :=
  ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z →
    ‖quadTerm χ z‖ ≤ Cq * Real.sqrt (Fintype.card F)

/-- At `Cq = 3` the generic Prop IS the round-18 `QuarticWeilInput` (definitional). -/
theorem quarticWeilInputC_three_iff (χ : MulChar F ℂ) (G : Finset F) :
    QuarticWeilInputC χ G 3 ↔ QuarticWeilInput χ G :=
  Iff.rfl

/-- Generic integer-to-real conversion: `L² ≤ k²·p ⟹ |L| ≤ k·√p`. -/
theorem int_abs_le_k_sqrt {L k : ℤ} {p : ℕ} (hk : 0 ≤ k) (h : L ^ 2 ≤ k ^ 2 * (p : ℤ)) :
    |((L : ℤ) : ℝ)| ≤ (k : ℝ) * Real.sqrt p := by
  have h' : ((L : ℝ)) ^ 2 ≤ ((k : ℝ)) ^ 2 * (p : ℝ) := by exact_mod_cast h
  have h1 : Real.sqrt (((L : ℝ)) ^ 2) ≤ Real.sqrt (((k : ℝ)) ^ 2 * p) :=
    Real.sqrt_le_sqrt h'
  rw [Real.sqrt_sq_eq_abs] at h1
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rwa [Real.sqrt_mul (by positivity) (p : ℝ), Real.sqrt_sq hk'] at h1

/-- All-distinct tuples at generic constant: `|intQuartic| ≤ k√p + 1` (the round-20
Möbius normal form + `LegendreCubicHasseC` at the cross-ratio). -/
theorem intQuartic_distinct_boundC {k : ℤ} (hk : 0 ≤ k)
    (hH : LegendreCubicHasseC F (k ^ 2)) (hM : MobiusCrossRatioIdentity F)
    {a b c d : F} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    |((∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d))) : ℤ) : ℝ)|
      ≤ (k : ℝ) * Real.sqrt (Fintype.card F) + 1 := by
  obtain ⟨hlam0, hlam1⟩ := crossRatio_ne_zero_ne_one hab hac had hbc hbd hcd
  set lam : F := (a - c) * (b - d) / ((a - d) * (b - c)) with hlam
  set L : ℤ := ∑ s : F, quadraticChar F (s * ((s - 1) * (s - lam))) with hL
  have hLb : L ^ 2 ≤ k ^ 2 * (Fintype.card F : ℤ) :=
    hH 1 lam one_ne_zero hlam0 (fun h => hlam1 h.symm)
  have hLr : |((L : ℤ) : ℝ)| ≤ (k : ℝ) * Real.sqrt (Fintype.card F) :=
    int_abs_le_k_sqrt hk hLb
  have hid := hM a b c d hab hac had hbc hbd hcd
  set eps : ℤ := quadraticChar F ((a - d) * (b - c)) with heps
  have hepsr : |((eps : ℤ) : ℝ)| ≤ 1 := by
    rcases (quadraticChar_isQuadratic F) ((a - d) * (b - c)) with hq | hq | hq <;>
      simp [heps, hq]
  have hcast : ((∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d))) : ℤ) : ℝ)
      = ((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ) - 1 := by
    rw [hid, ← hlam, ← hL]
    push_cast
    ring
  rw [hcast]
  calc |((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ) - 1|
      ≤ |((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ)| + |(1 : ℝ)| := abs_sub _ _
    _ = |((eps : ℤ) : ℝ)| * |((L : ℤ) : ℝ)| + 1 := by rw [abs_mul, abs_one]
    _ ≤ 1 * ((k : ℝ) * Real.sqrt (Fintype.card F)) + 1 := by
        have hLnn : 0 ≤ |((L : ℤ) : ℝ)| := abs_nonneg _
        nlinarith [hepsr, hLr, hLnn]
    _ = (k : ℝ) * Real.sqrt (Fintype.card F) + 1 := by ring

/-- **The generic-constant quadratic face**: `LegendreCubicHasseC F k²` (for `k ≥ 1`)
gives the FULL quartic Weil face at constant `k + 1` — degenerate excluded, repeated
root `≤ 2 ≤ (k+1)√p`, all-distinct `≤ k√p + 1 ≤ (k+1)√p`.  The round-20 Möbius
discharge is reused verbatim (`mobiusCrossRatioIdentity_holds`). -/
theorem quarticWeilInputC_of_cubicHasseC (hF : ringChar F ≠ 2) {k : ℤ} (hk : 1 ≤ k)
    (hH : LegendreCubicHasseC F (k ^ 2)) (G : Finset F) :
    QuarticWeilInputC (quadCharC F) G ((k : ℝ) + 1) := by
  have hM : MobiusCrossRatioIdentity F := mobiusCrossRatioIdentity_holds hF
  have hk0 : (0 : ℤ) ≤ k := by linarith
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ _hz hdeg
  simp only [IsDegenerate, not_or] at hdeg
  obtain ⟨hd1, hd2, hd3⟩ := hdeg
  rw [norm_quadTerm_quadCharC]
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := one_le_sqrt_card
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hboundify : ∀ m : ℤ, |m| ≤ 2 →
      |((m : ℤ) : ℝ)| ≤ ((k : ℝ) + 1) * Real.sqrt (Fintype.card F) := by
    intro m hm
    have h2 : |((m : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast hm
    nlinarith [hs1, hk1]
  have hrep : ∀ w r₁ r₂ : F, r₁ ≠ r₂ →
      (∀ s : F, (s - x₁) * (s - x₂) * ((s - y₁) * (s - y₂))
        = (s - w) ^ 2 * ((s - r₁) * (s - r₂))) →
      |((intQuartic ((x₁, x₂), (y₁, y₂)) : ℤ) : ℝ)|
        ≤ ((k : ℝ) + 1) * Real.sqrt (Fintype.card F) := by
    intro w r₁ r₂ hr heq
    refine hboundify _ ?_
    have hv : intQuartic ((x₁, x₂), (y₁, y₂))
        = ∑ s : F, quadraticChar F ((s - w) ^ 2 * ((s - r₁) * (s - r₂))) := by
      unfold intQuartic
      exact Finset.sum_congr rfl fun s _ => congrArg (quadraticChar F) (heq s)
    rw [hv]
    exact intQuartic_sq_factor_bound hF hr
  by_cases h12 : x₁ = x₂
  · have hy : y₁ ≠ y₂ := fun h => hd3 ⟨h12, h⟩
    exact hrep x₁ y₁ y₂ hy fun s => by rw [← h12]; ring
  by_cases h11 : x₁ = y₁
  · have hne : x₂ ≠ y₂ := fun h => hd1 ⟨h11, h⟩
    exact hrep x₁ x₂ y₂ hne fun s => by rw [h11]; ring
  by_cases h1y2 : x₁ = y₂
  · have hne : x₂ ≠ y₁ := fun h => hd2 ⟨h1y2, h⟩
    exact hrep x₁ x₂ y₁ hne fun s => by rw [h1y2]; ring
  by_cases h21 : x₂ = y₁
  · have hne : x₁ ≠ y₂ := fun h => hd2 ⟨h, h21⟩
    exact hrep x₂ x₁ y₂ hne fun s => by rw [h21]; ring
  by_cases h22 : x₂ = y₂
  · have hne : x₁ ≠ y₁ := fun h => hd1 ⟨h, h22⟩
    exact hrep x₂ x₁ y₁ hne fun s => by rw [h22]; ring
  by_cases hyy : y₁ = y₂
  · exact hrep y₁ x₁ x₂ h12 fun s => by rw [hyy]; ring
  -- all distinct: Möbius + generic-constant Hasse
  have hb := intQuartic_distinct_boundC hk0 hH hM h12 h11 h1y2 h21 h22 hyy
  calc |((intQuartic ((x₁, x₂), (y₁, y₂)) : ℤ) : ℝ)|
      ≤ (k : ℝ) * Real.sqrt (Fintype.card F) + 1 := hb
    _ ≤ ((k : ℝ) + 1) * Real.sqrt (Fintype.card F) := by nlinarith [hs1]

/-! ## 8. The parametric fourth-moment reduction (round-18 with generic `Cq`) -/

/-- **Parametric round-18 reduction**: `QuarticWeilInputC χ G Cq` and `|G|⁴ ≤ p` give
the fourth moment `≤ (3 + Cq)·|G|²·p` — degenerate mass `3|G|²·p` unconditional,
nondegenerate `|G|⁴·Cq√p ≤ Cq·|G|²·p`.  At `Cq = 3` this is exactly the round-18
`Cw = 6`; the rung constant is `Cw = 3 + Cq` and every downstream consumer takes `Cw`
as a parameter. -/
theorem fourthMoment_le_of_quarticWeilInputC (χ : MulChar F ℂ) (G : Finset F) {Cq : ℝ}
    (hCq : 0 ≤ Cq) (hW : QuarticWeilInputC χ G Cq)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      ≤ (3 + Cq) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  classical
  set Q : Finset ((F × F) × (F × F)) := (G ×ˢ G) ×ˢ (G ×ˢ G) with hQ
  set p : ℝ := (Fintype.card F : ℝ) with hpdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hp0 : 0 ≤ p := by positivity
  have hn0 : 0 ≤ n := by positivity
  have hnn : 0 ≤ ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hstep1 : ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      = ‖((∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hstep2 : ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4 ≤ ∑ z ∈ Q, ‖quadTerm χ z‖ := by
    rw [hstep1, fourthMoment_expand χ G]
    exact norm_sum_le _ _
  have hsplit : ∑ z ∈ Q, ‖quadTerm χ z‖
      = ∑ z ∈ Q.filter IsDegenerate, ‖quadTerm χ z‖
        + ∑ z ∈ Q.filter (fun z => ¬ IsDegenerate z), ‖quadTerm χ z‖ :=
    (Finset.sum_filter_add_sum_filter_not Q IsDegenerate _).symm
  have hdeg : ∑ z ∈ Q.filter IsDegenerate, ‖quadTerm χ z‖ ≤ 3 * n ^ 2 * p := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ p
      (fun z _ => norm_quadTerm_le_card χ z)) ?_
    rw [nsmul_eq_mul]
    have hcount : ((Q.filter IsDegenerate).card : ℝ) ≤ 3 * n ^ 2 := by
      have := card_filter_degenerate_le G
      rw [hndef]
      exact_mod_cast this
    nlinarith [hcount, hp0]
  have hnondeg : ∑ z ∈ Q.filter (fun z => ¬ IsDegenerate z), ‖quadTerm χ z‖
      ≤ n ^ 4 * (Cq * Real.sqrt p) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (Cq * Real.sqrt p)
      (fun z hz => ?_)) ?_
    · obtain ⟨hzQ, hzn⟩ := Finset.mem_filter.mp hz
      exact hW z hzQ hzn
    · rw [nsmul_eq_mul]
      have hcQ : (Q.card : ℝ) = n ^ 4 := by
        rw [hQ, Finset.card_product, Finset.card_product, hndef]
        push_cast; ring
      have hcle : ((Q.filter (fun z => ¬ IsDegenerate z)).card : ℝ) ≤ n ^ 4 := by
        rw [← hcQ]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hsq0 : 0 ≤ Cq * Real.sqrt p := by positivity
      nlinarith [hcle, hsq0]
  have hn2sq : n ^ 2 ≤ Real.sqrt p := by
    have h1 : Real.sqrt (n ^ 4) ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
    have hn20 : 0 ≤ n ^ 2 := sq_nonneg n
    rwa [show n ^ 4 = (n ^ 2) ^ 2 by ring, Real.sqrt_sq hn20] at h1
  have hsqmul : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  have hsqnn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have harith : n ^ 4 * (Cq * Real.sqrt p) ≤ Cq * n ^ 2 * p := by
    have hn20 : 0 ≤ n ^ 2 := sq_nonneg n
    have hmain : n ^ 2 * Real.sqrt p ≤ p := by
      have := mul_le_mul_of_nonneg_right hn2sq hsqnn
      nlinarith [this, hsqmul]
    nlinarith [mul_le_mul_of_nonneg_left hmain hn20, hCq,
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmain hn20) hCq]
  calc ∑ s : F, ‖shiftedCharSum χ G s‖ ^ 4
      ≤ ∑ z ∈ Q, ‖quadTerm χ z‖ := hstep2
    _ = _ + _ := hsplit
    _ ≤ 3 * n ^ 2 * p + n ^ 4 * (Cq * Real.sqrt p) := add_le_add hdeg hnondeg
    _ ≤ 3 * n ^ 2 * p + Cq * n ^ 2 * p := by linarith [harith]
    _ = (3 + Cq) * n ^ 2 * p := by ring

/-! ## 9. END-TO-END: the assembled pipeline to the r=2 rung quadratic face -/

/-- Generic-constant quadratic face from the case-split supply. -/
theorem quarticWeilInputC_of_pipeline (hF : ringChar F ≠ 2) {k : ℤ} (hk : 1 ≤ k)
    (h : (Fintype.card F : ℤ) ≤ k ^ 2 ∨ S2OutputSized F (k ^ 2)) (G : Finset F) :
    QuarticWeilInputC (quadCharC F) G ((k : ℝ) + 1) :=
  quarticWeilInputC_of_cubicHasseC hF hk (legendreCubicHasseC_cases hF h) G

/-- **THE PIPELINE (the lane deliverable)**: from
`q ≤ k² ∨ S2OutputSized F k²` (small-`q` arithmetic OR the S2 supply at achievable
constant `k`) all the way to the r=2 rung's quadratic-face fourth-moment bound with
the explicit weakened constant `Cw = k + 4`.  At the Hasse-sharp `k = 2` this is the
round-18/20 `Cw = 6` bound verbatim.  The moment S2 lands, this fires. -/
theorem fourthMoment_quadChar_of_s2output_pipeline (hF : ringChar F ≠ 2)
    {k : ℤ} (hk : 1 ≤ k)
    (h : (Fintype.card F : ℤ) ≤ k ^ 2 ∨ S2OutputSized F (k ^ 2))
    (G : Finset F) (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ ((k : ℝ) + 4) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hb := fourthMoment_le_of_quarticWeilInputC (quadCharC F) G
    (Cq := (k : ℝ) + 1) (by linarith)
    (quarticWeilInputC_of_pipeline hF hk h G) hp
  calc ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ (3 + ((k : ℝ) + 1)) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := hb
    _ = ((k : ℝ) + 4) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by ring

end ArkLib.ProximityGap.Frontier.R22StepanovAssembly

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.charSum_eq_card_sub_card
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.card_nplus_add_nminus
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.charSum_eq_two_nplus
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.nplus_card_le_of_s2output
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.s2Output_of_cubic_stepanov_S2
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.cubicStepanovUpper_of_s2output
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.cubicStepanovUpper_trivial
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.s2OutputSized_of_cubic_stepanov_params
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.legendreCubicHasseC_of_stepanovUpper
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.legendreCubicHasseC_of_card_le
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.legendreCubicHasseC_of_s2outputSized
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.legendreCubicHasseC_cases
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.legendreCubicHasse_of_s2output_sharp
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.quartic_even_bound_of_cubicHasseC
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.int_abs_le_k_sqrt
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.intQuartic_distinct_boundC
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.quarticWeilInputC_of_cubicHasseC
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.fourthMoment_le_of_quarticWeilInputC
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovAssembly.quarticWeilInputC_of_pipeline
#print axioms
  ArkLib.ProximityGap.Frontier.R22StepanovAssembly.fourthMoment_quadChar_of_s2output_pipeline
