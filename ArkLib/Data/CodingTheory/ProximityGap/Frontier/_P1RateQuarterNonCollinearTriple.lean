/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshCoordinate

/-!
# The non-collinear shared-fresh triple at the P1 predecessor

Successor of `_P1RateQuarterSharedFreshCoordinate.lean`.  That file left one residual:
`SharedFreshTripleFree` — no fresh coordinate outside a threshold joint set carries three
distinct bad scalars.  This file settles the structure of the remaining *non-collinear* case.

**Pencil rigidity (proved):** if the three witness sets share at least `k` common
coordinates, the pairwise divided-difference pencils coincide and the three witness codewords
are forced onto ONE pencil (`triple_pencil_rigidity`).  Combined with the collinear boost this
gives the exact dichotomy at P1 (`shared_triple_dichotomy`): every shared triple of threshold
witnesses either (a) lies on one pencil which jointly agrees with the stack on at least
`352321537 ≥ k` coordinates, or (b) has triple overlap at most `k - 1`.

**The rigidity premise is NOT forced at P1 (proved):** `3T < 2N`
(`triple_floor_negative`), i.e. `3T - 2N = -369098750 < 0 < k`, so the triple-overlap floor
is vacuous and the dichotomy cannot unconditionally collapse the non-collinear branch.

**The non-collinear escape is real (kernel-checked):** an explicit `RS[32,8]` stack over
`F_37` — satisfying all four P1 shape inequalities `2T - n > 0`, `3T - 2n < 0`,
`2T ≤ n + k - 1`, `k/n = 1/4` (with `T/n = 0.5625 ≈ 0.552`) — has three distinct bad scalars
`1,2,3` at radius `7/16` (threshold `18`) whose witnesses share the fresh coordinate
`18 ∉ J = {0,…,17}`, are **not** absorbed, have triple overlap `6 ≤ k - 1 = 7`, and are
provably NOT collinear: no pencil `(w₀, w₁)` (of arbitrary functions, let alone codewords)
reproduces all three witness codewords.  The construction (second divided difference equal to
a nonzero multiple of `A₁ + r·A₂` with five roots planted in the fresh region) uses only
coset-friendly products of linear factors, so it is expected to lift to the literal smooth P1
domain; `SharedFreshTripleFree` itself is therefore conjecturally **false** and the honest
target is the refined split recorded below.

**Residual split (proved reduction):** `SharedFreshTripleFree` follows from the pair of
refined residuals `CollinearTripleFree ∧ NonCollinearTripleFree`
(`sharedFreshTripleFree_of_split`), and the rigidity theorem confines the open content of the
non-collinear side to triple overlap `≤ k - 1` (`noncollinear_triple_overlap_le`).

Executable certificate: `scripts/probes/probe_rate_quarter_p1_noncollinear_triple.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000

open Finset Polynomial
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal Polynomial

/-! ## Triple pencil rigidity (generic) -/

namespace ProximityGap.SharedFreshPencil

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {A : Type} [AddCommGroup A] [Module F A]

/-- **Triple pencil rigidity.**  If the code separates on `kk` points and the three witness
sets of three distinct bad scalars share at least `kk` common coordinates, the three witness
codewords lie on a single pencil. -/
theorem triple_pencil_rigidity (C : Submodule F (ι → A)) (kk : ℕ)
    (hsep : ∀ v ∈ C, ∀ w ∈ C, ∀ D : Finset ι,
      kk ≤ D.card → (∀ x ∈ D, v x = w x) → v = w)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃)
    {S₁ S₂ S₃ : Finset ι} {u₀ u₁ p₁ p₂ p₃ : ι → A}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) (hp₃ : p₃ ∈ C)
    (ha₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (ha₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (ha₃ : ∀ i ∈ S₃, p₃ i = u₀ i + γ₃ • u₁ i)
    (hcard : kk ≤ (S₁ ∩ S₂ ∩ S₃).card) :
    ∃ w₀ ∈ C, ∃ w₁ ∈ C,
      p₁ = w₀ + γ₁ • w₁ ∧ p₂ = w₀ + γ₂ • w₁ ∧ p₃ = w₀ + γ₃ • w₁ := by
  have hd12 := pencil_agrees_on_inter h12 ha₁ ha₂
  have hd13 := pencil_agrees_on_inter h13 ha₁ ha₃
  have heq : pencilDir γ₁ γ₂ p₁ p₂ = pencilDir γ₁ γ₃ p₁ p₃ := by
    apply hsep _ (pencilDir_mem C hp₁ hp₂) _ (pencilDir_mem C hp₁ hp₃)
      (S₁ ∩ S₂ ∩ S₃) hcard
    intro x hx
    obtain ⟨hx12, hx3⟩ := Finset.mem_inter.mp hx
    have hx13 : x ∈ S₁ ∩ S₃ :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx12).1, hx3⟩
    rw [(hd12 x hx12).2, (hd13 x hx13).2]
  refine ⟨pencilBase γ₁ γ₂ p₁ p₂, pencilBase_mem C hp₁ hp₂,
    pencilDir γ₁ γ₂ p₁ p₂, pencilDir_mem C hp₁ hp₂,
    (pencil_reproduces_first γ₁ γ₂ p₁ p₂).symm,
    (pencil_reproduces_second h12 p₁ p₂).symm, ?_⟩
  have hbase : pencilBase γ₁ γ₃ p₁ p₃ = pencilBase γ₁ γ₂ p₁ p₂ := by
    rw [pencilBase, pencilBase, heq]
  calc
    p₃ = pencilBase γ₁ γ₃ p₁ p₃ + γ₃ • pencilDir γ₁ γ₃ p₁ p₃ :=
      (pencil_reproduces_second h13 p₁ p₃).symm
    _ = pencilBase γ₁ γ₂ p₁ p₂ + γ₃ • pencilDir γ₁ γ₂ p₁ p₂ := by
      rw [hbase, heq]

end ProximityGap.SharedFreshPencil

/-! ## P1 dichotomy, arithmetic, and the refined residual split -/

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterNonCollinearTriple

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ProximityGap.SharedFreshPencil
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-- The rigidity premise is **not** forced at P1: even three full threshold witnesses need
not share a single coordinate (`3T < 2N`, i.e. `3T - 2N = -369098750`). -/
theorem triple_floor_negative : 3 * predecessorThreshold < 2 * N := by
  norm_num [predecessorThreshold_eq, N]

/-- Contrapositive of rigidity at P1: a non-collinear shared triple has triple overlap at
most `k - 1`. -/
theorem noncollinear_triple_overlap_le (dom : Fin N ↪ F)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃)
    {S₁ S₂ S₃ : Finset (Fin N)} {u₀ u₁ p₁ p₂ p₃ : Fin N → F}
    (hp₁ : p₁ ∈ predecessorCode dom) (hp₂ : p₂ ∈ predecessorCode dom)
    (hp₃ : p₃ ∈ predecessorCode dom)
    (ha₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (ha₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (ha₃ : ∀ i ∈ S₃, p₃ i = u₀ i + γ₃ • u₁ i)
    (hnc : ¬ ∃ w₀ ∈ predecessorCode dom, ∃ w₁ ∈ predecessorCode dom,
      p₁ = w₀ + γ₁ • w₁ ∧ p₂ = w₀ + γ₂ • w₁ ∧ p₃ = w₀ + γ₃ • w₁) :
    (S₁ ∩ S₂ ∩ S₃).card ≤ k - 1 := by
  by_contra hbig
  rw [not_le] at hbig
  have hk : k ≤ (S₁ ∩ S₂ ∩ S₃).card := by
    have hkval : k = 268435456 := by norm_num [k]
    omega
  exact hnc (triple_pencil_rigidity (predecessorCode dom) k
    (predecessor_sep dom) h12 h13 hp₁ hp₂ hp₃ ha₁ ha₂ ha₃ hk)

/-- **The P1 shared-triple dichotomy.**  Every triple of threshold witnesses of distinct bad
scalars either lies on one pencil that jointly agrees with the stack on at least
`352321537 ≥ k` coordinates, or has triple overlap at most `k - 1`. -/
theorem shared_triple_dichotomy (dom : Fin N ↪ F)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    {S₁ S₂ S₃ : Finset (Fin N)} {u₀ u₁ p₁ p₂ p₃ : Fin N → F}
    (hT₁ : predecessorThreshold ≤ S₁.card) (hT₂ : predecessorThreshold ≤ S₂.card)
    (hT₃ : predecessorThreshold ≤ S₃.card)
    (hp₁ : p₁ ∈ predecessorCode dom) (hp₂ : p₂ ∈ predecessorCode dom)
    (hp₃ : p₃ ∈ predecessorCode dom)
    (ha₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (ha₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (ha₃ : ∀ i ∈ S₃, p₃ i = u₀ i + γ₃ • u₁ i) :
    (∃ w₀ ∈ predecessorCode dom, ∃ w₁ ∈ predecessorCode dom,
      ∃ D : Finset (Fin N), 352321537 ≤ D.card ∧
        ∀ x ∈ D, w₀ x = u₀ x ∧ w₁ x = u₁ x) ∨
    (S₁ ∩ S₂ ∩ S₃).card ≤ k - 1 := by
  by_cases hk : k ≤ (S₁ ∩ S₂ ∩ S₃).card
  · left
    obtain ⟨w₀, hw₀, w₁, hw₁, hc₁, hc₂, hc₃⟩ :=
      triple_pencil_rigidity (predecessorCode dom) k
        (predecessor_sep dom) h12 h13 hp₁ hp₂ hp₃ ha₁ ha₂ ha₃ hk
    obtain ⟨D, hD, _, _, hagr⟩ :=
      collinear_triple_forces_high_joint_agreement dom h12 h13 h23
        hT₁ hT₂ hT₃ hw₀ hw₁ hc₁ hc₂ hc₃ ha₁ ha₂ ha₃
    exact ⟨w₀, hw₀, w₁, hw₁, D, hD, hagr⟩
  · right
    have hkval : k = 268435456 := by norm_num [k]
    omega

/-! ### The refined residual split -/

/-- One explicit shared-triple witness: codeword, threshold witness set through `i`, line
agreement, and non-jointness. -/
def SharedTripleWitnessData (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (i : Fin N)
    (γ : F) (S : Finset (Fin N)) (p : Fin N → F) : Prop :=
  i ∈ S ∧ predecessorThreshold ≤ S.card ∧ p ∈ predecessorCode dom ∧
  (∀ e ∈ S, p e = u₀ e + γ • u₁ e) ∧
  ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁

theorem sharedWitnessAt_iff_data (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (i : Fin N) (γ : F) :
    SharedWitnessAt dom u₀ u₁ i γ ↔
      ∃ S p, SharedTripleWitnessData dom u₀ u₁ i γ S p := by
  constructor
  · rintro ⟨S, hiS, hcard, ⟨p, hp, ha⟩, hno⟩
    exact ⟨S, p, hiS, hcard, hp, ha, hno⟩
  · rintro ⟨S, p, hiS, hcard, hp, ha, hno⟩
    exact ⟨S, hiS, hcard, ⟨p, hp, ha⟩, hno⟩

/-- **Refined residual (OPEN).**  No *collinear* shared-fresh triple exists at the P1
predecessor.  By the collinear boost, such a triple carries a joint pencil with agreement at
least `352321537 ≥ k`; this residual asserts that even so it cannot exist. -/
def CollinearTripleFree (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (J : Finset (Fin N)),
    predecessorThreshold ≤ J.card →
    pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) J u₀ u₁ →
    ∀ i : Fin N, i ∉ J →
    ∀ γ₁ γ₂ γ₃ : F, γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
    ∀ S₁ S₂ S₃ p₁ p₂ p₃,
      SharedTripleWitnessData dom u₀ u₁ i γ₁ S₁ p₁ →
      SharedTripleWitnessData dom u₀ u₁ i γ₂ S₂ p₂ →
      SharedTripleWitnessData dom u₀ u₁ i γ₃ S₃ p₃ →
      (∃ w₀ ∈ predecessorCode dom, ∃ w₁ ∈ predecessorCode dom,
        p₁ = w₀ + γ₁ • w₁ ∧ p₂ = w₀ + γ₂ • w₁ ∧ p₃ = w₀ + γ₃ • w₁) →
      False

/-- **Refined residual (OPEN, conjecturally FALSE).**  No *non-collinear* shared-fresh
triple exists at the P1 predecessor.  The `F_37` realization below satisfies every P1 shape
inequality with coset-friendly ingredients, so this side is expected to fail at the literal
smooth P1 domain; a kernel-checked P1-scale lift is the designated refuting move. -/
def NonCollinearTripleFree (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (J : Finset (Fin N)),
    predecessorThreshold ≤ J.card →
    pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) J u₀ u₁ →
    ∀ i : Fin N, i ∉ J →
    ∀ γ₁ γ₂ γ₃ : F, γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
    ∀ S₁ S₂ S₃ p₁ p₂ p₃,
      SharedTripleWitnessData dom u₀ u₁ i γ₁ S₁ p₁ →
      SharedTripleWitnessData dom u₀ u₁ i γ₂ S₂ p₂ →
      SharedTripleWitnessData dom u₀ u₁ i γ₃ S₃ p₃ →
      ¬ (∃ w₀ ∈ predecessorCode dom, ∃ w₁ ∈ predecessorCode dom,
        p₁ = w₀ + γ₁ • w₁ ∧ p₂ = w₀ + γ₂ • w₁ ∧ p₃ = w₀ + γ₃ • w₁) →
      False

/-- **Reduction.**  The two refined residuals jointly close the previous file's
`SharedFreshTripleFree` residual (and hence, by its consumer, the fixed-witness branch). -/
theorem sharedFreshTripleFree_of_split (dom : Fin N ↪ F)
    (hc : CollinearTripleFree dom) (hnc : NonCollinearTripleFree dom) :
    SharedFreshTripleFree dom := by
  intro u₀ u₁ J hJcard hJ i hiJ
  rintro ⟨γ₁, γ₂, γ₃, h12, h13, h23, hw₁, hw₂, hw₃⟩
  obtain ⟨S₁, p₁, hd₁⟩ := (sharedWitnessAt_iff_data dom u₀ u₁ i γ₁).mp hw₁
  obtain ⟨S₂, p₂, hd₂⟩ := (sharedWitnessAt_iff_data dom u₀ u₁ i γ₂).mp hw₂
  obtain ⟨S₃, p₃, hd₃⟩ := (sharedWitnessAt_iff_data dom u₀ u₁ i γ₃).mp hw₃
  by_cases hcol : ∃ w₀ ∈ predecessorCode dom, ∃ w₁ ∈ predecessorCode dom,
      p₁ = w₀ + γ₁ • w₁ ∧ p₂ = w₀ + γ₂ • w₁ ∧ p₃ = w₀ + γ₃ • w₁
  · exact hc u₀ u₁ J hJcard hJ i hiJ γ₁ γ₂ γ₃ h12 h13 h23
      S₁ S₂ S₃ p₁ p₂ p₃ hd₁ hd₂ hd₃ hcol
  · exact hnc u₀ u₁ J hJcard hJ i hiJ γ₁ γ₂ γ₃ h12 h13 h23
      S₁ S₂ S₃ p₁ p₂ p₃ hd₁ hd₂ hd₃ hcol

end ArkLib.ProximityGap.Frontier.P1RateQuarterNonCollinearTriple

/-! ## Realizability of the non-collinear triple at the exact P1 shape

The `RS[32,8]/F_37` certificate produced by
`scripts/probes/probe_rate_quarter_p1_noncollinear_triple.py`.  Parameters `n = 32`, `k = 8`,
`T = 18` satisfy `2T - n > 0`, `3T - 2n < 0`, `2T ≤ n + k - 1`, `k/n = 1/4`. -/

namespace ArkLib.ProximityGap.Frontier.NonCollinearTripleRealizabilityF37

open ProximityGap.SharedFreshPencil

abbrev F37 := ZMod 37

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- The 32-point evaluation domain `0,…,31` in `F_37`. -/
def domainValues : Fin 32 → F37 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def dom : Fin 32 ↪ F37 := ⟨domainValues, by decide⟩

/-- First received row. -/
def u0 : Fin 32 → F37 := ![
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
  17, 18, 4, 27, 24, 19, 11, 5, 28, 14, 26, 2, 12, 25, 29, 27]

/-- Second received row. -/
def u1 : Fin 32 → F37 := ![
  2, 3, 10, 29, 29, 16, 33, 12, 33, 28, 3, 1, 28, 16, 8, 10,
  28, 31, 30, 2, 2, 14, 8, 27, 24, 17, 28, 22, 31, 22, 5, 22]

def u : WordStack F37 (Fin 2) (Fin 32) := ![u0, u1]

@[simp] theorem u_zero : u 0 = u0 := rfl
@[simp] theorem u_one : u 1 = u1 := rfl

/-- A generic degree-`≤ 7` polynomial from its eight coefficients. -/
noncomputable def octic (c0 c1 c2 c3 c4 c5 c6 c7 : F37) : F37[X] :=
  C c0 + C c1 * X ^ 1 + C c2 * X ^ 2 + C c3 * X ^ 3 +
    C c4 * X ^ 4 + C c5 * X ^ 5 + C c6 * X ^ 6 + C c7 * X ^ 7

theorem octic_natDegree_le_seven (c0 c1 c2 c3 c4 c5 c6 c7 : F37) :
    (octic c0 c1 c2 c3 c4 c5 c6 c7).natDegree ≤ 7 := by
  unfold octic
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c7 7).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c6 6).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c5 5).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c4 4).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c3 3).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c2 2).trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C_mul_X_pow_le c1 1).trans (by omega)))
  exact (natDegree_C c0).le.trans (by omega)

theorem octic_degree_lt_eight (c0 c1 c2 c3 c4 c5 c6 c7 : F37) :
    (octic c0 c1 c2 c3 c4 c5 c6 c7).degree < ((8 : ℕ) : WithBot ℕ) := by
  by_cases hzero : octic c0 c1 c2 c3 c4 c5 c6 c7 = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe 8
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp
      (lt_of_le_of_lt (octic_natDegree_le_seven c0 c1 c2 c3 c4 c5 c6 c7) (by omega))

/-- The known joint pair: `q₀ = 1 + X`, `q₁ = 2 + X³`. -/
noncomputable def q0poly : F37[X] := octic 1 1 0 0 0 0 0 0
noncomputable def q1poly : F37[X] := octic 2 0 0 1 0 0 0 0

/-- The three witness codewords (probe output, coefficients low→high). -/
noncomputable def linePoly : Fin 3 → F37[X] := ![
  octic 15 32 16 22 23 32 5 1,
  octic 5 26 30 33 16 20 30 19,
  octic 7 1 0 3 0 0 0 0]

/-- The three bad scalars. -/
def gamma : Fin 3 → F37 := ![1, 2, 3]

/-- The three witness sets, all containing the shared fresh coordinate `18`. -/
def witness : Fin 3 → Finset (Fin 32) := ![
  {2, 4, 8, 12, 13, 14, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30},
  {0, 4, 5, 6, 10, 11, 15, 18, 19, 20, 21, 22, 26, 27, 28, 29, 30, 31},
  {0, 1, 2, 3, 4, 5, 6, 18, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31}]

/-- The known joint set. -/
def J : Finset (Fin 32) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}

/-- Row-certificate interpolants for the non-jointness proofs (probe output). -/
noncomputable def rowCert : Fin 3 → F37[X] := ![
  octic 19 29 24 13 16 11 26 20,
  octic 1 2 16 19 11 23 16 20,
  octic 1 15 36 25 15 7 11 3]

/-- The interpolation core of each row certificate. -/
def rowCore : Fin 3 → Finset (Fin 32) := ![
  {2, 4, 8, 12, 13, 14, 16, 18},
  {0, 4, 5, 6, 10, 11, 15, 18},
  {0, 1, 2, 3, 4, 5, 6, 18}]

/-- The mismatch coordinate of each row certificate. -/
def rowMismatch : Fin 3 → Fin 32 := ![19, 19, 21]

theorem linePoly_degree_lt_eight (j : Fin 3) :
    (linePoly j).degree < ((8 : ℕ) : WithBot ℕ) := by
  fin_cases j <;> exact octic_degree_lt_eight _ _ _ _ _ _ _ _

theorem rowCert_degree_lt_eight (j : Fin 3) :
    (rowCert j).degree < ((8 : ℕ) : WithBot ℕ) := by
  fin_cases j <;> exact octic_degree_lt_eight _ _ _ _ _ _ _ _

theorem q0poly_degree_lt_eight : q0poly.degree < ((8 : ℕ) : WithBot ℕ) :=
  octic_degree_lt_eight 1 1 0 0 0 0 0 0

theorem q1poly_degree_lt_eight : q1poly.degree < ((8 : ℕ) : WithBot ℕ) :=
  octic_degree_lt_eight 2 0 0 1 0 0 0 0

/-! ### Closed finite-field certificate checks -/

set_option linter.flexible false in
/-- The joint pair explains the stack on `J`. -/
theorem joint_pair_agreement (e : Fin 32) (he : e ∈ J) :
    q0poly.eval (dom e) = u0 e ∧ q1poly.eval (dom e) = u1 e := by
  fin_cases e <;> simp [J] at he ⊢ <;>
    simp [q0poly, q1poly, octic, dom, domainValues, u0, u1]
  all_goals decide

set_option linter.flexible false in
/-- Each witness codeword agrees with its line on its witness set. -/
theorem witness_agreement (j : Fin 3) (e : Fin 32) (he : e ∈ witness j) :
    (linePoly j).eval (dom e) = u0 e + gamma j * u1 e := by
  fin_cases j <;> fin_cases e <;> simp [witness] at he ⊢ <;>
    simp [linePoly, octic, gamma, dom, domainValues, u0, u1]
  all_goals decide

set_option linter.flexible false in
/-- Each row certificate matches `u0` on its core. -/
theorem rowCert_core_agreement (j : Fin 3) (e : Fin 32) (he : e ∈ rowCore j) :
    (rowCert j).eval (dom e) = u0 e := by
  fin_cases j <;> fin_cases e <;> simp [rowCore] at he ⊢ <;>
    simp [rowCert, octic, dom, domainValues, u0]
  all_goals decide

set_option linter.flexible false in
/-- Each row certificate mismatches `u0` at its mismatch coordinate. -/
theorem rowCert_mismatch (j : Fin 3) :
    (rowCert j).eval (dom (rowMismatch j)) ≠ u0 (rowMismatch j) := by
  fin_cases j <;>
    simp [rowCert, octic, rowMismatch, dom, domainValues, u0] <;> decide

/-! ### Non-jointness from the first-row certificates -/

/-- A single unexplainable row on `S` forbids a joint explanation on `S`. -/
theorem not_pairJointAgreesOn_of_firstRow
    (S D : Finset (Fin 32)) (hDS : D ⊆ S) (e : Fin 32) (heS : e ∈ S)
    (L : F37[X]) (hL : L.degree < ((8 : ℕ) : WithBot ℕ)) (hDcard : 8 ≤ D.card)
    (hcore : ∀ i ∈ D, L.eval (dom i) = u0 i)
    (hmis : L.eval (dom e) ≠ u0 e) :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
        Set (Fin 32 → F37)) S u0 u1 := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  change v0 ∈ ReedSolomon.code dom 8 at hv0
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv0
  obtain ⟨p0, hp0deg, hv0⟩ := hv0
  have hp0eq : p0 = L := by
    apply sub_eq_zero.mp
    apply CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp0deg hL))
      D hDcard
    intro i hi
    have hreceived := (hagree i (hDS hi)).1
    have hpoly : p0.eval (dom i) = u0 i := by
      rw [hv0] at hreceived
      simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply] using hreceived
    rw [eval_sub, hpoly, hcore i hi, sub_self]
  apply hmis
  have hfresh := (hagree e heS).1
  rw [hv0, hp0eq] at hfresh
  simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply] using hfresh

theorem rowCore_subset_witness (j : Fin 3) : rowCore j ⊆ witness j := by
  fin_cases j <;> decide

theorem rowMismatch_mem_witness (j : Fin 3) : rowMismatch j ∈ witness j := by
  fin_cases j <;> decide

theorem rowCore_card (j : Fin 3) : 8 ≤ (rowCore j).card := by
  fin_cases j <;> decide

/-- No joint pair explains the stack on any of the three witness sets. -/
theorem witness_not_joint (j : Fin 3) :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
        Set (Fin 32 → F37)) (witness j) u0 u1 :=
  not_pairJointAgreesOn_of_firstRow (witness j) (rowCore j)
    (rowCore_subset_witness j) (rowMismatch j) (rowMismatch_mem_witness j)
    (rowCert j) (rowCert_degree_lt_eight j) (rowCore_card j)
    (rowCert_core_agreement j) (rowCert_mismatch j)

/-! ### Literal MCA events at radius `7/16` (threshold `18`) -/

theorem mass_eighteen :
    ((1 : ℝ≥0) - (7 / 16 : ℝ≥0)) * (Fintype.card (Fin 32) : ℝ≥0) = 18 := by
  apply NNReal.coe_injective
  have hle : (7 / 16 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 16)]
    norm_num
  rw [NNReal.coe_mul, NNReal.coe_sub hle]
  push_cast [Fintype.card_fin]
  norm_num

theorem witness_card (j : Fin 3) : (witness j).card = 18 := by
  fin_cases j <;> decide

/-- The explicit decode certificate for the `j`-th scalar. -/
noncomputable def decode (j : Fin 3) :
    CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.McaDecode
      dom 8 (7 / 16) u (gamma j) where
  S := witness j
  P := linePoly j
  hdeg := linePoly_degree_lt_eight j
  hcard := by
    rw [witness_card, mass_eighteen]
    norm_num
  hagree := by
    intro e he
    simpa only [u_zero, u_one, smul_eq_mul] using witness_agreement j e he
  hnjp := by
    simpa only [u_zero, u_one] using witness_not_joint j

theorem mcaEvent_index (j : Fin 3) :
    _root_.ProximityGap.mcaEvent
      ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
        Set (Fin 32 → F37)) (7 / 16) u0 u1 (gamma j) := by
  have := (decode j).mcaEvent
  simpa only [u_zero, u_one] using this

/-! ### The joint set, the shared fresh coordinate, and non-absorption -/

theorem joint_on_J :
    _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
        Set (Fin 32 → F37)) J u0 u1 := by
  refine ⟨fun e ↦ q0poly.eval (dom e),
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval q0poly
      q0poly_degree_lt_eight (fun i ↦ rfl),
    fun e ↦ q1poly.eval (dom e),
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval q1poly
      q1poly_degree_lt_eight (fun i ↦ rfl), ?_⟩
  intro e he
  exact joint_pair_agreement e he

theorem J_card : J.card = 18 := by decide

theorem shared_mem_witness (j : Fin 3) : (18 : Fin 32) ∈ witness j := by
  fin_cases j <;> decide

theorem shared_not_mem_J : (18 : Fin 32) ∉ J := by decide

/-- The triple overlap of the three witnesses is `6 ≤ k - 1 = 7`: exactly the rigidity
escape hatch the dichotomy leaves open. -/
theorem triple_overlap_card :
    (witness 0 ∩ witness 1 ∩ witness 2).card = 6 := by decide

set_option linter.flexible false in
theorem q0poly_core_agreement :
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 32)),
      q0poly.eval (dom i) = u0 i := by
  intro i hi
  fin_cases i <;> simp at hi ⊢ <;>
    simp [q0poly, octic, dom, domainValues, u0]
  all_goals decide

theorem q0poly_mismatch_at_shared :
    q0poly.eval (dom (18 : Fin 32)) ≠ u0 (18 : Fin 32) := by
  simp [q0poly, octic, dom, domainValues, u0]
  decide

/-- **Non-absorption.**  No joint pair explains the stack on `J ∪ {18}`. -/
theorem not_joint_on_insert_shared :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
        Set (Fin 32 → F37)) (insert (18 : Fin 32) J) u0 u1 :=
  not_pairJointAgreesOn_of_firstRow (insert (18 : Fin 32) J)
    {0, 1, 2, 3, 4, 5, 6, 7} (by decide) (18 : Fin 32)
    (Finset.mem_insert_self _ _) q0poly q0poly_degree_lt_eight (by decide)
    q0poly_core_agreement q0poly_mismatch_at_shared

/-! ### Non-collinearity -/

/-- The witness codewords as domain functions. -/
noncomputable def lineFun (j : Fin 3) : Fin 32 → F37 :=
  fun e ↦ (linePoly j).eval (dom e)

set_option linter.flexible false in
theorem lineFun_at_zero :
    lineFun 0 (0 : Fin 32) = 15 ∧ lineFun 1 (0 : Fin 32) = 5 ∧
      lineFun 2 (0 : Fin 32) = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [lineFun, linePoly, octic, dom, domainValues]

/-- **The triple is not collinear**: no pencil of *arbitrary functions* — in particular no
pencil of codewords — reproduces all three witness codewords.  The three evaluations at
coordinate `0` satisfy `p₁ - 2p₂ + p₃ = 12 ≠ 0`, while any pencil forces `0`. -/
theorem not_collinear :
    ¬ ∃ w₀ w₁ : Fin 32 → F37,
      lineFun 0 = w₀ + (1 : F37) • w₁ ∧
      lineFun 1 = w₀ + (2 : F37) • w₁ ∧
      lineFun 2 = w₀ + (3 : F37) • w₁ := by
  rintro ⟨w₀, w₁, h1, h2, h3⟩
  have e1 := congrFun h1 (0 : Fin 32)
  have e2 := congrFun h2 (0 : Fin 32)
  have e3 := congrFun h3 (0 : Fin 32)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3
  rw [lineFun_at_zero.1] at e1
  rw [lineFun_at_zero.2.1] at e2
  rw [lineFun_at_zero.2.2] at e3
  have h12 : (12 : F37) = 0 := by linear_combination e1 - 2 * e2 + e3
  exact absurd h12 (by decide)

theorem gammas_distinct :
    gamma 0 ≠ gamma 1 ∧ gamma 0 ≠ gamma 2 ∧ gamma 1 ≠ gamma 2 := by decide

/-- **Realizability of the non-collinear shared-fresh triple at the P1 shape.**  The exact
non-collinear analogue of the configuration `NonCollinearTripleFree` forbids at P1 exists in
a rate-quarter Reed--Solomon code satisfying every P1 shape inequality.  Any proof of the P1
residual must therefore exclude such triples by the literal P1 counting, not by the clauses,
linearity, rate shape, or pencil rigidity (the triple overlap here is `6 ≤ k - 1`). -/
theorem nonCollinearSharedFreshTriple_realizable :
    ∃ (i : Fin 32) (J' : Finset (Fin 32)) (γ₁ γ₂ γ₃ : F37),
      i ∉ J' ∧ 18 ≤ J'.card ∧
      _root_.ProximityGap.pairJointAgreesOn
        ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
          Set (Fin 32 → F37)) J' u0 u1 ∧
      ¬ _root_.ProximityGap.pairJointAgreesOn
        ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
          Set (Fin 32 → F37)) (insert i J') u0 u1 ∧
      γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
      (∀ jdx : Fin 3,
        _root_.ProximityGap.mcaEvent
          ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
            Set (Fin 32 → F37)) (7 / 16) u0 u1 (gamma jdx) ∧
        i ∈ witness jdx ∧ (witness jdx).card = 18 ∧
        ¬ _root_.ProximityGap.pairJointAgreesOn
          ((ReedSolomon.code dom 8 : Submodule F37 (Fin 32 → F37)) :
            Set (Fin 32 → F37)) (witness jdx) u0 u1) ∧
      ¬ ∃ w₀ w₁ : Fin 32 → F37,
        lineFun 0 = w₀ + γ₁ • w₁ ∧
        lineFun 1 = w₀ + γ₂ • w₁ ∧
        lineFun 2 = w₀ + γ₃ • w₁ := by
  refine ⟨18, J, gamma 0, gamma 1, gamma 2,
    shared_not_mem_J, le_of_eq J_card.symm, joint_on_J, not_joint_on_insert_shared,
    gammas_distinct.1, gammas_distinct.2.1, gammas_distinct.2.2, ?_, ?_⟩
  · intro jdx
    exact ⟨mcaEvent_index jdx, shared_mem_witness jdx, witness_card jdx,
      witness_not_joint jdx⟩
  · exact not_collinear

end ArkLib.ProximityGap.Frontier.NonCollinearTripleRealizabilityF37

/-! ## Axiom audit -/

open ProximityGap.SharedFreshPencil
open ArkLib.ProximityGap.Frontier.P1RateQuarterNonCollinearTriple
open ArkLib.ProximityGap.Frontier.NonCollinearTripleRealizabilityF37

#print axioms triple_pencil_rigidity
#print axioms triple_floor_negative
#print axioms noncollinear_triple_overlap_le
#print axioms shared_triple_dichotomy
#print axioms sharedFreshTripleFree_of_split
#print axioms mcaEvent_index
#print axioms joint_on_J
#print axioms not_joint_on_insert_shared
#print axioms triple_overlap_card
#print axioms not_collinear
#print axioms nonCollinearSharedFreshTriple_realizable
