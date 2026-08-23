/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCMomentSupBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvPrize_MomentToSupCapstone

/-!
# `B6_connect_all` — the FULL prize chain over the actual periods, one open input (#444)

This is the **integrative connect-all** attempt: take every proven brick of the campaign and
literally compose them into one theorem whose conclusion is the prize sup bound
`M ≤ 2√e·√(n·log p)` over the **actual** Gauss-period objects `η_b = Σ_{y∈G} ψ(b·y)` and the
**actual** additive energy `rEnergy G r`, with the per-`b` sup `M = max_{b≠0}‖η_b‖` entered as a
hypothesis `hM : ∀ b≠0, ‖η_b‖ ≤ M` (the standard "sup is achieved/bounded" packaging).

## What is wired (all proven, axiom-clean, in-tree)

1. **The algebraic spine** (`DCMomentSupBound.eta_pow_le_dc`, ⇐ `subgroup_gaussSum_moment`,
   `sum_nonzero_moment`): for every `b ≠ 0`,
   `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}` where `q = card F`, `E_r = rEnergy G r`.
   This is `M^{2r} ≤ S` with `S := q·E_r − |G|^{2r} = Σ_{b≠0}‖η_b‖^{2r}` (the DC-subtracted moment).
2. **The optimization last mile** (`MomentToSup.prize_sup_of_saddle_concrete`): pure real analysis
   converting the moment budget `M^{2r} ≤ (p−1)·E·…` (via the `r`-th-root step, the `(p−1)^{1/r}≤e`
   saddle choice, and `(2r−1)‼ ≤ (2r)ʳ`) into `M ≤ 2√e·√(n·log p)`.
3. **The char-0 anchor** (`hbessel`): `E_r^{ℂ}(G) ≤ (2r−1)‼·|G|^r` is **PROVEN unconditionally**
   in `Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic` (Lam–Leung antipodal closure). Here it
   is consumed as the named real `Echar0` with `hbessel : Echar0 ≤ wickOdd r * n^r`. (It is a real
   number = the char-0 energy of the same `2^k`-th-root multiset; discharging it requires no open
   input — only re-instantiating the dyadic char-0 brick at the matching `(k,r)`.)

## THE SINGLE OPEN INPUT — `SaddleEnergyBound` (BGK/Paley at β=4)

Everything above is proven. The chain closes **iff** the char-`p` DC-subtracted moment `S` is
controlled by the char-0 energy `Echar0` at the saddle depth `r ≈ ln q`:

> **`SaddleEnergyBound ψ G p r Echar0`** :=  `Σ_{b≠0}‖η_b‖^{2r} ≤ (p−1)·Echar0`.

This is exactly `A_r ≤ Wick_r` in DC-subtracted form (`DCEnergyCorrection.DCEnergyBound`), exactly
`W_wrap ≤ SLACK + n^{2r}/p` (`WKSlackBudget.budget_equiv`), and exactly the BGK/Paley square-root-
cancellation wall at β=4. Best PROVEN upper bound is BGK `n^{1−o(1)}`; empirically true (`c≈0.6`).
It is **NOT** discharged here. It is the one named open `Prop`, and `connect_all_prize` proves the
prize **follows from it** axiom-clean.

## Honest scope

`connect_all_prize` is a genuine **conditional theorem**: `SaddleEnergyBound ⟹ M ≤ 2√e·√(n log p)`,
over the real `η`/`rEnergy` objects, with the open content isolated in one hypothesis. It is **NOT**
a proof of the prize. The `hbessel` input is proven in-tree (so it is not a second open core, merely
not re-derived inside this file); `hsup`/`hM` are the trivial sup packaging. The minimal open set is
therefore **exactly `{SaddleEnergyBound}`**. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCMomentSupBound ArkLib.ProximityGap.DCSubtractedMoment
open ProximityGap.Frontier.MomentToSup

namespace ArkLib.ProximityGap.Frontier.B6ConnectAll

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **THE SINGLE OPEN INPUT.** The DC-subtracted nonprincipal `2r`-th moment of the Gauss periods is
controlled by the char-0 energy `Echar0`:
`Σ_{b≠0}‖η_b‖^{2r} ≤ (p−1)·Echar0`. With `p = card F` and `Echar0 = E_r^{ℂ}(G)`, this is the
BGK/Paley square-root-cancellation conjecture at β=4 (= `A_r ≤ Wick_r` DC-subtracted). Open. -/
def SaddleEnergyBound (ψ : AddChar F ℂ) (G : Finset F) (p : ℝ) (r : ℕ) (Echar0 : ℝ) : Prop :=
  ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) ≤ (p - 1) * Echar0

/-- **CONNECT-ALL: the full prize chain over the actual periods, one open input.**

Inputs:
* `b₀`      — any nonzero frequency (instantiate at the extremal one to bound `M = max_{b≠0}‖η_b‖`;
              the bound holds for `‖η_{b₀}‖` at *every* `b₀≠0`, so in particular at the max).
* `hsaddle` — **the single open input** `SaddleEnergyBound` = BGK/Paley at β=4.
* `hbessel` — the char-0 anchor `Echar0 ≤ (2r−1)‼·nʳ`, **PROVEN in-tree**
              (`gaussianEnergyBound_dyadic`); consumed here as a hypothesis on the real `Echar0`.
* `hpcard`  — `p = card F` (ties the abstract `p` to the field size).
* `hncard`  — `n = |G|` (ties the abstract `n` to the subgroup size).
* the saddle-window / positivity side conditions (`hr`, `hrlo`, `hrhi`, `hp`, …), all benign.

Conclusion: the **prize sup bound** `M ≤ 2√e·√(n·log p)` = `M ≤ C·√(n·log q)`, `C = 2√e`.

Composition: `eta_pow_le_dc` (per-`b` sup ≤ DC-subtracted moment, ⇐ the proven moment identity)
gives `M^{2r} ≤ Σ_{b≠0}‖η_b‖^{2r} =: S`; `hsaddle` gives `S ≤ (p−1)·Echar0`; `hbessel` gives
`Echar0 ≤ wickOdd r·nʳ`; then `prize_sup_of_saddle_concrete` (the proven optimization) closes it. -/
theorem connect_all_prize
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (n p Echar0 : ℝ) (b₀ : F) (hb₀ : b₀ ≠ 0)
    (hpcard : p = (Fintype.card F : ℝ)) (hncard : n = (G.card : ℝ))
    (hp : 3 ≤ p) (hr : 1 ≤ r)
    (hrlo : Real.log (p - 1) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ 2 * Real.log p)
    (hsaddle : SaddleEnergyBound ψ G p r Echar0)
    (hbessel : Echar0 ≤ wickOdd r * n ^ r) :
    ‖eta ψ G b₀‖ ≤ 2 * Real.sqrt (Real.exp 1) * Real.sqrt (n * Real.log p) := by
  classical
  -- M := ‖η_{b₀}‖, the value at the (caller-chosen, e.g. extremal) nonzero frequency.
  set M : ℝ := ‖eta ψ G b₀‖ with hMdef
  have hMnn : 0 ≤ M := norm_nonneg _
  -- S := the DC-subtracted nonprincipal moment Σ_{b≠0}‖η_b‖^{2r}.
  set S : ℝ := ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) with hS
  -- (1) per-b term ≤ DC-subtracted moment.
  -- eta_pow_le_dc : ‖η_{b₀}‖^{2r} ≤ q·E_r − |G|^{2r} = S (sum_nonzero_moment).
  have hSeq : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) = S :=
    (sum_nonzero_moment hψ G r).symm
  have hMsup : M ^ (2 * r) ≤ S := by
    have := eta_pow_le_dc hψ G r hb₀
    rw [hSeq] at this
    exact this
  -- Recast as (M^2)^r ≤ S for the rpow capstone (exact natCast).
  have hsup : (M ^ 2) ^ (r : ℝ) ≤ S := by
    have hrw : (M ^ 2) ^ (r : ℝ) = M ^ (2 * r) := by
      rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm]
    rw [hrw]; exact hMsup
  -- (2) the open input S ≤ (p−1)·Echar0.
  have hsaddle' : S ≤ (p - 1) * Echar0 := hsaddle
  -- (3) compose with the proven optimization capstone.
  exact prize_sup_of_saddle_concrete M n p S Echar0 r hMnn
    (by rw [hncard]; positivity) hp hr hrlo hrhi hsup hsaddle' hbessel

/-- **The minimal-open-set statement, in one line.** `connect_all_prize` shows the prize sup bound
follows from the SINGLE open `Prop` `SaddleEnergyBound` (everything else proven in-tree or trivial).
This corollary records that fact as a clean implication for a fixed extremal frequency `b₀`. -/
theorem prize_of_saddle_only
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (n p Echar0 : ℝ) (b₀ : F) (hb₀ : b₀ ≠ 0)
    (hpcard : p = (Fintype.card F : ℝ)) (hncard : n = (G.card : ℝ))
    (hp : 3 ≤ p) (hr : 1 ≤ r)
    (hrlo : Real.log (p - 1) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ 2 * Real.log p)
    (hbessel : Echar0 ≤ wickOdd r * n ^ r) :
    SaddleEnergyBound ψ G p r Echar0 →
      ‖eta ψ G b₀‖ ≤ 2 * Real.sqrt (Real.exp 1) * Real.sqrt (n * Real.log p) :=
  fun hsaddle => connect_all_prize hψ G r n p Echar0 b₀ hb₀ hpcard hncard hp hr
    hrlo hrhi hsaddle hbessel

end ArkLib.ProximityGap.Frontier.B6ConnectAll

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.B6ConnectAll.connect_all_prize
#print axioms ArkLib.ProximityGap.Frontier.B6ConnectAll.prize_of_saddle_only
