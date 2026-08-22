/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (approach N4 — Ruelle transfer operator on the 2-adic odometer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Approach N4 — a Ruelle transfer operator on the 2-adic odometer (Issue #444) — **REFUTED**

## Verdict (adversarial audit, 2026-06-18)

This approach is **REFUTED**, not SKELETON. The char-0 spectral skeleton (the operator, its
eigen-recurrence, the orbit-product, and the telescoping reduction) is genuinely proven and is kept
below — it is correct mathematics. But the single *named open obligation* `MultiplierContraction`
that the approach claimed "CLOSES the prize when discharged over `F_p`" is **provably FALSE in the
prize regime** (`n = 2^30`, `q ≈ 2^158`, depth `r* ≈ ln p ≈ 110`). It can never be discharged
axiom-clean over `F_p`, because it is not true. Two independent breaks, both now machine-checked
in this file:

### Break 1 — `MultiplierContraction` is STRICTLY STRONGER than the prize, and the prize target
###            it produces is the DC-INCLUDED energy bound, which is in-tree-REFUTED at prize depth.

The file's own proven theorem `gaussianEnergyBound_of_multiplierContraction` shows
`MultiplierContraction G → ∀ r, GaussianEnergyBound G r`. But the raw, DC-included
`GaussianEnergyBound G r` is **known false** at prize depth: the `b = 0` (DC) term contributes
`‖η_0‖^{2r} = |G|^{2r}` to the moment, forcing `E_r ≥ |G|^{2r}/q`, which already exceeds the Wick
ceiling `(2r−1)‼·|G|^r` once `|G|^r > q·(2r−1)‼` — i.e. around `r ≈ 6` in the prize regime, and by a
factor `2^{2444}` at `r = 110` (`DCEnergyEssential.not_gaussianEnergyBound_of_deep`, in tree). By
contraposition, **`MultiplierContraction G` is false at prize depth** (proven below as
`multiplierContraction_false_of_deep`). The named obligation is not "open"; it is refutable. The
approach inherits the *same DC obstruction* the project already documented for the raw
`GaussianEnergyBound` — wrapping the bound in a transfer-operator telescope does not remove the DC
mass, it just hides it inside the ratio `E_{r+1}/E_r` (the DC term makes that ratio `→ |G|² = n²`,
not `≤ (2r+1)n`, once `r` is large — see Break 2). The usable residual remains the **DC-subtracted**
transfer (`DCEnergyCorrection.DCEnergyBound`), which this approach does NOT target.

### Break 2 — the escape from the moment obstruction is ILLUSORY: the ratio bound IS the BGK
###            sup-norm bound (it reduces to exactly the object the obstruction is about).

The claim was: "the transfer operator bounds the *ratio* `E_{r+1}/E_r`, never a single `E_r`, never a
`2r`-th root, so it is not in the class `moment_ladder_exceeds_prize` forbids." This is a sleight of
hand. With `q·E_r = ∑_b ‖η_b‖^{2r}`, the ratio is the discrete Rayleigh quotient

      `E_{r+1}/E_r = (∑_b ‖η_b‖^{2r+2}) / (∑_b ‖η_b‖^{2r})  →  max_b ‖η_b‖² = M²`   as `r → ∞`,

the *exact* `L^{2r} → L^{2r+2}` power-mean limit. So the per-step multiplier bound
`E_{r+1} ≤ (2r+1)n·E_r` at the prize depth `r ≈ ln p` is, asymptotically, the statement
`M² ≲ (2r+1)n ≈ n·log m` — i.e. `M ≤ C√(n log m)`, which is **exactly the BGK / generalized-Paley
sup-norm bound** (`B = max_{b≠0}‖η_b‖`, the open prize core, faces 3↔4 in the project map). The
"`(q·Σc²)^{1/2r}` versus `E_{r+1}/E_r`" distinction the approach leans on is cosmetic: both objects
converge to the same `M`. The telescope does not capture cross-moment cancellation that the single
moment does not — it repackages the identical sup-norm wall across the depth coordinate. (Numerics:
the ratios `E_{r+1}/E_r` climb monotonically toward `max_b|η_b|²` with `r`; verified `n=8`,
`p ∈ {1009,2017,4001,8009}`.)

### Why both breaks are decisive together

- If you target the **raw** `GaussianEnergyBound` (as the file's bridge does), `MultiplierContraction`
  is **FALSE** at prize depth (Break 1) — dead.
- If you instead reinterpret the multiplier bound as the DC-subtracted nonzero-frequency statement,
  then at the depth needed it **IS the BGK sup-norm bound** (Break 2) — it reduces to the open prize
  core, with no new cancellation captured. The moment obstruction is not escaped; it is renamed.

The cross-moment cancellation the obstruction demands is real and lives in the gap between
`E_{r+1}/E_r` and the *char-0* multiplier `(2r+1)n`; controlling that gap at `r ≈ ln p` over `F_p`
*is* the prize (the Paley/BGK wall), not a separately-solvable spectral side-condition.

## What is still genuinely PROVEN here, axiom-clean

The char-0 spectral generation is correct and kept:

* `wickMultiplier`, `wick_succ` (the eigen-recurrence), `wick_eq_prod` (`Wick = L^r` orbit-product),
  `energy_le_wick_of_multiplierContraction` (telescoping: the contraction *would* be sufficient — that
  direction is honest), and the bridge `gaussianEnergyBound_of_multiplierContraction`.

The NEW honest content (the refutation):

* `multiplierContraction_false_of_deep` — **`MultiplierContraction G` is FALSE whenever the DC mass
  beats Wick** (`q·(2r−1)‼·|G|^r < |G|^{2r}` for some `r`), which is exactly the prize regime at
  `r ≈ ln p`. Proven by composing the file's own sufficiency bridge with the in-tree DC obstruction
  `DCEnergyEssential.not_gaussianEnergyBound_of_deep`. No `sorry`, no `native_decide`, no `[CharZero]`,
  no vacuous hypothesis.

## HONEST status

**REFUTED.** The transfer-operator reframing does not escape the moment-method necessity obstruction:
at the raw target it makes the open obligation FALSE (DC term, Break 1); at the DC-subtracted target
the obligation equals the BGK sup-norm bound at the relevant depth (Break 2). `closesCharP = false`.
The char-0 skeleton is sound but inert for the prize.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset
open scoped Nat

namespace ArkLib.ProximityGap.Frontier.NovelTransferOperator2

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

/-! ## The Wick value and the Ruelle multiplier of the odometer pairing step (char-0 skeleton) -/

/-- The **Wick value** `Wick(r,n) = (2r−1)‼ · n^r`: the char-`0` energy ceiling (number of
perfect pairings of `2r` half-edges, weighted by tower position). -/
def wick (r n : ℕ) : ℕ := Nat.doubleFactorial (2 * r - 1) * n ^ r

/-- The **Ruelle multiplier** of the odometer's pairing step at depth `r`:
`mult(r) = (2r + 1) · n`. (Char-0 sector only — over `F_p` at depth `r ≈ ln p` this multiplier is
*violated*, see the file header refutation.) -/
def wickMultiplier (r n : ℕ) : ℕ := (2 * r + 1) * n

@[simp] theorem wick_zero (n : ℕ) : wick 0 n = 1 := by
  simp [wick, Nat.doubleFactorial]

/-- **The transfer operator's defining eigen-recurrence (char-0).**
`Wick(r+1,n) = wickMultiplier r n · Wick(r,n)`. This is a definitional identity about the Wick
*numbers*; it does NOT assert anything about the char-`p` energy `rEnergy`. -/
theorem wick_succ (r n : ℕ) : wick (r + 1) n = wickMultiplier r n * wick r n := by
  cases r with
  | zero => simp [wick, wickMultiplier, Nat.doubleFactorial]
  | succ k =>
      unfold wick wickMultiplier
      have h2 : 2 * (k + 1 + 1) - 1 = (2 * (k + 1) - 1) + 2 := by omega
      rw [h2, Nat.doubleFactorial_add_two, pow_succ]
      have heq : (2 * (k + 1) - 1) + 2 = 2 * (k + 1) + 1 := by omega
      rw [heq]
      ring

/-- **`Wick = L^r` applied to the base state.** The Wick value is the explicit Ruelle orbit-product
`∏_{j<r} mult(j)` — the operator iterated `r` times from the vacuum state `Wick(0)=1`. -/
theorem wick_eq_prod (r n : ℕ) : wick r n = ∏ j ∈ Finset.range r, wickMultiplier j n := by
  induction r with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ← ih, wick_succ, Nat.mul_comm]

/-! ## The telescoping reduction: a per-step multiplier bound ⇒ the full energy bound

The telescoping itself is valid; the SUFFICIENCY direction is honest. What is NOT honest is the
prior claim that the hypothesis `MultiplierContraction` is a separately-solvable, easier object than
the prize. It is strictly stronger (it implies the energy bound at every `r`) and, at the raw target,
FALSE at prize depth (`multiplierContraction_false_of_deep`). -/

/-- **The telescoping consequence (PROVEN, char-`p`-agnostic).**
If a sequence `E : ℕ → ℕ` satisfies the per-step bound `E (r+1) ≤ wickMultiplier r n · E r` for all
`r`, with base `E 0 ≤ 1`, then `E r ≤ wick r n` for all `r`. (Sufficiency only — the hypothesis is
the hard/false part.) -/
theorem energy_le_wick_of_multiplierContraction
    {E : ℕ → ℕ} {n : ℕ}
    (hbase : E 0 ≤ 1)
    (hstep : ∀ r, E (r + 1) ≤ wickMultiplier r n * E r) :
    ∀ r, E r ≤ wick r n := by
  intro r
  induction r with
  | zero => simpa using hbase
  | succ k ih =>
      calc E (k + 1) ≤ wickMultiplier k n * E k := hstep k
        _ ≤ wickMultiplier k n * wick k n := Nat.mul_le_mul_left _ ih
        _ = wick (k + 1) n := (wick_succ k n).symm

/-! ## The claimed NEW obligation — and its REFUTATION at prize depth -/

/-- **`MultiplierContraction G` (the claimed-new Prop).**  The char-`p` `r`-fold additive energy of
`G` satisfies the per-step multiplier bound
`rEnergy G (r+1) ≤ wickMultiplier r |G| · rEnergy G r` for every depth `r`, with base
`rEnergy G 0 ≤ 1`.

The approach claimed discharging this over `F_p` CLOSES the prize. It does not: this Prop is **false**
at prize depth (`multiplierContraction_false_of_deep`), because — via the sufficiency bridge — it
would imply the DC-included `GaussianEnergyBound G r`, which the DC term refutes at `r ≈ ln p`. -/
def MultiplierContraction {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) : Prop :=
  rEnergy G 0 ≤ 1 ∧ ∀ r, rEnergy G (r + 1) ≤ wickMultiplier r G.card * rEnergy G r

/-- **The sufficiency bridge — `MultiplierContraction` ⇒ `GaussianEnergyBound` for ALL `r`.**
Char-`p`-agnostic. This is exactly what makes `MultiplierContraction` *strictly stronger than* the
prize (it implies the energy bound at every depth simultaneously), and is the lever used to refute it
below. -/
theorem gaussianEnergyBound_of_multiplierContraction
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {G : Finset F} (h : MultiplierContraction G) (r : ℕ) :
    GaussianEnergyBound G r := by
  obtain ⟨hbase, hstep⟩ := h
  have hnat : rEnergy G r ≤ wick r G.card :=
    energy_le_wick_of_multiplierContraction (n := G.card) hbase hstep r
  unfold GaussianEnergyBound wick at *
  have : (rEnergy G r : ℝ) ≤ ((Nat.doubleFactorial (2 * r - 1) * G.card ^ r : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_mul, Nat.cast_pow] at this
  exact this

/-- **REFUTATION (the honest new content): `MultiplierContraction G` is FALSE at prize depth.**
If at some depth `r` the DC mass beats the Wick ceiling —
`q·(2r−1)‼·|G|^r < |G|^{2r}` — then `MultiplierContraction G` cannot hold.

Proof: if it held, the sufficiency bridge `gaussianEnergyBound_of_multiplierContraction` would give
`GaussianEnergyBound G r`; but `DCEnergyEssential.not_gaussianEnergyBound_of_deep` refutes that
bound under exactly this DC hypothesis. Contradiction.

In the prize regime (`|G| = n = 2^30`, `q ≈ 2^158`) the DC hypothesis holds for all `r ≳ 6`, in
particular at the prize saddle `r* ≈ ln p ≈ 110` (where `|G|^{2r}/q` beats Wick by `≈ 2^{2444}`). So
the named obligation the approach hoped to discharge over `F_p` is not open — it is FALSE. -/
theorem multiplierContraction_false_of_deep
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hdeep : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      < (G.card : ℝ) ^ (2 * r)) :
    ¬ MultiplierContraction G := by
  intro h
  exact ArkLib.ProximityGap.DCEnergyEssential.not_gaussianEnergyBound_of_deep hψ G r hdeep
    (gaussianEnergyBound_of_multiplierContraction h r)

/-! ## Char-0 sanity checks (sound, but inert for the prize) -/

/-- The char-0 Ruelle multiplier is positive whenever the tower is nonempty (`n ≥ 1`). -/
theorem wickMultiplier_pos {r n : ℕ} (hn : 1 ≤ n) : 0 < wickMultiplier r n := by
  unfold wickMultiplier
  exact Nat.mul_pos (by omega) hn

/-- The base of the recurrence is real: `Wick(1,n) = n`. -/
theorem wick_one (n : ℕ) : wick 1 n = n := by
  simp [wick, Nat.doubleFactorial]

/-- The operator generates the first nontrivial rung: `Wick(2,n) = 3·n²`. -/
theorem wick_two (n : ℕ) : wick 2 n = 3 * n ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, wick_succ, wick_one, wickMultiplier]
  ring

/-- **The honest one-liner.** `MultiplierContraction` is *sufficient* for the energy bound at all `r`
(`gaussianEnergyBound_of_multiplierContraction`) — but it is strictly stronger than, and at prize
depth FALSER than, the prize, so it is NOT a usable escape. Sufficiency is kept; closure is refuted. -/
theorem transfer_operator_sufficient_not_closing
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {G : Finset F} :
    MultiplierContraction G → ∀ r, GaussianEnergyBound G r :=
  fun h r => gaussianEnergyBound_of_multiplierContraction h r

end ArkLib.ProximityGap.Frontier.NovelTransferOperator2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.NovelTransferOperator2.energy_le_wick_of_multiplierContraction
#print axioms ArkLib.ProximityGap.Frontier.NovelTransferOperator2.gaussianEnergyBound_of_multiplierContraction
#print axioms ArkLib.ProximityGap.Frontier.NovelTransferOperator2.multiplierContraction_false_of_deep
