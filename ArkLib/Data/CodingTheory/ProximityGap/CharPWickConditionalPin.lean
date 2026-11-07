/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The char-`p` Wick conditional pin: the prize sup-norm bound from the single inequality `c_r ≤ 1` (#444)

This file formalizes the **conditional pin** that Shaw's `docs/kb/direct-charp-supnorm-assault-2026-06-15.md`
names as the constructive next step.  Six independent routes (induction-on-depth, van der Corput, cumulant/MGF,
Gauss-sum mult-independence, the moment identity, the crossCell split) ALL reduce the prize sup-norm bound
`M(μ_n) ≤ √(2 n log m)` to the SAME single hypothesis: the char-`p` deep-moment Wick bound

  `E_r(μ_n, F_q) ≤ (2r−1)‼ · n^r`   at depth `r ≍ log m`.

The SHARPEST attackable form of that hypothesis (the induction route) is the **normalized recursion**

  `a_{r+1} = (a_r + 2r·c_r) / (1 + 2r)`,  `a_r := E_r / Wick_r`,  `c_r := cross_r / (2r·n·Wick_r)`,

with `Wick_r := (2r−1)‼·n^r`, where the whole prize collapses to the SINGLE monotonicity inequality
`c_r ≤ 1` (equivalently `cross_r ≤ 2r·n·Wick_r`).  Here we **prove** (axiom-clean, no `sorry`):

* the recursion is an EXACT identity — it is just the in-tree exact recursion `rEnergy_succ`
  (`E_{r+1} = n·E_r + cross_r`) normalized by `Wick_r`;  hence
* the single inequality `c_r ≤ 1 ∀ r` (`cross_r ≤ 2r·n·Wick_r`), with the proven base `E_1 = n = Wick_1`,
  drives the clean induction `E_r ≤ Wick_r ∀ r ≥ 1`;  and
* this feeds the exact `2r`-th moment identity (`eta_pow2r_le_card_mul_energy`) to give the prize-floor
  sup-norm bound `‖η_b‖^{2r} ≤ q · (2r−1)‼ · n^r` for **every** `b` and the conditional consumer
  `‖η_b‖ ≤ (q·(2r−1)‼)^{1/(2r)} · √n`.

The PROBE (`scripts/probes/probe_normalized_wick_recursion.py`, exact integer `E_r` over PROPER thin `μ_n`,
`p ≈ n^4`, two primes per `n`, never `n = q−1`) confirms (i) the recursion is an exact identity at every
`r, n` (`rec_ok = True`), and (ii) `c_r ≤ 1` AND `a_r ≤ 1` on every clean rung (the `c_r` tick-up at
`r ≈ r* = log p` is the finite-field DC/wraparound artifact, not signal).

## What is proven (all axiom-clean, char-`p`, any finite `G`)

* `cross`              : the off-diagonal autocorrelation mass `cross_r = E_{r+1} − |G|·E_r` (def + `cross_eq`).
* `wick`               : `Wick_r = (2r−1)‼ · n^r` (def).
* `wick_one`           : `Wick_1 = n`.
* `wick_succ`          : `Wick_{r+1} = (2r+1) · n · Wick_r` (`r ≥ 1`)  — the recursion's normalizer step.
* `rEnergy_le_wick_of_crossBound` : **THE INDUCTIVE PIN.**  if `cross_r ≤ 2r·n·Wick_r ∀ r ≥ 1`
  (the single inequality `c_r ≤ 1`), then `E_r ≤ Wick_r = (2r−1)‼·n^r` for all `r ≥ 1`.
* `eta_pow2r_le_wick_of_crossBound` : the consumer — `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for every `b`.
* `eta_le_wick_rpow_of_crossBound`  : the `2r`-th-root sup-norm form `‖η_b‖ ≤ (q·(2r−1)‼)^{1/(2r)}·√n`.
* `card_pow_le_card_mul_rEnergy`    : the principal-coefficient lower bound `n^{2r} ≤ q·E_r`
  (unconditional; `η_0 = n`).
* `card_pow_le_card_mul_wick_of_crossBound` / `not_crossBoundedByWick_of_lt` : the necessary
  condition `n^{2r} ≤ q·(2r−1)‼·n^r` (i.e. `n^r ≤ q·(2r−1)‼`) for EVERY `r ≥ 1` under
  `CrossBoundedByWick`, and its contrapositive.
* `not_crossBoundedByWick_production` : at `|G| = 2^30`, `q < 2^159` the hypothesis is FALSE
  (witnessed at depth `r = 6`).

## Honest scope — this is a CONDITIONAL pin; it does NOT close the prize

The single hypothesis `CrossBoundedByWick` (`cross_r ≤ 2r·n·Wick_r ∀ r ≥ 1`, i.e. `c_r ≤ 1`) is the
raw, ALL-ORDERS form of the char-`p` deep-moment Wick input (CLAUDE.md face #3).  It is STATED, not
proved, and as an all-orders statement it is **not** an open analytic statement at the intended
production scale — it is FALSE there.  Through the (correct) induction it implies
`E_r ≤ (2r−1)‼·n^r` for every `r ≥ 1`, while the principal (`b = 0`) term of the moment identity
gives `E_r ≥ n^{2r}/q` unconditionally; so it forces `n^r ≤ q·(2r−1)‼` at every depth.  At the
sponsor parameters `n = 2^30`, `q < 2^159`, depth `r = 6` violates this with a wide margin
(`n^6 = 2^180` but `q·11‼ < 2^159·2^14 = 2^173`, since `11‼ = 10395 < 16384`); this refutation is
the checked theorem `not_crossBoundedByWick_production` (not a Lean kernel inconsistency — it only
shows this `Prop` fails for such `G`).  Caveat: the obstruction is exactly the displayed
quantitative condition, not a statement about every finite `n, q` (e.g. singleton `G` satisfies the
raw Wick bounds).  It is also FALSE in the thick `β ≲ 3` window.

A usable version of the input must therefore be restricted to finite depths obeying the
DC/wraparound guard `n^r ≤ q·(2r−1)‼` (in particular `r` well below the depth where `n^r` exceeds
`q`), or reformulated as a principal-subtracted moment/cross inequality (removing the `b = 0`
contribution `n^{2r}/q`), with the recursion re-derived for that object; neither is done here.

What IS proved here, axiom-clean, is the implication `CrossBoundedByWick ⟹ E_r ≤ Wick_r` and
`⟹ ‖η_b‖ ≤ (q·(2r−1)‼)^{1/(2r)}·√n` (the conditional induction and the norm extraction are valid).
This is a *conditional* pin via the MOMENT/Wick face — distinct from
`OpenCoreConditionalPin.WorstCaseIncidenceBounded` (the INCIDENCE face) — whose hypothesis, in the raw
all-orders form stated, is refuted at production by the theorem above.  Nothing here certifies
`c_r ≤ 1` at any depth.

## References
- Shaw, `docs/kb/direct-charp-supnorm-assault-2026-06-15.md` (#444). The six-route convergence.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open scoped Nat
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.CharPMomentRecursion (rEnergy_succ autocorr)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one eta_pow2r_le_card_mul_energy)

namespace ArkLib.ProximityGap.CharPWickConditionalPin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The off-diagonal autocorrelation mass `cross_r` -/

/-- The off-diagonal autocorrelation mass `cross_r = ∑_{s∈G} ∑_{t∈G, t≠s} C_r(s − t)`, exactly the
non-`|G|·E_r` part of the in-tree exact recursion `rEnergy_succ`. -/
noncomputable def cross (G : Finset F) (r : ℕ) : ℕ :=
  ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t)

/-- **`E_{r+1} = |G|·E_r + cross_r`** — the in-tree exact recursion, repackaged with `cross`. -/
theorem cross_eq (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) = G.card * rEnergy G r + cross G r := by
  rw [rEnergy_succ]; rfl

/-! ### The char-`0` Wick normalizer `Wick_r = (2r−1)‼ · n^r` -/

/-- The char-`0` Wick / Gaussian sup-moment normalizer `Wick_r = (2r−1)‼ · n^r`. -/
def wick (n r : ℕ) : ℕ := (2 * r - 1)‼ * n ^ r

/-- `Wick_1 = n` (since `(2·1−1)‼ = 1‼ = 1`). -/
theorem wick_one (n : ℕ) : wick n 1 = n := by
  unfold wick; norm_num

/-- **The normalizer recursion step `Wick_{r+1} = (2r+1)·n·Wick_r` for `r ≥ 1`.**
Uses `Nat.doubleFactorial_add_two` with `2r−1 ≥ 1`: `(2r+1)‼ = (2r+1)·(2r−1)‼`. -/
theorem wick_succ (n r : ℕ) (hr : 1 ≤ r) :
    wick n (r + 1) = (2 * r + 1) * n * wick n r := by
  unfold wick
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hdf : (2 * (k + 1) + 1)‼ = (2 * (k + 1) + 1) * (2 * (k + 1) - 1)‼ := by
    have h : 2 * (k + 1) + 1 = (2 * (k + 1) - 1) + 2 := by omega
    rw [h, Nat.doubleFactorial_add_two]
  have hexp : 2 * (k + 1 + 1) - 1 = 2 * (k + 1) + 1 := by omega
  rw [hexp, hdf]
  ring

/-! ### The single open hypothesis `c_r ≤ 1` (`cross_r ≤ 2r·n·Wick_r`) -/

/-- **The raw all-orders Wick hypothesis, as one `Prop`:** `c_r ≤ 1` for all `r ≥ 1`, i.e. the
off-diagonal autocorrelation mass `cross_r` is at most `2r·n·Wick_r`.  Stated, NOT proved.

Caution: because it quantifies over ALL depths `r ≥ 1`, it forces `n^r ≤ q·(2r−1)‼` at every depth
(`card_pow_le_card_mul_wick_of_crossBound`), and is therefore FALSE at the production scale
`n = 2^30`, `q < 2^159` (`not_crossBoundedByWick_production`, depth `r = 6`); it is also false in the
thick window (`β ≲ 3`).  The char-`p` Wick input that could still be open must be restricted to
finite depths obeying that guard or stated in principal-subtracted form. -/
def CrossBoundedByWick (G : Finset F) : Prop :=
  ∀ r : ℕ, 1 ≤ r → cross G r ≤ 2 * r * (G.card * wick G.card r)

/-! ### THE INDUCTIVE PIN: `c_r ≤ 1 ⟹ E_r ≤ Wick_r` -/

/-- **THE INDUCTIVE PIN.**  If the single inequality `c_r ≤ 1` (`CrossBoundedByWick`) holds, then the
`r`-fold additive energy satisfies the char-`0` Wick bound `E_r ≤ (2r−1)‼·n^r = Wick_r` for all `r ≥ 1`.

Clean induction from the proven base `E_1 = n = Wick_1` (`rEnergy_one`, `wick_one`) through the exact
recursion `E_{r+1} = n·E_r + cross_r` (`cross_eq`): if `E_r ≤ Wick_r` and `cross_r ≤ 2r·n·Wick_r`, then
`E_{r+1} = n·E_r + cross_r ≤ n·Wick_r + 2r·n·Wick_r = (2r+1)·n·Wick_r = Wick_{r+1}` (`wick_succ`). -/
theorem rEnergy_le_wick_of_crossBound (G : Finset F) (hC : CrossBoundedByWick G) :
    ∀ r : ℕ, 1 ≤ r → rEnergy G r ≤ wick G.card r := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [rEnergy_one, wick_one]
      · have ihk : rEnergy G k ≤ wick G.card k := ih hk
        have hcross : cross G k ≤ 2 * k * (G.card * wick G.card k) := hC k hk
        calc rEnergy G (k + 1)
            = G.card * rEnergy G k + cross G k := cross_eq G k
          _ ≤ G.card * wick G.card k + 2 * k * (G.card * wick G.card k) :=
                Nat.add_le_add (Nat.mul_le_mul_left _ ihk) hcross
          _ = (2 * k + 1) * G.card * wick G.card k := by ring
          _ = wick G.card (k + 1) := (wick_succ G.card k hk).symm

/-! ### The consumer: the prize-floor sup-norm bound -/

/-- **The conditional prize-floor moment bound: `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`** for every `b` and every
`r ≥ 1`, assuming the single inequality `c_r ≤ 1` (`CrossBoundedByWick`).  Compose the inductive pin
with the exact `2r`-th moment identity `eta_pow2r_le_card_mul_energy`. -/
theorem eta_pow2r_le_wick_of_crossBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hC : CrossBoundedByWick G) (r : ℕ) (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r) := by
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * rEnergy G r := eta_pow2r_le_card_mul_energy hψ G r b
    _ ≤ (Fintype.card F : ℝ) * (wick G.card r : ℝ) := by
        gcongr; exact_mod_cast rEnergy_le_wick_of_crossBound G hC r hr
    _ = (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r) := by
        unfold wick; push_cast; ring

/-- **The conditional prize-floor sup-norm bound (the `2r`-th-root form):**
`‖η_b‖ ≤ (q·(2r−1)‼)^{1/(2r)} · √n` for every `b` and every `r ≥ 1`, assuming `c_r ≤ 1`.

Note the prize-shape: the `√n = n^{1/2}` floor with the slowly-growing factor `(q·(2r−1)‼)^{1/(2r)}`.
At the prize depth `r ≍ log m` with `(2r−1)‼ ≈ (2r/e)^r` and `q^{1/(2r)} = √(n log m)`-scale, this is
the BGK / `√(n log(q/n))` prize floor — conditional on `CrossBoundedByWick` (`c_r ≤ 1` at ALL
depths), whose raw all-orders form is refuted at production scale by
`not_crossBoundedByWick_production`; the theorem is a valid implication, not a usable unconditional
bound there. -/
theorem eta_le_wick_rpow_of_crossBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hC : CrossBoundedByWick G) (r : ℕ) (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖
      ≤ ((Fintype.card F : ℝ) * ((2 * r - 1)‼ : ℝ)) ^ (((2 * r : ℕ) : ℝ)⁻¹)
          * (G.card : ℝ) ^ ((2 : ℝ)⁻¹) := by
  set x : ℝ := ‖eta ψ G b‖ with hxdef
  have hx : 0 ≤ x := norm_nonneg _
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hdf : (0 : ℝ) ≤ ((2 * r - 1)‼ : ℝ) := by positivity
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have h : x ^ (2 * r) ≤ (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r) :=
    eta_pow2r_le_wick_of_crossBound hψ G hC r hr b
  have hmono := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ x ^ (2*r)) h
    (by positivity : (0:ℝ) ≤ (((2 * r : ℕ):ℝ))⁻¹)
  have hlhs : (x ^ (2*r)) ^ ((((2 * r : ℕ):ℝ))⁻¹) = x :=
    Real.pow_rpow_inv_natCast hx (by omega)
  rw [hlhs] at hmono
  -- reshape the RHS: (q · df · n^r)^{1/(2r)} = (q·df)^{1/(2r)} · n^{1/2}
  have hrhs : ((Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r)) ^ ((((2 * r : ℕ):ℝ))⁻¹)
      = ((Fintype.card F : ℝ) * ((2 * r - 1)‼ : ℝ)) ^ ((((2 * r : ℕ):ℝ))⁻¹)
          * (G.card : ℝ) ^ ((2 : ℝ)⁻¹) := by
    rw [show (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r)
          = ((Fintype.card F : ℝ) * ((2 * r - 1)‼ : ℝ)) * (G.card : ℝ) ^ r by ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (G.card : ℝ) r, ← Real.rpow_mul hn]
    congr 1
    rw [eq_comm]
    have h2r : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
    rw [h2r]
    field_simp
  rwa [hrhs] at hmono

/-! ### A necessary condition, and the production-scale refutation of the all-orders hypothesis -/

/-- **The principal-coefficient lower bound `n^{2r} ≤ q·E_r`** (unconditional).  The `b = 0`
coefficient is `η_0 = ∑_{y∈G} ψ(0) = |G|`, and one term of the exact `2r`-th moment identity is at
most the whole moment sum (`eta_pow2r_le_card_mul_energy` at `b = 0`). -/
theorem card_pow_le_card_mul_rEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) :
    (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r := by
  have h := eta_pow2r_le_card_mul_energy hψ G r 0
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta]
  rwa [h0, Complex.norm_natCast] at h

/-- **`CrossBoundedByWick` forces `n^{2r} ≤ q·Wick_r` at every depth `r ≥ 1`** (equivalently
`n^r ≤ q·(2r−1)‼`): combine the inductive pin `E_r ≤ Wick_r` with the principal lower bound
`n^{2r} ≤ q·E_r`. -/
theorem card_pow_le_card_mul_wick_of_crossBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hC : CrossBoundedByWick G) (r : ℕ) (hr : 1 ≤ r) :
    G.card ^ (2 * r) ≤ Fintype.card F * wick G.card r := by
  have h1 := card_pow_le_card_mul_rEnergy hψ G r
  have h2 : (rEnergy G r : ℝ) ≤ (wick G.card r : ℝ) := by
    exact_mod_cast rEnergy_le_wick_of_crossBound G hC r hr
  have h3 : (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (wick G.card r : ℝ) :=
    h1.trans (by gcongr)
  exact_mod_cast h3

/-- **Contrapositive:** a single depth `r ≥ 1` with `q·Wick_r < n^{2r}` refutes the all-orders
hypothesis `CrossBoundedByWick`. -/
theorem not_crossBoundedByWick_of_lt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {r : ℕ} (hr : 1 ≤ r) (hlt : Fintype.card F * wick G.card r < G.card ^ (2 * r)) :
    ¬ CrossBoundedByWick G := fun hC =>
  absurd (card_pow_le_card_mul_wick_of_crossBound hψ G hC r hr) (not_le.mpr hlt)

/-- **The raw all-orders Wick hypothesis is FALSE at production scale.**  For `|G| = 2^30` and
`q < 2^159`, depth `r = 6` gives `q·11‼·n^6 < 2^159·10395·2^180 < 2^360 = n^{12}`, contradicting the
necessary condition `card_pow_le_card_mul_wick_of_crossBound`.  (A refutation of this `Prop` for such
`G`, not a Lean kernel inconsistency.) -/
theorem not_crossBoundedByWick_production {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hn : G.card = 2 ^ 30) (hq : Fintype.card F < 2 ^ 159) :
    ¬ CrossBoundedByWick G := by
  refine not_crossBoundedByWick_of_lt hψ G (r := 6) (by norm_num) ?_
  rw [hn]
  have hw : wick (2 ^ 30) 6 = 10395 * (2 ^ 30) ^ 6 := by
    unfold wick
    norm_num [Nat.doubleFactorial]
  rw [hw]
  calc Fintype.card F * (10395 * (2 ^ 30) ^ 6)
      < 2 ^ 159 * (10395 * (2 ^ 30) ^ 6) := (Nat.mul_lt_mul_right (by positivity)).mpr hq
    _ ≤ (2 ^ 30) ^ (2 * 6) := by norm_num

end ArkLib.ProximityGap.CharPWickConditionalPin

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.cross_eq
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.wick_succ
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.rEnergy_le_wick_of_crossBound
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.eta_pow2r_le_wick_of_crossBound
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.eta_le_wick_rpow_of_crossBound
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.card_pow_le_card_mul_wick_of_crossBound
#print axioms ArkLib.ProximityGap.CharPWickConditionalPin.not_crossBoundedByWick_production
