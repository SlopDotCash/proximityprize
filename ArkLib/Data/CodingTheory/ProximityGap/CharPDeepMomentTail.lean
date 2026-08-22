/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The unconditional deep-moment tail of the subgroup Gauss sum (Issue #407, "L4")

This file closes the **unconditional** loop on the additive-moment recursion of
`CharPMomentRecursion.lean`: iterate the free growth ceiling
`rEnergy_succ_le : E_{r+1} ≤ |G|²·E_r` from the exact base cases to obtain a closed-form
upper bound on the `r`-fold additive energy `E_r = rEnergy G r`, then push it through the exact
`2r`-th moment identity `subgroup_gaussSum_moment : ∑_b ‖η_b‖^{2r} = q·E_r` (a single term ≤ the
sum) to get a **Markov / moment** sup-norm bound on `‖η_b‖ = |∑_{y∈G} ψ(b·y)|` that holds for
**every** `b` and **every** order `r`, fully unconditionally (no Weil, no sum-product, no
Lam–Leung, no subgroup hypothesis — any finite `G ⊆ F`).

## What is proven (all axiom-clean, char-`p`, any finite `G`)

* `rEnergy_zero`        : `E_0 = 1`.
* `rEnergy_one`         : `E_1 = |G|`.
* `rEnergy_le_pow`      : `E_r ≤ |G|^{2r}`             — iterate from `E_0 = 1`.
* `rEnergy_le_pow_sharp`: `E_r ≤ |G|^{2r-1}` (`r ≥ 1`) — the sharper iterate from `E_1 = |G|`.
* `eta_pow2r_le_card_mul_energy` : `‖η_b‖^{2r} ≤ q·E_r` for every `b` (single term ≤ moment sum).
* `eta_pow2r_le`        : `‖η_b‖^{2r} ≤ q·|G|^{2r}`    — the unconditional deep-tail moment bound.
* `eta_pow2r_le_sharp`  : `‖η_b‖^{2r} ≤ q·|G|^{2r-1}` (`r ≥ 1`).
* `eta_le_rpow`         : `‖η_b‖ ≤ q^{1/(2r)}·|G|` (`r ≥ 1`) — the `2r`-th-root Markov form, for
                          every `b` and every `r`.

## Honest scope — this is the NON-PRIZE regime, it does NOT close the prize

The bound `‖η_b‖ ≤ q^{1/(2r)}·|G|` has the trivial `|G|`-floor multiplied by the Markov factor
`q^{1/(2r)} → 1` as `r → ∞`. So the best this unconditional route can ever reach is the
**trivial** bound `‖η_b‖ ≈ |G| = n` (no square-root cancellation). Quantitatively:

* The Markov factor `q^{1/(2r)}` becomes `O(1)` only once `2r ≳ log q`. In the prize regime
  `q ≈ n·2^{128}` (so `log q ≈ log n + 128·log 2`), that means `r ≳ ½·log q ≈ 64`, i.e. an order
  `r = Θ(log q)` deep in the tail — and even there the bound is only `≈ n`, never `√n`.
* The companion no-go `Frontier/_MomentMethodNoGo.lean` proves the matching **lower** bound
  `(q·E_r)^{1/(2r)} ≥ n` for every `r`. Together with `eta_pow2r_le` here, the two bounds
  **pin the moment route at `n`**: there is no order `r` at which any additive-moment / energy
  argument certifies `‖η_b‖ < n`, let alone the prize floor `‖η_b‖ ≲ √(n·log(q/n))`.
* The prize moment depth is `r ≍ log m` (short), where the *prize* energy input
  `E_r ≤ (2r-1)‼·n^r` (Lam–Leung, char-0, NOT this `|G|^{2r}` bound) would give the `√n` floor —
  but its char-`p` transfer to `r ≈ log q` is exactly the open BGK/Lam–Leung wall (CLAUDE.md
  face #3), and is **not** addressed here.

So this is a genuine unconditional theorem, honestly scoped as **off-prize**: it is the trivial
`L²`/energy ceiling of the moment ladder, complementary to the `_MomentMethodNoGo` floor, and it
neither needs nor establishes any square-root cancellation.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.CharPMomentRecursion (freq rEnergy_eq_sum_freq_sq sum_freq rEnergy_succ_le)

namespace ArkLib.ProximityGap.CharPDeepMomentTail

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Exact base cases of the energy ladder -/

/-- `E_0 = 1`: the only `0`-tuple is empty, both sides sum to `0`. -/
theorem rEnergy_zero (G : Finset F) : rEnergy G 0 = 1 := by
  unfold rEnergy; simp

/-- The level-`1` sum-frequency is `0/1`-valued: `freq G 1 d ≤ 1` (at most one length-`1` tuple
sums to a given `d`, namely `v = ![d]` when `d ∈ G`). -/
theorem freq_one_le_one (G : Finset F) (d : F) : freq G 1 d ≤ 1 := by
  unfold freq
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Fintype.mem_piFinset] at ha hb
  have hae : a 0 = d := by have := ha.2; simpa [Fin.sum_univ_one] using this
  have hbe : b 0 = d := by have := hb.2; simpa [Fin.sum_univ_one] using this
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this; rw [hae, hbe]

/-- `E_1 = |G|`: the `1`-fold additive energy is just the diagonal count `#{(x,y)∈G² : x = y}`.
Proven via `E_r = ∑_d freq²`, with `freq G 1` being `0/1`-valued (so `freq² = freq`) and total
mass `|G|`. -/
theorem rEnergy_one (G : Finset F) : rEnergy G 1 = G.card := by
  rw [rEnergy_eq_sum_freq_sq]
  have hsq : ∀ d : F, freq G 1 d ^ 2 = freq G 1 d := by
    intro d; have := freq_one_le_one G d; interval_cases (freq G 1 d) <;> simp
  simp_rw [hsq]
  rw [sum_freq G 1, pow_one]

/-! ### Iterating the free growth ceiling `E_{r+1} ≤ |G|²·E_r` -/

/-- **The unconditional deep-tail energy bound `E_r ≤ |G|^{2r}`.** Iterate the free growth
ceiling `rEnergy_succ_le : E_{r+1} ≤ |G|²·E_r` from `E_0 = 1`. Fully unconditional (any finite
set, char-`p`, no analytic input). -/
theorem rEnergy_le_pow (G : Finset F) (r : ℕ) :
    rEnergy G r ≤ G.card ^ (2 * r) := by
  induction r with
  | zero => rw [rEnergy_zero]; simp
  | succ k ih =>
      calc rEnergy G (k + 1) ≤ G.card ^ 2 * rEnergy G k := rEnergy_succ_le G k
        _ ≤ G.card ^ 2 * G.card ^ (2 * k) := Nat.mul_le_mul_left _ ih
        _ = G.card ^ (2 * (k + 1)) := by rw [← pow_add]; ring_nf

/-- **The sharper deep-tail energy bound `E_r ≤ |G|^{2r-1}` for `r ≥ 1`.** Same iteration but
starting from the exact `E_1 = |G|` instead of `E_0 = 1` — one extra factor of `|G|` saved. -/
theorem rEnergy_le_pow_sharp (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    rEnergy G r ≤ G.card ^ (2 * r - 1) := by
  induction r with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [rEnergy_one]; simp
      · have ihk := ih hk
        calc rEnergy G (k + 1) ≤ G.card ^ 2 * rEnergy G k := rEnergy_succ_le G k
          _ ≤ G.card ^ 2 * G.card ^ (2 * k - 1) := Nat.mul_le_mul_left _ ihk
          _ = G.card ^ (2 * (k + 1) - 1) := by rw [← pow_add]; congr 1; omega

/-! ### The Markov / moment sup-norm bound on `‖η_b‖` (every `b`, every `r`) -/

/-- A single Gauss-sum modulus power is bounded by the full `2r`-th moment (a single term ≤ the
nonnegative sum): `‖η_b‖^{2r} ≤ q·E_r` for **every** `b`. Uses the exact moment identity
`subgroup_gaussSum_moment`. -/
theorem eta_pow2r_le_card_mul_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r := by
  rw [← subgroup_gaussSum_moment hψ G r]
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) ?_ (Finset.mem_univ b)
  intro i _; positivity

/-- **The unconditional deep-tail moment bound: `‖η_b‖^{2r} ≤ q·|G|^{2r}`** for every `b` and
every `r`. Compose `eta_pow2r_le_card_mul_energy` with `rEnergy_le_pow`. -/
theorem eta_pow2r_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r) := by
  calc ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r :=
        eta_pow2r_le_card_mul_energy hψ G r b
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r) := by
        gcongr
        exact_mod_cast rEnergy_le_pow G r

/-- The sharper deep-tail moment bound `‖η_b‖^{2r} ≤ q·|G|^{2r-1}` (`r ≥ 1`). -/
theorem eta_pow2r_le_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) := by
  calc ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r :=
        eta_pow2r_le_card_mul_energy hψ G r b
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) := by
        gcongr
        exact_mod_cast rEnergy_le_pow_sharp G r hr

/-- **The `2r`-th-root (Markov) form, for every `b` and every `r ≥ 1`:**
`‖η_b‖ ≤ q^{1/(2r)}·|G|`. This is the unconditional deep-tail sup-norm bound. Note the trivial
`|G|`-floor: as `r → ∞` the Markov factor `q^{1/(2r)} → 1`, so the bound tends to the *trivial*
`‖η_b‖ ≈ |G|`; it never reaches the prize floor `√|G|`. See the file docstring for the off-prize
scope and the matching `_MomentMethodNoGo` lower bound that pins the route at `|G|`. -/
theorem eta_le_rpow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) (hr : 1 ≤ r)
    (b : F) :
    ‖eta ψ G b‖ ≤ (Fintype.card F : ℝ) ^ ((((2 * r : ℕ) : ℝ))⁻¹) * (G.card : ℝ) := by
  set x : ℝ := ‖eta ψ G b‖ with hxdef
  have hx : 0 ≤ x := norm_nonneg _
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have h : x ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r) := eta_pow2r_le hψ G r b
  have hmono := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ x ^ (2*r)) h
    (by positivity : (0:ℝ) ≤ (((2 * r : ℕ):ℝ))⁻¹)
  have hlhs : (x ^ (2*r)) ^ ((((2 * r : ℕ):ℝ))⁻¹) = x :=
    Real.pow_rpow_inv_natCast hx (by omega)
  rw [hlhs] at hmono
  have hrhs : ((Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r)) ^ ((((2 * r : ℕ):ℝ))⁻¹)
      = (Fintype.card F : ℝ) ^ ((((2 * r : ℕ):ℝ))⁻¹) * (G.card : ℝ) := by
    rw [Real.mul_rpow hq (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (G.card : ℝ) (2*r), ← Real.rpow_mul hn,
        mul_inv_cancel₀ (by positivity : ((2*r : ℕ):ℝ) ≠ 0), Real.rpow_one]
  rwa [hrhs] at hmono

end ArkLib.ProximityGap.CharPDeepMomentTail

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_zero
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_one
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_le_pow
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_le_pow_sharp
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.eta_pow2r_le
#print axioms ArkLib.ProximityGap.CharPDeepMomentTail.eta_le_rpow
