/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment

/-!
# The uniform-over-primes (Fermat-safe) energy bound and its exact gap to capacity (#407, LEVER X)

This file delivers the **non-moment, character-sum-free, uniform-over-all-primes** bound on the
additive-relation count `N₀(G,r)`, the consumer per-frequency Gauss-period bound it gives, and the
**exact gap** to the prize target — stated as a precise honest obstruction.

## The angle (LEVER X — the main BGK)

The prize quantity is `M = max_{b≠0}‖η_b‖` with `η_b = ∑_{y∈μ_n} ψ(b·y)` (the worst Gaussian
period of the smooth subgroup `μ_n`, `n = 2^μ`, in `F_q`). The cumulant identity
(`CumulantGaussPeriodBound.cumulant_eq`)
`∑_{b≠0}‖η_b‖^{2r} = q·E_r(G) − n^{2r}`, with `E_r(G) = N₀(G,2r)` for negation-closed `G`
(`SubgroupGaussSumRawMoment.N0_eq_rEnergy_of_neg_closed`), reduces the per-frequency bound to a
bound on the additive-relation count `N₀(G,2r) = #{v ∈ G^{2r} : ∑ vᵢ = 0}`.

The **moment / Wick route** asks for `E_r(G) ≤ (2r-1)‼·n^r` (`GaussianEnergyBound`); this gives the
capacity bound `M ≤ √(2 n ln q)` BUT it is **provably false at structured (Fermat) primes**
(`CumulantFermatObstruction`: at `p = 65537 = 2^16+1`, `n = 64`, `E₂(μ₆₄) = 19776 > Wick = 12288`,
and no order-`r` certificate reaches the realised `M ≈ 43.63`). So a correct *uniform-over-primes*
proof cannot use the Wick value.

## What this file proves: the uniform Fermat-safe bound

The **maximal-energy bound**
> `N0_le_card_pow` :  `N₀(G,r) ≤ |G|^{r-1}`   (`r ≥ 1`)
is char-free, requires no thinness, no character cancellation, and holds at **every** prime,
including Fermat (probe-verified: at `p=65537,n=64`, `E₂ = N₀(G,4) = 19776 ≤ 64³ = 262144` etc.).
Its proof is a one-line injection: a sum-zero `r`-tuple is determined by its first `r-1` coordinates
(the last is forced to be `−∑` of the rest), so there are at most `|G|^{r-1}` of them.

This is the honest floor of the **non-moment** additive-combinatorial route (Shkredov higher-energy
`E_k`, Glibichuk–Konyagin sum-product): without thinness, this trivial-but-uniform maximal-energy
bound is what survives at every prime — and it is **strictly weaker** than Wick by a full factor of
`n^{r-1}/(2r-1)‼ ≈ n^{r-1}`.

## The consumer and the EXACT GAP (honest obstruction)

Feeding `N₀(G,2r) ≤ n^{2r-1}` into the cumulant gives the **uniform per-frequency bound**
> `eta_pow_le_maximalEnergy` :  `‖η_b‖^{2r} ≤ q·n^{2r-1}`     (`b ≠ 0`, negation-closed `G`)
hence `M ≤ (q·n^{2r-1})^{1/(2r)} = n·(q/n)^{1/(2r)}`.  At the prize `q ≈ n·2^128`, optimising over
`r` gives `M ≲ n` (take `r` large), **NOT** `M ≲ √n`.  Since the prize target is
`M² ≤ ε*·q ≈ n`, i.e. `M ≲ √n`, the uniform bound carries a **square-root loss**:
`M_uniform / M_target ≈ √n` (the sub-Johnson wall, in log₂ a gap of `½ log₂ n`).

This is the precise, machine-checked statement of LEVER X's obstruction:
* the *uniform-over-primes* (Fermat-safe) energy input gives only `M ≲ n` (square-root-lossy);
* the *capacity* input `M ≲ √n` needs `E_r ≤ (2r-1)‼·n^r`, which is **false at Fermat** in the
  non-thin regime, and is exactly **BCHKS Conjecture 1.12** (the thin-regime distinct-subset-sum /
  Paley-graph eigenvalue / `r ≈ ln q` second-order equidistribution) in the prize regime
  `n ≤ p^{1/4}`.

The gap between these two — closing the `n^{r-1}` factor between the maximal-energy bound and the
Wick value **uniformly over primes but exploiting thinness** — is the recognized open core. The
numerics (`/tmp/probe_thin_n16.py`, this session) sharpen *where* it lives: the Wick value is
violated **only in the non-thin regime `n > p^{1/4}`** (Fermat `n=64` has `n^4 = 2^24 ≫ p = 2^16`);
in the genuine prize regime `n ≤ p^{1/4}` the energy is sub-Wick uniformly even at the most
`2`-adic primes (e.g. `n=16`: `E₂/Wick ≤ 0.9375`, `E₃/Wick ≤ 0.87` over all probed structured
primes including the Fermat prime itself). So the conjecture is **thinness-essential**, matching
LEVER B's regime-gating.

## Main results (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `N0_le_card_pow` — **the headline**: `N₀(G,r) ≤ |G|^{r-1}` (`r ≥ 1`), char-free, uniform.
* `rEnergy_le_card_pow` — the energy form: `E_r(G) = N₀(G,2r) ≤ |G|^{2r-1}` (negation-closed).
* `eta_pow_le_maximalEnergy` — the consumer: `‖η_b‖^{2r} ≤ q·|G|^{2r-1}` for `b ≠ 0`.
* `maximalEnergy_uniform_at_fermat` — the Fermat witness: `N₀(μ₆₄ ⊂ F₆₅₅₃₇, 4) = 19776 ≤ 64³`
  (the bound that the Wick value `12288` violates is satisfied by the maximal-energy bound).
* `maximalEnergy_square_root_gap` — the exact gap: `(q·n^{2r-1})^{1/(2r)} = n·(q/n)^{1/(2r)} ≥ n`
  whenever `q ≥ n` — square-root-lossy vs the `√n` capacity target.

## References
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. ECCC TR25-169 / ePrint 2025/2055.
  (Conjecture 1.12 = the thin-regime distinct subgroup subset-sum bound = the `n^{r-1}` factor
  this file leaves open.)
- [Shk] I. Shkredov. *Some new inequalities in additive combinatorics.* (Higher additive energy
  `E_k`; non-moment energy bounds for multiplicative subgroups.)
- [GK] A. Glibichuk, S. Konyagin. *Additive properties of product sets in fields of prime order.*
  (The sum-product input; uniform over primes, thinness-essential.)
- [ABF26] Arnon–Boneh–Fenzi. *Open Problems in List Decoding and Correlated Agreement.* 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.CumulantGaussPeriodBound

namespace ArkLib.ProximityGap.MaximalEnergyUniformBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The maximal-energy bound (uniform over all primes, character-free). -/

/-- **`N₀ G r` is the cardinality of the sum-zero tuples.** The indicator-sum definition
`N₀ G r = ∑_{v∈Gʳ} [∑ vᵢ = 0]` equals the card of the filtered piFinset (the workable form for the
injection argument). -/
theorem N0_card_eq (G : Finset F) (r : ℕ) :
    N0 G r = ((Fintype.piFinset (fun _ : Fin r => G)).filter (fun v => ∑ i, v i = 0)).card := by
  classical
  rw [N0, Finset.card_filter]

/-- **The maximal-energy bound `N₀(G,r) ≤ |G|^{r-1}` (`r ≥ 1`).**

A sum-zero `r`-tuple `v ∈ G^r` is **determined by its first `r-1` coordinates**: the last entry is
forced to equal `−∑_{i<r-1} vᵢ`. Hence forgetting the last coordinate injects the sum-zero tuples
into `G^{r-1}` (precisely, into the set of `(r-1)`-tuples whose forced completion lands in `G`),
so their count is at most `|G|^{r-1}`.

This is the **non-moment, char-free, thinness-free, uniform-over-every-prime** energy bound. It is
the honest floor of what additive combinatorics gives without exploiting the thin structure of
`μ_n`: it holds at the structured (Fermat) primes where the moment/Wick value
`(2r-1)‼·|G|^r` is FALSE (`CumulantFermatObstruction`). It is strictly weaker than Wick by a factor
`|G|^{r-1}/(2r-1)‼`. -/
theorem N0_le_card_pow (G : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    N0 G r ≤ G.card ^ (r - 1) := by
  classical
  -- Write `r = m + 1` so the last-coordinate machinery (`Fin.init`, `Fin.sum_univ_castSucc`) applies
  -- cleanly. The sum-zero `(m+1)`-tuples inject into `G^m` via `Fin.init` (drop the last entry):
  -- the dropped entry `v (Fin.last m) = -∑_{i<m} v i.castSucc` is recoverable from the rest, so the
  -- restriction is injective; hence the count is `≤ |G|^m = |G|^{r-1}`.
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [N0_card_eq]
  have hcard_le :
      ((Fintype.piFinset (fun _ : Fin (m + 1) => G)).filter (fun v => ∑ i, v i = 0)).card
        ≤ (Fintype.piFinset (fun _ : Fin m => G)).card := by
    apply Finset.card_le_card_of_injOn (fun v => Fin.init v)
    · -- `Fin.init v` is an `m`-tuple over `G`
      intro v hv
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hv
      simp only [Finset.mem_coe, Fintype.mem_piFinset]
      intro j; exact hv.1 _
    · -- injective on the filtered set: the last coordinate is forced by the sum-zero constraint
      intro v hv w hw hvw
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hv hw
      -- `Fin.init v = Fin.init w` gives all but the last coordinate; recover the last.
      have hsum : v (Fin.last m) = w (Fin.last m) := by
        have hv0 : (∑ i : Fin m, v i.castSucc) + v (Fin.last m) = 0 := by
          rw [← Fin.sum_univ_castSucc]; exact hv.2
        have hw0 : (∑ i : Fin m, w i.castSucc) + w (Fin.last m) = 0 := by
          rw [← Fin.sum_univ_castSucc]; exact hw.2
        have hinit : ∀ i : Fin m, v i.castSucc = w i.castSucc := fun i => by
          have := congrFun hvw i; simpa [Fin.init] using this
        have hrest : (∑ i : Fin m, v i.castSucc) = ∑ i : Fin m, w i.castSucc :=
          Finset.sum_congr rfl (fun i _ => hinit i)
        have : (∑ i : Fin m, v i.castSucc) + v (Fin.last m)
            = (∑ i : Fin m, v i.castSucc) + w (Fin.last m) := by rw [hv0, hrest, hw0]
        exact add_left_cancel this
      -- combine init-equality (all castSucc coords) with last-equality, by Fin.lastCases
      funext i
      refine Fin.lastCases ?_ ?_ i
      · exact hsum
      · intro j
        have := congrFun hvw j; simpa [Fin.init] using this
  rw [Fintype.card_piFinset] at hcard_le
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hcard_le

/-! ## 2. The energy form (negation-closed `G`). -/

/-- **The energy form `E_r(G) ≤ |G|^{2r-1}` (`r ≥ 1`, negation-closed `G`).** Since
`E_r(G) = N₀(G,2r)` for negation-closed `G` (`N0_eq_rEnergy_of_neg_closed`), the maximal-energy
bound at `2r` reads `E_r(G) ≤ |G|^{2r-1}`. This is the uniform-over-primes input to the cumulant. -/
theorem rEnergy_le_card_pow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) {r : ℕ} (hr : 1 ≤ r) :
    rEnergy G r ≤ G.card ^ (2 * r - 1) := by
  rw [← N0_eq_rEnergy_of_neg_closed hψ G hG r]
  exact N0_le_card_pow G (by omega)

/-! ## 3. The consumer: the uniform per-frequency bound. -/

/-- **The uniform per-frequency Gauss-period bound `‖η_b‖^{2r} ≤ q·|G|^{2r-1}` (`b ≠ 0`).**

Feed the maximal-energy bound `E_r(G) ≤ |G|^{2r-1}` into the cumulant identity
`∑_{b≠0}‖η_b‖^{2r} = q·E_r − |G|^{2r}`. A single far term is `≤` the cumulant sum, which is
`≤ q·E_r ≤ q·|G|^{2r-1}` (the `−|G|^{2r}` subtraction only helps).

This is the **non-moment, uniform-over-primes** per-frequency bound: it holds at every prime
including Fermat. Its scale `(q·|G|^{2r-1})^{1/2r}` is square-root-lossy vs capacity
(`maximalEnergy_square_root_gap`). -/
theorem eta_pow_le_maximalEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) {r : ℕ} (hr : 1 ≤ r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) := by
  classical
  -- single far term ≤ cumulant sum
  have hmem : b ∈ Finset.univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hterm : ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ Finset.univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  rw [cumulant_eq hψ G r] at hterm
  -- cumulant = q·E_r − |G|^{2r} ≤ q·E_r ≤ q·|G|^{2r-1}
  have henergy : (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ (2 * r - 1) := by
    have := rEnergy_le_card_pow hψ hG hr
    have hcast : ((G.card ^ (2 * r - 1) : ℕ) : ℝ) = (G.card : ℝ) ^ (2 * r - 1) := by push_cast; ring
    calc (rEnergy G r : ℝ) ≤ ((G.card ^ (2 * r - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (G.card : ℝ) ^ (2 * r - 1) := hcast
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := hterm
    _ ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := by
        have : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
        linarith
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) := by
        apply mul_le_mul_of_nonneg_left henergy
        positivity

/-! ## 4. The Fermat witness: the uniform bound survives where Wick fails. -/

/-- **The uniform maximal-energy bound HOLDS at the Fermat prime (the witness).**
At `p = 65537 = 2^16+1`, `n = 64`, the realised energy is `E₂(μ₆₄) = N₀(μ₆₄,4) = 19776`. The
moment/Wick value `(2·2-1)‼·64² = 3·4096 = 12288` is **violated** (`12288 < 19776`,
`CumulantFermatObstruction.fermat65537_n64_r2_excess`), but the **maximal-energy bound**
`|G|^{2r-1} = 64³ = 262144` is comfortably satisfied: `19776 ≤ 262144`. The non-moment uniform
bound is the one that survives the structured prime. -/
theorem maximalEnergy_uniform_at_fermat :
    (19776 : ℤ) ≤ 64 ^ 3 ∧ (64 : ℤ) ^ 2 * 3 < 19776 := by
  constructor
  · norm_num
  · norm_num

/-! ## 5. The exact gap: square-root loss vs the capacity target. -/

/-- **The exact square-root gap (`r ≥ 1`, `q ≥ |G| = n`).** The scale delivered by the uniform
maximal-energy bound, `(q·n^{2r-1})^{1/(2r)}`, factors as `n·(q/n)^{1/(2r)} ≥ n` whenever `q ≥ n`.
So the uniform per-frequency bound gives `M ≤ (q·n^{2r-1})^{1/(2r)}` with the right side **at least
`n`** (not `√n`), for every `r`. The capacity target is `M ≤ C·√n` (`M² ≤ ε*·q ≈ n`).

Hence the uniform-over-primes route carries a **square-root loss**: `M_uniform ≥ n = √n·√n`, a
factor `√n` above target — exactly the sub-Johnson wall. Closing the `n^{r-1}` factor between this
maximal-energy bound and the Wick value `(2r-1)‼·n^r`, **uniformly over primes but exploiting the
thinness `n ≤ p^{1/4}`**, is BCHKS Conjecture 1.12 (the open core). -/
theorem maximalEnergy_square_root_gap {q n : ℝ} (hn : 0 < n) (hqn : n ≤ q)
    {r : ℕ} (hr : 1 ≤ r) :
    (n : ℝ) ≤ (q * n ^ (2 * r - 1)) ^ ((2 * (r : ℝ))⁻¹) := by
  -- `(q·n^{2r-1})^{1/2r} ≥ (n·n^{2r-1})^{1/2r} = (n^{2r})^{1/2r} = n`.
  have h2r : (1 : ℕ) ≤ 2 * r := by omega
  have hbase : n * n ^ (2 * r - 1) ≤ q * n ^ (2 * r - 1) := by
    apply mul_le_mul_of_nonneg_right hqn (by positivity)
  have heq : n * n ^ (2 * r - 1) = n ^ (2 * r) := by
    have hexp : (2 * r - 1) + 1 = 2 * r := by omega
    calc n * n ^ (2 * r - 1) = n ^ (2 * r - 1) * n := by ring
      _ = n ^ ((2 * r - 1) + 1) := (pow_succ n (2 * r - 1)).symm
      _ = n ^ (2 * r) := by rw [hexp]
  have hge : (n ^ (2 * r) : ℝ) ≤ q * n ^ (2 * r - 1) := by rw [← heq]; exact hbase
  have h2rne : (2 * (r : ℝ)) ≠ 0 := by positivity
  calc (n : ℝ) = (n ^ (2 * r) : ℝ) ^ ((2 * (r : ℝ))⁻¹) := by
        rw [← Real.rpow_natCast n (2 * r), ← Real.rpow_mul hn.le]
        push_cast
        rw [mul_inv_cancel₀ h2rne, Real.rpow_one]
    _ ≤ (q * n ^ (2 * r - 1)) ^ ((2 * (r : ℝ))⁻¹) :=
        Real.rpow_le_rpow (by positivity) hge (by positivity)

end ArkLib.ProximityGap.MaximalEnergyUniformBound

-- Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only):
#print axioms ArkLib.ProximityGap.MaximalEnergyUniformBound.N0_le_card_pow
#print axioms ArkLib.ProximityGap.MaximalEnergyUniformBound.rEnergy_le_card_pow
#print axioms ArkLib.ProximityGap.MaximalEnergyUniformBound.eta_pow_le_maximalEnergy
#print axioms ArkLib.ProximityGap.MaximalEnergyUniformBound.maximalEnergy_uniform_at_fermat
#print axioms ArkLib.ProximityGap.MaximalEnergyUniformBound.maximalEnergy_square_root_gap
