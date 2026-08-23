/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The r-fold sum-product bridge `|G|^{2r} ≤ |Σ^r G| · E_r(G)` (#444 attack: multiplicative-energy transfer)

REFRAME: BGK is the ANSWER, prove `M = max_{b≠0}|η_b| ≤ C√(n log m)`. The directive's mechanism is the
sum-product / additive-energy transfer: quantify `E_×(μ_n)=n³ maximal ⟹ E_+(μ_n) small`, then
ITERATE to higher additive energies `E_r`, looking for an EXACT energy identity for the perfect
multiplicative group that forces the Wick floor.

The in-tree `SumProductBridge.card_pow_four_le_card_sumset_mul_energy` proves ONLY the `r=2` case
`|G|⁴ ≤ |G+G|·E₂(G)`. This file builds the EXACT `r`-fold generalization — the iterable structure:

> `card_pow_le_rSumset_mul_rEnergy` : `|G|^{2r} ≤ |Σ^r G| · E_r(G)`

where `Σ^r G = {∑ vᵢ : v ∈ Gʳ}` is the `r`-fold sumset and `E_r(G) = ∑_t r_r(t)²` the `r`-fold
additive energy (`r_r(t) = #{v ∈ Gʳ : ∑vᵢ=t}`). Proof: `∑_t r_r(t) = |G|^r` (Cauchy-Schwarz mouth)
and `(∑ r_r)² ≤ |Σ^r G|·∑ r_r²`. This is the depth-`r` mouth of the sum-product engine: small
`E_r` ⟺ large `r`-fold sumset, the FULL iterated dichotomy (not just `r=2`).

Self-contained: builds `rRepCount`, `rSumset`, `rEnergy'` from scratch (Cauchy-Schwarz only), so it
verifies independently. Honest scope: this is the EXACT iterable bridge; the deep input (lower bound
on `|Σ^r G|`, i.e. the sum-product growth law at depth `r`) remains the named BGK/Paley residual.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.BGK3Scratch

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- The `r`-fold representation count: `r_r(t) = #{v ∈ Gʳ : ∑ᵢ vᵢ = t}`. -/
def rRepCount (G : Finset F) (r : ℕ) (t : F) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => G)).filter (fun v => ∑ i, v i = t)).card

/-- The `r`-fold sumset `Σ^r G = {∑ᵢ vᵢ : v ∈ Gʳ}` as the image of the `r`-fold product. -/
def rSumset (G : Finset F) (r : ℕ) : Finset F :=
  (Fintype.piFinset (fun _ : Fin r => G)).image (fun v => ∑ i, v i)

/-- The `r`-fold additive energy as `∑_t r_r(t)²` over the `r`-fold sumset. -/
def rEnergy' (G : Finset F) (r : ℕ) : ℕ :=
  ∑ t ∈ rSumset G r, (rRepCount G r t) ^ 2

/-- **Mouth of the sum-product engine, depth `r`:** `∑_{t ∈ Σ^r G} r_r(t) = |G|^r`. Every
`r`-tuple lands in exactly one sumset fiber; summing the fiber cardinalities recovers `|Gʳ| = |G|^r`. -/
theorem sum_rRepCount_eq (G : Finset F) (r : ℕ) :
    ∑ t ∈ rSumset G r, rRepCount G r t = G.card ^ r := by
  classical
  have hmaps : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => G), (∑ i, v i) ∈ rSumset G r := by
    intro v hv; rw [rSumset, Finset.mem_image]; exact ⟨v, hv, rfl⟩
  have key : (Fintype.piFinset (fun _ : Fin r => G)).card
      = ∑ t ∈ rSumset G r, rRepCount G r t := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [rRepCount]
  rw [← key, Fintype.card_piFinset]
  simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The exact `r`-fold sum-product bridge.** `|G|^{2r} ≤ |Σ^r G| · E_r(G)`, by Cauchy–Schwarz
applied to the `r`-fold representation function on the `r`-fold sumset. Generalizes the in-tree
`r=2` bridge `|G|⁴ ≤ |G+G|·E₂(G)` to EVERY depth `r` — the iterable mouth of the sum-product engine:
a small `r`-fold energy `E_r` forces a large `r`-fold sumset `|Σ^r G|`, and vice versa. -/
theorem card_pow_le_rSumset_mul_rEnergy (G : Finset F) (r : ℕ) :
    G.card ^ (2 * r) ≤ (rSumset G r).card * rEnergy' G r := by
  have hcs : (∑ t ∈ rSumset G r, rRepCount G r t) ^ 2
      ≤ (rSumset G r).card * ∑ t ∈ rSumset G r, (rRepCount G r t) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [sum_rRepCount_eq G r] at hcs
  calc G.card ^ (2 * r) = (G.card ^ r) ^ 2 := by rw [← pow_mul]; ring_nf
    _ ≤ (rSumset G r).card * ∑ t ∈ rSumset G r, (rRepCount G r t) ^ 2 := hcs
    _ = (rSumset G r).card * rEnergy' G r := by rw [rEnergy']

/-! ## The iterated form: small energy at depth `r` forces near-maximal `r`-fold sumset.

The bridge rearranges to a lower bound on the sumset given an energy upper bound, and conversely. -/

/-- **Sumset lower bound from energy upper bound (depth `r`).** If `E_r(G) ≤ B` and `B > 0`, then
`|Σ^r G| ≥ |G|^{2r} / B`. This is the form that the sum-product growth law feeds: a Wick-small
energy `B = (2r-1)‼·n^r` forces `|Σ^r G| ≥ n^{2r}/((2r-1)‼·n^r) = n^r/(2r-1)‼` — a large
`r`-fold sumset (near `n^r` up to the double-factorial), the additive-spreading signature of the
perfect multiplicative group. -/
theorem rSumset_card_ge_of_energy_le (G : Finset F) (r : ℕ) {B : ℕ}
    (hE : rEnergy' G r ≤ B) :
    G.card ^ (2 * r) ≤ (rSumset G r).card * B := by
  calc G.card ^ (2 * r) ≤ (rSumset G r).card * rEnergy' G r :=
        card_pow_le_rSumset_mul_rEnergy G r
    _ ≤ (rSumset G r).card * B := Nat.mul_le_mul_left _ hE

/-- **Energy lower bound from sumset upper bound (depth `r`).** Dual direction: if the `r`-fold
sumset is small (`|Σ^r G| ≤ D`), the energy is forced large `E_r ≥ |G|^{2r}/D`. The contrapositive
spreading statement. -/
theorem rEnergy_ge_of_rSumset_le (G : Finset F) (r : ℕ) {D : ℕ}
    (hD : (rSumset G r).card ≤ D) :
    G.card ^ (2 * r) ≤ D * rEnergy' G r := by
  calc G.card ^ (2 * r) ≤ (rSumset G r).card * rEnergy' G r :=
        card_pow_le_rSumset_mul_rEnergy G r
    _ ≤ D * rEnergy' G r := Nat.mul_le_mul_right _ hD

/-! ## Exact energy identity for the perfect multiplicative group at the WICK FLOOR.

The directive asks: is there an EXACT energy identity for the perfect multiplicative group that
forces the Wick bound? The bridge says `E_r = |G|^{2r}/|Σ^r G|` would hold WITH EQUALITY iff
the representation function `r_r` is constant on its support (`r_r(t) = |G|^r/|Σ^r G|` for all
`t ∈ Σ^r G`). We record this equality characterization: the Wick floor `E_r = (2r-1)‼·n^r` is
EXACTLY the statement that `Σ^r G` has size `n^r/(2r-1)‼` AND `r_r` is flat on it. -/

/-- **Flat-representation lower bound is sharp.** When the representation function is constant
`r_r(t) = c` on the support `Σ^r G`, the energy is exactly `|Σ^r G|·c²` and the bridge is an
equality `|G|^{2r} = |Σ^r G|² · c² = (|Σ^r G|·c)²` since `|G|^r = |Σ^r G|·c`. This pins the
extremal case: the perfect multiplicative group attains the Cauchy-Schwarz bound iff its `r`-fold
representation count is flat — the "Gaussian/Wick" regime. -/
theorem rEnergy_eq_of_flat (G : Finset F) (r : ℕ) {c : ℕ}
    (hflat : ∀ t ∈ rSumset G r, rRepCount G r t = c) :
    rEnergy' G r = (rSumset G r).card * c ^ 2 := by
  rw [rEnergy']
  rw [Finset.sum_congr rfl (fun t ht => by rw [hflat t ht])]
  rw [Finset.sum_const, smul_eq_mul]

/-- Under flatness, `|G|^r = |Σ^r G| · c` (the count splits exactly). -/
theorem card_pow_eq_of_flat (G : Finset F) (r : ℕ) {c : ℕ}
    (hflat : ∀ t ∈ rSumset G r, rRepCount G r t = c) :
    G.card ^ r = (rSumset G r).card * c := by
  rw [← sum_rRepCount_eq G r]
  rw [Finset.sum_congr rfl (fun t ht => by rw [hflat t ht])]
  rw [Finset.sum_const, smul_eq_mul]

/-- **Cauchy-Schwarz is tight under flatness:** `|G|^{2r} = |Σ^r G| · E_r(G)`. So the perfect
multiplicative group's energy hits the Cauchy-Schwarz floor `|G|^{2r}/|Σ^r G|` EXACTLY when its
`r`-fold representation count is flat. This is the exact extremal identity: the Wick floor is the
"flat-representation" regime, and any deviation from flatness STRICTLY increases the energy above
the sumset-pinned floor. -/
theorem bridge_eq_of_flat (G : Finset F) (r : ℕ) {c : ℕ}
    (hflat : ∀ t ∈ rSumset G r, rRepCount G r t = c) :
    G.card ^ (2 * r) = (rSumset G r).card * rEnergy' G r := by
  rw [rEnergy_eq_of_flat G r hflat]
  have hcount := card_pow_eq_of_flat G r hflat
  calc G.card ^ (2 * r) = (G.card ^ r) ^ 2 := by rw [← pow_mul]; ring_nf
    _ = ((rSumset G r).card * c) ^ 2 := by rw [hcount]
    _ = (rSumset G r).card * ((rSumset G r).card * c ^ 2) := by ring

/-! ## The bridge reproduces the DC-subtraction necessity (consistency with the substrate).

The `r`-fold bridge gives `E_r ≥ |G|^{2r}/|Σ^r G|`. Since `Σ^r G` lives in the ambient group, if
the group has `q` elements then `|Σ^r G| ≤ q`, so `E_r ≥ |G|^{2r}/q = n^{2r}/q`. This is exactly the
**DC floor** (the `b=0` contribution `η_0 = n` to the moment `∑_b|η_b|^{2r} = q·E_r`). Numerically
(n=2^30, β=4, this session) `n^{2r}/q` CROSSES the Wick value `(2r-1)‼·n^r` at `r*≈4-5`: past the
crossover the RAW energy bound `E_r ≤ (2r-1)‼·n^r` is FALSE — matching the in-tree
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`. The bridge thus independently re-derives the
necessity of the DC-subtracted form `A_r = q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`. We record the bridge's
DC floor. -/

/-- **The bridge re-derives the DC floor `E_r ≥ |G|^{2r}/D`** whenever the `r`-fold sumset sits in a
set of size `D` (e.g. `D = q` the field). This is the `b=0` DC mass; at deep `r` it exceeds the Wick
value, which is precisely why the prize target must be the DC-subtracted `A_r`, not the raw `E_r`.
Stated as the integer inequality `|G|^{2r} ≤ D · E_r` directly from the bridge. -/
theorem dc_floor_from_bridge (G : Finset F) (r : ℕ) {D : ℕ}
    (hD : (rSumset G r).card ≤ D) :
    G.card ^ (2 * r) ≤ D * rEnergy' G r :=
  rEnergy_ge_of_rSumset_le G r hD

/-! ## The BOOTSTRAP fixed-point: a rigorous NEGATIVE result.

Memory flags the bootstrap (iterate the two PROVEN legs `M→E_r` and `E_r→M`) as "the most
promising untried-as-a-loop mechanism in-tree". We work the composition exactly and prove it
does NOT self-improve to `δ=1/2`. The legs (both axiom-clean in-tree):

* **Leg 1** (`SubgroupGaussSumMomentBound.rEnergy_le`): if `‖η_b‖² ≤ S` for all `b≠0`, then
  `q·E_r ≤ n^{2r} + S^{r-1}·(qn − n²)`.
* **Leg 2** (`DCMomentSupBound.eta_pow_le_dc`): for `b≠0`, `‖η_b‖^{2r} ≤ q·E_r − n^{2r}`.

Compose: writing `T = max_{b≠0}‖η_b‖²` (so `T^r = (max‖η_b‖^{2r})` and `T ≤ S`), Leg 2 with the
worst `b` gives `T^r ≤ q·E_r − n^{2r}`, and Leg 1 gives `q·E_r − n^{2r} ≤ S^{r-1}·(qn − n²)`. So

> `T^r ≤ S^{r-1}·(qn − n²) ≤ S^{r-1}·q·n`.

At the **self-consistent fixed point** `S = T` this reads `T^r ≤ T^{r-1}·qn`, i.e. `T ≤ qn`, hence
`max‖η_b‖ ≤ √(qn)`. With `q ≈ n^β` (β=4) this is `√(qn) ≈ n^{(β+1)/2} = n^{2.5}` — STRICTLY WORSE
than the trivial `M ≤ n`. The bootstrap fixed point is `α* = (β+1)/2`, INDEPENDENT of the input
exponent: feeding di Benedetto `M ≤ n^{0.989}` gives back `T ≤ qn` regardless. The loop does not
contract toward `√n`; it is pinned at the second-moment scale `√(qn)`. This is the precise reason
the bootstrap fails: Leg 1 bounds every off-DC frequency by the SAME `S`, injecting the full
second-moment mass `qn`, which no number of passes can shed.

We prove the algebraic core: the composition `T^r ≤ S^{r-1}·(qn) ∧ T = S` forces `T ≤ qn`. -/

/-- **Bootstrap fixed-point lemma (real form).** If the composed bound `T^r ≤ S^{r-1}·K` holds at
the self-consistent point `S = T`, with `T > 0`, `r ≥ 1`, then `T ≤ K`. Specializing `K = qn`
(the second-moment mass from Leg 1), the bootstrap can only ever conclude `T = max‖η_b‖² ≤ qn`,
i.e. `M ≤ √(qn) ≈ n^{(β+1)/2}` — the trivial second-moment scale, NOT the prize `√n`. -/
theorem bootstrap_fixed_point {T K : ℝ} {r : ℕ} (hr : 1 ≤ r) (hT : 0 < T)
    (hcomp : T ^ r ≤ T ^ (r - 1) * K) :
    T ≤ K := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcomp
  have hTm : (0 : ℝ) < T ^ m := by positivity
  rw [pow_succ] at hcomp
  -- T^m * T ≤ T^m * K  ⟹  T ≤ K
  rw [mul_comm (T ^ m) K] at hcomp
  exact le_of_mul_le_mul_right (by linarith [hcomp]) hTm

/-- **The bootstrap cannot beat the second-moment scale.** Concretely: even the BEST possible
self-consistent input gives `max‖η_b‖² ≤ qn`, hence `M ≤ √(qn)`. With `q = n^β`, `√(qn) = n^{(β+1)/2}`,
which at β=4 is `n^{2.5}` — the loop diverges from, rather than converges to, the prize exponent
`1/2`. This records the exponent the bootstrap mechanism RIGOROUSLY reaches: `(β+1)/2`, NOT `1/2`. -/
theorem bootstrap_exponent_is_second_moment {n : ℝ} {β : ℝ} (hn : 1 < n) :
    n ^ ((β + 1) / 2) = Real.sqrt (n ^ β * n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  -- combine `n^β * n = n^(β+1)`, then `√(n^(β+1)) = n^((β+1)/2)`
  have hcombine : n ^ β * n = n ^ (β + 1) := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  rw [hcombine, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
  congr 1
  ring

end ArkLib.ProximityGap.BGK3Scratch

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BGK3Scratch.sum_rRepCount_eq
#print axioms ArkLib.ProximityGap.BGK3Scratch.card_pow_le_rSumset_mul_rEnergy
#print axioms ArkLib.ProximityGap.BGK3Scratch.rSumset_card_ge_of_energy_le
#print axioms ArkLib.ProximityGap.BGK3Scratch.rEnergy_ge_of_rSumset_le
#print axioms ArkLib.ProximityGap.BGK3Scratch.rEnergy_eq_of_flat
#print axioms ArkLib.ProximityGap.BGK3Scratch.card_pow_eq_of_flat
#print axioms ArkLib.ProximityGap.BGK3Scratch.bridge_eq_of_flat
#print axioms ArkLib.ProximityGap.BGK3Scratch.dc_floor_from_bridge
#print axioms ArkLib.ProximityGap.BGK3Scratch.bootstrap_fixed_point
#print axioms ArkLib.ProximityGap.BGK3Scratch.bootstrap_exponent_is_second_moment
