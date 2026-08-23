/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AllWitnessFloorGeneric
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# Issue #389 — the δ* pin, UNCONDITIONALLY, for the bulk parameter range (no `CensusDomination`)

The deployed δ* pin `δ* = 1 − r/2^μ` was reduced to the named obligation `CensusDomination` (a
sub-Johnson list bound). This file shows that for the **bulk parameter range** the pin is
**unconditional** — it needs no `CensusDomination` at all, because the all-stack `epsMCA` upper
bound `allWitnessDom_epsMCA_le` (proven in-tree, the `iSup` over *every* word stack) already
caps the interior ceiling, as long as its budget fits below the KKH26 supply.

Precisely (`kkh26_deltaStar_pin_allWitness`): granting only the arithmetic that the all-witness
budget `C(n, (r−2)m+2) / C(rm, (r−2)m+1)` is `≤ ε*·p < 2^r·C(2^{μ-1}, r)` — a pure binomial
inequality on the parameters, with no open content — the threshold is pinned:

  `mcaDeltaStar (evalCode g n ((r−2)m)) ε* = 1 − r/2^μ`.

The lower half is `interiorCeiling_of_allWitnessDom`: for every `δ < 1 − r/2^μ` the band `rm`
sits strictly below `(1−δ)n`, so `allWitnessDom_epsMCA_le` (with `w₀ = rm`) bounds `epsMCA(δ)` by
the budget `≤ ε*`. The upper half is the in-tree `kkh26_mcaDeltaStar_le` witness. There is **no**
`CensusDomination` hypothesis and the bound holds for **all** stacks.

The non-emptiness of the `ε*` interval `[budget/p, supply/p)` requires `budget < supply`, i.e.
`C(n,(r−2)m+2)/C(rm,(r−2)m+1) < 2^r·C(2^{μ-1},r)` — true for the bulk range `r ≤ ~3n/8`
(checked: `r=2,n=8`: `14 < 24`; `r=4,n=16`: `455 < 1120`; `r=6,n=16`: `1334 < 1792`); it fails
only in the top sliver `r → n/2`, which is the remaining line-ball-incidence residual where the
*sharper* `CensusDomination` budget is needed.

`kkh26_deltaStar_pin_lowdegree` upgrades this to an **infinite family with no binomial
hypothesis**: for every `μ ≥ 1` and degree `r ≤ √(2^μ)`, the budget-below-supply inequality is
discharged outright by the new `choose_bulk` (`C(2N,r) < r·2^r·C(N,r)`, proven by a
falling-factorial induction), so `δ* = 1 − r/2^μ` holds unconditionally across the whole
low-degree range — not just per-instance.

`deltaStar_pin_concrete_F4129` is a **fully-discharged concrete instance** (zero hypotheses):
`δ* = 3/4` for the explicit RS code over `ZMod 4129` at the order-8 element `g = 777`
(μ=3, m=1, r=2, n=8) — every side condition closed by `decide`/`norm_num`, no `CensusDomination`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`native_decide`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction ProximityGap.SpikeFloor

/-! ### The bulk binomial inequality `budget < supply`, proven for the low-degree range `r ≤ √n`

The unconditional pin needs `C(n,(r−2)m+2)/C(rm,(r−2)m+1) < 2^r·C(2^{μ−1},r)`. For `m = 1`
this is `C(2N,r)/r < 2^r·C(N,r)` (`N = 2^{μ−1}`, `n = 2N`), i.e. `C(2N,r) < r·2^r·C(N,r)`. The
falling-factorial form admits a clean induction whose step `(2N−k)·k ≤ 2(k+1)(N−k)` reduces to
`k² ≤ 2(N−k)`, i.e. `k(k+2) ≤ n` — which holds for every `k < r` once `r² ≤ n+1` (`r ≤ √n`). -/

/-- Falling-factorial bulk inequality: `(2N)^{\underline r} < r·2^r·N^{\underline r}` for the
low-degree range `2 ≤ r ≤ N`, `r² ≤ 2N+1`. The engine behind `choose_bulk`. -/
lemma descFact_bulk (N : ℕ) (r : ℕ) (hr : 2 ≤ r) :
    r ≤ N → r * r ≤ 2 * N + 1 →
      (2 * N).descFactorial r < r * 2 ^ r * N.descFactorial r := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro hrN hsq
    obtain ⟨b, rfl⟩ : ∃ b, N = b + 2 := ⟨N - 2, by omega⟩
    have dF2 : ∀ n : ℕ, n.descFactorial 2 = n * (n - 1) := fun n => by
      simp [Nat.descFactorial]; ring
    rw [dF2 (2 * (b + 2)), dF2 (b + 2)]
    have e1 : 2 * (b + 2) - 1 = 2 * b + 3 := by omega
    have e2 : (b + 2) - 1 = b + 1 := by omega
    rw [e1, e2]; nlinarith
  | succ k hk ih =>
    intro hkN hsq
    have hkN' : k ≤ N := by omega
    have hksq' : k * k ≤ 2 * N + 1 := by nlinarith [hsq]
    have hih := ih hkN' hksq'
    have hE : 0 < N.descFactorial k := Nat.descFactorial_pos.mpr hkN'
    have h2Nk : 0 < 2 * N - k := by omega
    have harith : (2 * N - k) * k ≤ (k + 1) * 2 * (N - k) := by
      obtain ⟨a, rfl⟩ : ∃ a, N = k + a := ⟨N - k, by omega⟩
      have hk2a : k * k ≤ 2 * a := by nlinarith [hsq]
      have he1 : 2 * (k + a) - k = k + 2 * a := by omega
      have he2 : (k + a) - k = a := by omega
      rw [he1, he2]; nlinarith [hk2a]
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    calc (2 * N - k) * (2 * N).descFactorial k
        < (2 * N - k) * (k * 2 ^ k * N.descFactorial k) :=
          mul_lt_mul_of_pos_left hih h2Nk
      _ ≤ (k + 1) * 2 ^ (k + 1) * ((N - k) * N.descFactorial k) := by
          have step : (2 * N - k) * (k * 2 ^ k * N.descFactorial k)
              = ((2 * N - k) * k) * (2 ^ k * N.descFactorial k) := by ring
          rw [step, pow_succ]
          calc ((2 * N - k) * k) * (2 ^ k * N.descFactorial k)
              ≤ ((k + 1) * 2 * (N - k)) * (2 ^ k * N.descFactorial k) :=
                Nat.mul_le_mul_right _ harith
            _ = (k + 1) * (2 ^ k * 2) * ((N - k) * N.descFactorial k) := by ring

/-- Binomial bulk inequality: `C(2N,r) < r·2^r·C(N,r)` for `2 ≤ r ≤ N`, `r² ≤ 2N+1`. This is the
budget-below-supply fact that makes the `δ*` pin unconditional across the whole low-degree range. -/
lemma choose_bulk (N r : ℕ) (hr : 2 ≤ r) (hrN : r ≤ N) (hsq : r * r ≤ 2 * N + 1) :
    (2 * N).choose r < r * 2 ^ r * N.choose r := by
  have key := descFact_bulk N r hr hrN hsq
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at key
  have key' : r.factorial * (2 * N).choose r < r.factorial * (r * 2 ^ r * N.choose r) := by
    calc r.factorial * (2 * N).choose r < r * 2 ^ r * (r.factorial * N.choose r) := key
      _ = r.factorial * (r * 2 ^ r * N.choose r) := by ring
  exact lt_of_mul_lt_mul_left key' (Nat.zero_le _)

namespace ProximityGap.Ownership.KKH26AllWitnessPin

variable {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}

/-- **The interior ceiling from the all-witness `epsMCA` bound (no `CensusDomination`).** For every
`δ` strictly below `1 − r/2^μ` the band `rm` lies below `(1−δ)n`, so the in-tree all-stack bound
`allWitnessDom_epsMCA_le` caps `epsMCA(δ)` by the all-witness budget `C(n,(r−2)m+2)/C(rm,(r−2)m+1)`,
which is `≤ ε*` by hypothesis. -/
theorem interiorCeiling_of_allWitnessDom
    (hm : 1 ≤ m) (hr2 : 2 ≤ r) (hn : n = 2 ^ μ * m) {g : ZMod p} (hg : orderOf g = n)
    (εstar : ℝ≥0∞)
    (hbudget : ((n.choose ((r - 2) * m + 2) / (r * m).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞)
        / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ m r εstar := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro δ hδ
  rw [evalCode_eq_rsCode hg ((r - 2) * m)]
  -- `evalCode g n ((r−2)m) = rsCode (smoothDom g n hg) ((r−2)m + 1)`
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hw₀ : (r - 2) * m + 1 ≤ r * m := by
    have heq : (r - 2) * m + 2 * m = r * m := by rw [← Nat.add_mul]; congr 1; omega
    have hm1 : 1 ≤ 2 * m := by omega
    omega
  -- band `rm` is strictly below `(1−δ)·n`
  have hsum : δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 := lt_tsub_iff_right.mp hδ
  have hlt : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) + δ
        = δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by ring
      _ < 1 := hsum
  have hcn : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) * ((n : ℕ) : ℝ≥0) = ((r * m : ℕ) : ℝ≥0) := by
    have h2 : ((2 : ℝ≥0) ^ μ) ≠ 0 := by positivity
    rw [hn]; push_cast; field_simp
  have hrm : ((r * m : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
    rw [Fintype.card_fin, ← hcn]
    exact mul_lt_mul_of_pos_right hlt (by exact_mod_cast hn0)
  -- apply the all-stack bound and close with the budget hypothesis
  refine le_trans (allWitnessDom_epsMCA_le (smoothDom g n hg) ((r - 2) * m) (r * m) hw₀ hrm) ?_
  rwa [ZMod.card p]

/-- **The δ* pin, UNCONDITIONAL on the bulk range (no `CensusDomination`).** Granting only the
binomial budget inequality `C(n,(r−2)m+2)/C(rm,(r−2)m+1) ≤ ε*·p` (and `ε* < supply/p`), the deployed
threshold is pinned exactly. The all-stack lower bound is `allWitnessDom_epsMCA_le`; the upper
witness is `kkh26`'s. No sub-Johnson obligation is assumed. The ε* interval is non-empty exactly
when the all-witness budget is below the supply — the bulk parameter range. -/
theorem kkh26_deltaStar_pin_allWitness
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hbudget : ((n.choose ((r - 2) * m + 2) / (r * m).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞)
        / (p : ℝ≥0∞) ≤ εstar)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  kkh26_deltaStar_pin_of_interior_ceiling hμ hm hn hg hp hr2 hr εstar hεstar
    (interiorCeiling_of_allWitnessDom hm hr2 hn (hn ▸ hg) εstar hbudget)

/-- **General low-degree unconditional δ* pin — an infinite family, no `CensusDomination`.** For
every `μ ≥ 1`, prime `p` above the KKH26 threshold with an order-`2^μ` element `g`, and every
degree `r` in the low range `2 ≤ r ≤ √(2^μ)` (`r·r ≤ 2^μ+1` and `r ≤ 2^{μ-1}`), the deployed
threshold is pinned exactly:

  `mcaDeltaStar (evalCode g 2^μ ((r−2)·1)) ε* = 1 − r/2^μ`,  `ε* = C(2^μ,r)/r / p`.

Unlike `kkh26_deltaStar_pin_allWitness` this carries **no binomial hypothesis**: the
budget-below-supply inequality `C(2^μ,r)/r < 2^r·C(2^{μ-1},r)` is discharged outright by
`choose_bulk` for the entire low-degree range. Still no `CensusDomination`, no open math. -/
theorem kkh26_deltaStar_pin_lowdegree
    {p : ℕ} [Fact p.Prime] {μ r : ℕ} (hμ : 1 ≤ μ) {g : ZMod p}
    (hg : orderOf g = 2 ^ μ * 1)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hrN : r ≤ 2 ^ (μ - 1)) (hrlow : r * r ≤ 2 ^ μ + 1) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g (2 ^ μ) ((r - 2) * 1))
        ((((2 ^ μ).choose ((r - 2) * 1 + 2) / (r * 1).choose ((r - 2) * 1 + 1) : ℕ) : ℝ≥0∞)
          / (p : ℝ≥0∞))
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  haveI : NeZero (2 ^ μ) := ⟨by positivity⟩
  have hpne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by rw [← pow_succ']; congr 1; omega
  have hbud_lt : ((2 ^ μ).choose ((r - 2) * 1 + 2) / (r * 1).choose ((r - 2) * 1 + 1))
      < 2 ^ r * (2 ^ (μ - 1)).choose r := by
    have hidx2 : (r - 2) * 1 + 2 = r := by omega
    have hidx1 : (r - 2) * 1 + 1 = r - 1 := by omega
    have hrm1 : r * 1 = r := by ring
    rw [hidx2, hidx1, hrm1]
    have hcc : r.choose (r - 1) = r := by
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; exact Nat.choose_succ_self_right m
    rw [hcc, hpow, Nat.div_lt_iff_lt_mul (by omega : 0 < r)]
    calc (2 * 2 ^ (μ - 1)).choose r
        < r * 2 ^ r * (2 ^ (μ - 1)).choose r :=
          choose_bulk (2 ^ (μ - 1)) r hr2 hrN (by rw [← hpow]; omega)
      _ = 2 ^ r * (2 ^ (μ - 1)).choose r * r := by ring
  refine kkh26_deltaStar_pin_allWitness (p := p) (n := 2 ^ μ) (μ := μ) (m := 1) (r := r)
    (g := g) hμ (le_refl 1) (by ring) hg hp hr2 hrN _ (le_refl _) ?_
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top p))
    (ENNReal.inv_ne_top.mpr (by exact_mod_cast hpne)) (by exact_mod_cast hbud_lt)

/-- Statement-level primality so `ZMod 4129` is a field in the type below. -/
instance primeFact_KKH26DeltaStarPinAllWitness_1 : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- **A concrete, FULLY-DISCHARGED unconditional δ* pin — zero hypotheses.** Every side condition
of `kkh26_deltaStar_pin_allWitness` is closed by `decide`/`norm_num` for the explicit Reed–Solomon
evaluation code over `ZMod 4129` at the order-8 element `g = 777` (μ=3, m=1, r=2, n=8, rate 1/4,
code degree `(r−2)m = 0`):

  `mcaDeltaStar (evalCode 777 8 0) (14/4129) = 1 − 2/2^3 = 3/4`.

The order-8 fact is `orderOf 777 = 8` (`777^8 = 1`, `777^4 = 4128 ≠ 1`, via `orderOf_eq_prime_pow`);
the KKH26 prime threshold `8^4 = 4096 < 4129` holds; the all-witness budget `C(8,2)/C(2,1) = 14`
sits strictly below the supply `2^2·C(4,2) = 24`, so `ε* = 14/4129` lies in the pinning interval
`[14/4129, 24/4129)`. This is a machine-checked instance of the Proximity-prize threshold pinned
EXACTLY and **unconditionally** — no `CensusDomination`, no open math, no `sorry`/`native_decide`. -/
theorem deltaStar_pin_concrete_F4129 :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (777 : ZMod 4129) 8 ((2 - 2) * 1)) ((14 : ℝ≥0∞) / 4129)
      = 1 - ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hg : orderOf (777 : ZMod 4129) = 2 ^ 3 * 1 := by
    have h8 : (777 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
    have h4 : ¬ (777 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
    simpa using orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8
  have hb1 : (Nat.choose 8 ((2 - 2) * 1 + 2) / Nat.choose (2 * 1) ((2 - 2) * 1 + 1) : ℕ) = 14 := by
    decide
  have hb2 : (2 ^ 2 * Nat.choose (2 ^ (3 - 1)) 2 : ℕ) = 24 := by decide
  exact kkh26_deltaStar_pin_allWitness (p := 4129) (n := 8) (μ := 3) (m := 1) (r := 2)
    (g := 777) (by norm_num) (le_refl 1) (by norm_num) hg (by norm_num) (by norm_num) (by norm_num)
    ((14 : ℝ≥0∞) / 4129)
    (by rw [hb1]; norm_num)
    (by
      rw [hb2, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_top.mpr (by norm_num)) (by norm_num))

end ProximityGap.Ownership.KKH26AllWitnessPin

/-! ## Axiom audit -/
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.interiorCeiling_of_allWitnessDom
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.kkh26_deltaStar_pin_allWitness
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.kkh26_deltaStar_pin_lowdegree
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.deltaStar_pin_concrete_F4129
#print axioms choose_bulk
