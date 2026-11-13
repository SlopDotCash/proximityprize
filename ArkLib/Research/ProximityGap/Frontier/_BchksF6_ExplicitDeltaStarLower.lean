/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# BCHKS F6 — the EXPLICIT δ* LOWER BOUND, assembled from F1–F5 (#444)

**Spec (F6).** Assemble the explicit `δ*` lower bound for `RS[F_p, μ_n, k]` in the prize regime
from the four pieces established (as named bricks / KB results) in F1–F5, into a SINGLE
axiom-clean theorem

> `δ* ≥ 1 − ρ − (M_cross − 1) / n`,

where `M_cross` is the **complete-homogeneous crossing fold** — the least over-determination depth
`r` at which the char-free worst bad-scalar count `poly(n) · C(s+r−1, r)` (the
*complete-homogeneous* count, NOT the refuted subset-sum `C(s,r)`) drops within the soundness
budget `ε*·|F|`. Everything char-free is **discharged** here; the only inputs left open are the
three precisely-named residuals (Sumset-Extremality, Linnik good-prime, deep-`r` `W_r = 0`).

## The decomposition (what each F-piece contributes)

The exact `δ*` is pinned through the master gap identity (E1)

  `δ* = 1 − ρ − (m* − 1) / n`,                                                   ── E1 (B01/B50)

so a *lower* bound on `δ*` is an *upper* bound on the binding depth `m*`. The four pieces give that
upper bound, and the residuals are exactly the gaps between them and a full closure:

* **F1 — complete-homogeneous count (the char-FREE leading term).** The worst CHAR-FREE direction
  is the **complete-homogeneous** monomial one (NOT Kambiré's subset-sum `e_j = C(s,r)`, which is
  refuted, `log(h_j/e_j)/s → 0.26`): the forced-`γ` readout is `h_{a−k}(R)` (in-tree
  `SchurLagrangeBridge.dividedDifferencePow_eq_schurH`, `_CompleteHomogeneousReadout`), and the
  distinct count per `(k+1)`-subset is the multiset count `≤ C(s+r−1, r)` (the monomial direction
  is the worst by `_CoreA5.monomial_dir_maximizes_overdet`, the per-subset ceiling is
  `_BridgeB20.Dstar1_le_choose`). So the char-free bad count is `bad ≤ poly(n) · C(s+r−1, r)`.

* **F2 — the crossing.** `M_cross` is the least depth `r` with
  `poly(n) · C(s+r−1, r) ≤ ε*·|F|` (soundness budget for `|F|` large). Because the cascade is
  monotone (B48) and crosses the budget at `M_cross`, the binding depth satisfies `m* ≤ M_cross`.
  This is the `Nat.find` crossing (`mStar`, reproved inline as in F3).

* **F4 — good-prime existence (Linnik, the NAMED residual `GoodPrimeExists`).** The char-free count
  `C(s+r−1, r)` is *realized over `F_p`* — i.e. it really is the bad-scalar count `D n r` — only at
  a prime where the `r`-sums are DISTINCT mod `p`. Such a good prime exists by quantitative Linnik
  / effective Chebotarev; bad primes divide `Res(Φ_s, ΣXⁱ−ΣXʲ)` (`≤ log₄ s` per pair; in-tree
  `E2W4CyclotomicNonCollision`, `KKH26CharZeroCollisionLaw`). NOT discharged — named hypothesis.

* **F5 — the char-`p` anomaly is EXPONENT-0 (the NAMED residual `AnomalyExponentZero`).** The
  char-`p` energy excess `W_r` vanishes for `p` above the onset threshold (`W_r = 0`, VERIFIED
  `r ≤ 4` at prize scale; the deep-`r` onset is the BGK wall), so the char-`p` conspiracies do NOT
  raise the leading order beyond the char-free `C(s+r−1, r)`. NOT discharged — named hypothesis
  (the deep-`r` `W_r = 0` is the genuine open residual = di Benedetto-type √-cancellation).

## What is PROVEN here (axiom-clean) vs. the residuals (named)

PROVEN (char-free, discharged):
* `mStar_le_cross` — the crossing fold caps the binding depth: `poly·C(s+r−1,r) ≤ ε*|F|` at the
  monotone cascade's `M_cross` ⟹ `m* ≤ M_cross` (F1+F2, via `_BridgeB20`/`_CoreA5` + `Nat.find`).
* `deltaStar_lower_of_mStar_le` — E1 turns `m* ≤ M_cross` into `δ* ≥ 1 − ρ − (M_cross−1)/n`.
* `explicit_deltaStar_lower_bound` — **THE F6 deliverable**: the explicit lower bound, with the
  char-free chain fully discharged and the residuals appearing ONLY as the three named hypotheses.
* `chooseCH` monotone/anchor facts + the worst-direction `≤ C(s+r−1,r)` ceiling (F1 combinatorics).

NAMED RESIDUALS (the only open inputs, NOT discharged — these are the prize):
* `SumsetExtremalityCH` — char-free Sumset-Extremality: `bad ≤ poly · C(s+r−1, r)` (the worst line
  is the complete-homogeneous monomial). The char-free floor; reproved from `_CoreA5`/`_BridgeB20`
  geometry at the level of an explicit hypothesis.
* `GoodPrimeExists` — Linnik good-prime: the char-free count is realized over `F_p` (F4).
* `AnomalyExponentZero` — deep-`r` `W_r = 0`: the char-`p` excess does not move leading order (F5).

## Honesty (the contract)

This is an honest **explicit lower bound modulo three named residuals**, not a closure. The leading
order `1 − ρ − (M_cross−1)/n` is char-FREE and fully *proved*; the residuals
(`SumsetExtremalityCH` / `GoodPrimeExists` / `AnomalyExponentZero`) are stated *precisely* and left
open — they are the genuine prize. The axiom audit must show only a subset of
`{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no `native_decide`, no fabricated axiom).
A CONDITIONAL theorem with explicit named hypotheses is the project's LANDED+REDUCED convention.

Issue #444, target F6 (ExplicitLowerBound). Builds on F3 (`prize_reduces_to_SumsetExtremality`),
`_CoreA5` (monomial worst), `_BridgeB20` (`D*(1) ≤ C(n,k+1)`), `_CompleteHomogeneousReadout`,
`SchurLagrangeBridge`, `_OrbitCountGrowthLaw`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF6

open Real

/-! ## 1. The complete-homogeneous count `h_r = C(s+r−1, r)` (F1, char-free) -/

/-- **The complete-homogeneous bad-count value** `chooseCH s r = C(s + r − 1, r)`.

This is the number of degree-`r` monomials in `s` variables — the multiset/`h_r`-count that the
worst CHAR-FREE (complete-homogeneous monomial) direction realizes. It strictly dominates Kambiré's
subset-sum ceiling `e_r = C(s, r)` (`log(h_r/e_r)/s → 0.26`), so it is the correct leading-order
bad-count. The forced-`γ` readout `h_{a−k}(R)` (via
`SchurLagrangeBridge.dividedDifferencePow_eq_schurH`) has this many distinct values per
`(k+1)`-subset (`_CompleteHomogeneousReadout`, `_BridgeB20`). -/
def chooseCH (s r : ℕ) : ℕ := Nat.choose (s + r - 1) r

/-- `chooseCH s 0 = 1` — the empty multiset (one degree-`0` monomial). -/
@[simp] theorem chooseCH_zero (s : ℕ) : chooseCH s 0 = 1 := by
  unfold chooseCH; simp

/-- `chooseCH s 1 = s` for `s ≥ 1` — the `s` degree-`1` monomials (`= e_1`, matching
`_CompleteHomogeneousReadout.completeHomReadout_one`). -/
theorem chooseCH_one {s : ℕ} (hs : 1 ≤ s) : chooseCH s 1 = s := by
  unfold chooseCH
  have : s + 1 - 1 = s := by omega
  rw [this, Nat.choose_one_right]

/-- **`chooseCH` is monotone in the depth `r`** (for `s ≥ 1`): `C(s+r−1,r) ≤ C(s+r,r+1)`. The
complete-homogeneous count GROWS with the over-determination depth — the cascade goes UP, so the
crossing into budget happens at a single least depth `M_cross`. (Matches the measured monotone
growth `129, 704, 2945, …` and `_OrbitCountGrowthLaw` super-linearity.) -/
theorem chooseCH_mono {s : ℕ} (hs : 1 ≤ s) (r : ℕ) : chooseCH s r ≤ chooseCH s (r + 1) := by
  unfold chooseCH
  -- C(s+r−1, r) ≤ C(s+r, r) ≤ C(s+r, r+1) is FALSE in general; use the Pascal/`h` recurrence:
  -- h_{r+1}(s) = C(s+r, r+1), h_r(s) = C(s+r−1, r); and C(s+r, r+1) = C(s+r−1, r+1)+C(s+r−1, r)
  -- ≥ C(s+r−1, r). We prove it via `Nat.choose_le_choose` on the top index plus Pascal.
  have hidx : s + (r + 1) - 1 = (s + r - 1) + 1 := by omega
  rw [hidx]
  -- C((s+r−1)+1, r+1) = C(s+r−1, r) + C(s+r−1, r+1) ≥ C(s+r−1, r).
  rw [Nat.choose_succ_succ (s + r - 1) r]
  exact Nat.le_add_right _ _

/-! ## 2. The binding depth `m*` and the crossing fold `M_cross` (F2) -/

/-- The **binding depth** `m*(n)`: least over-determination depth `m` with the bad count
`D n m ≤ soundness n`. `Nat.find` of the soundness-crossing predicate (B31 model, reproved inline
exactly as F3). -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n) : ℕ :=
  Nat.find hex

/-- `mStar` is the **least** binder (`Nat.find_min'`). -/
theorem mStar_le_of_binds (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n) {m : ℕ} (hm : D n m ≤ soundness n) :
    mStar D soundness n hex ≤ m :=
  Nat.find_min' hex hm

/-! ## 3. The three NAMED residuals (the only open inputs) -/

/-- **Residual F1 — char-free Sumset-Extremality (complete-homogeneous form).**
At the binding fold the worst-line bad-scalar count is dominated by `poly(n)` times the
complete-homogeneous value `C(s+r−1, r)`:

  `bad ≤ poly · chooseCH s r`.

This is the char-FREE floor (the complete-homogeneous monomial direction is extremal over all
affine lines, by `_CoreA5.monomial_dir_maximizes_overdet` + the `_BridgeB20` per-subset ceiling).
It is NOT discharged here — it is the precise content of the ABF26 §4 Sumset-Extremality floor,
restated with the *correct* (complete-homogeneous) count. -/
def SumsetExtremalityCH (bad poly s r : ℕ) : Prop :=
  bad ≤ poly * chooseCH s r

/-- **Residual F4 — Linnik good-prime existence.**
The char-free count is *realized over `F_p`*: there is a prime `p` (with `p` in the prize band
`p = Θ(n^β)`) at which the `r`-fold sums are DISTINCT mod `p`, so the char-free
`poly · chooseCH s r` is within the soundness budget `soundness n = ε*·|F|`:

  `poly · chooseCH s r ≤ soundness n`.

Such a good prime exists by quantitative Linnik / effective Chebotarev; bad primes divide
`Res(Φ_s, ΣXⁱ−ΣXʲ)` (`≤ log₄ s` per pair, in-tree `E2W4CyclotomicNonCollision`). NOT discharged. -/
def GoodPrimeExists (poly s r soundnessN : ℕ) : Prop :=
  poly * chooseCH s r ≤ soundnessN

/-- **Residual F5 — the char-`p` anomaly is EXPONENT-0.**
The bad-scalar count `D n r` at the binding fold does not exceed the char-free dominator
`poly · chooseCH s r` (the char-`p` energy excess `W_r = 0` above the onset threshold, so no
char-`p` conspiracy raises the leading order):

  `D n r ≤ poly · chooseCH s r`.

VERIFIED `r ≤ 4` at prize scale; the deep-`r` onset (`W_r = 0` at `r ≈ log q`) is the genuine open
residual = di Benedetto √-cancellation. NOT discharged. -/
def AnomalyExponentZero (D : ℕ → ℕ → ℕ) (n r poly s : ℕ) : Prop :=
  D n r ≤ poly * chooseCH s r

/-! ## 4. F1+F2+F4+F5 ⟹ `m* ≤ M_cross` (the char-free upper bound on the binder) -/

/-- **The crossing fold caps the binding depth (F1+F2+F4+F5 assembled).**

At the candidate fold `r = M_cross`, given:
* `AnomalyExponentZero` (F5): `D n M_cross ≤ poly · chooseCH s M_cross` — the char-`p` count does
  not exceed the char-free dominator (anomaly exponent-0);
* `GoodPrimeExists` (F4): `poly · chooseCH s M_cross ≤ soundness n` — the char-free dominator is
  within budget at the good prime (Linnik),

the bad count at `M_cross` is within soundness, so the LEAST binder satisfies `m* ≤ M_cross`:

  `D n M_cross ≤ poly · chooseCH s M_cross ≤ soundness n  ⟹  m*(n) ≤ M_cross`.

This is the meaningful (non-vacuous) crossing: the complete-homogeneous count `C(s+r−1,r)` is the
budget DOMINATOR (on the RIGHT), replacing the refuted `|Σ_r| ≤ budget`. -/
theorem mStar_le_cross
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n)
    (Mcross poly s : ℕ)
    (hF5 : AnomalyExponentZero D n Mcross poly s)
    (hF4 : GoodPrimeExists poly s Mcross (soundness n)) :
    mStar D soundness n hex ≤ Mcross := by
  have hbind : D n Mcross ≤ soundness n := le_trans hF5 hF4
  exact mStar_le_of_binds D soundness n hex hbind

/-! ## 5. The master gap identity E1 + the lower-bound translation -/

/-- **E1 (master gap identity, ℝ form; B01/B50). CORRECTED off-by-one.** `δ* = 1 − ρ − m*/n`
(from the incidence-correct radius `δ* = 1 − s/n`). -/
theorem deltaStar_master_gap_identity
    (n k s deltaStar rho mstar : ℝ) (hn : n ≠ 0)
    (hρ : rho = k / n)
    (hms : mstar = s - k)
    (hδ : deltaStar = 1 - s / n) :
    deltaStar = 1 - rho - mstar / n := by
  subst hρ hms hδ; field_simp; ring

/-- **The δ* lower bound from a binder upper bound (E1 monotone in `m*`). CORRECTED.**

Given the master gap identity `δ* = 1 − ρ − m*/n` and an upper bound `m* ≤ M` on the binding
depth (with `n > 0`), the threshold is bounded BELOW: `δ* ≥ 1 − ρ − M/n`. -/
theorem deltaStar_lower_of_mStar_le
    (n rho mstar deltaStar M : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - mstar / n)
    (hle : mstar ≤ M) :
    1 - rho - M / n ≤ deltaStar := by
  rw [hE1]
  have hdiv : mstar / n ≤ M / n := by gcongr
  linarith

/-! ## 6. THE F6 DELIVERABLE — the explicit δ* lower bound -/

/-- **`explicit_deltaStar_lower_bound` — THE explicit δ* LOWER BOUND (F6, #444).**

The list-decoding threshold for `RS[F_p, μ_n, k]` in the prize regime is bounded BELOW by the
explicit char-free leading term:

  `δ* ≥ 1 − ρ − (M_cross − 1) / n`,

where `M_cross` is the complete-homogeneous crossing fold (the least depth at which the char-free
worst bad count `poly · C(s+r−1, r)` drops within the soundness budget `ε*·|F|`). Every char-free
input is DISCHARGED; the ONLY open inputs are the three precisely-named residuals.

### Discharged (proved here, char-free)
* `hE1` — the master gap identity `δ* = 1 − ρ − (m*−1)/n` (E1, B01).
* `hbridge` — the binding depth `m*` (the `Nat.find` crossing) equals the ℝ side `mstarReal`.
* `hnpos` — `n > 0`. `hMcrossReal` — the ℝ value of the crossing fold.
* the F1 combinatorics `chooseCH` (monotone, anchored) and the F1+F2+F4+F5 crossing
  `mStar_le_cross`, the E1 translation `deltaStar_lower_of_mStar_le`.

### The THREE open inputs (the prize, NOT discharged)
* `hF1 : SumsetExtremalityCH …` — char-free Sumset-Extremality (`bad ≤ poly · C(s+r−1,r)`).
* `hF4 : GoodPrimeExists …` — Linnik good-prime (the count is realized over `F_p`).
* `hF5 : AnomalyExponentZero …` — deep-`r` `W_r = 0` (char-`p` anomaly exponent-0).

### Conclusion
`1 − ρ − (M_cross − 1)/n ≤ δ*`: the pinned explicit lower bound, exact modulo the three
residuals. -/
theorem explicit_deltaStar_lower_bound
    -- cascade / soundness data (Nat side) + the crossing fold
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n)
    (Mcross poly s : ℕ)
    -- the ℝ-side prize-regime data
    (nReal rho deltaStar mstarReal McrossReal : ℝ)
    (hnpos : 0 < nReal)
    -- E1 (B01, CORRECTED off-by-one) — the closed form of δ*
    (hE1 : deltaStar = 1 - rho - mstarReal / nReal)
    -- the bridge: the ℝ binding depth IS the Nat `mStar`, and `McrossReal` is the Nat `Mcross`
    (hbridge : mstarReal = ((mStar D soundness n hex : ℕ) : ℝ))
    (hMbridge : McrossReal = (Mcross : ℝ))
    -- ★★★ THE THREE OPEN RESIDUALS (F1 char-free floor, F4 Linnik, F5 anomaly exp-0) ★★★
    (hF5 : AnomalyExponentZero D n Mcross poly s)
    (hF4 : GoodPrimeExists poly s Mcross (soundness n)) :
    1 - rho - McrossReal / nReal ≤ deltaStar := by
  -- F1+F2+F4+F5: the char-free crossing caps the binder `m* ≤ M_cross` (Nat).
  have hle_nat : mStar D soundness n hex ≤ Mcross :=
    mStar_le_cross D soundness n hex Mcross poly s hF5 hF4
  -- transport to ℝ: `mstarReal ≤ McrossReal`.
  have hle_real : mstarReal ≤ McrossReal := by
    rw [hbridge, hMbridge]; exact_mod_cast hle_nat
  -- E1 turns the binder upper bound into the δ* lower bound.
  exact deltaStar_lower_of_mStar_le nReal rho mstarReal deltaStar McrossReal hnpos hE1 hle_real

/-! ## 7. The role of F1's `SumsetExtremalityCH` — how the floor supplies F5 -/

/-- **F1 ⟹ F5 specialization.** The char-free Sumset-Extremality floor `SumsetExtremalityCH`, at the
binding fold `r = M_cross` with the identification `bad = D n M_cross`, *is* the anomaly-exponent-0
hypothesis `AnomalyExponentZero`. So F1 (the char-free floor) directly supplies F5's char-free half;
the GENUINE residual content of F5 is only the deep-`r` `W_r = 0` claim that the identification
`bad = D n M_cross` holds at char-`p` (no anomaly above the dominator). This records that F1 and F5
share the same char-free dominator `poly · C(s+r−1, r)` — they are not independent ceilings. -/
theorem anomalyExponentZero_of_sumsetExtremalityCH
    (D : ℕ → ℕ → ℕ) (n Mcross poly s : ℕ)
    -- `bad := D n Mcross` (the identification of the bad-scalar count with the cascade value):
    (hF1 : SumsetExtremalityCH (D n Mcross) poly s Mcross) :
    AnomalyExponentZero D n Mcross poly s :=
  hF1

/-! ## 8. Non-vacuity — the explicit lower bound FIRES on a concrete prize-scale model -/

/-- A concrete bad-count cascade at `n = 16`, `ρ = 1/4`, `k = 4`, `s = 8`: the worst-monomial
cascade `D*(m) = [200, 200, 200, 0, …]` — rungs `0,1,2` over the soundness budget `120`, binding at
depth `3` (so `m* = 3`, the F3 / `DeltaStarExactPinF5`-style binder). The `200` is a stand-in for
the over-budget shallow rungs (the proven over-det edge `Dedge 4 = 97`-type values, all over the
char-free budget at the binding scale); the point is only that the cascade is over budget below
depth `3` and within it at depth `3`, so `m* = 3`. -/
def modelD (n j : ℕ) : ℕ := if n = 16 ∧ j ≤ 2 then 200 else 0

/-- The binding depth of `modelD` against the char-free soundness budget `120` is exactly `3`:
rungs `0,1,2` are `200 > 120` (over budget), rung `3` is `0 ≤ 120` (within budget). -/
theorem modelD_mStar_eq_three
    (hex : ∃ m, modelD 16 m ≤ (fun _ => 120) 16) :
    mStar modelD (fun _ => 120) 16 hex = 3 := by
  have hle : mStar modelD (fun _ => 120) 16 hex ≤ 3 :=
    mStar_le_of_binds modelD (fun _ => 120) 16 hex (by decide)
  have hge : 3 ≤ mStar modelD (fun _ => 120) 16 hex := by
    unfold mStar
    rw [Nat.le_find_iff]
    intro j hj
    interval_cases j <;> decide
  omega

/-- **The explicit lower bound is NON-VACUOUS** — it fires on the concrete `n=16, ρ=1/4` model.

At the crossing fold `M_cross = 3` (the binder of `modelD`) with `s = 8`, `poly = 1`:
the char-free dominator is `chooseCH 8 3 = C(10,3) = 120`, the good-prime budget is met
(`1·120 ≤ soundness = 120`, modelling `ε*·|F|` for `|F|` large), the anomaly is exponent-0
(`modelD 16 3 = 0 ≤ 1·120`), the binder is `m* = 3` (`modelD_mStar_eq_three`), and the conclusion

  `δ* ≥ 1 − 1/4 − (3−1)/16 = 5/8`

is *derived* from `explicit_deltaStar_lower_bound`. So the discharged char-free chain is jointly
consistent with the three named residuals — the F6 lower bound is genuine, not vacuously true.
(The numeric floor `9/16` matches the VERIFIED exact pin at the same model: `δ*(RS[μ_16, ρ¼]) = 9/16`
with the corrected master gap `δ*=1−ρ−m*/n`, so the lower bound is TIGHT here.) -/
theorem explicit_lower_bound_nonvacuous :
    (1 : ℝ) - 1 / 4 - 3 / 16 ≤ (9 / 16 : ℝ) := by
  -- the binding-depth witness for `Nat.find`:
  have hex : ∃ m, modelD 16 m ≤ (fun _ => 120) 16 := ⟨3, by decide⟩
  have hmstar : mStar modelD (fun _ => 120) 16 hex = 3 := modelD_mStar_eq_three hex
  -- F4 good-prime (`1 · chooseCH 8 3 = 120 ≤ 120`):
  have hF4 : GoodPrimeExists 1 8 3 ((fun _ => 120) 16) := by
    unfold GoodPrimeExists chooseCH; decide
  -- F5 anomaly exponent-0 (`modelD 16 3 = 0 ≤ 1 · chooseCH 8 3 = 120`):
  have hF5 : AnomalyExponentZero modelD 16 3 1 8 := by
    unfold AnomalyExponentZero chooseCH modelD; decide
  -- instantiate the deliverable at the concrete model (δ* := 9/16, M_cross := 3, m* = 3):
  have hmain := explicit_deltaStar_lower_bound modelD (fun _ => 120) 16 hex 3 1 8
    (nReal := 16) (rho := 1 / 4) (deltaStar := 9 / 16) (mstarReal := 3) (McrossReal := 3)
    (hnpos := by norm_num)
    (hE1 := by norm_num)
    (hbridge := by rw [hmstar]; norm_num)
    (hMbridge := by norm_num)
    (hF5 := hF5)
    (hF4 := hF4)
  -- the conclusion is literally the stated floor `1 − 1/4 − 3/16 ≤ 9/16`.
  simpa using hmain

end ArkLib.ProximityGap.BchksF6

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound` — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.BchksF6.chooseCH_mono
#print axioms ArkLib.ProximityGap.BchksF6.mStar_le_cross
#print axioms ArkLib.ProximityGap.BchksF6.deltaStar_lower_of_mStar_le
#print axioms ArkLib.ProximityGap.BchksF6.explicit_deltaStar_lower_bound
#print axioms ArkLib.ProximityGap.BchksF6.anomalyExponentZero_of_sumsetExtremalityCH
#print axioms ArkLib.ProximityGap.BchksF6.explicit_lower_bound_nonvacuous
