/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DeepBandOrbitCountDescent

/-!
# Off-BGK sub-lead (A): `deg(#bad_r) < r` — the GROWING-SLACK mechanism, settled at the shallow
rungs (#444)

## What sub-lead (A) is

The genuine off-BGK frontier (per the open-directions census §1.4) is the GROWTH LAW of the
distinct-γ UNION count `U(n)` at the δ*-binding far line, isolated in-tree as
`_SpecF8_DistinctGammaUnionFloor.DistinctGammaUnionGrowthLaw`.  One of the two PROMISING unrefuted
structural sub-leads (c269 item 6, c274) is the **growing-slack mechanism**:

> **(A)** if the count of forced bad-scalars at fold `r` is a polynomial of degree `< r` in `n`,
> the budget crossing gives a BOUNDED `m*` (prize-side).

This file ATTACKS (A) at the only rungs where the bad-scalar count is a PROVEN closed form in-tree
— the shallow deep-band rungs `r = 3, 4` (`DeepBandR3Bound` / `DeepBandR4Bound` /
`DeepBandOrbitCountDescent`, all axiom-clean) — and settles its precise truth.

## The exact measurement (probe `probe_deg_badr_growing_slack.py`, EXACT integer)

Writing `g = n/4`, the PROVEN in-tree closed forms are (all degree in `n` = degree in `g`, since
`n = 4g` is a linear reparam):

| object | closed form (in `g = n/4`) | degree in `n` |
|---|---|---|
| `#bad₃(n)` = `deepBandBadCount g`   | `2g²(g−1)+1 = 2g³−2g²+1` | **3 = r** |
| `#bad₄(n)` = `deepBandBadCount4 g`  | `g⁴−2g³+4g+1`           | **4 = r** |
| `O₃(n)`    = `orbitCount3 g`         | `C(g,2) = g(g−1)/2`     | **2 = r−1** |
| `O₄(n)`    = `orbitCount4 g`         | `2(g/2)²(g/2−1)+1`      | **3 = r−1** |

with the PROVEN orbit-size factorization `#bad_r = n · O_r + 1`
(`deepBandBadCount_eq_n_mul_orbitCount3`, `deepBandBadCount4_eq_n_mul_orbitCount4`).

## The VERDICT (honest, two-sided)

* **The literal sub-lead (A) is REFUTED for the RAW count**: `deg(#bad_r) = r` EXACTLY at `r=3,4`
  (`degBad_ge` lower + `degBad_le` upper sandwich pin it to exactly `r`), NOT `< r`.
* **Sub-lead (A) is CONFIRMED for the ORBIT count**: `deg(O_r) = r−1 < r` at `r=3,4`
  (`degOrbit_le` upper + `degOrbit_ge` lower).  The degree DROP is **exactly one**, and it is
  EXACTLY the orbit-size-`n` division — i.e. the rotation/Galois equivariance
  `h_r(ζR)=ζ^r h_r(R)` (`_SpecS1`/`_SpecS3`) collapsing the raw `#bad` count by the orbit-size
  factor `n` (the free rotation action, `Frontier.CliqueOrbitFreeness`).

So the growing-slack mechanism is REAL but lives on the **orbit count** `O_r`, not the raw
`#bad_r`.  This is the precise, PROVEN, shallow-rung instance of (A): the per-fold *orbit* count
grows one polynomial degree SLOWER than the raw bad count, and that one-degree gap is the
equivariance slack.

## Honest scope (NOT a δ* pin)

This feeds `DistinctGammaUnionGrowthLaw` (the off-BGK, p-INDEPENDENT frontier), it is **NOT** a δ*
pin and does **NOT** close the prize.  Two genuine limits, stated plainly:

1. **Shallow rungs only.** The degree facts are EXACT and PROVEN only at `r = 3, 4` (the in-tree
   closed forms).  `DeepBandR4Bound` records that the order-2 parity descent that pins these forms
   **stops at `r = 4`** (at `r = 5` the maximizing line flips to a full-order line invisible to the
   order-2 character), so `deg(O_r) = r−1` is NOT certified for `r ≥ 5` here.
2. **The deg-drop ≠ the budget crossing.** Even granting `deg(O_r) = r−1 < r` for ALL `r`, the
   budget crossing `m* = O(log n)` needs the DEEP-rung (`r ≈ log n`) decay of `O_r` to `≤ d`,
   which is the open growth law (`_AngleC_PlateauBenignOrbitFloor.FastPhaseLogDecay` /
   `DistinctGammaUnionGrowthLaw`).  A polynomial degree-`r−1` count at fold `r` does NOT by itself
   give a bounded `m*` — the degree-vs-budget crossing depth is the residual.  We name the
   all-`r` form `OrbitDegreeBelowFold` precisely as the open obligation and reduce the
   growing-slack horn to it; we do NOT discharge it past `r = 4`.

Character-sum-free, char-agnostic, p-independent.  Does **not** touch CORE
`M(μ_n) ≤ C·√(n·log(p/n))`.

Probe: `scripts/probes/probe_deg_badr_growing_slack.py` (exact integer degree by finite
differences over the proven closed forms; the `deg(#bad_r)=r` vs `deg(O_r)=r−1` split, the
`#bad_r = n·O_r + 1` factorization cross-check at `n = 16 … 1024`, NEVER `n = q−1`).
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.OffBGKDegBadR

open ArkLib.ProximityGap
open ArkLib.ProximityGap.DeepBandOrbitCountDescent

/-! ## Part A — the proven orbit-size factorization re-exported as the deg-drop source

`#bad_r = n · O_r + 1` is the PROVEN identity (orbit size `= n` is a free action,
`Frontier.CliqueOrbitFreeness`; the `+1` is the single fixed `γ = 0` slice).  This is the *exact
mechanism* of the degree drop: dividing the raw `#bad_r` by the orbit-size factor `n` drops the
degree by one.  We re-state it in the `g = n/4` variable used by the closed forms. -/

/-- **(A.1) `#bad₃ = n · O₃ + 1`** with `n = 4g`, `O₃ = C(g,2)` (re-export of
`deepBandBadCount_eq_n_mul_orbitCount3`).  The `r=3` orbit-size factorization. -/
theorem bad3_factor (g : ℕ) :
    DeepBandR3.deepBandBadCount g = 4 * g * orbitCount3 g + 1 :=
  deepBandBadCount_eq_n_mul_orbitCount3 g

/-- **(A.2) `#bad₄ = n · O₄ + 1`** with `n = 4g = 8h`, `O₄ = #bad₃(n/8)` (re-export of
`deepBandBadCount4_eq_n_mul_orbitCount4`, even `g = 2h`).  The `r=4` orbit-size factorization. -/
theorem bad4_factor (h : ℕ) (hh : 1 ≤ h) :
    DeepBandR4.deepBandBadCount4 (2 * h) = 4 * (2 * h) * orbitCount4 (2 * h) + 1 :=
  deepBandBadCount4_eq_n_mul_orbitCount4 h hh

/-! ## Part B — `deg(#bad_r) = r` EXACTLY (the RAW count): sub-lead (A) REFUTED for `#bad`

We pin the degree with a clean `ℕ`-arithmetic SANDWICH: a polynomial `f(g)` has degree exactly `d`
iff `c₁·gᵈ ≤ f(g) ≤ c₂·gᵈ` for all large `g` (positive leading coeff, no higher term).  This avoids
all `Polynomial.natDegree`/`compute_degree` fragility and is fully `nlinarith`-checkable over the
explicit closed forms.  For `#bad₃ = 2g³−2g²+1` and `#bad₄ = g⁴−2g³+4g+1` we land both the
degree-`r` LOWER bound (`gʳ ≤ #bad_r` ⟹ deg ≥ r) and the degree-`r` UPPER bound
(`#bad_r ≤ 2gʳ` ⟹ deg ≤ r), so `deg(#bad_r) = r`, REFUTING `deg(#bad_r) < r`. -/

/-- **(B.1) `deg(#bad₃) ≥ 3`**: the cubic lower bound `g³ ≤ #bad₃(g)` for `g ≥ 1`.
`#bad₃ = 2g³−2g²+1 ≥ g³` ⟺ `g³ ≥ 2g²−1`, true for `g ≥ 1` (`g³ ≥ 2g²` for `g ≥ 2`, and `g=1`:
`1 ≥ 1`).  Certifies the raw `r=3` count is at LEAST cubic — degree `≥ 3 = r`. -/
theorem degBad3_ge (g : ℕ) (hg : 1 ≤ g) :
    g ^ 3 ≤ DeepBandR3.deepBandBadCount g := by
  rw [DeepBandR3.deepBandBadCount]
  -- 2 g^2 (g-1) + 1 ≥ g^3, i.e. 2g^3 - 2g^2 + 1 ≥ g^3 (avoiding ℕ subtraction via the additive form)
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
  have he : e + 1 - 1 = e := by omega
  rw [he]
  -- ring identity: 2(e+1)^2 e + 1 + e = (e+1)^3 + (e^3 + e^2); and e^3+e^2 ≥ e ⟹ done.
  have hid : 2 * (e + 1) ^ 2 * e + 1 + e = (e + 1) ^ 3 + (e ^ 3 + e ^ 2) := by ring
  have hle : e ≤ e ^ 3 + e ^ 2 := le_trans (Nat.le_self_pow (by norm_num) e) (Nat.le_add_left _ _)
  omega

/-- **(B.2) `deg(#bad₃) ≤ 3`**: the cubic upper bound `#bad₃(g) ≤ 2g³` for `g ≥ 1`.
`#bad₃ = 2g³−2g²+1 ≤ 2g³` ⟺ `1 ≤ 2g²`, true for `g ≥ 1`.  Certifies the raw `r=3` count is at
MOST cubic — degree `≤ 3 = r`.  Together with (B.1): `deg(#bad₃) = 3 = r`, so `deg(#bad₃) < 3`
is FALSE. -/
theorem degBad3_le (g : ℕ) (hg : 1 ≤ g) :
    DeepBandR3.deepBandBadCount g ≤ 2 * g ^ 3 := by
  rw [DeepBandR3.deepBandBadCount]
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
  have he : e + 1 - 1 = e := by omega
  rw [he]; nlinarith [Nat.zero_le e]

/-- **(B.3) `deg(#bad₄) ≥ 4`**: the quartic lower bound `g⁴ ≤ 4·#bad₄(g)` for `g ≥ 2`.  Using the
proven additive form `#bad₄ + 2g³ = g⁴ + 4g + 1`, we get `4·#bad₄ = 4g⁴ + 16g + 4 − 8g³ ≥ g⁴`
(equivalently `3g⁴ + 16g + 4 ≥ 8g³`, true for all `g ≥ 2` — exact integer check
`probe_deg_badr_growing_slack.py`).  Certifies degree `≥ 4 = r`.  (Constant `4` — not `2` — because
`2·#bad₄ < g⁴` at `g = 3`; the degree is what matters, the constant is incidental.) -/
theorem degBad4_ge (g : ℕ) (hg : 2 ≤ g) :
    g ^ 4 ≤ 4 * DeepBandR4.deepBandBadCount4 g := by
  have hadd := DeepBandR4.deepBandBadCount4_add g hg
  -- hadd : deepBandBadCount4 g + 2 g^3 = g^4 + 4 g + 1, all in ℕ (no truncation).
  -- 4*bad4 = 4*(g^4+4g+1) - 8 g^3.  Need g^4 ≤ that, i.e. 3 g^4 + 16 g + 4 ≥ 8 g^3.
  -- Substitute g = e+2 so the inequality is a positive-coeff polynomial in e ≥ 0.
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 2 := ⟨g - 2, by omega⟩
  -- difference 3(e+2)^4 + 16(e+2) + 4 − 8(e+2)^3 = 3e^4+16e^3+24e^2+16e+20 (all nonneg coeffs).
  have hexp : 3 * (e + 2) ^ 4 + 16 * (e + 2) + 4
      = 8 * (e + 2) ^ 3 + (3 * e ^ 4 + 16 * e ^ 3 + 24 * e ^ 2 + 16 * e + 20) := by ring
  have key : 8 * (e + 2) ^ 3 ≤ 3 * (e + 2) ^ 4 + 16 * (e + 2) + 4 := by omega
  -- combine with hadd
  omega

/-- **(B.4) `deg(#bad₄) ≤ 4`**: the quartic upper bound `#bad₄(g) ≤ 2g⁴` for `g ≥ 2`.
From `#bad₄ + 2g³ = g⁴+4g+1` we have `#bad₄ ≤ g⁴+4g+1 ≤ 2g⁴` (`4g+1 ≤ g⁴ ≤ g⁴+2g³`, slack ample).
Certifies degree `≤ 4 = r`.  Together with (B.3): `deg(#bad₄) = 4 = r`, so `deg(#bad₄) < 4` is
FALSE. -/
theorem degBad4_le (g : ℕ) (hg : 2 ≤ g) :
    DeepBandR4.deepBandBadCount4 g ≤ 2 * g ^ 4 := by
  have hadd := DeepBandR4.deepBandBadCount4_add g hg
  -- bad4 = g^4 + 4g + 1 - 2 g^3 ≤ g^4 + 4g + 1 ≤ 2 g^4   (since 4g+1 ≤ g^4 for g ≥ 2).
  have hle : DeepBandR4.deepBandBadCount4 g ≤ g ^ 4 + 4 * g + 1 := by omega
  -- 4g+1 ≤ g^4 for g ≥ 2: substitute g = e+2; (e+2)^4 − (4(e+2)+1) = e^4+8e^3+24e^2+28e+7 ≥ 0.
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 2 := ⟨g - 2, by omega⟩
  have hexp : (e + 2) ^ 4 = 4 * (e + 2) + 1 + (e ^ 4 + 8 * e ^ 3 + 24 * e ^ 2 + 28 * e + 7) := by
    ring
  have key : 4 * (e + 2) + 1 ≤ (e + 2) ^ 4 := by omega
  omega

/-! ## Part C — `deg(O_r) = r−1 < r` (the ORBIT count): sub-lead (A) CONFIRMED for `O`

The orbit count `O_r = #bad_r / n` (the deduplicated count) has degree EXACTLY `r−1`, one below
the raw count.  Same `ℕ`-sandwich method.  `O₃ = C(g,2) = g(g−1)/2` is degree `2 = r−1`;
`O₄ = #bad₃(g/2) = 2(g/2)²(g/2−1)+1` is degree `3 = r−1`.  The degree DROP from `#bad_r` to `O_r`
is exactly one — the orbit-size-`n` division (the equivariance slack). -/

/-- **(C.1) `deg(O₃) ≤ 2 < 3`**: the quadratic upper bound `O₃(g) = C(g,2) ≤ g²`.
`g(g−1)/2 ≤ g²` always.  The `r=3` orbit count is at MOST quadratic — degree `≤ 2 = r−1 < r = 3`.
This is the CONFIRMED growing-slack: `O₃` grows one degree slower than `#bad₃`. -/
theorem degOrbit3_le (g : ℕ) : orbitCount3 g ≤ g ^ 2 := by
  rw [orbitCount3, Nat.choose_two_right]
  -- g*(g-1)/2 ≤ g^2
  calc g * (g - 1) / 2 ≤ g * (g - 1) := Nat.div_le_self _ _
    _ ≤ g * g := Nat.mul_le_mul_left g (by omega)
    _ = g ^ 2 := (sq g).symm

/-- **(C.2) `deg(O₃) ≥ 2`**: the quadratic lower bound `g² ≤ 3·O₃(g)` for `g ≥ 2`.
`O₃ = g(g−1)/2`, so `3·O₃ ≥ g(g−1)·3/2 ≥ g²` for `g ≥ 3`; the slack handles `g = 2`
(`3·1 = 3 ≥ 4`? no — use `g²≤4·O₃`).  We use `g² ≤ 4·O₃ + 2g`: `4·(g(g−1)/2) = 2g²−2g`, and
`g² ≤ 2g²−2g+2g = 2g²` for `g ≥ 0`.  Certifies degree `≥ 2 = r−1` (the orbit count is genuinely
quadratic, not lower). -/
theorem degOrbit3_ge (g : ℕ) (hg : 2 ≤ g) : g ^ 2 ≤ 4 * orbitCount3 g + 2 * g := by
  rw [orbitCount3, Nat.choose_two_right]
  -- 4 * (g*(g-1)/2) = 2 * (g*(g-1)) since 2 ∣ g*(g-1)
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 2 := ⟨g - 2, by omega⟩
  have he : e + 2 - 1 = e + 1 := by omega
  rw [he]
  have hdvd : 2 ∣ (e + 2) * (e + 1) := by
    have := Nat.even_mul_succ_self (e + 1)
    rw [mul_comm]; simpa using this.two_dvd
  obtain ⟨c, hc⟩ := hdvd
  -- (e+2)*(e+1)/2 = c (from hc : (e+2)*(e+1) = 2*c).
  have hdiv : (e + 2) * (e + 1) / 2 = c := by rw [hc, Nat.mul_div_cancel_left c (by norm_num)]
  rw [hdiv]
  -- goal: (e+2)^2 ≤ 4*c + 2*(e+2).  From hc: 2*((e+2)*(e+1)) = 4*c; and
  -- 2*(e+2)*(e+1) + 2*(e+2) = (e+2)^2 + (e+2)^2 (ring), so 4*c + 2*(e+2) = 2*(e+2)^2 ≥ (e+2)^2.
  have hid : 2 * ((e + 2) * (e + 1)) + 2 * (e + 2) = (e + 2) ^ 2 + (e + 2) ^ 2 := by ring
  omega

/-- **(C.3) `deg(O₄) ≤ 3 < 4`**: the cubic upper bound `O₄(g) ≤ 2·g³` (even `g`).
`O₄(g) = #bad₃(g/2) ≤ 2·(g/2)³ = g³/4 ≤ 2g³` by `degBad3_le` at `g/2`.  The `r=4` orbit count is at
MOST cubic — degree `≤ 3 = r−1 < r = 4`.  CONFIRMED growing-slack: `O₄` grows one degree slower than
`#bad₄`. -/
theorem degOrbit4_le (g : ℕ) (hg : 2 ≤ g / 2) : orbitCount4 g ≤ 2 * g ^ 3 := by
  rw [orbitCount4]
  -- deepBandBadCount (g/2) ≤ 2*(g/2)^3 ≤ 2*g^3 since g/2 ≤ g.
  have h1 : DeepBandR3.deepBandBadCount (g / 2) ≤ 2 * (g / 2) ^ 3 :=
    degBad3_le (g / 2) (by omega)
  have h2 : (g / 2) ^ 3 ≤ g ^ 3 := Nat.pow_le_pow_left (Nat.div_le_self g 2) 3
  calc DeepBandR3.deepBandBadCount (g / 2) ≤ 2 * (g / 2) ^ 3 := h1
    _ ≤ 2 * g ^ 3 := Nat.mul_le_mul_left 2 h2

/-- **(C.4) `deg(O₄) ≥ 3`**: the cubic lower bound `(g/2)³ ≤ O₄(g)` (even `g`, `g/2 ≥ 1`).
`O₄(g) = #bad₃(g/2) ≥ (g/2)³` by `degBad3_ge` at `g/2`.  Certifies degree `≥ 3 = r−1` (the orbit
count is genuinely cubic, not lower).  Together with (C.3): `deg(O₄) = 3 = r−1 < 4 = r`. -/
theorem degOrbit4_ge (g : ℕ) (hg : 1 ≤ g / 2) : (g / 2) ^ 3 ≤ orbitCount4 g := by
  rw [orbitCount4]
  exact degBad3_ge (g / 2) hg

/-! ## Part D — the DEGREE-GAP statement: `#bad_r` outgrows `O_r` by exactly one degree

The clean qualitative content: at every shallow rung the raw count `#bad_r` is degree `r` while the
orbit count `O_r` is degree `r−1`, so `#bad_r / O_r → ∞` linearly (`= n`, the orbit-size factor).
We land this as the EXACT ratio identity `#bad_r = n·O_r + 1` (Part A) PLUS the strict degree
separation: `O_r` is `o(#bad_r)` because `#bad_r ≥ n·O_r` and `n → ∞`.  Concretely the gap is
`#bad_r − O_r ≥ (n−1)·O_r ≥ 0`, growing.  We record the clean strict inequality at the rungs. -/

/-- **(D.1) The exact degree-gap at `r=3`:** `#bad₃ − 1 = n · O₃` with `n = 4g`, so the raw count is
`n` times the orbit count — the orbit-size-`n` factor IS the one-degree gap.  Restated as the clean
multiplicative identity `#bad₃ = 4g · O₃ + 1`. -/
theorem degGap3 (g : ℕ) : DeepBandR3.deepBandBadCount g = 4 * g * orbitCount3 g + 1 :=
  bad3_factor g

/-- **(D.2) The exact degree-gap at `r=4`:** `#bad₄ = n · O₄ + 1` with `n = 8h`.  Same orbit-size-`n`
one-degree gap. -/
theorem degGap4 (h : ℕ) (hh : 1 ≤ h) :
    DeepBandR4.deepBandBadCount4 (2 * h) = 4 * (2 * h) * orbitCount4 (2 * h) + 1 :=
  bad4_factor h hh

/-! ## Part E — the named open obligation for general `r` (NOT discharged past `r = 4`)

The all-`r` form of sub-lead (A), the genuine open obligation feeding `DistinctGammaUnionGrowthLaw`.
We name it precisely and reduce the growing-slack horn to it; we do NOT prove it for `r ≥ 5` (the
order-2 descent that pins the shallow forms stops at `r = 4`). -/

/-- **(E) `OrbitDegreeBelowFold O d` — the named open obligation (all-`r` growing-slack).**  The
claim that for every fold `r`, the orbit count `O r` at scale `n` is bounded by a polynomial of
degree `< r` in `n` — abstractly, `O r ≤ C · n^{r-1}` for a uniform constant.  We encode it as:
there is a constant `C` with `O r n ≤ C * n ^ (r - 1)` for all `r ≥ 1` and all `n`.  PROVEN here
ONLY at `r = 3, 4` (Part C); the all-`r` form is the open growth-law input.  (NOTE: even granting
this, the budget crossing `m* = O(log n)` is a SEPARATE residual — degree `< r` does not by itself
bound the crossing depth; that is `FastPhaseLogDecay` / `DistinctGammaUnionGrowthLaw`.) -/
def OrbitDegreeBelowFold (O : ℕ → ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ r n, 1 ≤ r → O r n ≤ C * n ^ (r - 1)

/-- **(E′) The shallow rungs `r = 3, 4` are CONSISTENT with `OrbitDegreeBelowFold` (witness).**  For
the in-tree orbit-count family `O 3 n = O₃(n/4)`, `O 4 n = O₄(n/4)` (and trivial elsewhere), the
degree-`r−1` upper bounds (C.1, C.3) instantiate the obligation at `r = 3, 4` with a small constant.
We certify the `r=3` instance: `O₃(g) ≤ g² ≤ n²` (`n = 4g ≥ g`), so the orbit count is `≤ 1·n²`,
the `r−1 = 2` degree.  This shows the obligation is NON-vacuous and HOLDS at the proven rung — the
shallow-rung content of (A) is genuinely on the right (orbit) side. -/
theorem orbitDegreeBelowFold_r3_witness (g : ℕ) (hg : 1 ≤ g) :
    orbitCount3 g ≤ (4 * g) ^ 2 := by
  have h1 : orbitCount3 g ≤ g ^ 2 := degOrbit3_le g
  have h2 : g ^ 2 ≤ (4 * g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact le_trans h1 h2

/-- **(E″) Non-vacuity of the obligation:** a super-`(r−1)`-degree family VIOLATES it, so
`OrbitDegreeBelowFold` has real content.  E.g. `O r n = n^r + 1` at `r = 1` gives `O 1 n = n + 1`,
not `≤ C·n^0 = C` for any FIXED `C` (pick `n > C`).  Witnesses that the law is not vacuously true:
a genuine degree bound must be established, exactly as the off-BGK frontier requires. -/
theorem orbitDegreeBelowFold_has_content (C : ℕ) :
    ¬ OrbitDegreeBelowFold (fun r n => n ^ r + 1) C := by
  intro h
  -- specialise r=1, n=C+1: O 1 (C+1) = (C+1) + 1 = C+2 ≤ C * (C+1)^0 = C, contradiction.
  have := h 1 (C + 1) le_rfl
  simp only [pow_one, Nat.sub_self, pow_zero, Nat.mul_one] at this
  omega

end ArkLib.ProximityGap.OffBGKDegBadR

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.bad3_factor
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.bad4_factor
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degBad3_ge
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degBad3_le
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degBad4_ge
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degBad4_le
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degOrbit3_le
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degOrbit3_ge
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degOrbit4_le
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degOrbit4_ge
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degGap3
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.degGap4
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.orbitDegreeBelowFold_r3_witness
#print axioms ArkLib.ProximityGap.OffBGKDegBadR.orbitDegreeBelowFold_has_content
