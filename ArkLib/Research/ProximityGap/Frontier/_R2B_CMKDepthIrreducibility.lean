/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# CMK depth irreducibility: the abstract moment-problem form is REFUTED (#466 round 2, lane CMK)

Round 1 (`docs/kb/deltastar-466-round1-outcomes-2026-07-01.md`, §E) left ONE new machinery
standing: "CMK moment-problem rigidity" — the hope that an abstract
Christoffel–Markov–Krein-type theorem of the shape

> `μ = (1/m)·Σᵢ δ_{xᵢ}` (m equal real atoms) ∧ second moment pinned EXACTLY at the Parseval
> value `m₂ = P₂` ∧ Wick envelope `|m_{2r}| ≤ K^r·(2r−1)‼·n^r` for all `r ≤ R`
> ⟹ `maxᵢ|xᵢ| ≤ C(K)·√(n·log m)`

might hold at some depth `R ≪ log m`, shortcutting the `r ≈ ln q` obligation of the open core.

**This brick lands the machine-checked countermodel gate: the abstract form is FALSE at every
depth `R ≪ log m`.** The refuting measure is the *symmetric 4-value equal-atom measure*: `m`
equal atoms, TWO at `±T` (one each) and `(m−2)/2` at each of `±s`, with
`s² = (m·P₂ − 2T²)/(m−2)` — so Parseval is EXACT by construction, ALL odd moments vanish
identically (better than the true η-field, whose per-atom first moment is `−n/(q−1)`), and it is
an actual positive measure, hence every implicit Hankel-PSD / Krein / Christoffel constraint
holds automatically.  The only active constraints on the edge `T` are the even Wick envelopes
`r = 1..R`, and they admit `T ≈ √n·√(2R/e)·(m/2)^{1/(2R)}`: the factor `m^{1/(2R)}` blows up for
`R ≪ log m`.

**Honest P₂** (read off the in-tree substrate, not approximated): from
`GaussPeriodParsevalFloor.sum_sq_erase_zero` (`Σ_{b≠0}‖η_b‖² = q·n − n²`) and coset-constancy of
`η` (`q − 1 = n·m` frequencies, `n` per multiplicative coset of `μ_n`), the per-atom second
moment of the `m`-atom coset-value measure is exactly
`P₂ = n(q−n)/(q−1) = n − (n−1)/m` at `q = n·m + 1` — the value used verbatim below.

## The concrete gate instance (exact rationals; matches `probe_466b_cmk_countermeasure.py`)

`n = 2^10`, `m = 2^40` atoms, Wick depth `R = 5` vs `log m`: `ln m = 40·ln 2 ≈ 27.73`, certified
below by `L = 28 > ln m` (`Real.log_two_lt_d9`); edge `T = 900`.  All five moment constraints
hold with exact-rational slack (tightest: `r = 5` at ratio `0.597`), Parseval is an identity,
`s² ≥ 0`, and yet `T² = 810000 > 16·n·L = 458752`, i.e. `T > 4·√(n·L) ≥ 4·√(n·ln m)` — the
measure's edge exceeds FOUR times the target scale while satisfying every abstract-CMK input to
depth 5 (vs `⌈log m⌉ = 28`).  At the prize scale the probe gives the same refutation with margin
`12×√(2n·ln m)` at `R = 11` (`n = 2^30`, `m = 2^128`, exact integer arithmetic), and the
admissible edge falls back to `≈ √(2n·ln m)` only at `R ≈ ln m` (binding depth plateaus at
`r* = 88 ≈ ln(m/2)`) — exactly recovering the KNOWN conditional moment bound
(`GaussPeriodMomentBound` / `prize_scale_bound_at_saddle`; cited, not re-landed).

## Verdict

Depth is IRREDUCIBLE for moment-only inputs: moment data to depth `R` buys edge control
`m^{1/(2R)}`, so no theorem from {equal atoms + exact Parseval + Wick-to-depth-R} can bound the
spectral edge at the prize scale for `R ≪ log m`.  CMK cannot shortcut the `r ≈ ln q` Wick
obligation; the composition CMK ∘ TPS dies with it (TPS supplies only `r ≈ β = O(1)`).

**HONESTY / SCOPE.**  This kills ONLY the abstract-moment form of CMK (the round-1 §E shape:
moments as the *only* inputs).  A `b_k`-native (Jacobi-recurrence / Hankel-window) CMK variant
consuming MORE than moments is NOT touched by this countermodel — but round-1 P4 independently
found that no `O(1)`-window Hankel functional pins the turnover per-prime, so that route is
separately squeezed.  This brick neither proves nor disproves CORE; the open core stays open.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Self-contained
(Mathlib-only imports; consumes no cone substrate — it is a pure exact-arithmetic countermodel).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility

/-! ## The toy-honest instance parameters -/

/-- `n = 2^10`: the Wick-envelope scale (the toy analogue of `n = |μ_n| = 2^30`). -/
def nScale : ℕ := 1024

/-- `m = 2^40`: the number of equal atoms (the toy analogue of `m = (q−1)/n = 2^128`). -/
def mAtoms : ℕ := 2 ^ 40

/-- The edge atom `T = 900`: the countermeasure places one atom at `+T` and one at `−T`. -/
def T : ℕ := 900

/-- `L = 28 = ⌈ln m⌉`: certified below (`log_mAtoms_lt_L`) via `Real.log_two_lt_d9`. -/
def L : ℕ := 28

/-- Wick depth `R = 5 ≪ log m ≈ 27.7`: the "depth-reduced" regime the abstract CMK claim
would need. -/
def wickDepth : ℕ := 5

/-- Numerator of `s²` over `(m−2)`: `A = m·n − (n−1) − 2T²` (as a literal; provenance in
`A_def`). -/
def A : ℕ := 1125899905221601

/-- Provenance of the literal `A`: it is exactly `m·n − (n−1) − 2T²` (in `ℤ`, avoiding
`ℕ`-subtraction pitfalls). -/
theorem A_def : (A : ℤ) = mAtoms * nScale - (nScale - 1) - 2 * T ^ 2 := by
  norm_num [A, mAtoms, nScale, T]

/-- The honest Parseval value `P₂ = (m·n − (n−1))/m = n − (n−1)/m`
(= `n(q−n)/(q−1)` at `q = n·m + 1`, from `GaussPeriodParsevalFloor.sum_sq_erase_zero` +
coset-constancy of `η`). -/
def P2 : ℚ := ((mAtoms : ℚ) * nScale - (nScale - 1)) / mAtoms

/-- `s² = A/(m−2)`: chosen so that Parseval is EXACT (see `parseval_exact`). -/
def s2 : ℚ := (A : ℚ) / ((mAtoms : ℚ) - 2)

/-- The `2r`-th moment of the symmetric 4-value equal-atom measure:
`m_{2r} = (2·T^{2r} + (m−2)·(s²)^r)/m`  (2 atoms at `±T`, `(m−2)/2` at each of `±s`;
all ODD moments vanish identically by symmetry). -/
def momentEven (r : ℕ) : ℚ :=
  (2 * (T : ℚ) ^ (2 * r) + ((mAtoms : ℚ) - 2) * s2 ^ r) / mAtoms

/-- `(2r−1)‼`: the Wick/Gaussian moment coefficients — `wick 1 = 1`, `wick 2 = 3`,
`wick 3 = 15`, `wick 4 = 105`, `wick 5 = 945`. -/
def wick : ℕ → ℕ
  | 0 => 1
  | r + 1 => (2 * r + 1) * wick r

theorem wick_one : wick 1 = 1 := rfl
theorem wick_two : wick 2 = 3 := rfl
theorem wick_three : wick 3 = 15 := rfl
theorem wick_four : wick 4 = 105 := rfl
theorem wick_five : wick 5 = 945 := rfl

/-! ## The measure is well-formed -/

/-- `s² ≥ 0`: the `±s` atoms are real. -/
theorem s2_nonneg : 0 ≤ s2 := by
  simp only [s2, A, mAtoms]
  norm_num

/-- The atom count closes: `2` edge atoms + `2·(2^39 − 1)` bulk atoms = `m`, with
`(m−2)/2 = 2^39 − 1` a genuine integer (no parity fudge). -/
theorem atomCount_closes : 2 + 2 * (2 ^ 39 - 1) = mAtoms := by
  norm_num [mAtoms]

/-- **Parseval is EXACT**: the second moment of the countermeasure equals the honest in-tree
Parseval value `P₂` on the nose (not approximately). -/
theorem parseval_exact : momentEven 1 = P2 := by
  simp only [momentEven, s2, P2, A, mAtoms, nScale, T]
  norm_num

/-! ## The Wick envelope holds to full depth `R = 5` (exact rationals) -/

theorem momentEven_one_le : momentEven 1 ≤ (wick 1 : ℚ) * (nScale : ℚ) ^ 1 := by
  simp only [momentEven, s2, A, mAtoms, nScale, T, wick_one]
  norm_num

theorem momentEven_two_le : momentEven 2 ≤ (wick 2 : ℚ) * (nScale : ℚ) ^ 2 := by
  simp only [momentEven, s2, A, mAtoms, nScale, T, wick_two]
  norm_num

theorem momentEven_three_le : momentEven 3 ≤ (wick 3 : ℚ) * (nScale : ℚ) ^ 3 := by
  simp only [momentEven, s2, A, mAtoms, nScale, T, wick_three]
  norm_num

theorem momentEven_four_le : momentEven 4 ≤ (wick 4 : ℚ) * (nScale : ℚ) ^ 4 := by
  simp only [momentEven, s2, A, mAtoms, nScale, T, wick_four]
  norm_num

theorem momentEven_five_le : momentEven 5 ≤ (wick 5 : ℚ) * (nScale : ℚ) ^ 5 := by
  simp only [momentEven, s2, A, mAtoms, nScale, T, wick_five]
  norm_num

/-- **The full Wick envelope** (`K = 1`): `m_{2r} ≤ (2r−1)‼·n^r` for every `1 ≤ r ≤ R = 5`. -/
theorem momentEven_wick_bound :
    ∀ r : ℕ, 1 ≤ r → r ≤ wickDepth →
      momentEven r ≤ (wick r : ℚ) * (nScale : ℚ) ^ r := by
  intro r h1 h5
  simp only [wickDepth] at h5
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact momentEven_one_le
  · exact momentEven_two_le
  · exact momentEven_three_le
  · exact momentEven_four_le
  · exact momentEven_five_le

/-! ## The edge exceeds `4·√(n·ln m)` -/

/-- The exact-rational edge gate: `T² > 16·n·L` (i.e. `T > 4·√(n·L)`), stated multiplicatively
to avoid reals: `810000 > 458752`. -/
theorem edge_exceeds_rat : 16 * (nScale : ℚ) * (L : ℚ) < (T : ℚ) ^ 2 := by
  simp only [nScale, L, T]
  norm_num

/-- The `L ≥ ln m` certificate: `Real.log m = 40·ln 2 < 40·0.6931471808 < 28 = L`
(via `Real.log_two_lt_d9`). -/
theorem log_mAtoms_lt_L : Real.log (mAtoms : ℝ) < (L : ℝ) := by
  have hm : (mAtoms : ℝ) = (2 : ℝ) ^ (40 : ℕ) := by norm_num [mAtoms]
  have hL : (L : ℝ) = 28 := by norm_num [L]
  rw [hm, hL, Real.log_pow]
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  push_cast
  linarith

/-- **The real-valued edge verdict**: `T² > 16·n·ln m`, i.e. the countermeasure's edge strictly
exceeds `4·√(n·ln m)` — while satisfying every abstract-CMK input to depth `R = 5 ≪ ln m`. -/
theorem edge_exceeds_real :
    16 * (nScale : ℝ) * Real.log (mAtoms : ℝ) < (T : ℝ) ^ 2 := by
  have hlog := log_mAtoms_lt_L
  have hpos : (0 : ℝ) < 16 * (nScale : ℝ) := by norm_num [nScale]
  have h1 : 16 * (nScale : ℝ) * Real.log (mAtoms : ℝ) < 16 * (nScale : ℝ) * (L : ℝ) :=
    mul_lt_mul_of_pos_left hlog hpos
  have h2 : 16 * (nScale : ℝ) * (L : ℝ) < (T : ℝ) ^ 2 := by
    simp only [nScale, L, T]; norm_num
  linarith

/-! ## The packaged countermodel gate -/

/-- **THE GATE (existential form).**  There is a symmetric 4-value equal-atom configuration —
edge `±Tₑ` (one atom each), bulk `±s` (`(m−2)/2` atoms each, `s² = σ ≥ 0`) — which satisfies

1. EXACT Parseval: `m₂ = P₂` (the honest in-tree value `n − (n−1)/m`),
2. the full Wick envelope `m_{2r} ≤ (2r−1)‼·n^r` for all `1 ≤ r ≤ R = 5`,
3. yet `Tₑ² > 16·n·L` with `L > ln m` (`log_mAtoms_lt_L`), i.e. edge `> 4·√(n·ln m)`.

Since the configuration is an actual positive measure, every Hankel-PSD / Krein / Christoffel
constraint holds implicitly; hence NO theorem with only the abstract-CMK inputs at depth
`R ≪ log m` can bound the edge at the `√(n·log m)` scale.  The abstract form of CMK
moment-problem rigidity is refuted. -/
theorem cmk_abstract_form_countermodel :
    ∃ Te σ : ℚ, 0 ≤ σ ∧
      (2 * Te ^ 2 + ((mAtoms : ℚ) - 2) * σ) / mAtoms = P2 ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ wickDepth →
        (2 * Te ^ (2 * r) + ((mAtoms : ℚ) - 2) * σ ^ r) / mAtoms
          ≤ (wick r : ℚ) * (nScale : ℚ) ^ r) ∧
      16 * (nScale : ℚ) * (L : ℚ) < Te ^ 2 := by
  refine ⟨(T : ℚ), s2, s2_nonneg, ?_, ?_, ?_⟩
  · -- direct: the exact-Parseval identity (same content as `parseval_exact`)
    simp only [s2, P2, A, mAtoms, nScale, T]
    norm_num
  · intro r h1 h5
    have := momentEven_wick_bound r h1 h5
    simpa only [momentEven] using this
  · exact edge_exceeds_rat

end ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility

#print axioms ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility.parseval_exact
#print axioms ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility.momentEven_wick_bound
#print axioms ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility.log_mAtoms_lt_L
#print axioms ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility.edge_exceeds_real
#print axioms ArkLib.ProximityGap.Frontier.CMKDepthIrreducibility.cmk_abstract_form_countermodel
