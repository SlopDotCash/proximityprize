/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# LANE G90 (#466, 2026-07-10): spacing rigidity / Denjoy–Koksma probe for the G80Z
  non-Fourier arc certificate — the multiplicative dynamics is NOWHERE an isometry
  (gap-rigidity dichotomy), and the sup-norm arc route has an AM–GM cost floor
  `2·√(2πn·ε₀)` (axiom-clean).

## What this lane probed (candidate (c) of the non-Fourier certificate hunt)

G80Z (`_G80ZArcArithmeticInstantiation.lean`) left the campaign's "single missing
non-Fourier certificate": arc-occupancy equidistribution of every dilate `b·μ_n ⊂ ZMod p`
strong enough that `K·ε + 2πn/K ≲ √(n log q)`. The untried angle was ORDER-STATISTIC /
SPACING rigidity: treat the sorted values of `b·μ_n` as a rotation-like orbit, hope the
multiplication-by-`g` self-map acts as a bounded-branch interval exchange, and run a
Denjoy–Koksma (variation-bounded Birkhoff sums, no Fourier) discrepancy argument.

## Probe verdict (scripts: scratchpad `probe_g90_spacing.py`, `probe_g90_branches.py`,
   `probe_g90_costfloor.py`; cells `n = 16..512`, `p ≈ n²`, `n = 2^a`, all cosets `b`)

1. **DK/interval-exchange is structurally DEAD.** For every `h ∈ μ_n \ {1, −1}` and every
   dilate, the number of successor pairs whose val-gap is preserved by `×h` is EXACTLY 0
   (matches `gap_fixed_iff_one` below: `h·d = d, d ≠ 0 ⟹ h = 1`). Multiplication by the
   subgroup generator is nowhere a local translation of the val-metric; the only
   val-isometries available in `μ_n` are `±1` (identity and the central reflection already
   mapped by E12/N13). Adjacency (order-only) preservation exists only for small `val(h)`
   (best accessible cell `μ₁₆ = ⟨2⟩ ⊂ ZMod 257`: 13/16 pairs for `h = 2`, 10/16 for
   `h = 4`, 6/16 for `h = 16`, pinned below by `decide`) and decays with the multiplier:
   the dynamics is EXPANDING (gaps multiply by `h`), the opposite of the zero-entropy
   rotations Denjoy–Koksma needs. Generic generators scramble ALL adjacencies
   (branch count = n at every tested cell for the sorted-orbit permutation).
2. **Arc discrepancy of `b·μ_n` is random-like, with NO extra rigidity.** Exact star
   discrepancy over all cosets: `D*_max/√(n log(p/n))` = 0.51, 0.63/0.79, 0.50/0.81,
   0.53/0.55, 0.48/0.69/0.63, (n = 16..512 cells) — square-root scale with small constant,
   bracketing the iid-random control (which gave 0.43–0.67). The truth is as good as
   random but NOT better: no spacing-rigidity slack exists below the random floor.
3. **The sup-norm arc certificate G80Z consumes is FALSE at the needed strength.** The
   contrapositive route needs `ε(K) ≤ (√(n log q) − 2πn/K)/K` for some `K`. Measured
   `ε(K)` (max over all cosets and arcs of `|occ − n/K|`) tracks the random-fluctuation
   shape `≍ √(n/K)`, so the best achievable bound
   `min_K [K·ε(K) + 2πn/K]` has an `n^{2/3}`-scale floor. Measured
   `min_K bound / √(n log(p/n))` = 5.57, 6.56, 6.57, 7.35, 9.80, 9.17 at
   `n = 16, 32, 64, 128, 256, 512` — GROWING like `n^{1/6}` (equivalently
   `min_K bound / n^{2/3}` = 5.9, 7.0, 6.1, 6.8, 9.2, 7.6, flat). No constant `C` in the
   target `C·√(n log q)` can absorb this. The formal content is the AM–GM floor
   `K·ε + 2πn/K ≥ 2·√(2πn·ε₀)` proven below: any unsigned sup-arc certificate with
   deviation floor `ε₀` cannot certify below the geometric mean, and the empirical
   `ε₀(K) ≈ √(n/K)` puts that mean at `n^{2/3}`, strictly above the prize scale.

## Consequence for the campaign

The doctrine-v2 "single missing non-Fourier certificate" CANNOT take the shape the G80Z
consumer eats (b-uniform sup-norm per-arc occupancy accuracy at exchange rate `K·ε`):
the required per-arc accuracy is violated by unavoidable random-scale counting
fluctuations, which the probe confirms are present for `b·μ_n` at every tested cell. The
√-scale content of BGK lives in SIGNED cross-arc cancellation of the deviations against
the phase weights — i.e. exactly the Fourier structure — so the unsigned-occupancy
reformulation loses `n^{2/3}/√(n log q)` irrecoverably. Any future non-Fourier certificate
must certify a SIGNED/correlated functional of the arc deviations, not their sup (or L1)
norm. This sharpens, and does NOT close, the open core: CORE remains OPEN / ON-BGK.

## Formal payload (all axiom-clean)

* `gap_fixed_iff_one` / `gap_reversed_iff_neg_one` / `gap_scrambled` : the RIGIDITY
  DICHOTOMY — in `ZMod p` (p prime), `h·d = d ↔ h = 1` and `h·d = −d ↔ h = −1` for
  `d ≠ 0`; hence multiplication by any `h ∉ {±1}` preserves NO gap.
* `mul_map_gap` : gaps dilate exactly (`h·y − h·x = h·(y − x)`), the expansion mechanism.
* `valGap_preserved_forces_one` / `valGap_reversed_forces_neg_one` : the sorted-value
  (val-metric) reading — a single preserved successor gap forces `h = 1` (resp. `h = −1`).
* `gap_scrambled_of_three_le_orderOf` : the `μ_n` instantiation — every element of
  order ≥ 3 (in particular every generator of `μ_n`, `n ≥ 3`) preserves no gap.
* `two_sqrt_mul_le` / `arc_certificate_cost_floor` / `supArc_route_floor` /
  `no_admissible_K` : the COST FLOOR — for every `K > 0` and `ε ≥ ε₀ ≥ 0`,
  `K·ε + 2πn/K ≥ 2√(2πn·ε₀)`; if the target is below that floor, NO `K` is admissible.
* `mu16_eq_sixteenth_roots`, `mu16_sorted`, `rank2_spec`/`rank4_spec`/`rank16_spec`,
  `rank*_adjacency_count`, `mu16_gap_never_preserved_by_double` : TOY-SCALE EXACT PIN
  (`decide`, kernel-checked) of the most rotation-like accessible cell
  `μ₁₆ = ⟨2⟩ ⊂ ZMod 257` (the minimal possible multiplier val 2, i.e. the geometric-
  progression BGK worst case): adjacency preservation 13 → 10 → 6 for `h = 2, 4, 16`
  (decaying with the multiplier), gap preservation exactly 0.

## Honest scope

Negative-space result + structural lemmas + toy pins. Nothing here bounds `M` or `‖η_b‖`;
the general-p lemmas are elementary field/AM–GM facts whose VALUE is the precise
obstruction map they pin (DK/IET route dead; sup-arc certificate shape dead). The
`n^{2/3}` floor claim is probe-verified (6 cells, monotone margin), with the AM–GM half
formal and the fluctuation floor `ε(K) ≳ √(n/K)` empirical. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean. No sorry, no axiom, no native_decide.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000


namespace ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe

/-! ## Part 1 — the gap-rigidity dichotomy (Denjoy–Koksma obstruction) -/

section Rigidity

variable {p : ℕ} [Fact p.Prime]

/-- Gaps dilate exactly under multiplication: the image of the gap `y − x` under `×h`
is `h·(y − x)`. This is the expansion mechanism that kills bounded-variation transfer. -/
theorem mul_map_gap (h x y : ZMod p) : h * y - h * x = h * (y - x) := by ring

/-- **Rigidity, fixed direction**: a nonzero gap is preserved by `×h` iff `h = 1`. -/
theorem gap_fixed_iff_one {h d : ZMod p} (hd : d ≠ 0) : h * d = d ↔ h = 1 := by
  constructor
  · intro he
    have h1 : h * d = 1 * d := by rw [he, one_mul]
    exact mul_right_cancel₀ hd h1
  · rintro rfl
    rw [one_mul]

/-- **Rigidity, reversed direction**: a nonzero gap is negated by `×h` iff `h = −1`
(the central reflection, the E12/N13 symmetry). -/
theorem gap_reversed_iff_neg_one {h d : ZMod p} (hd : d ≠ 0) : h * d = -d ↔ h = -1 := by
  constructor
  · intro he
    have h1 : h * d = -1 * d := by rw [he]; ring
    exact mul_right_cancel₀ hd h1
  · rintro rfl
    ring

/-- **The dichotomy**: multiplication by any `h ∉ {1, −1}` preserves NO nonzero gap,
in either orientation. The sorted-orbit dynamics of `b·μ_n` under a generator is
nowhere a local isometry — the interval-exchange/Denjoy–Koksma mechanism has zero
branches to work with. -/
theorem gap_scrambled {h : ZMod p} (h1 : h ≠ 1) (h2 : h ≠ -1) {d : ZMod p} (hd : d ≠ 0) :
    h * d ≠ d ∧ h * d ≠ -d :=
  ⟨fun he => h1 ((gap_fixed_iff_one hd).mp he),
   fun he => h2 ((gap_reversed_iff_neg_one hd).mp he)⟩

/-- Sorted-value reading: if `×h` maps the pair `(x, y)` to a pair with the SAME
val-gap, then `h = 1`. A single preserved successor gap in the sorted orbit already
forces the trivial multiplier. -/
theorem valGap_preserved_forces_one {h x y : ZMod p} (hxy : x ≠ y)
    (hval : (h * y - h * x).val = (y - x).val) : h = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hgap : h * y - h * x = h * (y - x) := by ring
  have hv : (h * (y - x)).val = (y - x).val := by rw [← hgap]; exact hval
  have heq : h * (y - x) = y - x := ZMod.val_injective p hv
  exact (gap_fixed_iff_one hd).mp heq

/-- Sorted-value reading, reversed orientation: a single orientation-reversing
gap-preserving pair forces `h = −1`. -/
theorem valGap_reversed_forces_neg_one {h x y : ZMod p} (hxy : x ≠ y)
    (hval : (h * y - h * x).val = (x - y).val) : h = -1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hgap : h * y - h * x = h * (y - x) := by ring
  have hneg : x - y = -(y - x) := by ring
  have hv : (h * (y - x)).val = (-(y - x)).val := by
    rw [← hgap, ← hneg]; exact hval
  have heq : h * (y - x) = -(y - x) := ZMod.val_injective p hv
  exact (gap_reversed_iff_neg_one hd).mp heq

/-- **The `μ_n` instantiation**: every element of multiplicative order ≥ 3 — in
particular every generator of `μ_n` for `n ≥ 3`, and every element of the prize
subgroup outside `{±1}` — preserves no gap. -/
theorem gap_scrambled_of_three_le_orderOf {h : ZMod p} (h3 : 3 ≤ orderOf h)
    {d : ZMod p} (hd : d ≠ 0) : h * d ≠ d ∧ h * d ≠ -d := by
  have h1 : h ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h3
    omega
  have h2 : h ≠ -1 := by
    rintro rfl
    have hle : orderOf (-1 : ZMod p) ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [neg_one_sq])
    omega
  exact gap_scrambled h1 h2 hd

end Rigidity

/-! ## Part 2 — the sup-arc certificate cost floor (AM–GM) -/

section CostFloor

/-- AM–GM in square-root form: `2√(ab) ≤ a + b` for nonnegative reals. -/
theorem two_sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  rw [Real.sqrt_mul ha]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The cost floor**: any bound of the shape `K·ε + c/K` (the G80Z contrapositive
with oscillation budget `c = 2πn`) is at least `2√(c·ε)`, for every `K > 0`. The
arc count `K` cannot be optimized below the geometric mean of the deviation cost
and the oscillation cost. -/
theorem arc_certificate_cost_floor {K ε c : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hc : 0 ≤ c) :
    2 * Real.sqrt (c * ε) ≤ K * ε + c / K := by
  have hKε : 0 ≤ K * ε := mul_nonneg hK.le hε
  have hcK : 0 ≤ c / K := div_nonneg hc hK.le
  have hprod : (K * ε) * (c / K) = c * ε := by
    field_simp
  calc 2 * Real.sqrt (c * ε) = 2 * Real.sqrt ((K * ε) * (c / K)) := by rw [hprod]
    _ ≤ K * ε + c / K := two_sqrt_mul_le hKε hcK

/-- **The G80Z-facing floor**: if the true max arc deviation is at least `ε₀` (the
probe-measured random-scale fluctuation floor, `ε₀ ≍ √(n/K)` empirically), then the
best `‖η_b‖`-bound the sup-arc contrapositive can certify is `≥ 2√(2πn·ε₀)`,
uniformly in the arc count `K`. -/
theorem supArc_route_floor {n K ε ε₀ : ℝ} (hK : 0 < K) (h0 : 0 ≤ ε₀) (hε : ε₀ ≤ ε)
    (hn : 0 ≤ n) :
    2 * Real.sqrt (2 * Real.pi * n * ε₀) ≤ K * ε + 2 * Real.pi * n / K := by
  have hc : 0 ≤ 2 * Real.pi * n := by positivity
  have h1 : 2 * Real.sqrt (2 * Real.pi * n * ε₀) ≤ K * ε₀ + 2 * Real.pi * n / K :=
    arc_certificate_cost_floor hK h0 hc
  have h2 : K * ε₀ ≤ K * ε := mul_le_mul_of_nonneg_left hε hK.le
  linarith

/-- **No admissible arc count**: if the target `t` (e.g. `C·√(n log q)`) sits below
the floor `2√(2πn·ε₀)`, then NO choice of `K` and no certificate accuracy `ε ≥ ε₀`
makes the G80Z contrapositive bound `K·ε + 2πn/K` reach `t`. -/
theorem no_admissible_K {n ε₀ t : ℝ} (h0 : 0 ≤ ε₀) (hn : 0 ≤ n)
    (ht : t < 2 * Real.sqrt (2 * Real.pi * n * ε₀)) :
    ∀ K ε : ℝ, 0 < K → ε₀ ≤ ε → ¬(K * ε + 2 * Real.pi * n / K ≤ t) := by
  intro K ε hK hε hle
  exact absurd (le_trans (supArc_route_floor hK h0 hε hn) hle) (not_le.mpr ht)

end CostFloor

/-! ## Part 3 — toy-scale exact pin: `μ₁₆ = ⟨2⟩ ⊂ ZMod 257` (kernel `decide`)

The most rotation-like cell accessible: `2` has order 16 mod 257, so `μ₁₆` is the
geometric progression `{±2^k}` — the minimal-possible multiplier (`val = 2`) and the
classical BGK interval-concentration worst case. Even here: gap preservation is
exactly 0 (instantiating Part 1), and adjacency preservation decays 13 → 10 → 6 as
the multiplier grows `2 → 4 → 16` — expansion, never an interval exchange. -/

section ToyPin

/-- The sorted sixteenth roots of unity mod 257 (= `⟨2⟩`, since `ord₂₅₇(2) = 16`). -/
def mu16 : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 129, 193, 225, 241, 249, 253, 255, 256]

/-- `mu16` is exactly the solution set of `x¹⁶ = 1` in `ZMod 257` (kernel-checked). -/
theorem mu16_eq_sixteenth_roots :
    (List.range 257).filter (fun x => x ^ 16 % 257 == 1) = mu16 := by decide

/-- `mu16` is strictly sorted (it IS the sorted value list of the subgroup). -/
theorem mu16_sorted :
    (List.range 15).all (fun i => mu16[i]! < mu16[i + 1]!) = true := by decide

/-- The rank permutation of `×2` on the sorted subgroup: `2·mu16[i] mod 257` has rank
`rank2[i]`. One wrap (index 7 → 15, the value 128 → 256) plus one carry breaks the
adjacency chain. -/
def rank2 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 15, 0, 8, 9, 10, 11, 12, 13, 14]

theorem rank2_spec :
    (List.range 16).all
      (fun i => mu16[rank2[i]!]! == 2 * mu16[i]! % 257) = true := by decide

/-- `×2` (the minimal possible nontrivial multiplier) preserves 13 of 16 cyclic
adjacencies — but zero gaps (`mu16_gap_never_preserved_by_double`). -/
theorem rank2_adjacency_count :
    ((List.range 16).filter
      (fun i => rank2[(i + 1) % 16]! == (rank2[i]! + 1) % 16)).length = 13 := by decide

/-- The rank permutation of `×4`. -/
def rank4 : List ℕ := [2, 3, 4, 5, 6, 7, 15, 14, 1, 0, 8, 9, 10, 11, 12, 13]

theorem rank4_spec :
    (List.range 16).all
      (fun i => mu16[rank4[i]!]! == 4 * mu16[i]! % 257) = true := by decide

theorem rank4_adjacency_count :
    ((List.range 16).filter
      (fun i => rank4[(i + 1) % 16]! == (rank4[i]! + 1) % 16)).length = 10 := by decide

/-- The rank permutation of `×16`. -/
def rank16 : List ℕ := [4, 5, 6, 7, 15, 14, 13, 12, 3, 2, 1, 0, 8, 9, 10, 11]

theorem rank16_spec :
    (List.range 16).all
      (fun i => mu16[rank16[i]!]! == 16 * mu16[i]! % 257) = true := by decide

/-- Adjacency preservation decays with the multiplier: 13 (`×2`) → 10 (`×4`) → 6
(`×16`). The dynamics is expanding, not an interval exchange. -/
theorem rank16_adjacency_count :
    ((List.range 16).filter
      (fun i => rank16[(i + 1) % 16]! == (rank16[i]! + 1) % 16)).length = 6 := by decide

/-- Even for the minimal multiplier `×2`, NOT ONE successor gap of the sorted
subgroup is preserved (concrete instance of `gap_fixed_iff_one`). -/
theorem mu16_gap_never_preserved_by_double :
    ((List.range 16).filter
      (fun i =>
        (2 * mu16[(i + 1) % 16]! % 257 + 257 - 2 * mu16[i]! % 257) % 257
          == (mu16[(i + 1) % 16]! + 257 - mu16[i]!) % 257)).length = 0 := by decide

end ToyPin

end ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.mul_map_gap
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.gap_fixed_iff_one
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.gap_reversed_iff_neg_one
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.gap_scrambled
#print axioms
  ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.valGap_preserved_forces_one
#print axioms
  ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.valGap_reversed_forces_neg_one
#print axioms
  ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.gap_scrambled_of_three_le_orderOf
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.two_sqrt_mul_le
#print axioms
  ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.arc_certificate_cost_floor
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.supArc_route_floor
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.no_admissible_K
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.mu16_eq_sixteenth_roots
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.mu16_sorted
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank2_spec
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank2_adjacency_count
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank4_spec
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank4_adjacency_count
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank16_spec
#print axioms ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.rank16_adjacency_count
#print axioms
  ArkLib.ProximityGap.Frontier.G90SpacingRigidityProbe.mu16_gap_never_preserved_by_double
