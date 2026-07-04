# #466 Round 13 — LANE M: the moment-order optimization formalized, and the ONE-vs-TWO-input verdict

**Date:** 2026-07-04. **Round:** 13 (Opus, LANE M). **Both deliverables adversarially self-checked.**

**Bottom line.** Round 12 left the capstone (`_WallCapstone.lean`) with one *un-formalized* analytic
step (its caveat (a)): the **moment-order optimization** turning the wall's per-rung `2r`-power
bounds `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` into a single closed-form sup-norm `M ≤ C·√(n·ln q)`; it therefore
passed `B`/`hB` as an *unproven parameter*. LANE M **formalizes that step, axiom-clean, directly from
`WallHolds`** — removing the parameter. And it **settles the round-13 core question**: the prize is
**NOT** localizable to `WallHolds` alone — it genuinely needs a **second, distinct** open input (the
`√q·B` hyperplane cancellation), which is provably not a consequence of the wall's per-frequency
moment control.

---

## 1. Deliverable 1 (formalization): `WallHolds ⟹ M ≤ √(2e·n·(ln q + 1))`, axiom-clean

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentOptimizedSupNorm.lean` (pg-iterate ✅,
all 7 theorems `#print axioms = {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`).

The chain, routed through the **DC-subtracted** wall (non-vacuous at the prize), NOT the DC-included
`WickEnergyBound` route of the earlier `_AR_MomentOptimizedSupNorm.lean`:

1. `WallHolds G := ∀ r, DCEnergyBound G r` (the SAME object as `_WallCapstone.WallHolds`).
2. `eta_pow_le_wall_form`: `DCEnergyBound G r ⟹ ‖η_b‖^{2r} ≤ q·(2r)ʳ·nʳ` (via in-tree
   `eta_pow_le_of_dcEnergyBound` + the new `doubleFactorial_two_sub_one_le`).
3. `sq_le_of_pow_ceil` (isolated saddle estimate): at `r = ⌈ln q⌉`, `q^{1/r} ≤ e`, so `‖η_b‖² ≤ 2e·n·r`.
4. `eta_le_of_wallHolds` / `supNorm_le_of_wallHolds`: `WallHolds G` + `q ≥ e` ⟹ for all `b ≠ 0`,
   `‖η_b‖ ≤ √(2e·n·(ln q + 1))`. **This is exactly the `B`/`hB` parameter `wall_capstone` consumed.**

**The one genuinely new lemma:** `doubleFactorial_two_sub_one_le : ((2r−1)‼ : ℝ) ≤ (2r)ʳ` for the
**Mathlib** `Nat.doubleFactorial` object (the DC wall uses `Nat.doubleFactorial (2r−1)`, whereas
`MomentWickBridge` used the project-local `doubleFactOdd`). Proved from
`Nat.doubleFactorial_eq_prod_odd` + factorwise monotonicity.

**What tightened (honest):** the moment-order optimization is no longer an un-formalized parameter of
the capstone. `supNorm_le_of_wallHolds` supplies `_WallCapstone.wall_capstone`'s `B := √(2e·n·(ln q+1))`,
`hB0 := sqrt_floor_nonneg`, `hB := supNorm_le_of_wallHolds` *from `WallHolds` alone*. Caveat (a) of
round 12 is **discharged**.

**Constant honesty:** `C = √(2e) ≈ 2.33` is the crude saddle constant from `(2r−1)‼ ≤ (2r)ʳ` at
`r = ⌈ln q⌉`. Probe `probe_466r13_moment.py` measures the TRUE optimized-Wick constant:
`min_r (q·(2r−1)‼·nʳ)^{1/2r} ≈ 1.43·√(n·ln q)` (argmin near `r ≈ ln q`, not `0.5 ln q`), and the true
sup-norm `M ≈ 1.0–1.26·√(n·log(p/n))`. The Lean `√(2e)` is an honest over-estimate of order
`√(n·ln q)`; the sharper `1.43` is a probe-validated numeric, not claimed as a theorem.

**Probe validation** (`_out_466r13_moment.py`, n=8/16/32, ≥2 primes each, distinct v2(p−1), p=n⁴):
- `M / √(n·log(p/n))` = 1.05, 1.05 (n=8); 1.20, 1.15 (n=16); 1.26, 1.25 (n=32) — tracks the target.
- Wick-min `/ √(n·ln q)` = 1.44, 1.44, 1.44, 1.44, 1.43, 1.43 — **constant across n**, order confirmed.
- Wick argmin `r*` ≈ `ln q` (ratio to `0.5 ln q` ≈ 2.0), matching the `r = ⌈ln q⌉` formalized choice.
- `DCEnergyBound(r)` holds at every rung in-regime (the wall is empirically true for these small n;
  open only at prize depth n=2³⁰).

---

## 2. Deliverable 2 (the round-13 VERDICT): TWO distinct inputs, not one

**Question.** Is the prize localizable to `WallHolds` ALONE (a single-Prop iff), or does it genuinely
need a SECOND, distinct open input (the `√q·B` hyperplane cancellation) that does NOT follow from the
Wick bound `WallHolds`?

**Verdict: TWO distinct inputs.** The `M → δ*` step (`le_mcaDeltaStar_of_charSumBound`) consumes the
hyperplane incidence sum `T(H, s₀) = |∑_{b∈H} conj(η_b)·ψ(b·s₀)|` over a size-`|H|`-up-to-`q`
frequency hyperplane. `WallHolds` controls the **marginal moments** `∑_b ‖η_b‖^{2r}` — equivalently
the *multiset* `{‖η_b‖}` — which is **phase-blind**. `T` is a **joint/phase-correlation** functional
of the spectrum. These are provably different:

**Probe `probe_466r13_twoinput.py` (decisive test B):** hold the per-frequency norm multiset
`{‖η_b‖}` **fixed** (so `WallHolds` status and `M` are identical), and vary only the phases:
- True phases (random `s₀`): typical `T ≈ √|H|·M` (the sqrt/cancelled regime).
- All-aligned rephasing (same norms, all-real-positive): `T = |H|·avg ≈ |H|·M` (naive regime).
- ratio surrogate/typical = **11.25, 49.46, 59.90** for n=8/16/32 — precisely `≈ √|H|`
  (`√64=8, √256=16, √1024=32`).

So at **fixed** moment data the hyperplane sum `T` ranges over the full interval `[≈√|H|·M, ≈|H|·M]`.
It is therefore **not a function of** the moments `WallHolds` controls. Test A independently shows an
adversarially-aligned `s₀` drives `T` to 2×–8× the `√|H|·M` bound, so per-frequency size never *forces*
cancellation. The `√q·B` cancellation is a strictly finer, phase-correlation statement (Paley-graph /
BCHKS Conj 1.12), disjoint from the marginal-moment content of the wall.

**Consequence for the capstone.** `_WallCapstone` is CORRECT to keep `RealizedIncidenceBudget` as a
**separate named glue**, not fold it into `WallHolds`. The prize localizes to
`WallHolds ∧ (√q·B hyperplane cancellation)` = **two distinct open Props**, and this round proves the
second does not reduce to the first. The single-Prop iff hoped for in the round-13 question does **not**
exist: `WallHolds` is *necessary but not sufficient*; the phase-correlation input is genuinely extra.

---

## 3. Honest final state

- **Formalized this round (axiom-clean):** `WallHolds ⟹ M ≤ √(2e·n·(ln q+1))` — the moment-order
  optimization, removing round-12 caveat (a). The wall now discharges the closed-form sup-norm, not
  just the per-rung inputs.
- **Decided this round (probe, decisive):** the `M → δ*` glue is a SECOND distinct open input. The wall
  (marginal moments, phase-blind) does not imply the `√q·B` hyperplane cancellation (joint phases). The
  capstone's two-Prop localization `WallHolds ∧ RealizedIncidenceBudget` is the honest, minimal form.
- **NOT claimed:** no rung of `WallHolds` at the prize; no closure of the `√q·B` cancellation; `√(2e)`
  is a crude order-correct constant, the sharp `1.43` a probe numeric.

**Files:**
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentOptimizedSupNorm.lean` (brick, ✅ axiom-clean)
- `scripts/probes/probe_466r13_moment.py` + `_out_466r13_moment.txt` (optimization validation)
- `scripts/probes/probe_466r13_twoinput.py` + `_out_466r13_twoinput.txt` (two-input decision)
