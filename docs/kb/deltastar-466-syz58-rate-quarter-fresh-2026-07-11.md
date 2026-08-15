# δ* #466 — SYZ58: curve (ℓ>2) events are out of scope for the rate-1/4 prize ceiling (2026-07-11)

## Question

Fresh angle on the rate-1/4 ceiling: circumvent the SYZ5 integer-`D` no-go (floor `1/2 > 43/96`)
by moving from the affine-line pair event to the higher-degree **curve / power-generator event**
`mcaEventCurve` at `ℓ > 2`. Its degree-`(ℓ−1)` pencil conditions in `γ` donate `(ℓ−1)` bad scalars
per degenerate non-core point, so the yield scales with `ℓ` while the rank cost does not — which
should dissolve the non-integer `D = 7/3` crossing that pins the SYZ5 floor.

**Angle 1 (curve events) requires an in-scope check FIRST. Verdict: OUT OF SCOPE.**

## Scope audit (the decisive finding)

The prize threshold is
`ProximityGap.MCAThresholdLedger.mcaDeltaStar C ε* = sSup {δ ≤ 1 | epsMCA C δ ≤ ε*}`
(`MCAThresholdLedger.lean:86`). `epsMCA` is the **`Fin 2` affine-line** error `u₀ + γ·u₁`.

The curve / power-generator event is a genuinely **distinct** error function:

- `ProximityGap.epsMCACurve C ℓ δ` (`MCACurveEvent.lean:63`), equivalently
  `ProximityGap.Jo26Gen.epsMCAGen` at the *power* generator
  (`Jo26GeneratorMCA.epsMCAGen_powGen_eq_epsMCAP`, `epsMCAGen_val_eq_epsMCACurve`).
- It coincides with `epsMCA` **only at `ℓ = 2`**: `epsMCACurve_two_eq_epsMCA`
  (`MCACurveEvent.lean:93`), `epsMCAGen_pairGen_eq_epsMCA` (`Jo26GeneratorMCA.lean:636`). For
  `ℓ > 2` it is a strict extension.
- **No threshold object in the tree is a `sSup` over `epsMCACurve`.** Grep confirms: no
  `mcaDeltaStarCurve`, no `deltaStarP`, nothing. `mcaDeltaStar` — the object both the `43/96` pin
  (`_P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_le_common_delta`) and the `3/8` floor
  (`_P1RateQuarterOperationalBracket.threeEighths_le_rateQuarter_mcaDeltaStar`) bound — is `sSup`
  over `epsMCA` = `epsMCAGen` at the *pair* generator, exclusively.

So inflating `epsMCACurve` at radius `< 43/96` says nothing about `epsMCA` there, hence nothing
about `mcaDeltaStar`.

## The arithmetic (correct — but on the wrong error function)

Replaying the SYZ9 channel-wall elimination with per-core yield `Y = ℓ − 1`:

```
budget-beat  B < D·Y·c ,   rank  D·(t−k) < n−k = R ,   c = n − t
⟹ (t−k)·B < Y·(n−k)·(n−t)                      [curveChannel_master, ℕ, axiom-clean]
⟹ radius floor  δ > (1−ρ)/(1 + Y·(1−ρ))
```

At `ρ = 1/4` (`1−ρ = 3/4`) the floor is `3/(4+3Y)`:

| ℓ | Y=ℓ−1 | floor 3/(4+3Y) |
|---|-------|----------------|
| 2 | 1 | 3/7 ≈ 0.4286 (SYZ9 real-`D` inf; SYZ5 integer-refines to 1/2) |
| 3 | 2 | 3/10 = 0.30 |
| 4 | 3 | 3/13 ≈ 0.2308 |

So the `D = 7/3` obstruction **genuinely dissolves**: the curve channel starves only below
`3/(4+3Y)`, already below `43/96 ≈ 0.4479` at `ℓ = 3`. The intuition in the angle is arithmetically
sound. It just targets `epsMCACurve`, not `epsMCA`.

## In-tree consistency wall (proves the two objects cannot be identified)

If the `ℓ = 3` curve channel *did* bound `mcaDeltaStar`, it would give `mcaDeltaStar ≤ 3/10`. But
`threeEighths_le_rateQuarter_mcaDeltaStar : 3/8 ≤ mcaDeltaStar` is already **unconditionally**
landed on the same `epsMCA`-defined object. Since `3/10 < 3/8`, a curve-channel bound on
`mcaDeltaStar` would contradict a proven theorem. Therefore the curve channel provably does **not**
bound the prize object — the extant `3/8` lower bracket forces `epsMCA` and `epsMCACurve` apart at
rate `1/4`. This is a *proof* of out-of-scope-ness, not a convention.

No back-transfer rescues it: padding a pair-bad stack `(u₀,u₁) ↦ (u₀,u₁,0,…,0)` gives a curve-bad
stack (`epsMCA ≤ epsMCACurve`), which only pushes the *curve* threshold below the prize threshold —
wrong direction. A genuine `ℓ>2` curve event with nonzero higher rows uses a degree-`(ℓ−1)`
combiner that is not an affine line, so it entails no pair event.

## What was landed

`Frontier/_SYZ58RateQuarterCurveEventScope.lean` (pure `ℕ`/`ℚ`, axiom-clean, no `sorry`):

- `curveChannel_master` — the `ℓ`-scaled SYZ9 elimination `m·B < Y·R·c` (axioms: `propext`,
  `Quot.sound` only — no `Classical.choice`).
- `rateQuarterCurveFloor Y = 3/(4+3Y)`; `_one = 3/7`, `_two = 3/10`.
- `rateQuarterCurveFloor_two_lt_ceiling` : `3/10 < 43/96 + 1/(3·2^30)` (obstruction dissolves).
- `rateQuarterCurveFloor_two_lt_goodFloor` : `3/10 < 3/8` (consistency wall ⇒ out of scope).
- `curve_event_out_of_scope_rateQuarter` — packaged verdict.

## Verdict

Curve/generator events (`ℓ>2`) are **out of scope** for the sponsor's rate-1/4 ceiling object
`mcaDeltaStar` (a `sSup` over the `Fin 2` pair event `epsMCA`). The higher-degree pencil yield
dissolves the SYZ5 integer-`D` floor, but only for the distinct error `epsMCACurve` that the prize
does not consume. **No new production ceiling below `43/96` follows.** The `43/96` pin and the `3/8`
floor stand unchanged. Angles 2 (two-radius stacking) and 3 (affine shifts) were not pursued —
angle 1 was to be resolved first, and it resolves to a hard scope barrier.

Barrier, not a pin. Consistent with SYZ5 (`_SYZ5RateQuarterChannelCeiling.lean`) and SYZ9
(`_SYZ9ChannelRankWall.lean`).
