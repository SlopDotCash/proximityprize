# G264: general joint-gate sign-freedom — the G263 no-go is r-uniform, not a fixed-depth island

Date: 2026-07-13
Issue: #466
Branch: `research/proximity-prize` only (#499)

## Result

G263 certified, at the single minimal cell `m = 5`, that the joint two-rank centered covariance gate
is sign-free: four explicit nonnegative-integer kernels realize all four sign quadrants of
`(Cov_5 W, Cov_6 W)`, with structural cause the linear independence (nonzero `2x2` minor) of the two
centered per-class functionals. G263 leaves the general mechanism asserted in prose but proved only
by four hand-picked witnesses at one cell.

G264 upgrades this to a **theorem for every cell and every rank pair**. For an arbitrary cyclic
length `m`, arbitrary integer weight profiles whose centered functionals `f, g : Z/m -> Z` are
zero-sum (the DC-subtraction property `sum_x f x = 0`, from `sum_centeredFunctional_eq_zero`), and
*any* coordinate pair `i != j` at which the minor `D = f i * g j - f j * g i` is nonzero, the
nonnegative-integer cone realizes **all four open sign quadrants** of `(<W,f>, <W,g>)`.

## Closed-form Cramer witness

For a target sign pair `(s, t)` in `{+-1}^2` set

```text
a = s*g j - t*f j,   b = t*f i - s*g i,   W = c*1 + a*e_i + b*e_j
```

with `c = max(0, -min(a,b,0))` a nonnegative offset keeping every entry `>= 0`. Because `f` and `g`
are zero-sum, the constant offset `c*1` contributes nothing (`covPairing_add_const`), and Cramer's
identity gives **exactly**

```text
<W,f> = a*f i + b*f j = s*D,      <W,g> = a*g i + b*g j = t*D.
```

Hence `sign <W,f> = s*sign D` and `sign <W,g> = t*sign D`, so ranging `(s, t)` over `{+-1}^2` hits
all four sign quadrants regardless of the sign of `D`. No `decide`, no fixed cell, no rank
restriction.

## Why it matters (r-uniform, thinness-relevant)

G263 was a single-cell countermodel. G264 shows the sign-freedom holds at *every* cell and *every*
rank pair for which the two centered rank functionals are independent. G64 already forces exactly
that independence at the two live sponsor ranks (`r = 5, 6`) at prize depth, so this is not a
fixed-depth island: the joint gate carries no cross-rank sign-forcing leverage at the actual prize
face. Combining the two ranks supplies zero additional structure over two independent single-rank
gates.

## What is proved (axiom-clean over Z, `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`)

- `covPairing_add_const`: constant-offset invariance against any zero-sum functional (general form of
  G263's `centeredCov_add_const`; total-mass / principal inflation carries zero gate information).
- `covPairing_indicator`, `covPairing_twoAtom`: the pairing algebra of single-support and two-atom
  kernels.
- `cramer_pairings`: the exact witness identity `<W,f> = s*D`, `<W,g> = t*D`.
- `joint_gate_sign_free_of_minor`: for every `(s, t)` a nonnegative-integer kernel realizes
  `(s*D, t*D)`.
- `joint_gate_all_quadrants`: all four open sign quadrants realized (sign normalized by `sign D`;
  `hD` guarantees each quadrant genuinely open).
- `g263_functionals_zero_sum`, `g263_recovered_from_general`: recover the landed G263 minimal cell
  (`m = 5`, minor `15`) from the general theorem, tying the r-uniform statement to the certified
  countermodel.
- `not_prizeClosure`: route status marker (axiom-free).

## Scope (honest)

Route no-go, an r-uniform strengthening of G263, not a sponsor-prime estimate and not prize closure.
The surviving admissible route is unchanged: a genuinely row-labelled sponsor Jacobi/cyclotomic
covariance proved directly against the row label at each rank. CORE OPEN / ON-BGK.

## Artifacts

Formal payload: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G264JointGateSignFreedomGeneral.lean`;
probe: `scripts/probes/g264_joint_gate_sign_freedom_general_probe.py`; DISPROOF entry:
`[466-G264-joint-gate-sign-freedom-general]`.
