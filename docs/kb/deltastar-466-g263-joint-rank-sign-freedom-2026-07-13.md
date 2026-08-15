# G263: the joint two-rank centered covariance gate is sign-free

Date: 2026-07-13
Issue: #466
Branch: `research/proximity-prize` only (#499)

## Result

After G252–G262 the single surviving CORE face is the DC-subtracted (centered) row-labelled
covariance gate, required (G214/G225) to hold **independently at rank five and rank six**. For a
weighted kernel `W` and rank weight `R_r` on the cyclic quotient `Z/m`,

```text
Cov_r(W) = m * sum_x W[x] R_r[x] - (sum_x W[x])(sum_x R_r[x])
         = Re sum_{chi != 1} What(chi) * conj(Rhat_r(chi)).
```

Subtracting `(sum W)(sum R)` removes exactly the principal Fourier product, so `Cov_r` sees only
the nonprincipal modes. Equivalently `Cov_r(W) = <W, f_r>` with the **centered per-class
functional** `f_r[x] = m*R_r[x] - sum_y R_r[y]`, which satisfies `sum_x f_r[x] = 0`.

The open hope after G262 and the Fable referee was that the **joint** constraint (one and the same
`W` must satisfy the gate at both ranks) could restrict the adversary enough to give a
sign/positivity/norm certificate the leverage it provably lacks at a single rank (G205
single-depth sign no-go; G253/G258 single-rank centering no-go).

**G263 closes that hope.** The map `W |-> (Cov_5 W, Cov_6 W) = (<W,f5>, <W,f6>)` is `Z`-linear.
When `f5, f6` are linearly independent (rank two), the nonnegative-integer kernel cone maps onto
all four open sign quadrants `(sign Cov_5, sign Cov_6) in {(+,+),(+,-),(-,+),(-,-)}`. Hence the
joint two-rank gate is exactly as unforced as two independent single-rank gates: **no cross-rank
coupling leverage exists.**

## Exact minimal certificate (`m = 5`)

Rank weights `R5 = (0,1,0,1,2)`, `R6 = (1,0,2,0,1)`. Centered functionals

```text
f5 = (-4, 1, -4, 1, 6),   f6 = (1, -4, 6, -4, 1),   sum f5 = sum f6 = 0.
```

They are rank-two independent (the `2x2` minor `det[[f5_0,f6_0],[f5_1,f6_1]] = (-4)(-4)-(1)(1)=15`),
and independent of the all-ones principal mode. Four nonnegative-integer weighted kernels — three
of them **single-class indicators** — realize all four sign patterns:

```text
W++ = e_4          -> cov5 = +6, cov6 = +1
W+- = e_3          -> cov5 = +1, cov6 = -4
W-+ = e_2          -> cov5 = -4, cov6 = +6
W-- = e_0 + e_3    -> cov5 = -3, cov6 = -3.
```

All entries are in `{0,1}` (genuine sparse, prize-thin, nonnegative kernels, not signed vectors).
A bounded-support (`support <= 4`) stress at `m in {16,17}` with non-constant rank functionals
still realizes all four quadrants, so sparsity does not restore forcing.

## Why new (not a G253/G258/G262 wrapper)

- G205 is a single-depth sign no-go; G253/G254/G255/G258 are single-rank centering / positivity /
  support / marginal-phase no-gos. None of them fence the **joint** gate: the possibility remained
  that the r=5 and r=6 gates, taken together, over-constrain one `W`.
- G262 (with the Fable referee) proved the sponsor super-Wick mass excess is annihilated by
  centering — a total-mass no-go. G263 is orthogonal: it shows the *centered* joint gate itself is
  sign-free because the two centered functionals are independent, so the joint image is the whole
  plane.
- The binding mechanism is a genuinely new invariant: **rank-two independence of the two centered
  per-class functionals**, which is what makes the nonnegative cone surject onto all four sign
  quadrants. This is structural, stable across the surrogate, and not a numerical estimate.

## Scope (honest)

Route no-go on the joint two-rank gate, not a sponsor-prime estimate and not prize closure. The
surviving admissible route remains a genuinely row-labelled sponsor Jacobi/cyclotomic covariance
estimate proved directly against the row label at **each** rank; combining rank five and rank six
supplies no additional sign-forcing structure. CORE OPEN / ON-BGK.

## Formal payload

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G263JointRankSignFreedom.lean`:
  `centeredCov`, `centeredFunctional`, `centeredCov_eq_dot` (the covariance is the pairing against
  the centered functional), `sum_centeredFunctional_eq_zero` (centering), `centeredCov_add_const`
  (constant-offset invariance — total-mass carries zero gate information),
  `centeredFunctional_R5/R6`, `centeredFunctionals_independent` (`minor = 15`),
  `centeredFunctionals_lin_indep`, the four witnesses `cov_pp/pm/mp/mm`, `kernels_nonneg`, and the
  packaged `joint_rank_sign_freedom`.
  Axioms `[propext, Classical.choice, Quot.sound]` on all; no `sorry`, no `native_decide`.
- Self-contained probe: `scripts/probes/g263_joint_rank_sign_freedom_probe.py`.
