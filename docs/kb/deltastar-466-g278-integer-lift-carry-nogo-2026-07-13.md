# #466 G278: integer-lift carry symmetry and two-block insufficiency

Date: 2026-07-13

Branch: `research/proximity-prize` only, per #499

Status: axiom-clean structural lemma plus exact calibrated no-go, not prize closure

## Question

G268 proved that the complete characteristic-zero antipodal alignment floor is far below the two
production gates. The missing relation mass must therefore be genuinely characteristic-`p`.
Can the missing mass be localized by the ordinary integer carry of the modular relation?

For the order-`n` dyadic subgroup `G <= F_p^*`, use canonical representatives in
`{1,...,p-1}`. For `|A|=r`, `|B|=r-1`, define

```text
2y + sum(B) - z - sum(A) = k p
J_{r,k} = number of such relations
J_r = sum_k J_{r,k}
A_r = p J_r - B_r
B_r = n^2 C(n,r) C(n,r-1).
```

The gate is `A_r>0`, equivalently

```text
J_r >= need_r := floor(B_r/p)+1.
```

This is a direct characteristic-`p` decomposition of the actual weighted relation count. It does
not pass through moments, support size, primitive weighting, orbit counts, sparse norms, or a line
list wrapper.

## Exact structural facts

### Carry negation symmetry

Negate every relation variable in `F_p`, represented by `x -> p-x`. The total signed coefficient is

```text
2 + (r-1) - 1 - r = 0.
```

Therefore the integer numerator changes sign exactly:

```text
2(p-y) + ((r-1)p-sum(B)) - (p-z) - (rp-sum(A))
  = -(2y+sum(B)-z-sum(A)).
```

This is a bijection on the relation set, so

```text
J_{r,k} = J_{r,-k}.
```

A one-sided carry can never supply a signed bias. Only symmetric carry shells are intrinsic to this
split.

Lean: `liftNumerator_negated`, `carry_negates`.

### Every lawful antipodal packet has carry zero

For one antipodal pair represented by `x` and `p-x`, equal folded coefficients contribute

```text
c*x + c*(p-x) = c*p.
```

Summing all pairs gives `p*sum c`. The adjacent-rank relation has total coefficient sum zero, hence
every characteristic-zero antipodal packet has exact integer carry zero.

Thus:

```text
J_{r,0} = J_r^lawful + E_{r,0}
Sum_{k != 0} J_{r,k} = E_{r,!=0}.
```

Every nonzero carry is genuine characteristic-`p` wraparound, but the converse is false: carry zero
also contains a potentially large finite-characteristic residual `E_{r,0}`.

Lean: `antipodalLift_eq_mul_sum`, `lawful_antipodal_carry_zero`.

## Exact probe

Artifact: `scripts/probes/g278_integer_lift_carry_exact.py`.

Every reported count is an exact integer:

1. integer subset-sum profiles are computed by `UInt64` dynamic programming;
2. only the needed exact difference coefficients are computed, using `UInt64` dot products;
3. each dot product is asserted below `2^64`, so there is no wraparound;
4. `sum_k J_{r,k}` is independently checked against a modular subset-sum computation of `J_r`;
5. `J_{r,k}=J_{r,-k}` is hard-asserted in every cell.

No FFT, floating-point sign decision, or probabilistic test is used.

### Same-cell two-rank positive witness

At `(n,p)=(16,433)`, both live gates are positive, but neither carry block is individually
sufficient.

Rank 5:

```text
A_5 = +3,425,440
carry = {-3:1185, -2:105117, -1:1057270, 0:2380856,
          1:1057270, 2:105117, 3:1185}
J_0 = 2,380,856 < need = 4,700,090
J_lawful = 321,216
E_{!=0} = 2,327,144 < residualNeed = 4,378,874
J_0 + E_{!=0} = 4,708,000 >= need.
```

Rank 6:

```text
A_6 = +52,032
carry = {-3:8741, -2:531582, -1:4773523, 0:10052820,
          1:4773523, 2:531582, 3:8741}
J_0 = 10,052,820 < need = 20,680,392
J_lawful = 1,064,448
E_{!=0} = 10,627,692 < residualNeed = 19,615,944
J_0 + E_{!=0} = 20,680,512 >= need.
```

So the positive gate at each live rank needs both the visibly wrapped block and the hidden
zero-carry characteristic-`p` residual. This is not a rank-five island.

Lean: `p433_rank5_requires_both`, `p433_rank6_requires_both`,
`both_live_ranks_require_both_blocks`, and the two non-certification theorems.

### Cross-scale exact census

The probe also checks negative controls and the G268 late split-sign cell:

- `(16,577,r=5,6)`: both gates negative;
- `(32,3617,r=5,6)`: both gates negative;
- `(32,70753,r=5)`: positive;
- `(32,70753,r=6)`: negative.

In all eight rank-5/rank-6 cells:

```text
J_0 < need
E_{!=0} < residualNeed.
```

At the decisive late cell `(32,70753,5)`:

```text
A_5 = +132,970,510,400
J_lawful = 20,115,200
J_0 = 47,433,610
E_{0} = 27,318,410
E_{!=0} = 59,250,870
residualNeed = 84,689,918
E_{!=0}/residualNeed = 0.699621294.
```

Even all nonzero carries together supply only about 70% of the exact residual requirement. The
zero-carry characteristic-`p` residual is essential.

Across the broader exploratory 28-cell census at `n in {8,16,32}`, the ratio
`E_{!=0}/residualNeed` lies approximately in `0.53...0.86` at both positive and negative cells.
There is no observed one-block threshold law.

## Asymptotic calibration

A useful random-lift baseline explains why the zero-carry residual should remain a constant-order
piece rather than disappear at larger `n`. If the `r+1` positive and `r+1` negative representatives
were independent uniform variables on `[0,1]`, the carry weight at `k` would be

```text
pi_{r,k} = Eulerian(2r+1, r+k) / (2r+1)!.
```

This is the density of a sum of `2r+2` independent uniforms at the integer `r+1+k`.
Consequently:

```text
r=5: pi_0 = 0.393925565...,  sum_{k!=0} pi_k = 0.606074435...
r=6: pi_0 = 0.365370869...,  sum_{k!=0} pi_k = 0.634629131...
```

So even ideal equidistribution predicts that carry zero contains 36-39% of the finite-characteristic
bulk. The exact late cell is compatible with that scale (`J_0/J = 0.4446` at rank 5 and `0.3624` at
rank 6), though no random model is used in the theorem or probe.

Making this baseline rigorous for a thin multiplicative subgroup means proving that its
`2r+2`-variable weighted relation points equidistribute among integer slabs. Fourier expansion of
those slab indicators gives incomplete subgroup/interval exponential sums. This is not a free
geometry-of-numbers estimate.

## Literature and FS15-FS18 integration

- Freiman rectification transfers modular additive relations to integer relations only under
  hypotheses such as small doubling and containment/modeling in a short interval. A thin
  multiplicative subgroup at the sponsors has no such proved rectification hypothesis.
- Di Benedetto, Garaev, Garcia, Gonzalez-Sanchez, Shparlinski, and Trujillo,
  *New estimates for exponential sums over multiplicative subgroups and intervals in prime fields*
  (arXiv:2003.06165), prove a power saving for `|G|>p^(1/4)`. The sponsor scale is
  `|G| approximately p^(1/5.27)`, below that range. Even inside its range the exponent
  `31/2880` is far from the square-root-scale signed control needed here.
- Lam-Leung's characteristic-`p` vanishing-sum theory explains why the non-antipodal mass is genuine
  finite-characteristic kernel mass, but it does not distribute that mass among carries or lower
  bound `E_{r,0}`.
- FS15 gives Wick control only on its depth-specific good-prime set. FS16 proves the sharp
  `(2r)^(n/2)` resultant envelope but does not select either sponsor. FS17 unions finitely many
  depths without repairing the logarithmic-depth quantifier. FS18 completes the characteristic-zero
  pairing taxonomy only on that good set. G64/G262/G268 already force the sponsor to use the
  characteristic-`p` residual that this note splits.

## Binding inequality and verdict

The exact gate is

```text
E_{r,0} + E_{r,!=0} >= residualNeed.
```

A theorem proving only `E_{r,!=0} >= residualNeed` would be a genuinely weaker sufficient mechanism,
but the positive rank-5 and rank-6 witnesses refute that mechanism. A theorem proving only
`J_{r,0} >= need` is likewise refuted. Combining independent lower bounds on both blocks remains
logically possible, but the missing zero-carry estimate is an incomplete-subgroup/interval count on
the same thin sponsor relation variety. No existing rectification or explicit subgroup-interval
bound reaches its regime or constant.

**Verdict:** the naive integer-carry localization route is dead. The strongest proper carry block,
all `k!=0` relations together, is insufficient even when the actual gate is positive at both live
ranks. Characteristic-`p` wraparound is not synonymous with a nonzero integer carry. The minimal
surviving object remains the full row-labelled weighted kernel relation, equivalently the full signed
sponsor covariance. CORE OPEN / ON-BGK.
