# Issue #464: homological vanishing transfer gate

Date: 2026-06-26.

Status: **new-tool critique and transfer gate**, not a delta-star proof.

External sources:
- Issue source: <https://github.com/lalalune/ArkLib/issues/464>.
- Paper: arXiv:2606.26440, "Optimal homological vanishing: cancellation of character
  sums and Patterson's conjecture over F_q[t]" <https://arxiv.org/abs/2606.26440>.

## Thesis

The 2026-06-26 paper sweep correctly treated arXiv:2606.26440 as a serious new tool family.
The paper proves explicit homological vanishing lines for braid-group homology objects
`H_i(B_n, V^{⊗n})`, and its abstract says these vanishing lines give power-saving cancellation for
arithmetic sums over function fields.  It also applies the method to higher-order Gauss sums over
function fields and to near square-root cancellation for almost all character sums in Galois
extensions.

That is real machinery.  The criticism is narrower: it is not yet a plain-RS floor proof.

For issue #464, the statistic is prime-field and adversarial:

```text
M(p) = max_b |Σ_{x in μ_n} e_p(bx)|,
W_r(p),
or the high-depth DC-subtracted energy at p ≡ 1 mod n.
```

The homological theorem lives in an auxiliary model: function-field sums, braid-group/configuration
homology, or a fixed family of arithmetic sums with its own parameter.  To affect the prize, it must
produce a pointwise comparison from each prime-field prize instance into that model at the same
growing depth `r ≈ log p`.

## Critique Of The Earlier Optimistic Essay

The earlier impulse was:

```text
homological vanishing gives power saving over F_q[t]
=> use it to control the char-p wraparound surplus
=> prove the floor.
```

The weak point is the middle arrow.  Existing ArkLib cohomological gates already explain why fixed
AG/cohomological control does not close the plain-RS wall:

```text
_FrontierSwanConductor.lean
_JacobiFermatCohomology.lean
_CreateCorrelationLFunction.lean
_EquivariantDescentWeightDropREFUTED.lean
```

They identify the same failure in several languages:

```text
fixed-order Betti/Deligne/convexity control is field-scale or conductor-scale;
the prize needs growing-order, subgroup-scale, worst-case cancellation;
finite μ_n descent does not drop cohomological weight;
the missing theorem is a genuine subconvex/growing-order comparison, not another restatement.
```

arXiv:2606.26440 may be the right kind of new mathematics, because it is explicitly about optimal
homological vanishing and arithmetic cancellation.  But for plain RS it still needs a transfer
theorem of the form:

```text
for every prize prime p and prize depth r(p),
  prime-field wraparound statistic at p
    <= homological/function-field statistic at model(p, r(p)),
and the homological bound is uniform at that growing depth.
```

Without that, the function-field theorem remains evidence and a possible blueprint, not a floor
certificate.

## Lean Surface

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D0HomologicalVanishingTransferGate.lean
```

New declarations:

```lean
prime_bound_of_homological_transfer
fixed_depth_bound_transfers_on_matching_schedule
fixed_depth_bound_does_not_control_other_depths
uncoupled_homological_bound_does_not_bound_primes
convexity_envelope_compatible_with_target_failure
```

The positive transfer is deliberately simple: if a pullback from prize primes into the homological
model exists, and the prime statistic is pointwise bounded by the pulled-back homological statistic,
then a uniform homological bound transfers.

The no-go parts are the important guardrails:

```text
bounded auxiliary model + no comparison    is compatible with an arbitrary prime spike;
fixed-depth model bound + growing schedule is compatible with a spike at the next depth;
convexity/Betti envelope <= B              is compatible with failing every smaller target T < B.
```

## What A Winning Homological Tool Would Look Like

A useful next theorem is not "there exists a vanishing line" in isolation.  It must be
something like:

```text
HomologicalPrimeComparison(n, p, r):
  W_r^prime(p, μ_n) <= H_r^hom(model(n,p))

UniformGrowingDepthVanishing(n, p, r≈log p):
  H_r^hom(model(n,p)) <= Wick/slack prize budget
```

The first line is the transfer.  The second line is the uniform-in-growing-order cancellation.
Both are load-bearing.

## Verdict

The homological lead survives only as a sharpened open input.  It is a plausible place where new
mathematics could live, especially if the braid-group vanishing line can be made to see the
specific dyadic prime-field wraparound statistic.  But the current paper does not by itself supply
the pointwise prime-field comparison or the growing-depth uniformity needed for plain RS.

This pass therefore converts the lead into an exact proof obligation and prevents a false closure:

```text
homological vanishing + transfer + growing-depth budget fit => possible floor proof;
homological vanishing alone                          => no implication for the prime-field floor.
```
