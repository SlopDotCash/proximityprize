# Rate-quarter predecessor: the shared-fresh-coordinate residual is false at P1

## Status

Successor of the joint-witness bare-charge refutation
(`[rate-quarter-joint-witness-bare-charge]`, 2026-07-10).  That entry showed:
a known threshold joint-agreement set `J` forces every MCA event witness to
contain a fresh coordinate outside `J`, and any over-budget selected charge
puts **three distinct bad scalars on one shared fresh coordinate**.  This
note records the exact answer to "what does that configuration force for
Reed--Solomon codes".  Both its generic non-existence and the proposed
literal-P1 exclusion are **refuted**.

Formal kernels (no `sorry`, no declared axioms):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSharedFreshCoordinate.lean
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSharedFreshTripleRefuted.lean
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterCollinearMismatchCharge.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_shared_fresh_coordinate.py`
(deterministic; countermodel construction + 4481 pseudorandom pencil-law
checks + exact P1 arithmetic), and
`scripts/probes/probe_rate_quarter_p1_shared_fresh_triple_refutation.py`
(exact root-product ledger plus an `F_101`, `[32,8]` executable model).

## 1. Forced structure (proved, code-generic where possible)

Throughout: `C` a submodule code, witnesses `(S_j, p_j, γ_j)` meaning
`p_j ∈ C` and `p_j = u₀ + γ_j·u₁` on `S_j`, with `γ_j` pairwise distinct.

1. **Divided-difference pencil** (`pencilDir/pencilBase`,
   `pairJointAgreesOn_inter`): `w₁ = (γ₂−γ₁)⁻¹(p₂−p₁)`,
   `w₀ = p₁ − γ₁w₁` are codewords, `p_j = w₀ + γ_j w₁`, and
   `(w₀,w₁) = (u₀,u₁)` on `S₁ ∩ S₂`.  So every pair of distinct bad scalars
   produces a joint explanation on the pairwise intersection — at the P1
   predecessor of size at least `2T − N = 111,848,108`
   (`pairwise_inter_floor`).
2. **Witness incomparability** (`witness_not_subset`): `S₁ ⊆ S₂` is
   impossible when `S₁` carries the non-joint clause (the pencil would
   jointly explain on `S₁`).
3. **Distinct shared values** (`shared_values_distinct`): at a shared
   coordinate `i` with `u₁ i ≠ 0`, the witness codeword values
   `u₀(i)+γ_j u₁(i)` are pairwise distinct.
4. **Absorption dichotomy** (`pencil_absorption`, `predecessor_sep`): if
   `k ≤ |S₁ ∩ S₂ ∩ J|` then the pencil **equals** the known joint pair
   `(q₀,q₁)`, so every shared coordinate is absorbed into the *maximal*
   joint-agreement set.  At P1 this premise is **not forced**:
   `3T ≤ 2N + k − 1` (`absorption_not_forced`; indeed `3T − 2N < 0`).
5. **Collinear boost** (`collinear_agrees_on_pairCover`,
   `collinear_cover_floor`, `card_three_le_card_add_two_mul_pairCover`): if
   the three witness codewords lie on one pencil, that pencil agrees with
   the stack on the whole two-cover region `U` (union of pairwise
   intersections), and `3T ≤ N + 2|U|` gives
   `|U| ≥ ⌈(3T−N)/2⌉ = 352,321,537 ≥ k = 2^28`.  A collinear shared triple
   therefore forces a single joint pencil with **beyond-unique-decoding**
   agreement — yet `352,321,537 < T = 592,794,966`, so this still does not
   contradict the non-joint clauses.

## 2. Realizability countermodel (refutation of bare impossibility)

`RS[8,2]` over `F_11`, domain `0..7`, radius `1/2`, threshold `4`:

```text
u0 = [1,3,5,7,1,10,2,3]    u1 = [3,4,5,6,1,8,10,7]
J = {0,1,2,3} explained by (q0,q1) = (1+2X, 3+X)
gamma = 1,2,3 with witness codewords 4+5X, 10+X, 3+3X
witnesses {0,4,5,6}, {1,4,5,7}, {2,4,6,7}, shared fresh coordinate 4
```

Kernel-checked (`sharedFreshTriple_realizable`): all three scalars are
literal `mcaEvent`s; `J` is jointly explained; **no** joint pair explains
`J ∪ {4}` (so `4` is outside the maximal joint set of every explaining
pair); the triple is non-collinear.  Non-jointness is proved algebraically
(degree-`<2` interpolant pinned on a 2-point core + fresh mismatch), not by
code enumeration.

Consequence: no code-generic (even RS-generic, any parameters) impossibility
proof of the non-absorbed shared-fresh triple exists.  Any proof of the P1
cap through this branch must use the literal predecessor counting.

## 3. Literal P1 root-product refutation

`SharedFreshTripleFree` is false for **every** injective literal-P1 domain.
Let `J` be the first `T = 592,794,966` coordinates, let `C` be its complement,
and let `B` be the first

```text
2T - N - 1 = 111,848,107
```

coordinates.  With `f_B = product_{b in B}(X-dom(b))`, set

```text
q0 = X*f_B,  q1 = f_B.
```

The received pair is `(eval q0, eval q1)` on `J` and zero on `C`.  For every
`x in J \ B`, the zero codeword at scalar `gamma_x = -dom(x)` agrees on

```text
S_x = C union B union {x},   |S_x| = T.
```

Any joint explaining pair on `S_x` vanishes on the `|C| = 480,946,858 >= k`
complement coordinates, so Reed--Solomon uniqueness makes it the zero pair.
But `q1(x) != 0`, contradicting joint agreement at `x`.  Every `S_x` contains
the same fresh coordinate, while injectivity of `dom` makes all `gamma_x`
distinct.  The resulting shared-fresh fiber has exact size

```text
|J \ B| = N - T + 1 = 480,946,859.
```

The theorem `not_sharedFreshTripleFree` kernel-checks the literal refutation.
The earlier consumer `badFamily_card_le_N_of_sharedFreshTripleFree` remains a
valid implication, but its premise is unavailable on every P1 domain.

## 4. Correct collinear statement and surviving target

The counterexample is fully collinear: all selected decoded codewords are
zero.  Collinearity is nevertheless globally safe.  For a family lying on a
fixed codeword pencil `(w0,w1)`, nonjointness supplies a witness coordinate
where `(w0,w1)` differs from `(u0,u1)`.  At that coordinate

```text
w0(x) + gamma*w1(x) = u0(x) + gamma*u1(x)
```

determines `gamma` uniquely.  The theorem
`card_le_domain_of_collinear_witnesses` chooses one such mismatch per scalar
and proves the charge injective, hence every fully collinear family has size
at most `N`.

The fixed-joint-witness branch therefore returns to genuinely
**non-collinear/global** structure.  Pairwise pencils agree on at least
`2T-N`, but the plain Johnson denominator there is negative.  A closure must
control how many different pencil lines can coexist, or prove the simultaneous
degree-restricted divided-difference rank statement; excluding a local
shared-fresh triple is no longer a valid target.

## 5. What this is not

Not a proof of the predecessor uniform count, not a delta-star pin, and not
a refutation of `#bad ≤ N`.  The bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` is unchanged; the upper
endpoint's exactness still rests on the uniform predecessor residual.  This
result removes one proposed sufficient condition and supplies the correct
all-collinear cap; it does not prove or refute `#bad ≤ N`.
