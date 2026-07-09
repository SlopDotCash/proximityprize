# R349: antipodal orientation energy

## Candidate bridge

Write the negation-closed root subgroup as `H = A_eps union (-A_eps)`, where
`A_eps` chooses one orientation from every antipodal pair.  For every additive
frequency `b`,

`eta_H(b) = 2 Re(sum_{a in A_eps} e_p(ba))`.

Consequently `|eta_H(b)|^(2k) <= 4^k |sum_{a in A_eps} e_p(ba)|^(2k)` for
every orientation.  Averaging over orientations and then over `b` shows that
the following would imply the prize-scale moment estimate with only a factor
two after taking `2k`-th roots:

`E_eps E_k(A_eps) <= (2k-1)!! (n/2)^k` for `k` up to the logarithmic saddle.

Unlike a fixed-transversal argument, this target may exploit independent signs
without changing the real part that contains the original period.

## Exact probe

`scripts/probes/probe_r349_oriented_half_energy.py` enumerates every orientation
and computes all energies by exact integer convolution.  At depths `2..6`, the
orientation-averaged half-energy is below its Wick envelope in every tested
cell.  Representative ratios `average/Wick_half` are:

| `(p,n)` | `k=2` | `k=3` | `k=4` | `k=5` | `k=6` |
|---|---:|---:|---:|---:|---:|---:|
| `(521,8)` | .5833 | .2667 | .1010 | .03256 | .009095 |
| `(100049,8)` | .5833 | .2667 | .1010 | .03256 | .009092 |
| `(65537,16)` | .6250 | .3292 | .1545 | .06597 | .02592 |

The orientation dependence is zero through several low depths and remains
small when it first appears.  This is evidence, not a proof.

## Refutation of the generic B2 shortcut

Each transversal is plain combinatorial Sidon (`B_2`) whenever `H` is
Sidon-mod-negation.  That fact alone cannot prove the displayed Wick bound.
Take an integer `B_2` set of size `N` packed into an interval of length
`O(N^2)`, and embed it without wraparound in a much larger prime field.  Its
`k`-fold sums occupy only `O(kN^2)` values, so Cauchy gives

`E_k(A) >= N^(2k) / O(kN^2) = Omega(N^(2k-2)/k)`.

For growing `k` and `N`, this exceeds `(2k-1)!! N^k`.  Equivalently, a low
frequency sees the packed set almost in phase.  Thus the surviving R349 input
must use cyclotomic dispersion of the oriented transversals, not merely their
pair-sum uniqueness.  This also resolves the terminology trap between
combinatorial `B_2` sets and harmonic-analytic Sidon sets.

## Status

Open and prize-relevant.  The next proof target is an exact formula or upper
recurrence for the orientation average.  Expanding the average assigns a
parity constraint to the multiplicity of every antipodal pair in a relation;
the hope is that this removes enough characteristic-`p` wraparound relations
to prove a Wick recurrence even though no fixed transversal has such a known
bound.

## Adversarial audit: the original spike is a literal summand

The orientation average must not be advertised as an independent source of
randomness.  Write

`F_eps(b) = sum_j exp(2 pi i b eps_j a_j / p) = S(b) + i Y_eps(b)`.

Because changing the representative of an antipodal pair conjugates its
character value, `S(b) = eta_H(b)/2` is independent of `eps`.  Therefore

`E_eps |F_eps(b)|^(2k) = E_eps (S(b)^2 + Y_eps(b)^2)^k
                       >= |eta_H(b)|^(2k) / 4^k`.

The desired orientation-averaged Wick inequality does imply the prize bound,
but it already contains the original exceptional spike as its `Y=0` term.
Random orientation cannot average that spike away.  A proof still needs a
new arithmetic bound on the signed relation expansion; Khinchine or generic
`B_2` input alone is circular or false.  Thus R349 is a diagnostic coordinate
change, not yet a reduction to an easier theorem.

## Literature correction

The v3 dossier lists Chapman--Mudgal arXiv:2605.15434 among unrun
"anti-resonance" probes.  The paper is *Counting solutions to the quadratic
determinant equation*.  Its square-root error concerns integer solutions of
`x1*x2-x3*x4=h` in the boundary regime `h=N^2+O(N)`, using a Ramanujan-sum
symmetry.  It supplies no estimate for additive character sums over a thin
multiplicative subgroup and does not instantiate the R349 or CORE objects.
It should not remain on the live analytic queue without an additional,
explicit transfer theorem.
