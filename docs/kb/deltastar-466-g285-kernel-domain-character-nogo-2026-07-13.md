---
id: deltastar-466-g285-kernel-domain-character-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, weighted-kernel, row-labelled, characters, Jacobi-sums, no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G285: low-order kernel-domain characters do not carry the CORE sign

## One-line

Fourier analysis on the weighted-kernel input `u` gives genuinely row-labelled, predeclared odd
normals, but the canonical real order-two and order-four normals both mismatch the CORE sign in both
directions on exact subgroup cells, and at an injective-kernel prime they remain positive while the
adjacent-rank gate changes sign.

## Exact kernel decomposition

For `G=<zeta>` of order `n`, write `u=z/y`. Then

```text
2y-z = y(2-u)
```

and therefore, with the zero class counted with multiplicity,

```text
W_G(t) = sum_{j=0}^{n-1} 1_{(2-zeta^j)G}(t).
```

For the adjacent-rank profile `R_r`, define

```text
H_j = sum_{t in (2-zeta^j)G} R_r(t).
```

The exact gate and the first two canonical real character normals on the kernel input are

```text
A_r = p sum_j H_j - n^2 sum_t R_r(t),
K_2 = p sum_j (-1)^j H_j,
K_4 = p sum_j cos(pi*j/2) H_j.
```

These are not G282 carry-histogram Ramanujan sums and not G272 quotient-output character
truncations. The weights are placed on `u` before the nonlinear row label `u -> (2-u)G`, so they are
direct weighted-kernel-relation observables. `K_2` is canonical because the order-two character is
unique. `Re K_4` is canonical up to subgroup-generator inversion because inversion conjugates the
order-four pair and fixes its real part.

## Exact sign refutation

The probe reconstructs `G`, `W_G`, the subset-sum rows, and every `H_j` with integer arithmetic. It
asserts the class-decomposition identity before reading any normal. Exact witnesses:

```text
(n,p,r)       CORE A_r       K_2          Re K_4
(16,97,5)     -6,285,008     +6,125,744   +6,675,152
(16,113,5)    +1,727,120       -309,168     -341,712
```

Thus positivity of either or both normals does not imply the gate, and negativity does not track the
gate in the reverse direction. The complete 96-cell census gives:

```text
K_2: nonzero 96/96, sign agreement 55/96, all four (sign A, sign K_2) quadrants.
K_4: nonzero 94/96, sign agreement 52/94, both mismatch polarities.
```

At the injective-kernel cell `(n,p)=(16,2593)`:

```text
rank 5: A_5=+24,201,296, K_2=+184,663,088, Re K_4=+217,148,192
rank 6: A_6=-13,779,712, K_2=+495,947,552, Re K_4=+627,671,952.
```

So the normals do not repair the simultaneous-rank problem either. The exact agree-then-fail census
also finds `(16,881)`, `(16,1153)`, `(16,2593)`, and `(32,70753)` for both normals.

## Literature and asymptotic integration

Let `theta` be a character of `G` and extend it to a character `Theta` of `F_p^*`. For an outer
quotient character `chi`, the twisted kernel coefficient is

```text
S_{theta,chi} = sum_{u in G} theta(u) conj(chi)(2-u).
```

Using `1_G(u)=m^{-1} sum_{lambda|G=1} lambda(u)`, `m=(p-1)/n`, and `u=2x`, this is a full
`m`-term Jacobi average

```text
S_{theta,chi} = m^{-1} sum_lambda unit(theta,lambda,chi)
                              * J(Theta*lambda, conj(chi)).
```

This is the G228 quotient-Jacobi fanout on the multiplicative-character coset `Theta*H`, rather than
a bounded subfamily of the untwisted coset `H`. Classical Weil purity gives magnitude `sqrt(p)` for
every nonexceptional Jacobi term, but no archimedean sign and no comparison between those two cosets.
G233 supplies the binding asymptotic for the actual untwisted CORE factor: any Jacobi-column
reconstruction capturing half its sponsor mass needs coefficient `L2` mass at least `(m-n)/(4n)`,
namely `2^96` at P1 and `2^97` at P2 for unit weights. The twist does not evade that floor by
compression because it does not reconstruct the target factor at all. A useful transfer from the
twisted normal to CORE would need a new full-family cross-coset phase correlation, precisely the kind
of growing-order archimedean input absent from Weil/Hasse-Davenport. Low input conductor therefore
does not mean low Jacobi complexity or a weaker binding inequality.

FS15-FS18 remain fully respected. Their resultant/Wick ladder is almost-all-prime and fixed-depth;
this input-character transform neither selects the explicit sponsor prime nor changes the
`r ~ log p` exceptional-set inequality.

## Formal payload and scope

`Frontier/_G285KernelDomainCharacterNoGo.lean` defines the two normals and derives all recorded signs
from exact `H_j` lists, including the rank-five/rank-six split. The companion
`scripts/probes/g285_kernel_domain_character_probe.py` is the computation of record.

Closed: the two canonical lowest-order kernel-input character normals as odd sign certificates, and
the hope that their rank coupling repairs simultaneity.

Not closed: an independently justified full-family, row-labelled phase correlation. That remains the
sponsor Jacobi/BGK covariance itself. CORE remains OPEN / ON-BGK.
