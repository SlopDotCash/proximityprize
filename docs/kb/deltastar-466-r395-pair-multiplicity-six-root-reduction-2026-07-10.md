# Issue #466 R395: pair multiplicity four is a three-support exclusion

Date: 2026-07-10

R395 maps each ordered pair representation to its unordered two-element support. It proves:

```text
rep2(c) <= 2 * (# distinct pair supports representing c).
```

It also proves that two distinct supports representing the same sum are disjoint: sharing one root
forces the other root because both sums equal `c`. Therefore

```text
no nonzero c has three pair supports  =>  rep2(c) <= 4.
```

Failure is exactly three disjoint pair supports with one common nonzero sum. It is a six-root
configuration when all pairs are non-diagonal, and a five-root configuration when one support is
the singleton `{c/2}`. This is the arithmetic object whose absence was observed in 20,000 sequential
`n=128`, `p~n^4` prime cells. It is sharper than generic KSV Möbius coincidence, while remaining
genuinely new in the polynomial field-size regime.

## Correct resultant invariant

Fix one pair as base. The other two equal-sum equations give folded cyclotomic polynomials `f,g`.
The same primitive root modulo `p` is a common zero of `Phi_n,f,g`. Therefore the right arithmetic
certificate is the simultaneous ideal

```text
(Phi_n, f, g) intersect Z,
```

or an explicit integer Bezout certificate `A*f + B*g + C*Phi_n = D`, which forces `p | D`.
It is **not** enough to bound `gcd(Norm(f),Norm(g))`: norm divisibility may be witnessed at different
prime ideals over the same completely split prime. Exact experiments found this false shortcut in
practice (large equal norm gcds without a six-root fiber at one embedding). The next arithmetic
target is thus a polynomial-size simultaneous-ideal certificate for three disjoint pair supports.
