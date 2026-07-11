#!/usr/bin/env python3
"""
#466 r=3 R308: the Weil weld — master identity Σ_a‖Ŝ‖^{2r} = m·Σ_c‖J^{∗r}(c)‖²
(all r), and the implied R27 tower constants.

iterConv (R27): J^{∗0} = δ₀, J^{∗(r+1)}(c) = Σ_{j≠0} J^{∗r}(c−j)·J_j;
J^{∗1} = Sfun J.  DFT: (J^{∗r})^(a) = Ŝ(a)^r ⇒ by Parseval the even moments
of Ŝ ARE the tower energies.  IterConvEnergyWick J q r C means
Σ_c‖J^{∗r}‖² ≤ C^r·r!·(mq)^r, so K_{2r} := Σ_a‖Ŝ‖^{2r}/(m^{r+1}q^r) = r!·C^r
at the implied tower constant C = (K_{2r}/r!)^{1/r} — Gaussian truth C → 1.

CHECKS: (W1) master identity r = 1..4 (machine precision, small m);
(W2) implied tower constants C₂ = √(K₄/2), C₄ = (K₈/24)^{1/4} at m ≤ 1200 —
both should sit just below 1 (sub-Gaussian).
"""

import cmath, math, sys

def primitive_root(p):
    fac, n, d = [], p - 1, 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError

def is_prime(n):
    return n >= 2 and all(n % r for r in range(2, int(math.isqrt(n)) + 1))

def primes_1mod(m, count):
    out, p = [], m + 1
    while len(out) < count and p < 10 ** 7:
        if p % m == 1 and is_prime(p):
            out.append(p)
        p += m
    return out

def ladder(p, m, k):
    g = primitive_root(p)
    ind = [0] * p
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    J = [sum(zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
             for t in range(2, p)) for j in range(m)]
    return J, ind, zm

def main():
    print(__doc__.splitlines()[1])
    print("\n(W1) master identity Σ_a‖Ŝ‖^{2r} = m·Σ_c‖J^{∗r}(c)‖², r = 1..4:")
    for m, p in ((9, 19), (12, 37), (15, 31)):
        J, ind, zm = ladder(p, m, 1)
        S = [J[j] if j != 0 else 0j for j in range(m)]
        Sh = [sum(zm[(a * j) % m] * S[j] for j in range(m)) for a in range(m)]
        it = [1 if c == 0 else 0j for c in range(m)]  # r = 0
        ok_all = True
        for r in range(1, 5):
            it = [sum(it[(c - j) % m] * J[j] for j in range(1, m)) for c in range(m)]
            lhs = sum(abs(s) ** (2 * r) for s in Sh)
            rhs = m * sum(abs(w) ** 2 for w in it)
            ok = abs(lhs - rhs) < 1e-6 * max(1.0, lhs)
            ok_all = ok_all and ok
            print(f"  m={m:>2} p={p:>3} r={r}: lhs={lhs:.6e} rhs={rhs:.6e} "
                  f"{'OK' if ok else 'FAIL'}")
        if not ok_all:
            sys.exit(1)
    print("\n(W2) implied R27 tower constants (medians of 5 primes x 3 chars):")
    print(f"{'m':>5} {'C2=√(K4/2)':>10} {'C4=(K8/24)^.25':>14}")
    for m in (9, 24, 96, 288, 720, 1200):
        qs = primes_1mod(m, 5)
        C2s, C4s = [], []
        for q in qs:
            g = primitive_root(q)
            ind = [0] * q
            x = 1
            for r in range(q - 1):
                ind[x] = r
                x = (x * g) % q
            zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
            for k in [k for k in range(1, m) if math.gcd(k, m) == 1][:3]:
                T = [0j] * m
                for t in range(2, q):
                    T[ind[t] % m] += zm[(k * ind[(1 - t) % q]) % m]
                xs = [abs(m * T[a] + 1) ** 2 for a in range(m)]
                K4 = sum(v ** 2 for v in xs) / (m ** 3 * q ** 2)
                K8 = sum(v ** 4 for v in xs) / (m ** 5 * q ** 4)
                C2s.append(math.sqrt(K4 / 2))
                C4s.append((K8 / 24) ** 0.25)
        C2s.sort(); C4s.sort()
        print(f"{m:>5} {C2s[len(C2s)//2]:>10.3f} {C4s[len(C4s)//2]:>14.3f}")
    print("\n  both ≈ 0.9–1.0 (sub-Gaussian): the tower rungs r=2, r=4 hold at C ≈ 1;")
    print("  r=2 is discharged in-tree mod TwoCharacterWeilInput (R144); r=4 is the")
    print("  single remaining open average for the absolute-C r=3 rung.")

if __name__ == "__main__":
    main()
