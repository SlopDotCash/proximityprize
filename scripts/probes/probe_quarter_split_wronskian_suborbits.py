#!/usr/bin/env python3
"""Independent verification of the large-characteristic Wronskian gcd bound,
split-pencil subdegree/inner-degree/excess upgrades, and small-prime F_97 witness."""

from fractions import Fraction
from math import ceil, floor


def verify_wronskian_on_p1():
    """Explicitly compute W(u-1, v-1, uv-1) on P^1 over F_p (p = 1000003) and check
    both g^3 | W and the exact pole-zero divisor bound 3 * deg(g) <= H_u + H_v + 3*(|S|-2)."""
    p = 1000003

    def trim(a):
        a = [x % p for x in a]
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        return a

    def padd(a, b):
        n = max(len(a), len(b))
        return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

    def psub(a, b):
        n = max(len(a), len(b))
        return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])

    def pmul(a, b):
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i + j] = (c[i + j] + x * y) % p
        return trim(c)

    def pderiv(a):
        return trim([i * a[i] for i in range(1, len(a))]) if len(a) > 1 else [0]

    def pdivmod(a, b):
        a = list(a)
        db = len(b) - 1
        inv = pow(b[-1], p - 2, p)
        q = [0] * max(1, len(a) - db)
        while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
            coef = a[-1] * inv % p
            sh = len(a) - 1 - db
            q[sh] = coef
            for i in range(db + 1):
                a[sh + i] = (a[sh + i] - coef * b[i]) % p
            a = trim(a)
        return trim(q), a

    def pgcd(a, b):
        while not (len(b) == 1 and b[0] == 0):
            _, r = pdivmod(a, b)
            a, b = b, r
        inv = pow(a[-1], p - 2, p)
        return [x * inv % p for x in a]

    def pdeg(a):
        return -1 if (len(a) == 1 and a[0] == 0) else len(a) - 1

    def rred(f):
        g = pgcd(f[0], f[1])
        return (pdivmod(f[0], g)[0], pdivmod(f[1], g)[0])

    def rsub(f, g):
        return rred((psub(pmul(f[0], g[1]), pmul(g[0], f[1])), pmul(f[1], g[1])))

    def radd(f, g):
        return rred((padd(pmul(f[0], g[1]), pmul(g[0], f[1])), pmul(f[1], g[1])))

    def rmul(f, g):
        return rred((pmul(f[0], g[0]), pmul(f[1], g[1])))

    def rderiv(f):
        n, d = f
        return rred((psub(pmul(pderiv(n), d), pmul(n, pderiv(d))), pmul(d, d)))

    def det3(M):
        t0 = rmul(M[0][0], rsub(rmul(M[1][1], M[2][2]), rmul(M[1][2], M[2][1])))
        t1 = rmul(M[0][1], rsub(rmul(M[1][0], M[2][2]), rmul(M[1][2], M[2][0])))
        t2 = rmul(M[0][2], rsub(rmul(M[1][0], M[2][1]), rmul(M[1][1], M[2][0])))
        return radd(rsub(t0, t1), t2)

    one = ([1], [1])
    # S = {0, 1, inf}, chi = 1; u = t^2/(t-1), v = -(t-1)^2/t; H_u = H_v = 2; g = t^2 - t + 1 (deg 2).
    # Bound: 2 <= (2+2)/3 + 1 = 7/3.
    cases = [
        ("u=t^2/(t-1), v=-(t-1)^2/t", ([0, 0, 1], [p - 1, 1]), ([p - 1, 2, p - 1], [0, 1]), 2, 2, 3),
        ("u=t^3/(t-1), v=(t-1)^3/t", ([0, 0, 0, 1], [p - 1, 1]), ([p - 1, 3, p - 3, 1], [0, 1]), 3, 3, 3),
        ("u=t^3/(t-1)^2, v=-(t-1)^3/t", ([0, 0, 0, 1], [1, p - 2, 1]), ([1, p - 3, 3, p - 1], [0, 1]), 3, 3, 3),
    ]
    for label, u, v, hu, hv, scard in cases:
        f1 = rsub(u, one)
        f2 = rsub(v, one)
        f3 = rsub(rmul(u, v), one)
        d1, d2, d3 = rderiv(f1), rderiv(f2), rderiv(f3)
        dd1, dd2, dd3 = rderiv(d1), rderiv(d2), rderiv(d3)
        W = det3([[f1, f2, f3], [d1, d2, d3], [dd1, dd2, dd3]])
        assert not (len(W[0]) == 1 and W[0][0] == 0), f"Wronskian vanished for {label}"
        g = pgcd(f1[0], f2[0])
        g3 = pmul(g, pmul(g, g))
        _, rem = pdivmod(W[0], g3)
        assert rem == [0], f"g^3 does not divide W for {label}"
        dg = pdeg(g)
        assert Fraction(dg) <= Fraction(hu + hv, 3) + (scard - 2)
    print("Symbolic P^1 Wronskian checks passed (3 non-trivial S={0,1,inf} pairs).")


def verify_production_bounds():
    n = 2 ** 30
    D = 2 ** 28 - 2
    lam = Fraction(9 * D - 2 * n, 3)
    assert lam == Fraction(268435438, 3)

    # Verify (h=1, k=1) is globally optimal among all rectangles [0,h]x[0,k] and vanishing orders T>=1
    best_lam = Fraction(0)
    best_params = None
    for T in range(1, 7):
        for h in range(1, 20):
            for k in range(1, h + 1):
                tot = (h + 1) * (k + 1)
                codim = sum(1 for a in range(h + 1) for b in range(k + 1) if a + b < T)
                M = tot - codim
                if M <= 1:
                    continue
                is_list = sorted([i for i in range(h + 1) for _ in range(k + 1)])
                js_list = sorted([j for _ in range(h + 1) for j in range(k + 1)])
                Si = sum(is_list[-codim:]) - sum(is_list[:codim])
                Sj = sum(js_list[-codim:]) - sum(js_list[:codim])
                alpha = Fraction(Si + Sj, M * T)
                beta = Fraction(M - 1, 2 * T)
                if 3 * D > alpha * n:
                    cand = (3 * D - alpha * n) / beta
                    if cand > best_lam:
                        best_lam = cand
                        best_params = (h, k, T, M)
    assert best_params == (1, 1, 1, 3) and best_lam == lam

    subdeg = ceil(lam / 2)
    assert subdeg == 44_739_240
    assert D // subdeg == 6

    divs = sorted({d for i in range(1, int(D ** 0.5) + 1) if D % i == 0 for d in (i, D // i)})
    surviving = [t for t in divs if t <= 2 or t - 1 >= subdeg]
    assert surviving == [1, 2, 134_217_727, 268_435_454]

    expected = [
        (134_217_727, 1, 2, Fraction(268435426, 268435465), 6_004_798_742_593_547),
        (268_435_454, 2, 1, Fraction(268435414, 671088649), 3_002_399_237_079_048),
        (268_435_454, 1, 1, Fraction(134217713, 335544323), 12_009_597_529_926_331),
    ]
    for t, h, s, E_exp, g_exp in expected:
        m = t // h
        E = 2 * (lam - 4 * h) / (2 * (t + h) - lam)
        gmin = ceil(1 + (m - 1) * (lam / h - 4) / 2)
        assert E == E_exp and gmin == g_exp
        assert E / s >= Fraction(268435414, 671088649)

    E_min = Fraction(268435414, 671088649)
    assert floor(1 / (Fraction(2, 5) - E_min)) == 14_716_856
    assert floor(1 / (1 - Fraction(1, 3) - Fraction(1, 4) - E_min)) == 59
    assert floor(1 / (1 - Fraction(1, 3) - Fraction(1, 5) - E_min)) == 14
    assert floor(1 / (1 - Fraction(1, 4) - Fraction(1, 4) - E_min)) == 9
    assert floor(1 / (1 - Fraction(268435426, 268435465))) == 6_882_960
    print("All production suborbit, inner-degree, excess, and signature bounds verified.")


def verify_f97_deg7_split_pencil():
    """Verify the explicit degree-7 split pencil on mu_32 over F_97 showing that
    p > 3n alone does not obstruct split pencils without large-p bounds."""
    p = 97
    g = 5  # primitive root mod 97
    w = pow(g, (p - 1) // 32, p)
    assert pow(w, 16, p) == p - 1 and pow(w, 32, p) == 1
    H = [pow(w, i, p) for i in range(32)]

    def loc(idxs):
        poly = [1]
        for idx in idxs:
            r = H[idx]
            nxt = [0] * (len(poly) + 1)
            for i, c in enumerate(poly):
                nxt[i] = (nxt[i] - c * r) % p
                nxt[i + 1] = (nxt[i + 1] + c) % p
            poly = nxt
        return poly

    A = [3, 4, 17, 19, 21, 24, 25]
    B = [2, 11, 14, 22, 23, 28, 31]
    C = [0, 5, 6, 12, 18, 27, 30]
    c = 16
    assert len(set(A) | set(B) | set(C)) == 21
    LA, LB, LC = loc(A), loc(B), loc(C)
    for a, b, d in zip(LA, LB, LC):
        assert (a - c * b - (1 - c) * d) % p == 0
    print("Explicit degree-7 split pencil on mu_32 over F_97 verified (LA - 16*LB = -15*LC).")


if __name__ == "__main__":
    verify_wronskian_on_p1()
    verify_production_bounds()
    verify_f97_deg7_split_pencil()
