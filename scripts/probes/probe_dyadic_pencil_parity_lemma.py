#!/usr/bin/env python3
"""Checks for docs/research/proximity-gap/dyadic-radius-successor-list-three.md.

    python3 -O scripts/probes/probe_dyadic_pencil_parity_lemma.py lattice
        Brute force on mu_16: the unit-lattice condition (Psi-differences constant in all
        three roles) has exactly the true three-split pencils as solutions in degrees 3, 4.
        Expected: "degree 3: lattice 7 true 7 equal True", "degree 4: lattice 23 true 23 equal True".

    python3 -O scripts/probes/probe_dyadic_pencil_parity_lemma.py lemma N FILE
        FILE is the output of probe_mu32_split_pencil_verify.py in mode "pencil".
        Checks the parity lemma in all three roles of every listed pencil.

    python3 -O scripts/probes/probe_dyadic_pencil_parity_lemma.py regulator
        Prints det(log|1 - zeta^(a r)|) over odd classes for n = 8..256 (all nonzero).
"""
import cmath
import itertools
import math
import sys

from probe_mu32_split_pencil_verify import P, gen, poly


def canon(t, n):
    return min(tuple(sorted((s * x + r) % n for x in t)) for r in range(n) for s in (1, -1))


def true_pencils(n, m):
    g = gen(n)
    pts = [pow(g, i, P) for i in range(n)]
    out = set()
    for b in itertools.combinations(range(n), m):
        if b[0] != 0:
            break
        if canon(b, n) != b:
            continue
        pb = poly([pts[i] for i in b])
        rest = [i for i in range(n) if i not in b]
        d = {}
        for a in itertools.combinations(rest, m):
            u = [(x - y) % P for x, y in zip(poly([pts[i] for i in a]), pb)]
            i = next(i for i, x in enumerate(u) if x)
            inv = pow(u[i], P - 2, P)
            d.setdefault(tuple(x * inv % P for x in u), []).append(a)
        for group in d.values():
            for a, c in itertools.combinations(group, 2):
                if not set(a) & set(c):
                    out.add((b, frozenset([a, c])))
    return out


def lattice_solutions(n, m):
    k = n.bit_length() - 1
    odd = list(range(1, n // 2, 2))

    def psi(s, x):
        s = set(s)
        out = []
        for i in odd:
            c = 2 * (((x + n // 2) % n) in s)
            for a in range(k - 1):
                d = (i << a) % n
                c += ((x + d) % n in s) + ((x - d) % n in s)
            out.append(c)
        return out

    def const(s1, s2, on):
        ref = None
        for x in on:
            w = [p - q for p, q in zip(psi(s1, x), psi(s2, x))]
            if ref is None:
                ref = w
            elif ref != w:
                return False
        return True

    out = set()
    for b in itertools.combinations(range(n), m):
        if b[0] != 0:
            break
        if canon(b, n) != b:
            continue
        rest = [i for i in range(n) if i not in b]
        for a in itertools.combinations(rest, m):
            rest2 = [i for i in rest if i not in a]
            for c in itertools.combinations(rest2, m):
                if c < a:
                    continue
                if const(a, c, b) and const(a, b, c) and const(b, c, a):
                    out.add((b, frozenset([a, c])))
    return out


def lemma(n, path):
    rows = [eval(line) for line in open(path) if line.startswith("  (")]
    tested = 0
    for row in rows:
        sets = [set(x) for x in row]
        for r in range(3):
            for par in (0, 1):
                if sum(1 for x in sets[r] if x % 2 == par) >= 3:
                    for o in range(3):
                        if o == r:
                            continue
                        tested += 1
                        opp = [x for x in sets[o] if x % 2 != par]
                        assert all((x + n // 2) % n in sets[o] for x in opp), row
    print(f"{path}: {len(rows)} pencils, {tested} lemma instances, all hold")


def regulator():
    def det(mat):
        mat = [r[:] for r in mat]
        d = 1.0
        for c in range(len(mat)):
            p = max(range(c, len(mat)), key=lambda r: abs(mat[r][c]))
            if p != c:
                mat[c], mat[p] = mat[p], mat[c]
                d = -d
            d *= mat[c][c]
            for r in range(c + 1, len(mat)):
                f = mat[r][c] / mat[c][c]
                for j in range(c, len(mat)):
                    mat[r][j] -= f * mat[c][j]
        return d

    for k in range(3, 9):
        n = 2 ** k
        odd = list(range(1, n // 2, 2))
        mat = [[math.log(abs(1 - cmath.exp(2j * math.pi * a * r / n))) for r in odd] for a in odd]
        print(n, "det = %.6g" % det(mat))


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "lattice":
        for m in (3, 4):
            lat, tru = lattice_solutions(16, m), true_pencils(16, m)
            print(f"degree {m}: lattice {len(lat)} true {len(tru)} equal {lat == tru}")
    elif mode == "lemma":
        lemma(int(sys.argv[2]), sys.argv[3])
    else:
        regulator()
