#!/usr/bin/env python3
"""Exact mcaDeltaStar for RS[F_13, <5> (order 4), deg<2]  (lane L3-F13-order4).

n=4, k=2, rate 1/2, rho=1/2.  dom = <5> = (5^0,5^1,5^2,5^3) = (1,5,12,8).
Johnson = 1 - sqrt(1/2) ~ 0.293, capacity = 1/2.

Syndrome-reduced exact computation (collapses p^{2n} word pairs to p^{2(n-k)}
syndrome pairs).  Extracts the EXACT eps_mca step profile, the worst stack
achieving each level, and explicit 3-element witness sets + interpolating (a,b)
per bad scalar, to drive the Lean pin.
"""
from itertools import product, combinations
from math import sqrt
from fractions import Fraction

P = 13
N = 4
K = 2
G = 5
DOM = [pow(G, i, P) for i in range(N)]   # (1,5,12,8)


def rref(mat, p):
    m = [row[:] for row in mat]
    rows = len(m); cols = len(m[0]) if m else 0
    piv = []; r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p), None)
        if pr is None: continue
        m[r], m[pr] = m[pr], m[r]
        inv = pow(m[r][c], p-2, p)
        m[r] = [(x*inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p:
                f = m[i][c]
                m[i] = [(a-f*b) % p for a,b in zip(m[i], m[r])]
        piv.append(c); r += 1
        if r == rows: break
    return m[:r], piv


def nullspace(mat, p):
    red, piv = rref(mat, p)
    cols = len(mat[0])
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [0]*cols; v[f] = 1
        for r, c in enumerate(piv):
            v[c] = (-red[r][f]) % p
        basis.append(v)
    return basis


def solve_particular(H, s, p):
    rows = [H[i] + [s[i]] for i in range(len(H))]
    red, piv = rref(rows, p)
    n = len(H[0]); w = [0]*n
    for r, c in enumerate(piv):
        w[c] = red[r][n]
    return w


def ext_from(word, S):
    S = list(S)
    if len(S) <= K:
        return True
    base, rest = S[:K], S[K:]
    i, j = base
    xi, xj = DOM[i], DOM[j]
    invden = pow((xi-xj) % P, P-2, P)
    b = (word[i]-word[j])*invden % P
    a = (word[i]-b*xi) % P
    for r in rest:
        if (a+b*DOM[r]) % P != word[r] % P:
            return False
    return True


def line_witness(word, S):
    S = list(S)
    i, j = S[0], S[1]
    xi, xj = DOM[i], DOM[j]
    invden = pow((xi-xj) % P, P-2, P)
    b = (word[i]-word[j])*invden % P
    a = (word[i]-b*xi) % P
    return a, b


SUBSETS = [tuple(c) for size in range(K+1, N+1) for c in combinations(range(N), size)]

G_GEN = [[pow(x, j, P) for x in DOM] for j in range(K)]
H = nullspace(G_GEN, P)
assert len(H) == N-K
SYN = list(product(range(P), repeat=N-K))
# representative word per syndrome + its ext mask
REP = {s: solve_particular(H, list(s), P) for s in SYN}
EXT = {}
for s in SYN:
    w = REP[s]; m = 0
    for bit, S in enumerate(SUBSETS):
        if ext_from(w, S):
            m |= 1 << bit
    EXT[s] = m


def adm_mask(allow3, allow4):
    m = 0
    for bit, S in enumerate(SUBSETS):
        if (len(S) == 3 and allow3) or (len(S) == 4 and allow4):
            m |= 1 << bit
    return m


def eps_for(allow3, allow4, want_best=False):
    """max bad-gamma count over syndrome pairs; optionally return witness data."""
    adm = adm_mask(allow3, allow4)
    best = 0; best_info = None
    nz = [s for s in SYN if any(s)]
    for s0 in SYN:
        for s1 in nz:
            cnt = 0; bad_g = []
            for g in range(P):
                line = tuple((a+g*b) % P for a, b in zip(s0, s1))
                bm = EXT[line] & ~(EXT[s0] & EXT[s1]) & adm
                if bm:
                    cnt += 1; bad_g.append((g, bm))
            if cnt > best:
                best = cnt
                best_info = (s0, s1, bad_g)
    if want_best:
        return best, best_info
    return best


def main():
    rho = Fraction(K, N)
    print(f"RS[F_{P}, <{G}> order {N}, deg<{K}]  dom={DOM}  rho={rho}")
    print(f"  Johnson = 1 - sqrt(1/2) = {1-sqrt(0.5):.6f}")
    print(f"  capacity = {float(1-rho):.6f}")
    print(f"  UDR = {float((1-rho)/2):.6f}")

    # m-band: subset of size s admissible iff s >= (1-delta)*n.
    # delta in (1/4,1/2]: (1-delta)*4 in [2,3) -> allow size3 and size4
    # delta in (0,1/4]: (1-delta)*4 in [3,4) -> allow size3? 3>=thresh? thresh in [3,4)->size3 NO if thresh>3
    # Use exact in-tree clause card>=thresh.  Evaluate at representative deltas.
    print("\n  --- eps_mca step profile ---")
    for delta in [Fraction(0), Fraction(1,8), Fraction(1,4),
                  Fraction(3,8), Fraction(1,2), Fraction(5,8)]:
        thresh = (1-delta)*N
        a3 = (3 >= thresh)
        a4 = (4 >= thresh)
        e = eps_for(a3, a4)
        print(f"    delta={str(delta):>5}={float(delta):.4f}  thresh={float(thresh):.4f}"
              f"  size3adm={a3} size4adm={a4}  eps_mca={e}/{P}"
              f"  >J={float(delta)>1-sqrt(0.5)}")

    # Detailed worst stack at the above-Johnson band (size3+size4 allowed): this is
    # delta in (1/4, 1/2].  Get witnesses.
    print("\n  --- worst stack, band size3+size4 (delta in (1/4,1/2]) ---")
    best, info = eps_for(True, True, want_best=True)
    s0, s1, bad_g = info
    w0 = REP[s0]; w1 = REP[s1]
    print(f"    eps_mca = {best}/{P}")
    print(f"    syndrome s0={s0} -> rep u0={w0}")
    print(f"    syndrome s1={s1} -> rep u1={w1}")
    print(f"    bad scalars ({len(bad_g)}): {[g for g,_ in bad_g]}")
    for g, bm in bad_g:
        line = [(a+g*b) % P for a, b in zip(w0, w1)]
        # find an admissible witness set S (size>=3) where line extends but pair fails
        chosen = None
        for bit, S in enumerate(SUBSETS):
            if (bm >> bit) & 1 and len(S) >= 3:
                a, b = line_witness(line, S)
                # confirm
                ok = all((a+b*DOM[i]) % P == line[i] for i in S)
                chosen = (S, (a, b), ok)
                break
        # is u1 explainable on chosen S?
        S = chosen[0]
        u1ext = ext_from(w1, S)
        print(f"      g={g:>2}: line={line}  witnessS={S}  interp(a,b)={chosen[1]}"
              f"  ok={chosen[2]}  u1_ext_on_S={u1ext}")

    print("\n  delta* = sup{delta : eps_mca(C,delta) <= 1/2}.  1/2 = 6.5/13.")
    print("  Pick the largest band where eps_mca <= 6/13 (<=1/2), and the next band > 6/13.")


if __name__ == "__main__":
    main()
