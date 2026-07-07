#!/usr/bin/env python3
"""R18 WEILFORM probe: fourth moment of T_chi for quadratic chi.

T(t) = sum_{x in mu_n} chi(t-x), chi = Legendre mod p (chi(0)=0).
Checks:
 1. S4 = sum_t T(t)^4 vs 6 n^2 p (and vs 3 n^2 p).
 2. Degenerate classification: S(x,y) = sum_t chi((t-x1)(t-x2)(t-y1)(t-y2));
    f perfect square iff multiset multiplicities all even
    <=> ({x1,x2}={y1,y2} as multisets) or (x1=x2 and y1=y2).
    Degenerate exact values: 4 equal -> p-1 ; else -> p-2.
 3. Per-nondegenerate |S| <= 3 sqrt(p)  (Weil, m-1 with m = #distinct roots... check exact best constant seen).
 4. Degenerate total = n(p-1) + 3n(n-1)(p-2); S4 = degen + nondegen sum.
 5. E2(mu_n) additive energy; test any exact relation S4 ~ f(E2).
 6. Fourier identity: S4 = (1/p) * chi-twisted energy of eta.
"""
import sys, math
from itertools import product

def legendre_table(p):
    ch = [0]*p
    for a in range(1,p):
        ch[pow(a,(p-1)//2,p)==1 and a or a] = 0
    qr = set(pow(a,2,p) for a in range(1,p))
    for a in range(1,p):
        ch[a] = 1 if a in qr else -1
    return ch

def mu_n(p, n):
    # order-n subgroup of F_p^*
    assert (p-1) % n == 0
    g = None
    for cand in range(2, p):
        ok = True
        for q in prime_factors(p-1):
            if pow(cand, (p-1)//q, p) == 1:
                ok = False; break
        if ok:
            g = cand; break
    h = pow(g, (p-1)//n, p)
    G = []
    x = 1
    for _ in range(n):
        G.append(x); x = x*h % p
    assert len(set(G)) == n
    return G

def prime_factors(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def run(p, n):
    ch = legendre_table(p)
    G = mu_n(p, n)
    Gs = set(G)
    T = [sum(ch[(t-x) % p] for x in G) for t in range(p)]
    S4 = sum(v**4 for v in T)
    S2 = sum(v**2 for v in T)
    # degenerate classification + per-tuple sums
    degen_total = 0; nondegen_max = 0.0; nondeg_sum = 0; bad = 0
    sq = 3*math.sqrt(p)
    for x1,x2,y1,y2 in product(G, repeat=4):
        is_deg = (sorted([x1,x2]) == sorted([y1,y2])) or (x1==x2 and y1==y2)
        S = sum(ch[((t-x1)*(t-x2)*(t-y1)*(t-y2)) % p] for t in range(p))
        if is_deg:
            expected = p-1 if x1==x2==y1==y2 else p-2
            if S != expected: print(f"  DEGEN MISMATCH {x1,x2,y1,y2}: S={S} exp={expected}"); bad+=1
            degen_total += S
        else:
            nondeg_sum += S
            r = abs(S)/math.sqrt(p)
            nondegen_max = max(nondegen_max, r)
            if abs(S) > sq: print(f"  WEIL VIOLATION {x1,x2,y1,y2}: |S|={abs(S)} > 3sqrt p={sq:.2f}"); bad+=1
    degen_formula = n*(p-1) + 3*n*(n-1)*(p-2)
    # E2(mu_n)
    from collections import Counter
    sums = Counter((a+b)%p for a in G for b in G)
    E2 = sum(v*v for v in sums.values())
    print(f"p={p} n={n} p>=n^4:{p>=n**4} pmod2n={(p-1)%(2*n)==0}")
    print(f"  S2={S2} (np-n^2={n*p-n*n})  S4={S4}  6n^2p={6*n*n*p}  3n^2p={3*n*n*p}  ratio S4/(n^2 p)={S4/(n*n*p):.4f}")
    print(f"  degen_total={degen_total} formula={degen_formula} match={degen_total==degen_formula}")
    print(f"  nondeg_sum={nondeg_sum}  nondeg/S4={nondeg_sum/S4:+.4f}  max|S|/sqrt(p)={nondegen_max:.3f}")
    print(f"  E2(mu_n)={E2}  (3n^2-2n={3*n*n-2*n})  S4-degen vs -E2*?: (S4-degen)/E2={(S4-degen_total)/E2:+.4f}")
    print(f"  bound check: S4 <= 6n^2p: {S4 <= 6*n*n*p}")
    if bad: print(f"  *** {bad} ANOMALIES")
    return S4, degen_total, E2

if __name__ == "__main__":
    cells = [(41,8),(73,8),(97,8),(113,8),(97,16),(193,16),(257,16),(577,16)]
    for p,n in cells:
        run(p,n)
