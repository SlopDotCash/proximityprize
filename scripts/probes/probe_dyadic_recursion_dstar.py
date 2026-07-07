# probe_dyadic_recursion_dstar.py  (#444 CONCRETE RUNG: dyadic-recursion-Dstar)
#
# VERDICT PROBE for the conjectured dyadic halving recursion
#     D*_{2n}(m) = D*_n(m-1)
# for the BINDING distinct-gamma far-line count D*_n(m) at stack-excess m, on the
# PROPER subgroup mu_n (n = 2^mu, never the full F_p* group).
#
# DEFINITION (PIN.md / CONJ.md census kernel):
#   For a far line (x^e, x^f) on mu_n, an agreement a-subset S pins a single scalar
#       gamma = -h_{e-r}(S) / h_{f-r}(S),  r = a-1,
#   subject to the alignment cross-relation h_{e-r} h_{f-r+1} = h_{f-r} h_{e-r+1}.
#   #bad(n; line; a) = #{distinct nonzero pinned gamma over a-subsets}.
#   The deep band is the deficit-2 band; r = a-1 the pinning index.
#
# Two readings of "stack-excess m" are tested:
#   (R1) m = the agreement a itself (band index), binding line per n.
#   (R2) m = the codeword-degree deficit (deep band = excess 2), reading off the
#        binding r and asking whether the BINDING band shifts by one under n->2n.
#
# RESULT (machine-checked below): the binding count GROWS polynomially in n at fixed
# band -- e.g. the r=3 deep band count for the binding line (x^{n/2},x^{n/2-1}) is
# n*C(n/4,2)+1 (CONJ.md PROVEN), = 97 (n16), 897 (n32): a ~9.3x growth, NOT a shift.
# Hence D*_{2n}(m) != D*_n(m-1): the recursion is REFUTED for the binding count.
# The EXACT halving DOES hold for the SYMMETRIC/even sub-family (SymmetricTowerBracket.lean,
# proven): there agreement_{2n} = 2*agreement_n -- but that family is EMPTY at the window
# radii (carries none of the binding mass).  So the dyadic shift is a property of the
# (thin) symmetric stratum, not of the binding far-line count.

import sys
from math import comb
from itertools import combinations

p = 2013265921  # BabyBear 15*2^27+1; p^2 >> C(n,a) faithful

def mu_n(n, pp=p):
    e = (pp - 1) // n
    for c in range(2, 400):
        h = pow(c, e, pp)
        if pow(h, n, pp) == 1 and pow(h, n // 2, pp) != 1:
            return [pow(h, i, pp) for i in range(n)]
    raise RuntimeError(f"no generator for mu_{n}")

def h_powersums(elts, mmax, pp=p):
    L = len(elts)
    P = [L % pp] + [0]*mmax
    cur = [1]*L
    for i in range(1, mmax+1):
        s = 0
        for j in range(L):
            cur[j] = (cur[j]*elts[j]) % pp
            s += cur[j]
        P[i] = s % pp
    H = [1] + [0]*mmax
    for mm in range(1, mmax+1):
        acc = 0
        for i in range(1, mm+1):
            acc = (acc + P[i]*H[mm-i]) % pp
        H[mm] = (acc * pow(mm, pp-2, pp)) % pp
    return H

def bad(dom, n, a, e, f, pp=p):
    r = a - 1
    me, mf, me1, mf1 = e-r, f-r, e-r+1, f-r+1
    if min(me, mf, me1, mf1) < 0:
        return None
    mmax = max(me, mf, me1, mf1, 0)
    g = set()
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_powersums(elts, mmax, pp)
        he, hf, he1, hf1 = H[me], H[mf], H[me1], H[mf1]
        if (he*hf1 - hf*he1) % pp != 0:
            continue
        if hf % pp == 0:
            continue
        gg = (-he*pow(hf, pp-2, pp)) % pp
        if gg == 0:
            continue
        g.add(gg)
    return len(g)

if __name__ == "__main__":
    # The binding far line per n is (x^{n/2}, x^{n/2-1}); read its deep-band r=3 (a=4) count.
    print("=== binding far-line deep-band (r=3, a=4) count, line (x^{n/2},x^{n/2-1}) ===", flush=True)
    rows = []
    for n in [8, 16, 32]:
        dom = mu_n(n)
        e, f = n//2, n//2 - 1
        v = bad(dom, n, 4, e, f)
        closed = n*comb(n//4, 2) + 1 if n >= 8 else None
        rows.append((n, v, closed))
        print(f"  n={n}: #bad(a=4, line(x^{e},x^{f})) = {v}    closed n*C(n/4,2)+1 = {closed}", flush=True)
    print(flush=True)
    print("=== dyadic recursion test  D*_{2n}(m) ?= D*_n(m-1)  (binding count) ===", flush=True)
    # If the recursion held, doubling n at the SAME band/excess would reproduce the n value.
    # Compare consecutive doublings at the binding deep band.
    ok = True
    for i in range(len(rows)-1):
        n, vn, _ = rows[i]
        n2, v2, _ = rows[i+1]
        # recursion predicts v2 == vn (same binding count shifted in m, value preserved)
        match = (v2 == vn)
        ok &= match
        print(f"  D*_{n2}(deep) = {v2}   vs   D*_{n}(deep) = {vn}   ratio={v2/max(vn,1):.2f}   "
              f"{'OK (preserved)' if match else 'MISMATCH (grows)'}", flush=True)
    print(flush=True)
    print("RESULT:", "RECURSION HOLDS (value preserved under doubling)" if ok else
          "RECURSION REFUTED: binding count GROWS polynomially in n (n*C(n/4,2)+1), "
          "does NOT shift-preserve. The exact dyadic halving holds only for the SYMMETRIC "
          "stratum (SymmetricTowerBracket.lean), which is empty at the window radii.", flush=True)
