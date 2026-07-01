"""
probe_444_angleD_recursion.py  (#444 Angle D -- generating-function / Newton recursion across r)

GOAL: a recursion in r linking #bad(r,n)/O_P(r,n) to depth r-1 (deficit-2 band; possible descent
to mu_{n/2}), s.t. #bad(r,n) <= K = 2^r C(n/2,r) follows by induction from the r=3 base.

BAD test (verified vs Gaussian-elim digit-for-digit in prior workflows):
  (r+1)-subset S of mu_n is BAD for line (x^e,x^f) iff  D(S) := h_{e-r}(S) h_{f-r+1}(S)
  - h_{f-r}(S) h_{e-r+1}(S) = 0, with pinned gamma = -h_{e-r}(S)/h_{f-r}(S).
  h_m via Newton: h_m = (1/m) sum_{i=1}^m P_i h_{m-i}, P_i = power sum sum_{z in S} z^i.
  #bad = #distinct nonzero gamma (+[gamma=0 present]); O_P = #dilation-orbits (orbit size n/d,
  d=gcd(e-f,n)).

Fast pure-int implementation: precompute z^i tables per group element ONCE, then per subset combine.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter

P = 2013265921  # BabyBear, 2^27 | p-1
_wcache = {}
def w_of_order(n):
    if n in _wcache: return _wcache[n]
    e = (P-1)//n
    for c in range(2, 5000):
        h = pow(c, e, P)
        if pow(h, n, P) == 1 and pow(h, n//2, P) != 1:
            _wcache[n] = h; return h
    raise RuntimeError("no w")

def measure(n, e, f, r, want_fiber=False, want_orbits_of_subsets=False):
    a0 = r+1; k = r-1
    degs = [e-r, e-r+1, f-r, f-r+1]
    if min(degs) < 0:
        return None
    maxdeg = max(degs)
    w = w_of_order(n)
    mu = [pow(w, i, P) for i in range(n)]
    # power tables: powtab[elem_index][i] = mu[elem]^i  for i=0..maxdeg
    powtab = []
    for z in mu:
        row = [1]*(maxdeg+1)
        for i in range(1, maxdeg+1):
            row[i] = row[i-1]*z % P
        powtab.append(row)
    invm = [0]+[pow(m, P-2, P) for m in range(1, maxdeg+1)]  # 1/m mod P
    d = gcd((e-f) % n, n)
    mult = pow(w, (e-f) % n, P)

    De = e-r; De1 = e-r+1; Df = f-r; Df1 = f-r+1
    gammas = set(); gamma0 = False; inf_pins = 0
    fiber = Counter()           # gamma -> #subsets (nonzero gamma) if want_fiber
    bad_subsets = []            # store subset index tuples if want_orbits_of_subsets
    gamma_of = {}               # subset -> gamma (only if want_orbits_of_subsets)

    for Sidx in itertools.combinations(range(n), a0):
        # power sums
        # Ps[i] = sum over elements of z^i
        # compute h_m for m in 0..maxdeg
        Ps = [0]*(maxdeg+1)
        for ei in Sidx:
            row = powtab[ei]
            for i in range(1, maxdeg+1):
                Ps[i] += row[i]
        for i in range(1, maxdeg+1):
            Ps[i] %= P
        H = [0]*(maxdeg+1); H[0] = 1
        for m in range(1, maxdeg+1):
            s = 0
            for i in range(1, m+1):
                s += Ps[i]*H[m-i]
            H[m] = s % P * invm[m] % P
        her = H[De]; her1 = H[De1]; hfr = H[Df]; hfr1 = H[Df1]
        if (her*hfr1 - hfr*her1) % P != 0:
            continue
        # bad
        if hfr == 0:
            inf_pins += 1
            continue  # gamma undefined (genuine-count convention skips fully-degenerate inf)
        g = (-her * pow(hfr, P-2, P)) % P
        if g == 0:
            gamma0 = True
        else:
            gammas.add(g)
            if want_fiber: fiber[g] += 1
            if want_orbits_of_subsets:
                bad_subsets.append(Sidx); gamma_of[Sidx] = g
    # orbits of nonzero gammas
    rem = set(gammas); orbs = 0
    while rem:
        x0 = next(iter(rem)); cur = x0; o = set()
        for _ in range(n):
            o.add(cur); cur = cur*mult % P
        orbs += 1; rem -= o
    K = (1 << r) * comb(n//2, r)
    out = dict(nbad=len(gammas), gamma0=gamma0, OP=orbs, K=K, d=d, inf=inf_pins,
               SonV=len(gammas)+(1 if gamma0 else 0))
    if want_fiber: out['fiber'] = fiber
    if want_orbits_of_subsets: out['bad_subsets'] = bad_subsets; out['gamma_of'] = gamma_of
    return out

LINES = {
    3: lambda n: (n//2, n//2 - 1),
    4: lambda n: (n//2 + 2, n//4 + 1),
    5: lambda n: (n//2 + 1, n - 1),
    6: lambda n: (n//2 + 4, n//2 + 2),
}

if __name__ == "__main__":
    # which (r,n) cells to run; default n=16 all r + n=32 for r=3,4,5 (skip 3.4M r6n32)
    cells = [(3,16),(4,16),(5,16),(6,16),(3,32),(4,32),(5,32)]
    if len(sys.argv) > 1 and sys.argv[1] == "full":
        cells.append((6,32))
    print("=== CALIBRATION (reproduce O_P table {r3:(6,28),r4:(9,97),r5:(11,90),r6:(14,185)}) ===", flush=True)
    table = {3: {16:6, 32:28}, 4: {16:9, 32:97, 64:897}, 5: {16:11, 32:90}, 6: {16:14, 32:185}}
    for (r, n) in cells:
        e, f = LINES[r](n)
        res = measure(n, e, f, r)
        if res is None:
            print(f"r={r} n={n} line(x^{e},x^{f}): SKIP (neg deg)", flush=True); continue
        want = table.get(r, {}).get(n, "?")
        ok = "OK" if want == res['OP'] else f"!! want {want}"
        print(f"r={r} n={n} (x^{e},x^{f}) d={res['d']}: #bad={res['nbad']}(+{int(res['gamma0'])}z) "
              f"O_P={res['OP']} inf={res['inf']} K={res['K']} bad/K={res['nbad']/res['K']:.4f} [{ok}]", flush=True)
