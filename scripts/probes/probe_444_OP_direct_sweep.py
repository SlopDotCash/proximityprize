"""
probe_444_OP_direct_sweep.py  (#444 -- DIRECT O_P(c) sweep; check NubsCarson + my model)

Resolve the conflict between:
 - NubsCarson direct data: O_P -> 1 at the binding rung and persists (n=8, n=16, 3 primes).
 - My last-round descent-model claim: O_P=1 'fails at n=32' (char-0 O_P=3).
My model assumed the binding LEVEL SET has size n/2; but at n=8 binding (c=3, s=5) the level set
is >= s = 5 > n/2 = 4, so that assumption is FALSE off n=16. This probe computes O_P(c) DIRECTLY
(binding direction x^{n/2+1}+g x^{n/2-1}) for n=8,16 to (a) confirm NubsCarson, (b) find the
O_P=1 onset c and the level-set size there, (c) see whether 'level-set = n/2' is n=16-special.
"""
import itertools
from collections import Counter

def order(x, p):
    o, cur = 1, x
    while cur != 1: cur = cur*x % p; o += 1
    return o

def setup(n, p):
    g = 2
    while order(g, p) != p-1: g += 1
    w = pow(g, (p-1)//n, p)
    return w, [pow(w, i, p) for i in range(n)]

def solve_gamma(T, k, a, b, p):
    """Return gamma if x^a+gamma x^b is interpolable by deg<k on T (consistent), else None/'free'."""
    rows, rhs = [], []
    for t in T:
        rows.append([pow(t, i, p) for i in range(k)] + [(-pow(t, b, p)) % p]); rhs.append(pow(t, a, p))
    A = [r[:]+[rhs[i]] for i, r in enumerate(rows)]; ncol = k+1; piv = []; r = 0
    for col in range(ncol):
        pr = None
        for rr in range(r, len(A)):
            if A[rr][col] % p != 0: pr = rr; break
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]; inv = pow(A[r][col], p-2, p); A[r] = [x*inv % p for x in A[r]]
        for rr in range(len(A)):
            if rr != r and A[rr][col] % p != 0:
                f = A[rr][col]; A[rr] = [(A[rr][j]-f*A[r][j]) % p for j in range(ncol+1)]
        piv.append(col); r += 1
        if r == len(A): break
    for rr in range(len(A)):
        if all(A[rr][j] % p == 0 for j in range(ncol)) and A[rr][ncol] % p != 0: return None
    if k not in piv: return 'free'
    sol = [0]*ncol
    for idx, col in enumerate(piv): sol[col] = A[idx][ncol] % p
    return sol[k]

def levelset_size(gamma, T, k, a, b, p, mu):
    """For a found (gamma) with witness T, recover f and count |{x in mu : psi=gamma}|.
       Refit f (deg<k) on T to x^a+gamma x^b, then count agreement over all of mu."""
    # f(t) = t^a + gamma t^b on T; fit deg<k poly via solving Vandermonde (k unknowns, k eqns from first k of T)
    Tl = list(T)[:k]
    M = [[pow(t, i, p) for i in range(k)] for t in Tl]
    y = [(pow(t, a, p) + gamma*pow(t, b, p)) % p for t in Tl]
    # gaussian solve
    A = [M[i][:]+[y[i]] for i in range(k)]
    for col in range(k):
        pr = next((rr for rr in range(col, k) if A[rr][col] % p != 0), None)
        if pr is None: return None
        A[col], A[pr] = A[pr], A[col]; inv = pow(A[col][col], p-2, p); A[col] = [x*inv % p for x in A[col]]
        for rr in range(k):
            if rr != col and A[rr][col] % p != 0:
                f = A[rr][col]; A[rr] = [(A[rr][j]-f*A[col][j]) % p for j in range(k+1)]
    fc = [A[i][k] for i in range(k)]
    cnt = 0
    for x in mu:
        fx = sum(fc[i]*pow(x, i, p) for i in range(k)) % p
        if fx == (pow(x, a, p) + gamma*pow(x, b, p)) % p: cnt += 1
    return cnt

def sweep(n, k, p, cmax):
    w, mu = setup(n, p)
    a, b = n//2+1, n//2-1
    mult = pow(w, a-b, p)  # w^2
    print(f"n={n} k={k} p={p} binding x^{a}+g x^{b} (budget={n}):")
    for c in range(1, cmax+1):
        s = k+c
        if s > n: break
        bad = {}   # gamma -> a witness T
        for T in itertools.combinations(mu, s):
            gv = solve_gamma(T, k, a, b, p)
            if gv in (None, 'free'): continue
            if gv % p != 0 and gv not in bad:
                bad[gv] = T
        nz = list(bad.keys())
        # O_P via orbit under mult
        rem = set(nz); orbs = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; o = set()
            for _ in range(n):
                o.add(cur); cur = cur*mult % p
            orbs += 1; rem -= o
        nbad = len(nz) + 0
        # level-set size of one witness (if any)
        ls = None
        if nz:
            g0 = nz[0]; ls = levelset_size(g0, bad[g0], k, a, b, p, mu)
        tag = "  <-- O_P=1 onset" if orbs == 1 else ""
        print(f"  c={c} s={s}: #bad(nonzero)={nbad:5d}  O_P={orbs:4d}  level-set(one witness)={ls}"
              f"  {'<=budget' if nbad+1<=n else '>budget'}{tag}")

for (n, k, cmax) in [(8, 2, 5), (16, 4, 5)]:
    sweep(n, k, 65537, cmax)
    print()
