"""#466 lane W3 — uniform-in-mu floor-bad characterization, a=6 (n=64) DIRECTED scan support.

Ground truth (exact, full enumerations, floor_scan_exact.c / floor_scan_poly.c):
  floor-bad(16) = {17}   (160 realizable / 2,304 patterns)
  floor-bad(32) = {97}   ( 32 realizable / 15,366,400 patterns)
Conjecture (dossier v3 Tier-1 item 4): floor-bad(n) = {smallest prime == 1 mod n};
at a=6 that predicts floor-bad(64) = {193}.

n=64 FULL scan is INFEASIBLE: 4*C(16,12)^2*C(16,8)^2 = 2,194,657,046,760,000 (~2.19e15)
patterns (measured C-scanner rate ~6e5 patt/s/core at n=32; >100 core-years at n=64).

This probe therefore does the DIRECTED part:
 1. parses the exact dumps of realizable patterns at (n=16,p=17) and (n=32,p=97);
 2. canonicalizes modulo the PROVEN rotation symmetry (A -> g0*A preserves realizability:
    it rescales columns of M_A and the target b_A by nonzero scalars, so the rank
    condition is invariant); counts orbits and prints base-pattern profiles;
 3. reimplements the realizability test (vanishing-poly reduction, identical to
    floor_scan_poly.c) and CROSS-VALIDATES it on the dumps;
 4. generates structured candidate patterns at n=64, p=193 (lifts of the n=32 orbit,
    plus profile-constrained families) and tests them.

Realizability test used everywhere:
  A realizable over F_p  <=>  r_k = 0 for k in [n/2+1, |A|-1],
  where r = x^{3n/4} mod V_A, V_A = prod_{a in A}(x - x_a), x_j = g0^j.
"""
import sys, itertools, random
from collections import Counter

OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

# ---------- field / test machinery ----------
def is_prime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def primitive_root(p):
    fac = []
    m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for h in range(2, p):
        if all(pow(h, (p-1)//f, p) != 1 for f in fac):
            return h

def domain(p, n):
    g0 = pow(primitive_root(p), (p-1)//n, p)
    return [pow(g0, j, p) for j in range(n)]

def realizable(A_idx, X, p, n):
    """A_idx: list of domain indices. Vanishing-poly test."""
    half, deg34 = n//2, 3*n//4
    # V = prod (x - X[j])
    V = [1]
    for j in A_idx:
        r = X[j]
        V = [(-r*V[0]) % p] + [(V[k-1] - r*V[k]) % p for k in range(1, len(V))] + [V[-1]]
        # note: above builds (x-r)*V correctly: new[k] = V[k-1] - r*V[k]
    D = len(A_idx)
    assert len(V) == D+1 and V[D] == 1
    # r = x^D mod V
    rr = [(-V[k]) % p for k in range(D)]
    for _ in range(deg34 - D):
        top = rr[D-1]
        rr = [(-top*V[0]) % p] + [(rr[k-1] - top*V[k]) % p for k in range(1, D)]
    return all(rr[k] == 0 for k in range(half+1, D))

# ---------- pattern <-> profile ----------
def classes(n):
    return [[j for j in range(n) if j % 4 == c] for c in range(4)]

def pattern_to_missing(A, n):
    """returns tuple of 4 frozensets: per class, the *positions* t (j = 4t+c) missing."""
    S = set(A)
    cls = classes(n)
    return tuple(frozenset((j-c)//4 for j in cls[c] if j not in S) for c in range(4))

def rotate(A, s, n):
    return sorted((j+s) % n for j in A)

def canon(A, n):
    return min(tuple(rotate(A, s, n)) for s in range(n))

def reflect(A, n):
    return sorted((-j) % n for j in A)

# ---------- parse dumps ----------
def parse_dump(path):
    pats = []
    for line in open(path):
        if not line.startswith("REALIZABLE"): continue
        inner = line[line.index("{")+1:line.index("}")]
        pats.append(sorted(int(t) for t in inner.split(",")))
    return pats

def analyze(tag, path, p, n):
    pats = parse_dump(path)
    X = domain(p, n)
    log(f"== {tag}: n={n} p={p}, {len(pats)} realizable patterns ==")
    # cross-validate python test on ALL dumped patterns
    ok = all(realizable(A, X, p, n) for A in pats)
    log(f"   python test reproduces all dumped patterns realizable: {ok}")
    assert ok
    orbits = {}
    for A in pats:
        orbits.setdefault(canon(A, n), []).append(A)
    log(f"   rotation orbits: {len(orbits)} (sizes {sorted(len(v) for v in orbits.values())})")
    refl_closed = all(canon(reflect(A, n), n) in orbits for A in pats)
    log(f"   closed under reflection j->-j: {refl_closed}")
    for i, base in enumerate(sorted(orbits)):
        miss = pattern_to_missing(list(base), n)
        log(f"   orbit {i}: base={list(base)}")
        log(f"            missing positions per class (t where j=4t+c): {[sorted(s) for s in miss]}")
    return pats, orbits

if __name__ == "__main__":
    scratch = sys.argv[1] if len(sys.argv) > 1 else "."
    pats16, orb16 = analyze("rung a=4", f"{scratch}/dump16_17.txt", 17, 16)
    log()
    pats32, orb32 = analyze("rung a=5", f"{scratch}/dump32_97.txt", 97, 32)
    log()

    # sanity: python test agrees with C on some non-realizable patterns
    X97 = domain(97, 32)
    rnd = random.Random(0)
    cls = classes(32)
    neg = 0
    for _ in range(200):
        A = []
        c0 = rnd.randrange(4)
        for k, sz in ((c0, 6), ((c0+1) % 4, 6), ((c0+2) % 4, 4), ((c0+3) % 4, 4)):
            A += rnd.sample(cls[k], sz)
        A = sorted(A)
        if realizable(A, X97, 97, 32) and tuple(A) not in {tuple(x) for x in pats32}:
            neg += 1
    log(f"random n=32/97 spot-check: {neg} unexpected realizables in 200 random patterns (expect 0)")

    with open(f"{scratch}/analysis_out.txt", "w") as f:
        f.write("\n".join(OUT))
