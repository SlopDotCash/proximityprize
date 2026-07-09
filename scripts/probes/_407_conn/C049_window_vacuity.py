#!/usr/bin/env python3
"""
C049 attack: the radius-doubling 2delta in the interleaved MCA collapse pushes the
ONLY unconditional list bound (the MDS-incidence bound |interleavedList(a)|*C(a,k) <= C(n,k))
out of the prize window. Quantify the exponent gap as a function of (rho, beta, n).

In-tree facts being checked / instantiated (exact integer arithmetic):
  * interleavedList_card_le  (InterleavedListMDSBound.lean):
        |interleavedList(a)| * C(a,k) <= C(n,k),  a = 2t - n
    => crude certificate L <= C(n,k) / C(a,k).
    NON-VACUOUS only if a >= k  (else C(a,k)=0 for a<k, bound is 0 <= C(n,k), trivial).
    a = 2t - n >= k  <=>  t >= (n+k)/2  <=>  delta = 1 - t/n <= (1 - rho)/2.
  * mcaBad_card_le_interleavedList (InterleavedListMCACollapse.lean):
        #mcaBad(t) <= 1 + (n-a) * |interleavedList(a)|,  a = 2t - n  (DOUBLED radius)
    same-radius version (#bad <= 1 + (n-t)*|Lambda_2(t)|) is FALSE (counterexample below).

Prize regime: dyadic mu_n, n = 2^mu proper subgroup of F_q*, q ~ n^beta, beta in [4,5].
delta interior window: (1 - sqrt(rho), 1 - rho - Theta(1/log n)). NEVER full group.
"""
from math import comb, log2, sqrt, floor, log

def cert_exponent(n, k, t, q):
    """The MDS-incidence certificate at floor t: L <= C(n,k)/C(a,k), a = 2t-n.
    Returns (a, vacuous?, log2 of certificate ceiling, whether ceiling >= q)."""
    from math import lgamma
    def log2binom(N, K):
        if K < 0 or K > N:
            return float('-inf')   # C(N,K)=0
        return (lgamma(N+1) - lgamma(K+1) - lgamma(N-K+1)) / log(2)
    a = 2*t - n
    if a < 0:
        a = 0
    if a < k:
        # C(a,k) = 0  => interleavedList_card_le gives  L*0 <= C(n,k), i.e. 0 <= C(n,k): VACUOUS
        return a, True, float('inf'), True
    l2 = log2binom(n, k) - log2binom(a, k)     # log2( C(n,k)/C(a,k) )
    return a, False, l2, (l2 >= log2(q))

def window(n, rho):
    """Interior MCA window in delta: (1 - sqrt(rho), 1 - rho - c/log n).
    Return the three landmark radii: Johnson edge, half-window edge (1-rho)/2, capacity edge."""
    johnson = 1 - sqrt(rho)          # lower edge of open window
    capacity = 1 - rho               # upper edge (1 - rho)
    half = (1 - rho)/2               # MDS-incidence non-vacuity threshold delta <= (1-rho)/2
    # interior probe point: midpoint of (johnson, capacity), shaved by 1/log n
    mid = (johnson + capacity)/2 - 1.0/log2(n) if n > 2 else (johnson+capacity)/2
    return johnson, mid, capacity, half

print("="*100)
print("PART 1.  Same-radius collapse is FALSE  (re-verify the in-tree exhaustive counterexample)")
print("="*100)
# F3, n=4, C = span{(1,1,1,0),(0,1,2,1)}, f1=(0,0,0,1), f2=(0,0,1,0), t=3.
# Claim: all 3 scalars bad, interleaved list at floor t=3 is EMPTY.
p = 3
def vecs_span(basis, p, n):
    out = set()
    import itertools
    for coeffs in itertools.product(range(p), repeat=len(basis)):
        v = tuple(sum(coeffs[i]*basis[i][j] for i in range(len(basis))) % p for j in range(n))
        out.add(v)
    return out
n = 4
C = vecs_span([(1,1,1,0),(0,1,2,1)], p, n)
f1 = (0,0,0,1); f2 = (0,0,1,0)
def line(f1,f2,g,p,n):
    return tuple((f1[i] + g*f2[i]) % p for i in range(n))
def agree_set(u,v,n):
    return frozenset(i for i in range(n) if u[i]==v[i])
def joint_agree(f1,f2,g1,g2,n):
    return frozenset(i for i in range(n) if g1[i]==f1[i] and g2[i]==f2[i])

t = 3
def is_mca_bad(C,f1,f2,g,t,n,p):
    import itertools
    ln = line(f1,f2,g,p,n)
    # exists S with |S|>=t carrying a codeword match of the line AND no joint codeword pair on S
    for S in itertools.chain.from_iterable(itertools.combinations(range(n), r) for r in range(t, n+1)):
        Sset = set(S)
        # codeword match of line on S
        if any(all(ln[i]==c[i] for i in Sset) for c in C):
            # no joint pair on S
            ok = True
            for g1 in C:
                for g2 in C:
                    if all(g1[i]==f1[i] and g2[i]==f2[i] for i in Sset):
                        ok = False; break
                if not ok: break
            if ok:
                return True
    return False

bad = [g for g in range(p) if is_mca_bad(C,f1,f2,g,t,n,p)]
# interleaved list at SAME radius floor t
intlist_t = [(g1,g2) for g1 in C for g2 in C if len(joint_agree(f1,f2,g1,g2,n))>=t]
print(f"  F3 n=4 stack f1={f1} f2={f2} t={t}:")
print(f"    #mcaBad = {len(bad)} (scalars {bad}),  interleavedList@floor t = {len(intlist_t)} pairs")
same_radius_rhs = 1 + (n-t)*len(intlist_t)
print(f"    same-radius RHS 1+(n-t)*|Lambda2(t)| = {same_radius_rhs};  #bad={len(bad)} > RHS ?  {len(bad) > same_radius_rhs}")
# doubled radius floor a = 2t-n
a = 2*t-n
intlist_a = [(g1,g2) for g1 in C for g2 in C if len(joint_agree(f1,f2,g1,g2,n))>=a]
doubled_rhs = 1 + (n-a)*len(intlist_a)
print(f"    doubled-radius a=2t-n={a}: interleavedList@a = {len(intlist_a)} pairs, RHS 1+(n-a)*|.| = {doubled_rhs}; holds? {len(bad)<=doubled_rhs}")

print()
print("="*100)
print("PART 2.  Non-vacuity threshold:  MDS-incidence certificate alive  <=>  delta <= (1-rho)/2")
print("="*100)
print("  delta <= (1-rho)/2  is the HALF-window; the open prize window is (1-sqrt(rho), 1-rho).")
print("  half-edge (1-rho)/2 vs johnson-edge 1-sqrt(rho):")
for rho in [1/2, 1/4, 1/8, 1/16]:
    johnson = 1 - sqrt(rho); half = (1-rho)/2; cap = 1-rho
    inside = half > johnson
    print(f"    rho={rho:7.4f}:  johnson(lower window)={johnson:.4f}  half-edge={half:.4f}  capacity(upper)={cap:.4f}"
          f"   -> half-edge BELOW window? {half <= johnson}")

print()
print("="*100)
print("PART 3.  PRIZE REGIME: certificate is exponential (>= q) at every interior radius")
print("="*100)
print("  At interior delta, a = 2t-n = (1-2delta)n.  delta>(1-rho)/2 => a<k => C(a,k)=0 => VACUOUS.")
print("  Even just inside the half-edge, certificate C(n,k)/C(a,k) blows up to >= q.")
# prize-ish proper-subgroup configs: n=2^mu, q ~ n^beta, k = rho*n
configs = [
    # (n, rho, beta, q)   q chosen ~ n^beta, prime-ish magnitude (we only need log scale)
    (8,   1/4, 3.33, 1009),
    (16,  1/4, 4.0,  7681),
    (32,  1/4, 6.0,  None),     # q ~ 2^30
    (64,  1/4, 5.0,  None),
    (256, 1/4, 4.5,  None),
    (1024,1/4, 4.5,  None),
    (2**20, 1/4, 4.5, None),    # true prize scale
    (2**30, 1/4, 4.5, None),
    (2**20, 1/8, 5.0, None),
    (2**20, 1/16,5.0, None),
]
print(f"\n  {'n':>8} {'rho':>6} {'beta':>5} {'log2 q':>8} {'delta_int':>9} {'a':>10} {'k':>9} {'a>=k?':>6} {'log2 cert':>10} {'cert>=q?':>8}")
for (n, rho, beta, q) in configs:
    if q is None:
        log2q = beta*log2(n)
        q = 2**round(log2q)
    else:
        log2q = log2(q)
    k = max(1, round(rho*n))
    johnson, mid, cap, half = window(n, rho)
    delta = mid                      # interior probe point
    t = floor((1-delta)*n)
    a, vac, l2cert, ge_q = cert_exponent(n, k, t, q)
    cert_str = "inf(vac)" if vac else f"{l2cert:8.1f}"
    ge_str = "YES" if ge_q else "no"
    print(f"  {n:>8} {rho:>6.3f} {beta:>5.2f} {log2q:>8.1f} {delta:>9.4f} {a:>10} {k:>9} "
          f"{('Y' if a>=k else 'N'):>6} {cert_str:>10} {ge_str:>8}")

print()
print("="*100)
print("PART 4.  Quantify the EXPONENT GAP  log2(cert) as fn of (rho,beta,n) AT THE HALF-EDGE")
print("  (the BEST case for the certificate: delta exactly at the non-vacuity threshold (1-rho)/2)")
print("="*100)
print("  At delta=(1-rho)/2: a = (1-2delta)n = rho*n = k EXACTLY (boundary). C(a,k)=C(k,k)=1.")
print("  => cert = C(n,k)/1 = C(n,k) ~ 2^{n H(rho)}.  Compare to budget q ~ n^beta = 2^{beta log2 n}.")
print(f"\n  {'n':>8} {'rho':>6} {'log2 C(n,k)':>12} {'log2 q (b=4.5)':>14} {'cert/q exp gap':>14}")
for n in [16, 64, 256, 1024, 2**20, 2**30]:
    for rho in [1/4]:
        k = round(rho*n)
        l2C = log2(comb(n,k)) if n <= 4096 else n*( -rho*log2(rho) - (1-rho)*log2(1-rho) )  # H(rho)*n
        beta = 4.5
        l2q = beta*log2(n)
        print(f"  {n:>8} {rho:>6.3f} {l2C:>12.1f} {l2q:>14.1f} {l2C - l2q:>14.1f}")

print()
print("  CONCLUSION: at the half-edge (best case for the cert) the certificate is already")
print("  2^{n H(rho)} >> q = 2^{beta log n}: exponential in n vs polynomial budget. Strictly")
print("  INSIDE the window (delta>half-edge) a<k and the cert is literally VACUOUS (0<=C(n,k)).")
print("  The 2delta->delta radius doubling is exactly what moves a below k. Confirmed.")
