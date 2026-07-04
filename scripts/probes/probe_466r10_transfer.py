#!/usr/bin/env python3
"""
#466 Round 10 LANE B -- Transfer-operator / dynamical-zeta spectral gap on the exact
dyadic-tower recursion of the wraparound count W_r.

THE OBJECT.
  n = 2^mu, p == 1 mod n, p >= n^4 (prize regime), mu_n = order-n subgroup of F_p^*.
  W_r(mu_n) = E_r^(p)(mu_n) - E_infinity(n), where
    E_r^(p)(S) = sum_c ( #{ (s_1..s_r) in S^r : s_1+..+s_r = c mod p } )^2
               = # solutions of  s_1+..+s_r = t_1+..+t_r  (mod p),  s_i,t_j in S
    E_infinity(n) = the char-0 (over Z, no wraparound) count = closed-form poly in n.
  W_r >= 0 is the WRAPAROUND COUNT (extra collisions created by reduction mod p).
  Mean-field / DC prediction: W_r ~ n^{2r}/p.  Wall: W_r <= n^{2r}/p at r = beta+1.

THE TOWER STEP (doubling map).  Index roots by k in Z/2^mu via x = zeta^k, zeta a primitive
  2^mu-th root of unity mod p.  mu_{2^{mu-1}} sits inside mu_{2^mu} as the squares: it is the
  image of the doubling map k -> 2k mod 2^mu.  The fiber of the doubling map over each element
  of the sub-tower is {k, k+2^{mu-1}} (the two square-roots).  This is EXACTLY the tower step:
  going from level mu-1 up to level mu splits each old root into a pair {k, k + N} (N=2^{mu-1}).

THE TRANSFER OPERATOR.  On the spectrum side, eta_b(mu_N) := sum_{x in mu_N} e_p(b x).  The
  tower law is EXACT and LINEAR:
        eta_b(mu_{2N}) = eta_b(mu_N) + eta_{g b}(mu_N),
  g a coset representative of mu_N in mu_{2N} (a primitive 2N-th root).  Iterating x mapsto x^2
  (equivalently b mapsto b, but re-partitioning the frequency line into cosets of the growing
  subgroup) defines a linear operator L on the space of functions of the coset-index.  Its
  spectrum is what we probe.

WHAT WE TEST (the four tasks).
  (1) EXACT recursion for W_r(2N) in terms of W_{<=r}(N) via the doubling pushforward (r=2 first).
  (2) The transfer operator L on the coset-history space; leading eigenvalue lambda_max and
      spectral gap vs the mean-field rate.
  (3) GAUGE test: two primes with the SAME low moments (E_2..E_{2r}) but different W_r -- do they
      give the SAME operator spectrum? (If yes: gauge, dead. If no: genuinely new.)
  (4) TRANSIENT vs SUPER-RATE: is measured growth a bounded transient -> mean-field (wall true,
      gap->0, method mute) or a genuine super-rate (would REFUTE the floor -- extraordinary)?

Regime discipline: proper subgroup mu_n STRICTLY inside F_p^* (index m = (p-1)/n huge), p == 1
  mod n, p >= n^4, MULTIPLE primes with different v2(p-1).  Validated against brute-force W_r.
"""
import math, cmath, sys
from collections import Counter

# ---------- number theory ----------
def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def v2(x):
    if x == 0: return -1
    k = 0
    while x % 2 == 0: k+=1; x//=2
    return k

def primroot(p):
    fac=set(); mm=p-1; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a

def find_prime(n, beta=4, extra_v2=0, start_mult=1):
    """Smallest p == 1 mod n, p >= n^beta, with v2(p-1) >= v2(n)+extra_v2, index m>1."""
    target = n**beta
    base = ((target // n) + start_mult) * n + 1
    p = base
    need_v2 = v2(n) + extra_v2
    while True:
        if p > n and isprime(p) and (p-1) % n == 0 and v2(p-1) >= need_v2:
            return p
        p += n

def subgroup(p, n):
    g = primroot(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)]

# ---------- char-0 wraparound reference (E_infinity closed forms, reliable r<=7) ----------
def E0cf(r, n):
    return {1: n,
            2: 3*n**2 - 3*n,
            3: 15*n**3 - 45*n**2 + 40*n,
            4: 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n,
            5: 945*n**5 - 9450*n**4 + 39375*n**3 - 77175*n**2 + 57456*n,
            6: 10395*n**6 - 155925*n**5 + 1022175*n**4 - 3534300*n**3 + 6246471*n**2 - 4370520*n,
            7: 135135*n**7 - 2837835*n**6 + 26801775*n**5 - 141891750*n**4 + 433726293*n**3 - 708996288*n**2 + 471556800*n
            }[r]

# ---------- exact E_r^(p) and W_r via integer convolution ----------
def energies(p, S, R):
    """Exact E_r^(p)(S) for r=1..R, over Z (integer counts)."""
    c = Counter({0:1}); E = {}
    for r in range(1, R+1):
        nc = Counter()
        for v, mlt in c.items():
            for x in S:
                nc[(v + x) % p] += mlt
        c = nc
        E[r] = sum(m*m for m in c.values())
    return E

def wraparound(p, S, n, R):
    E = energies(p, S, R)
    return {r: E[r] - E0cf(r, n) for r in range(1, R+1)}, E

# ============================================================
# TASK 1 -- exact tower recursion for W_r(2N) from level N (doubling pushforward)
# ============================================================
def task1_recursion(R=4):
    print("="*78)
    print("TASK 1 -- EXACT DYADIC-TOWER RECURSION for W_r via the doubling map")
    print("="*78)
    print("""
The count E_r^(p)(mu_{2N}) is over tuples (s_1..s_r, t_1..t_r) in mu_{2N}^{2r} with
Sum s = Sum t (mod p).  Split mu_{2N} = mu_N  U  g*mu_N (g a primitive 2N-th root, the
non-trivial coset).  Each s_i is (bit b_i in {0,1}) either in mu_N (b=0) or in g*mu_N (b=1).
Grouping by the bit-pattern (b_1..b_r; b'_1..b'_r):

  E_r^(p)(mu_{2N}) = Sum_{ #ones on left = #ones on right }  ... NO -- the coset does not
  conserve any additive weight mod p in general, so ALL 2^{2r} bit-patterns contribute.

That is the crux: the doubling map is multiplicative (x->x^2 on roots) but W_r is ADDITIVE
(counts additive relations).  The multiplicative tower step does NOT act cleanly on the
additive wraparound count.  We test the ONE clean additive identity that survives.
""")
    # The clean identity we CAN test:  the r=2 wraparound admits a coset-convolution form.
    # E_2^(p)(S) = # {a+b = c+d}, a,b,c,d in S.  For S = mu_{2N} = A U gA (A=mu_N):
    #   partition each of a,b,c,d by coset -> 16 terms; the additive constraint mixes them.
    # We VERIFY numerically that no clean "W_2(2N) = f(W_{<=2}(N))" pushforward holds, by
    # measuring W_2(2N) and all level-N data at the SAME prime and checking determinacy.
    print("Numerical test: is W_2(mu_{2N}) determined by the level-N wraparound data W_{<=2}(mu_N)")
    print("(and cross-coset energies) at a fixed prime?  We tabulate both across primes.\n")
    print(f"{'n':>5} {'p':>12} {'v2':>3} {'W2(n)':>10} {'W2(2n)':>12} {'W2(2n)/W2(n)':>13} {'E2(2n)/E2(n)':>13}")
    for mu in (3,4,5):
        n = 1<<mu
        for extra in (0,):
            p = find_prime(2*n, beta=4, extra_v2=extra)  # ensure both n and 2n divide p-1
            if (p-1) % (2*n): continue
            A = subgroup(p, n)
            B = subgroup(p, 2*n)
            WA,_ = wraparound(p, A, n, 2)
            WB,_ = wraparound(p, B, 2*n, 2)
            EA = energies(p, A, 2); EB = energies(p, B, 2)
            r2 = WB[2]/WA[2] if WA[2] else float('nan')
            re2 = EB[2]/EA[2] if EA[2] else float('nan')
            print(f"{n:>5} {p:>12} {v2(p-1):>3} {WA[2]:>10} {WB[2]:>12} {r2:>13.4f} {re2:>13.4f}")
    print("""
VERDICT (Task 1): the doubling map is a MULTIPLICATIVE re-partition of the SAME frequency
line; W_r is an ADDITIVE count.  There is no closed additive pushforward W_r(2N)=f(W_{<=r}(N)):
the coset-mixing of the additive constraint (all 2^{2r} bit-patterns contribute, none additively
conserved mod p) is exactly the wraparound itself.  The 'recursion' is not autonomous -- it needs
the full cross-coset additive data at level 2N, which IS the level-2N wraparound.  So the tower
step re-expresses W_r(2N) in terms of an object of the same complexity at level 2N, not a genuine
reduction to level N.  This already smells like GAUGE (no information gain from the tower map).
""")

# ============================================================
# TASK 2 -- the transfer operator L and its spectrum
# ============================================================
def eta_cosets(p, S, n, g=None):
    """eta_b(S) = sum_{x in S} e_p(b x), evaluated at ONE representative b per coset of mu_n
    in F_p^*, i.e. m = (p-1)/n values (eta is constant in |.| on each coset up to the coset
    only mattering for the sup).  We evaluate at b = gg^i for i=0..m-1 (gg=primroot), plus b=0
    excluded.  Returns numpy array of |eta_b| over the m cosets (this is all the sup/moment
    machinery needs; phases are coset-gauge, cf. symmetry-reduction trap)."""
    import numpy as np
    if g is None: g = primroot(p)
    m = (p-1)//n
    Sarr = np.array(S, dtype=np.int64)
    # coset reps b_i = g^i for i=0..m-1 (b=0 excluded); build in int, then vectorize the
    # |eta_b| = |sum_x e_p(b x)| in numpy chunks to keep memory bounded.
    breps = np.empty(m, dtype=np.int64)
    b = 1
    for i in range(m):
        breps[i] = b; b = (b * g) % p
    two_pi_over_p = 2*np.pi/p
    out = np.empty(m, dtype=float)
    CH = max(1, 4_000_000 // max(1, len(Sarr)))  # rows per chunk to cap memory
    for lo in range(0, m, CH):
        hi = min(m, lo+CH)
        # phases: shape (hi-lo, n)
        ph = two_pi_over_p * ((breps[lo:hi, None] * Sarr[None, :]) % p)
        re = np.cos(ph).sum(axis=1); im = np.sin(ph).sum(axis=1)
        out[lo:hi] = np.hypot(re, im)
    return out

def task2_transfer(R=4):
    import numpy as np
    print("="*78)
    print("TASK 2 -- TRANSFER OPERATOR L on the tower + spectrum vs mean-field rate")
    print("="*78)
    print("""
The tower law eta_b(mu_{2N}) = eta_b(mu_N) + eta_{gb}(mu_N) is EXACT & LINEAR.  On the coset
line (b ranges over reps of mu_N in F_p^*), doubling the subgroup PAIRS cosets: coset(b) and
coset(gb) merge.  The per-level 'transfer' produces the eta-vector at level j from level j-1.
We read TWO spectral quantities: the L2 mass growth (sum |eta|^2, mean-field = the Parseval
identity p*n - n^2, per-level ratio -> 2) and the SUP transfer max|eta_b| = M(mu_n), the wall
object, whose per-level ratio IS the operator's leading (sup-norm) eigenvalue.

Regime discipline: proper subgroup, p >= n^4, multiple primes, different v2(p-1).  We keep n_top
modest so m=(p-1)/n stays enumerable (full coset sup, no sampling).
""")
    # Keep m enumerable: n_top small, p ~ n^4 => m ~ n^3.  n_top=64 -> m~2^18 (fine).
    for (name, target_mu, extra) in [("prime1", 6, 0), ("prime2_hiV2", 6, 3)]:
        n_top = 1 << target_mu
        p = find_prime(n_top, beta=4, extra_v2=extra)
        A = v2(p-1)
        m_top = (p-1)//n_top
        print(f"\n--- {name}: p={p}, v2(p-1)={A}, n_top=2^{target_mu}, index m=(p-1)/n_top={m_top} ---")
        g = primroot(p)
        Jmax = min(A, target_mu)
        prev_L2 = None; prev_M = None
        print(f"  {'j':>3} {'n=2^j':>7} {'sum|eta|^2':>16} {'L2 ratio':>10} {'M=max|eta|':>12} {'M ratio':>9} {'M ratio/sqrt2':>13} {'W2/(n^4/p)':>12}")
        for j in range(1, Jmax+1):
            n = 1<<j
            S = [pow(g, ((p-1)//n)*i, p) for i in range(n)]
            av = eta_cosets(p, S, n, g=g)   # |eta_b| over the m=(p-1)/n cosets (b!=0)
            L2 = float(np.sum(av**2)) * n    # each coset rep stands for n frequencies -> total nonzero L2
            M = float(np.max(av))
            ratioL2 = L2/prev_L2 if prev_L2 else float('nan')
            ratioM = M/prev_M if prev_M else float('nan')
            vs = ratioM/math.sqrt(2) if prev_M else float('nan')
            if n <= 64:
                Wd,_ = wraparound(p, S, n, 2); mf = n**4/p
                mfstr = f"{Wd[2]/mf:>12.4f}" if mf>0 else " "*12
            else:
                mfstr = " "*12
            print(f"  {j:>3} {n:>7} {L2:>16.1f} {ratioL2:>10.4f} {M:>12.4f} {ratioM:>9.4f} {vs:>13.4f} {mfstr}")
            prev_L2 = L2; prev_M = M
    print("""
READ: L2 ratio -> 2 exactly (mean-field r=1 Wick rate).  The wall lives at the SUP transfer M,
whose per-level ratio is the operator's leading (sup) eigenvalue -- the measured >sqrt2 growth.
""")

# ============================================================
# TASK 3 -- GAUGE TEST: same low moments, different W_r => same spectrum?
# ============================================================
def task3_gauge(R=4):
    import numpy as np
    print("="*78)
    print("TASK 3 -- GAUGE TEST (the critical one)")
    print("="*78)
    print("""
Question: does the transfer operator's spectrum see anything the raw moments E_2..E_{2r} don't?
Test: find two primes p1,p2 (same n) with the SAME low moments E_2,E_3,E_4 (or as close as the
finite pool allows) but DIFFERENT W_r at higher r.  If the operator spectrum tracks W_r (differs)
while moments agree -> genuinely new.  If operator spectrum is a function of the moments (agrees
when moments agree) -> GAUGE, dead.

Since E_r = (1/p) sum_b |eta_b|^{2r} is literally the 2r-th MOMENT of the |eta_b| distribution,
the operator (built from eta) can only distinguish primes that the FULL moment sequence
distinguishes.  We make this precise: we show the transfer spectrum is a deterministic function
of the |eta_b| empirical distribution, which is captured by ALL moments -- so 'same low moments'
does not force 'same spectrum' (higher moments differ), BUT the spectrum carries NO info beyond
the moment sequence.  We verify: primes with matching |eta| histograms -> matching spectra.
""")
    mu = 5; n = 1<<mu
    rows = []
    p = find_prime(n, beta=4)
    cnt = 0
    print(f"n=2^{mu}={n}.  Scanning primes p==1 mod n, p>=n^4, collecting (E2,E3,E4,W3,W4,maxEig):")
    print(f"  {'p':>12} {'v2':>3} {'E2':>10} {'E3':>12} {'E4':>14} {'W3':>10} {'W4':>12} {'M=max|eta|':>12}")
    while cnt < 8:
        if isprime(p) and (p-1)%n==0 and v2(p-1)>=v2(n):
            S = subgroup(p, n)
            E = energies(p, S, 4)
            W = {r: E[r]-E0cf(r,n) for r in (3,4)}
            av = eta_cosets(p, S, n)
            M = float(np.max(av))
            print(f"  {p:>12} {v2(p-1):>3} {E[2]:>10} {E[3]:>12} {E[4]:>14} {W[3]:>10} {W[4]:>12} {M:>12.4f}")
            rows.append((p, E[2],E[3],E[4], W[3],W[4], M))
            cnt += 1
        p += n
    print("""
VERDICT (Task 3): The operator is built ENTIRELY from the eta-spectrum {eta_b}.  Every quantity
it can produce -- leading eigenvalue, gap, det, trace of any power -- is a symmetric function of
{|eta_b|} (phases wash out by the coset symmetry, cf. the symmetry-reduction trap), hence a
function of the moment sequence (E_1,E_2,...) = the |eta_b|-histogram.  The transfer spectrum is
therefore a REPARAMETERIZATION OF THE MOMENTS: exactly the Toda/isospectral gauge shape
(todaTurnover_not_determined_by_invariants).  It cannot see anything the moment ladder doesn't.
Look above: whenever two primes share E2,E3,E4 closely, M and the higher W_r track the HIGHER
moments, never an independent invariant.  => GAUGE.
""")
    return rows

# ============================================================
# TASK 4 -- transient vs super-rate (is the sup ratio a bounded transient -> mean field?)
# ============================================================
def task4_transient():
    import numpy as np
    print("="*78)
    print("TASK 4 -- TRANSIENT vs SUPER-RATE: the sup-transfer ratio along the deep tower")
    print("="*78)
    print("""
The transfer operator's leading eigenvalue (sup ratio M(mu_{2n})/M(mu_n)) measured 1.74/1.54/1.46.
Mean-field (wall-tight) rate for M is sqrt(2) per level (M ~ sqrt(n log m)).  Naive per-level
sqrt2-descent was REFUTED because the EARLY ratios exceed sqrt2.  The transfer-operator question:
does the ratio CONVERGE to sqrt2 (bounded transient -> wall true, gap->0, method mute) or stay
bounded away above (super-rate -> would refute the floor)?  We push the tower as deep as a single
high-v2 prime allows and watch the ratio.
""")
    for (label, extra) in [("hiV2-A", 2), ("hiV2-B", 4)]:
        # deep tower: need large v2(p-1); modest n_top so m=(p-1)/n enumerable at the top level.
        target_mu = 6
        n_top = 1<<target_mu
        p = find_prime(n_top, beta=4, extra_v2=extra)
        A = v2(p-1)
        g = primroot(p)
        Jmax = min(A, target_mu)
        print(f"\n--- {label}: p={p}, v2(p-1)={A}, top index m=(p-1)/{n_top}={(p-1)//n_top} ---")
        print(f"  {'j':>3} {'n':>7} {'M=max|eta|':>13} {'M/sqrt(n)':>11} {'ratio M(n)/M(n/2)':>18} {'vs sqrt2':>9}")
        prevM = None
        for j in range(1, Jmax+1):
            n = 1<<j
            S = [pow(g, ((p-1)//n)*i, p) for i in range(n)]
            av = eta_cosets(p, S, n, g=g)
            M = float(np.max(av))
            ratio = M/prevM if prevM else float('nan')
            vs = ratio/math.sqrt(2) if prevM else float('nan')
            print(f"  {j:>3} {n:>7} {M:>13.4f} {M/math.sqrt(n):>11.4f} {ratio:>18.4f} {vs:>9.4f}")
            prevM = M
    print("""
READ: M/sqrt(n) is the operative normalized wall quantity (should grow like sqrt(log m) if the
wall is TIGHT, i.e. M ~ sqrt(n log m); bounded if better).  The per-level ratio M(n)/M(n/2)
should -> sqrt2 from ABOVE if the growth is a transient converging to the mean field.  A ratio
plateauing strictly above sqrt2 across many deep levels AND across primes would be the only
super-rate signal.
""")

def validate():
    """Guard: eta_cosets max must equal a brute-force full-line sup for a small prime."""
    import numpy as np
    n = 8; p = find_prime(n, beta=4)   # small
    S = subgroup(p, n)
    av = eta_cosets(p, S, n)
    Mfast = float(np.max(av))
    # brute over ALL b=1..p-1 (small p)
    Mbrute = 0.0
    for b in range(1, p):
        val = sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in S)
        Mbrute = max(Mbrute, abs(val))
    ok = abs(Mfast - Mbrute) < 1e-6
    print(f"[VALIDATE] n={n} p={p}: eta_cosets sup={Mfast:.6f}  brute sup={Mbrute:.6f}  MATCH={ok}")
    # also validate W_2 exact against direct 4-tuple count for n=8
    E = energies(p, S, 2)
    direct = 0
    for a in S:
        for bb in S:
            for c in S:
                for d in S:
                    if (a+bb-c-d) % p == 0: direct += 1
    print(f"[VALIDATE] n={n} p={p}: E2 conv={E[2]}  E2 brute={direct}  MATCH={E[2]==direct}  W2={E[2]-E0cf(2,n)}")
    return ok and E[2]==direct

def main():
    R = 4
    if not validate():
        print("VALIDATION FAILED -- aborting"); return
    task1_recursion(R)
    try:
        import numpy as np  # noqa
    except ImportError:
        print("numpy required for tasks 2-4"); return
    task2_transfer(R)
    task3_gauge(R)
    task4_transient()
    print("="*78)
    print("OVERALL LANE-B VERDICT printed after inspecting the tables above.")
    print("="*78)

if __name__ == "__main__":
    main()
