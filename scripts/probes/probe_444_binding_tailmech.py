#!/usr/bin/env python3
"""
probe_444_binding_tailmech.py   (#444, FRESH LENS [binding-restriction], part 2)

probe_444_binding_coset_confinement.py found N(20%) = O(1): the MAX house is attained on
a handful of cosets.  But that does NOT by itself give the sqrt(n log n) win, because the
union bound's sqrt(log m) comes from the MAX-OF-m-fluctuations mechanism (max of m roughly
independent sub-Gaussians ~ sqrt(2 log m)), not from how many cosets tie the max.

THE DECISIVE TEST OF THE LENS:
  If we could restrict the house to an O(n)-sized DISTINGUISHED subset of cosets (the
  "monomial / dilation-extremal" directions) and the TRUE max over ALL m cosets were
  ALWAYS attained inside that O(n) subset, then max-over-O(n) = max-over-m, and the
  union bound would honestly only pay sqrt(log n).

  So the lens lives or dies on:  IS THERE A NATURAL O(n)-SIZED SUBSET D(n) OF COSETS,
  DEFINABLE WITHOUT KNOWING p, SUCH THAT argmax_b |eta_b| in D(n) ALWAYS?

CANDIDATE D(n) (the only group-theoretic O(n) subsets available):
  (a) The n cosets containing a SUBGROUP-SHIFT direction b = (1 - zeta) for zeta in mu_n
      (the "antipodal/difference" directions -- the dyadic-tower extremizers).
  (b) The cosets of the SQUARES sub-tower: b in mu_{n/2}-multiples (index doubling).
  (c) ALL cosets (control: |D| = m, must always contain argmax trivially).

We compute argmax coset over ALL m, then check membership of argmax in each candidate D.
If argmax repeatedly FALLS OUTSIDE every O(n) candidate D, the lens is REFUTED: the worst
coset is NOT a monomial/dilation-distinguished direction, so restricting to O(n) directions
strictly lowers the achievable house and the bound proof would be UNSOUND.

Also: directly compare  max over D(n)  vs  max over all m  (the GAP is the soundness loss).
"""
import sympy, cmath, math

TWO_PI = 2.0 * math.pi


def musub_gen(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return g, h, [pow(h, j, p) for j in range(n)]


def period_abs(b, G, p):
    w = TWO_PI / p
    return abs(sum(cmath.exp(1j * w * ((b * y) % p)) for y in G))


def coset_index(b, g, m, n, p):
    """Which coset g^r * mu_n does b live in?  r in [0, m).  b = g^e => r = e mod m."""
    # discrete log of b base g (small p, brute force)
    cur = 1
    for e in range(p - 1):
        if cur == b % p:
            return e % m
        cur = (cur * g) % p
    return None


def analyze(n, p):
    g, h, G = musub_gen(n, p)
    m = (p - 1) // n
    # max over ALL m cosets:  reps g^0..g^{m-1}
    best = (-1.0, None)
    for r in range(m):
        b = pow(g, r, p)
        a = period_abs(b, G, p)
        if a > best[0]:
            best = (a, r)
    M_all, argr = best
    # candidate D(a): cosets of directions b = (1 - zeta), zeta in mu_n, zeta != 1
    Da_cosets = set()
    for zeta in G:
        b = (1 - zeta) % p
        if b == 0:
            continue
        Da_cosets.add(coset_index(b, g, m, n, p))
    # candidate D(b): the n/2-tower -- cosets of mu_{n/2} reps that are squares-shifts.
    # use b = (1 - zeta^2), zeta in mu_n (square-tower difference directions)
    Db_cosets = set()
    for zeta in G:
        b = (1 - pow(zeta, 2, p)) % p
        if b == 0:
            continue
        Db_cosets.add(coset_index(b, g, m, n, p))
    # max over D(a):
    def maxover(cosets):
        bb = -1.0
        for r in cosets:
            if r is None:
                continue
            b = pow(g, r, p)
            a = period_abs(b, G, p)
            if a > bb:
                bb = a
        return bb
    M_Da = maxover(Da_cosets)
    M_Db = maxover(Db_cosets)
    in_Da = argr in Da_cosets
    in_Db = argr in Db_cosets
    return m, M_all, M_Da, M_Db, len(Da_cosets), len(Db_cosets), in_Da, in_Db


def find_primes(n, count, pcap=200000):
    out = []
    m = 2
    while len(out) < count:
        p = n * m + 1
        if p > pcap:
            break
        if sympy.isprime(p):
            out.append(p)
        m += 1
    return out


print("=" * 110)
print("LENS [binding-restriction] part 2: is argmax_b |eta_b| ALWAYS inside an O(n) monomial/diff subset?")
print("  D(a) = cosets of {1-zeta : zeta in mu_n};  D(b) = cosets of {1-zeta^2}.  |D| should be ~O(n) << m.")
print("=" * 110)
print(f"{'n':>4} {'p':>8} {'m':>6} {'M_all':>8} {'M_Da':>8} {'M_Db':>8} {'M_Da/M_all':>10} "
      f"{'|Da|':>5} {'|Db|':>5} {'argInDa':>8} {'argInDb':>8}")
print("-" * 110)

for n in (8, 16, 32):
    for p in find_primes(n, 8):
        m, M_all, M_Da, M_Db, lDa, lDb, inDa, inDb = analyze(n, p)
        ratio = M_Da / M_all if M_all > 0 else float('nan')
        print(f"{n:>4} {p:>8} {m:>6} {M_all:>8.3f} {M_Da:>8.3f} {M_Db:>8.3f} {ratio:>10.4f} "
              f"{lDa:>5} {lDb:>5} {str(inDa):>8} {str(inDb):>8}")
    print("-" * 110)

print()
print("REFUTATION CRITERION:  if M_Da/M_all < 1 (strict) repeatedly, OR argInDa = False,")
print("the worst coset is NOT captured by the O(n) monomial/difference subset => lens REFUTED")
print("(restricting to O(n) directions loses house => sqrt(n log n) bound would be UNSOUND).")
print("CONFIRMATION:  M_Da/M_all == 1.000 and argInDa = True for ALL primes => lens SURVIVES this gate.")
