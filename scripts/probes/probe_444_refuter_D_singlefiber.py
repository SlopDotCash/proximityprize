#!/usr/bin/env python3
"""
probe_444_refuter_D_singlefiber.py   (#444 SEAM A -- REFUTER D)

Two independent jobs, exact arithmetic, multiple primes, proper subgroups (n != p-1),
correlated directions x^{n/2}=+-1 EXCLUDED.

JOB 1  single-fiber term scaling.
  For the TRUE worst weight-2 word u = x^a + x^b on mu_n (found by exact enumeration over
  ALL (a,b) with a!=b, a,b != n/2, max window list L), and for EVERY list member f
  (deg<k poly agreeing with u on >= s points of mu_n), split into even/odd:
     f(x) = F(x^2) + x G(x^2),  u(x) = u_e(x^2) + x u_o(x^2),
     P = F - u_e,  Q = G - u_o   (all polys in y over mu_N, N=n/2).
  Then by the DESCENT IDENTITY the agreement of f decomposes as
     |S| = 2*#{y: P=Q=0} + |S_1|,   S_1 = {y in mu_N : Q(y)!=0 and P(y)^2 = y Q(y)^2}.
  We measure, for each list member:
     - deg(P^2 - X*Q^2)  as a polynomial over F_p  (the curve P^2 = X Q^2 in (X,?))
     - actual |S_1|  (count of y in mu_N on the single fiber)
  CLAIM under test: |S_1| = O(k), NOT O(n).  REFUTATION = |S_1| grows with n at fixed rho.

JOB 2  weight-2 descent recursion.
  u = x^a + x^b.
    * SAME parity (a,b both even or both odd): claim u descends to a weight-2 word
      x^{a'} + x^{b'} on mu_N with a'=a//2, b'=b//2 (after factoring the common x-parity),
      i.e. the even-or-odd half-word is again a 2-term word on mu_N.
    * MIXED parity: claim u descends to a MONOMIAL PAIR (u_e and u_o each a single monomial).
    * depth: same-parity halving terminates at a monomial pair after exactly v2(a-b) levels.
  We verify by EXPLICIT polynomial bookkeeping of the even/odd split, descending level by
  level, and confirming the parent window list vs the child window list relationship
     L_parent(u on mu_n) <= branching^{depth} * (monomial-pair list)
  is consistent (we report the actual numbers, do not assume).

A refutation in EITHER job (|S_1| ~ n, or descent depth/structure wrong) is a WIN.
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

# ----------------------------------------------------------------------------- arithmetic
def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta)
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x * zeta) % p
    assert len(set(e)) == n
    return e

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def poly_trim(c):
    c = list(c)
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    return c

def poly_deg(c):
    c = poly_trim(c)
    if len(c) == 1 and c[0] == 0:
        return -1   # zero polynomial
    return len(c) - 1

def poly_sub(a, b, p):
    n = max(len(a), len(b))
    r = [0] * n
    for i in range(len(a)): r[i] = (r[i] + a[i]) % p
    for i in range(len(b)): r[i] = (r[i] - b[i]) % p
    return r

def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p); den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)): c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)

def peval(c, x, p):
    r = 0
    for a in reversed(c): r = (r * x + a) % p
    return r

# ----------------------------------------------------------------------------- list
def full_list(uvals, elts, k, s, p):
    """list of (coeffs, agreement_size) for deg<k polys agreeing with u on >= s pts of mu_n."""
    n = len(elts); seen = {}
    for T in itertools.combinations(range(n), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        seen[c] = ag
    return [(c, a) for c, a in seen.items() if a >= s]

def true_worst_weight2(n, k, s, p, exclude_half=True):
    """exact: worst (a,b), a!=b, (optionally a,b != n/2), maximizing window list L."""
    elts = subgroup(n, p)
    best = (-1, None, None)   # (L, (a,b), list)
    for a in range(0, n):
        for b in range(0, a):
            if exclude_half and (a == n // 2 or b == n // 2):
                continue
            u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
            lst = full_list(u, elts, k, s, p)
            if len(lst) > best[0]:
                best = (len(lst), (a, b), lst)
    return best, elts

# ----------------------------------------------------------------------------- even/odd split
def split_even_odd(coeffs, p):
    """f(x)=sum coeffs[i] x^i  ->  (F, G) with f(x)=F(x^2)+x G(x^2), polys in y."""
    F = [coeffs[i] for i in range(0, len(coeffs), 2)]
    G = [coeffs[i] for i in range(1, len(coeffs), 2)]
    return poly_trim(F or [0]), poly_trim(G or [0])

def word_split_even_odd(a, b, N, p):
    """u(x)=x^a+x^b ; return (u_e, u_o) polys in y s.t. u(x)=u_e(x^2)+x u_o(x^2).
       a monomial x^c contributes to u_e (if c even, y^{c/2}) or to u_o (if c odd, y^{(c-1)/2})."""
    ue = [0] * (N)   # degrees in y up to <N
    uo = [0] * (N)
    for c in (a, b):
        if c % 2 == 0:
            ue[(c // 2) % N] = (ue[(c // 2) % N] + 1) % p
        else:
            uo[((c - 1) // 2) % N] = (uo[((c - 1) // 2) % N] + 1) % p
    return poly_trim(ue), poly_trim(uo)

# ----------------------------------------------------------------------------- JOB 1
def job1_single_fiber(n, k, eta, beta=4.0, n_for_label=None):
    N = n // 2
    p = find_window_prime(n, beta)
    rho = k / n
    s = round((rho + eta) * n); s = max(s, k); s = min(s, n)
    (L, ab, lst), elts = true_worst_weight2(n, k, s, p)
    a, b = ab
    eltsN = sorted({(x * x) % p for x in elts})
    assert len(eltsN) == N, f"squaring map not 2:1 onto mu_N ({len(eltsN)} vs {N})"
    ue, uo = word_split_even_odd(a, b, N, p)
    max_S1 = -1
    max_deg = -1
    rows = []
    for (c, agree) in lst:
        F, G = split_even_odd(c, p)
        P = poly_sub(F, ue, p)
        Q = poly_sub(G, uo, p)
        # curve poly  R(X) = P(X)^2 - X Q(X)^2   (as polynomial in y=X)
        P2 = poly_mul(P, P, p)
        Q2 = poly_mul(Q, Q, p)
        XQ2 = poly_mul([0, 1], Q2, p)            # X * Q^2
        R = poly_sub(P2, XQ2, p)
        dR = poly_deg(R)
        # actual single-fiber count over mu_N
        s1 = 0; common = 0
        for y in eltsN:
            Pv = peval(P, y, p); Qv = peval(Q, y, p)
            if Pv == 0 and Qv == 0:
                common += 1
            elif Qv != 0 and (Pv * Pv - y * Qv * Qv) % p == 0:
                s1 += 1
        # cross-check the descent identity for this member
        assert 2 * common + s1 == agree, \
            f"DESCENT IDENTITY FAILED member agree={agree} 2*{common}+{s1}"
        max_S1 = max(max_S1, s1)
        max_deg = max(max_deg, dR)
        rows.append((agree, common, s1, dR, poly_deg(P), poly_deg(Q)))
    label = n_for_label or n
    print(f"  [JOB1] n={n}(N={N}) k={k} rho={rho:.4f} eta={eta} s={s} p={p}  "
          f"worst word x^{a}+x^{b}  L={L}")
    print(f"         identity verified for all {L} members; "
          f"max|S_1|={max_S1}  max deg(P^2-X Q^2)={max_deg}   "
          f"(k={k}, 2k-1={2*k-1}, n={n})")
    # show distribution
    s1vals = sorted({r[2] for r in rows})
    degvals = sorted({r[3] for r in rows})
    print(f"         |S_1| values seen: {s1vals}   deg(R) values seen: {degvals}")
    return dict(n=n, N=N, k=k, p=p, s=s, worst=(a, b), L=L,
                max_S1=max_S1, max_deg=max_deg, ratio_S1_over_k=max_S1 / k)

# ----------------------------------------------------------------------------- JOB 2
def v2(m):
    m = abs(m)
    if m == 0: return None
    c = 0
    while m % 2 == 0:
        m //= 2; c += 1
    return c

def descend_word(a, b, n):
    """one descent level of the word x^a+x^b on mu_n -> describe child on mu_{n/2}.
       returns (kind, child) where kind in {'same-even','same-odd','mixed'} and
       child is (a',b') for same-parity (a 2-term word on mu_{n/2}) or
       ((ce,), (co,)) monomial-pair exponents for mixed."""
    N = n // 2
    pa, pb = a % 2, b % 2
    if pa == pb:
        # same parity: both go to the SAME of u_e/u_o; the word halves to x^{a'}+x^{b'} on mu_N
        if pa == 0:
            return ('same-even', (a // 2 % N, b // 2 % N))
        else:
            return ('same-odd', ((a - 1) // 2 % N, (b - 1) // 2 % N))
    else:
        # mixed parity: one term -> u_e (a single monomial), the other -> u_o (a single monomial)
        if pa == 0:
            ce = a // 2 % N; co = (b - 1) // 2 % N
        else:
            ce = b // 2 % N; co = (a - 1) // 2 % N
        return ('mixed', (ce, co))

def job2_descent_depth():
    print("\n### JOB 2: weight-2 descent recursion structure ###")
    ok = True
    # exhaustive over (n, a, b) symbolic descent: verify
    #   (i) same-parity -> weight-2 child on mu_{n/2}
    #   (ii) mixed-parity -> monomial pair
    #   (iii) same-parity halving terminates at FIRST mixed level after exactly v2(a-b) levels
    for n in [16, 32, 64, 128]:
        for a in range(1, n):
            for b in range(0, a):
                depth_pred = v2(a - b)         # claimed number of same-parity levels before mixing
                # walk the descent
                ca, cb = a, b
                cn = n
                level = 0
                terminated_at = None
                trace = []
                while cn >= 2:
                    kind, child = descend_word(ca, cb, cn)
                    trace.append((cn, ca, cb, kind))
                    if kind == 'mixed':
                        terminated_at = level
                        break
                    # same parity -> continue halving on mu_{n/2}
                    ca, cb = child
                    cn //= 2
                    level += 1
                    if cn < 2:
                        terminated_at = None  # collapsed to mu_1 without ever mixing
                        break
                # the SAME-parity run length should equal v2(a-b)
                if terminated_at is not None and terminated_at != depth_pred:
                    ok = False
                    print(f"   DEPTH MISMATCH n={n} (a,b)=({a},{b}): "
                          f"v2(a-b)={depth_pred} but mixed first at level {terminated_at}")
                    print(f"       trace={trace}")
                    if not ok and n == 16:
                        pass
    print(f"   same-parity-depth == v2(a-b) for all (n,a,b) tested: {ok}")
    # numeric parent/child window-list relationship at small n
    print("\n   parent vs child window-list (numeric, worst weight-2 word):")
    for (n, k, eta) in [(16, 2, 0.125), (32, 2, 0.0625), (32, 4, 0.125)]:
        N = n // 2
        beta = 4.0
        p = find_window_prime(n, beta)
        rho = k / n
        s = round((rho + eta) * n); s = max(s, k); s = min(s, n)
        (L, ab, _), _ = true_worst_weight2(n, k, s, p)
        a, b = ab
        kind, child = descend_word(a, b, n)
        # child window list on mu_N with code deg < ceil(k/2) (even or odd half has ~k/2 coeffs)
        kc = max(1, (k + 1) // 2)
        pN = find_window_prime(N, beta)
        eltsN = subgroup(N, pN)
        if kind in ('same-even', 'same-odd'):
            ca, cb = child
            uc = [(pow(y, ca, pN) + pow(y, cb, pN)) % pN for y in eltsN]
            childname = f"x^{ca}+x^{cb}"
        else:
            ce, co = child
            uc = [(pow(y, ce, pN) + pow(y, co, pN)) % pN for y in eltsN]  # not exactly the descent word but a 2-term proxy
            childname = f"x^{ce}+x^{co}(monpair-proxy)"
        rhoc = kc / N
        sc = round((rhoc + eta) * N); sc = max(sc, kc); sc = min(sc, N)
        Lc = len(full_list(uc, eltsN, kc, sc, pN)) if comb(N, kc) <= 3_000_000 else None
        print(f"     n={n} k={k} worst x^{a}+x^{b}  L={L}  ->  kind={kind} child {childname} "
              f"on mu_{N} (kc={kc},sc={sc})  L_child={Lc}   v2(a-b)={v2(a-b)}")
    return ok

# ----------------------------------------------------------------------------- main
if __name__ == "__main__":
    print("### JOB 1: single-fiber term |S_1| scaling for TRUE worst weight-2 word ###")
    results = []
    # n=16,32 for several k; n=64 only for small k (enumeration cost C(n,k))
    configs = [
        (16, 2, 0.125),
        (16, 4, 0.0625),
        (32, 2, 0.0625),
        (32, 4, 0.125),
        (64, 2, 0.0625),
    ]
    for (n, k, eta) in configs:
        if comb(n, k) > 3_000_000:
            print(f"  [JOB1] n={n} k={k}: SKIP C(n,k)={comb(n,k)}")
            continue
        try:
            r = job1_single_fiber(n, k, eta)
            results.append(r)
        except AssertionError as e:
            print(f"  [JOB1] n={n} k={k}: ASSERTION {e}")
    print("\n  [JOB1 SUMMARY] (n, k, max|S_1|, |S_1|/k, max deg R, 2k-1):")
    for r in results:
        print(f"     n={r['n']:3d} k={r['k']} : max|S_1|={r['max_S1']:2d}  "
              f"|S_1|/k={r['ratio_S1_over_k']:.2f}  max deg(P^2-X Q^2)={r['max_deg']:2d}  2k-1={2*r['k']-1}")
    job2_descent_depth()
