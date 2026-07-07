#!/usr/bin/env python3
"""probe_466_floorbad64_decide.py -- DECIDE floor-bad(64) via the complement-polynomial
reformulation + a bilinear meet-in-the-middle (MITM) search.  Issue #466, lane FS1.

KEY REFORMULATION (derived & verified here at n=16,32 against the original residual test):
  Let A be an adjacent-7th-type pattern (subset of Z/n, |A| = 5n/8), points rho_j = omega^j
  (omega = primitive n-th root of unity in F_p, p = 1 mod n).  Let B = Z/n \ A be the
  COMPLEMENT (|B| = 3n/8) and Q_B(x) = prod_{j in B}(x - omega^j)  (monic, degree 3n/8).
  Then, with r(x) = x^{3n/4} mod P_A (P_A = prod_{j in A}(x-omega^j)):

      A realizable at p   <=>   deg r <= n/2   <=>   [x^i] Q_B = 0  for all i in [n/8+1, n/4-1].

  PROOF SKETCH: r*Q_B = x^{3n/4} Q_B mod (x^n - 1)  (since P_A Q_B = x^n - 1, deg(r Q_B) <= n-1).
  deg r <= n/2  <=>  deg(r Q_B) <= 7n/8  <=>  coeffs of (x^{3n/4}Q_B mod x^n-1) at degrees
  m in [7n/8+1, n-1] vanish; that coefficient equals b_{m-3n/4} = [x^{m-3n/4}]Q_B, and
  m-3n/4 ranges over [n/8+1, n/4-1].  (n=16: i=3; n=32: i=5,6,7; n=64: i=9..15.)

  This is TRANSLATION INVARIANT: A -> A+t sends [x^i]Q_B -> omega^{t(3n/8 - i)} [x^i]Q_B (unit
  scale), so realizability is preserved; the 4 rotations c0 are translates, so scanning c0=0 is
  COMPLETE for deciding floor-bad(n).

MITM at n=64 (c0=0 only):  Q_B = U * W  where
    U = Q_{b0} * Q_{b1}   (min-complement: b0 subset(4) of class 0, b1 subset(4) of class 1; deg 8)
    W = Q_{b2} * Q_{b3}   (maj-complement: b2 subset(8) of class 2, b3 subset(8) of class 3; deg 16)
  Condition [x^9..x^15](U W) = 0 is 7 equations, LINEAR in U for fixed W:
    sum_{a=0}^{8} U_a W_{i-a} = 0 (i=9..15), U_8=1  =>  A(W) (U_0..U_7) = -(W_1..W_7).
  Generic solution is a 1-dim affine line (8 unknowns, 7 eqns) -> enumerate p points, look up in a
  hash of all min-U's.  |min-U| = C(16,4)^2 = 3,312,400; |maj-W| = C(16,8)^2 = 165,636,900.

Subcommands:
  verify           cross-check the complement reformulation vs residual test (n=16, n=32 full)
  mitmtest <p>     validate the MITM engine at n=32 against the full residual scan (p=97 bad, else good)
  decide64 <p> [nproc]   run the full MITM decision at n=64 for prime p (=1 mod 64)
"""
import sys, itertools, time
from math import comb

# --------------------------------------------------------------------------- basics
def isprime(m):
    if m < 2: return False
    d = 2
    while d*d <= m:
        if m % d == 0: return False
        d += 1
    return True

def primitive_root(p):
    m = p-1; fac=[]; mm=m; d=2
    while d*d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fac.append(mm)
    for h in range(2, p):
        if all(pow(h, m//f, p) != 1 for f in fac):
            return h
    raise ValueError("no generator")

def mu_elems(p, n):
    assert (p-1) % n == 0 and isprime(p)
    g0 = pow(primitive_root(p), (p-1)//n, p)
    X = [pow(g0, j, p) for j in range(n)]
    assert len(set(X)) == n
    return g0, X

def pattern_params(n):
    m = n//4
    return m, m - m//4, m - m//2      # m, agr_min, agr_maj

def classes(n):
    return [[j for j in range(n) if j % 4 == c] for c in range(4)]

def poly_from_roots(roots, p):
    P = [1]
    for r in roots:
        Q = [0]*(len(P)+1)
        for i,c in enumerate(P):
            Q[i+1] = (Q[i+1] + c) % p
            Q[i]   = (Q[i]   - r*c) % p
        P = Q
    return P            # P[k] = coeff x^k, monic

def poly_mul(a, b, p):
    r = [0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai == 0: continue
        for j,bj in enumerate(b):
            r[i+j] = (r[i+j] + ai*bj) % p
    return r

# --------------------------------------------------------- ORIGINAL residual realizability test
def realizable_residual(p, n, X, A):
    """r = x^{3n/4} mod P_A ; realizable iff r_k==0 for k in [n/2+1, |A|-1].  (== scanner)."""
    half, deg34 = n//2, 3*n//4
    V = poly_from_roots([X[j] for j in A], p)     # P_A, monic, deg |A|
    D = len(V)-1                                  # |A|
    # r = x^deg34 mod V
    r = [(-V[k]) % p for k in range(D)]           # x^D mod V
    for _ in range(deg34 - D):
        top = r[D-1]; nr = [0]*D
        for k in range(D-1, 0, -1):
            nr[k] = (r[k-1] - top*V[k]) % p
        nr[0] = (-top*V[0]) % p
        r = nr
    return all(r[k] == 0 for k in range(half+1, D))

# --------------------------------------------------------- COMPLEMENT reformulation test
def realizable_complement(p, n, X, A):
    """A realizable  <=>  Q_B (complement poly) has zero coeffs at degrees [n/8+1, n/4-1]."""
    B = [j for j in range(n) if j not in set(A)]
    QB = poly_from_roots([X[j] for j in B], p)    # monic, deg 3n/8
    lo, hi = n//8 + 1, n//4 - 1
    return all(QB[i] % p == 0 for i in range(lo, hi+1))

# --------------------------------------------------------- enumerate full family (small n)
def patterns_iter(n):
    m, agr_min, agr_maj = pattern_params(n)
    cls = classes(n)
    cmin = list(itertools.combinations(range(m), agr_min))
    cmaj = list(itertools.combinations(range(m), agr_maj))
    for c0 in range(4):
        mn0, mn1, mj0, mj1 = c0, (c0+1)%4, (c0+2)%4, (c0+3)%4
        for a in cmin:
            for b in cmin:
                for d in cmaj:
                    for e in cmaj:
                        A = ([cls[mn0][i] for i in a] + [cls[mn1][i] for i in b]
                             + [cls[mj0][i] for i in d] + [cls[mj1][i] for i in e])
                        yield c0, sorted(A)

def cmd_verify():
    print("== VERIFY complement reformulation vs residual test ==")
    # n=16 : FULL exact enumeration (2304*4 patterns) residual vs complement
    for (p, exp) in [(17,160),(97,0),(193,0),(257,0)]:
        _, X = mu_elems(p, 16)
        cr = cc = 0; mismatch = 0
        for c0, A in patterns_iter(16):
            r1 = realizable_residual(p, 16, X, A)
            r2 = realizable_complement(p, 16, X, A)
            if r1 != r2: mismatch += 1
            cr += r1; cc += r2
        tag = "OK" if (mismatch==0 and cr==exp) else "*** FAIL ***"
        print(f"  n=16 p={p:4d}: residual={cr:4d}  complement={cc:4d}  "
              f"mismatches={mismatch}  expected={exp}  {tag}", flush=True)
    # n=32 : residual-vs-complement on a random sample (full pure-python scan too slow)
    import random
    for p in [97, 193, 257]:
        _, X = mu_elems(p, 32)
        m, agr_min, agr_maj = pattern_params(32); cls = classes(32)
        rng = random.Random(4660+p); mism = 0; NS = 40000
        for _ in range(NS):
            c0 = rng.randrange(4)
            A = (rng.sample(cls[c0], agr_min)+rng.sample(cls[(c0+1)%4], agr_min)
                 +rng.sample(cls[(c0+2)%4], agr_maj)+rng.sample(cls[(c0+3)%4], agr_maj))
            if realizable_residual(p,32,X,sorted(A)) != realizable_complement(p,32,X,sorted(A)):
                mism += 1
        print(f"  n=32 p={p:4d}: residual==complement on {NS} random patterns: "
              f"mismatches={mism}  {'OK' if mism==0 else '*** FAIL ***'}", flush=True)

# =========================================================== MITM engine (n=32 validate / n=64)
import numpy as np

def class_root_arrays(p, n):
    """For each class c, the array of field elements omega^j, j in class c (16 or 8 of them)."""
    _, X = mu_elems(p, n)
    cls = classes(n)
    return [np.array([X[j] for j in cls[c]], dtype=np.int64) for c in range(4)], cls, X

def batch_poly_from_roots(R, p):
    """R:(B,k) int64 roots -> (B,k+1) monic coeff arrays (index 0..k, [:,k]==1) mod p."""
    B, k = R.shape
    P = np.zeros((B, k+1), dtype=np.int64); P[:, 0] = 1
    for t in range(k):
        r = R[:, t:t+1]
        nP = np.zeros_like(P)
        nP[:, 1:t+2] = P[:, 0:t+1]
        nP[:, 0:t+1] = (nP[:, 0:t+1] - r * P[:, 0:t+1]) % p
        P = nP
    return P

def batch_conv(A, Bp, p):
    """(N,a),(N,b)->(N,a+b-1) product mod p."""
    N, a = A.shape; b = Bp.shape[1]
    out = np.zeros((N, a+b-1), dtype=np.int64)
    for s in range(a):
        out[:, s:s+b] = (out[:, s:s+b] + A[:, s:s+1]*Bp) % p
    return out

def build_side(root_arr_c0, root_arr_c1, ksub, p):
    """All products Q_{s0}*Q_{s1} for s0,s1 = ksub-subsets of the two class root-arrays.
    Returns (polys (Npair, 2*ksub+1), pairs list of (idx0,idx1))."""
    subs = list(itertools.combinations(range(len(root_arr_c0)), ksub))
    R0 = np.array([[root_arr_c0[i] for i in s] for s in subs], dtype=np.int64)
    R1 = np.array([[root_arr_c1[i] for i in s] for s in subs], dtype=np.int64)
    P0 = batch_poly_from_roots(R0, p)      # (nsub, ksub+1)
    P1 = batch_poly_from_roots(R1, p)
    nsub = len(subs)
    ii = np.repeat(np.arange(nsub), nsub); jj = np.tile(np.arange(nsub), nsub)
    Ppair = batch_conv(P0[ii], P1[jj], p)  # (nsub^2, 2*ksub+1)
    return Ppair, subs, nsub

def pow_batch(a, e, p):
    r = np.ones_like(a); base = a % p
    while e > 0:
        if e & 1: r = (r*base) % p
        base = (base*base) % p
        e >>= 1
    return r

def mitm_decide(p, n, verbose=True, stop_first=True):
    """MITM over c0=0 family (translation-complete): count realizable patterns at p and
    return the first witness.  Returns (count, witness_or_None, stats).
    If stop_first, returns as soon as one witness is found (count>=1)."""
    m, agr_min, agr_maj = pattern_params(n)
    kU = 2*(m - agr_min)          # deg U (min-complement)
    kW = 2*(m - agr_maj)          # deg W (maj-complement)
    lo, hi = n//8 + 1, n//4 - 1   # condition degrees on Q_B = U*W
    ncond = hi - lo + 1
    assert ncond == kU - 1, "MITM assumes ncond = kU-1 (1-dim solution line)"
    roots, cls, X = class_root_arrays(p, n)
    csz = m
    ksub_min = m - agr_min
    ksub_maj = m - agr_maj

    # ----- min side: all U, hashed by packed key of coeffs U_0..U_{kU-1} (U_kU==1)
    submin = list(itertools.combinations(range(csz), ksub_min))
    R0 = np.array([[roots[0][i] for i in s] for s in submin], dtype=np.int64)
    R1 = np.array([[roots[1][i] for i in s] for s in submin], dtype=np.int64)
    P0 = batch_poly_from_roots(R0, p); P1 = batch_poly_from_roots(R1, p)
    nsub_min = len(submin)
    ii = np.repeat(np.arange(nsub_min), nsub_min); jj = np.tile(np.arange(nsub_min), nsub_min)
    Umat = batch_conv(P0[ii], P1[jj], p)          # (Nmin, kU+1)
    Nmin = Umat.shape[0]
    hcoef, Ukeys_sorted, order, Umat_sorted = _make_hash(Umat, kU, p)
    ndup = 0

    # ----- maj side: products Q_{b2}*Q_{b3}
    submaj = list(itertools.combinations(range(csz), ksub_maj))
    RM2 = np.array([[roots[2][i] for i in s] for s in submaj], dtype=np.int64)
    RM3 = np.array([[roots[3][i] for i in s] for s in submaj], dtype=np.int64)
    P2 = batch_poly_from_roots(RM2, p); P3 = batch_poly_from_roots(RM3, p)
    nmaj = len(submaj); Nmaj = nmaj*nmaj
    if verbose:
        print(f"  [n={n} p={p}] min-U={Nmin} (dupkeys={ndup})  maj-W={Nmaj:,}  "
              f"conds={ncond}@deg[{lo},{hi}]  kU={kU} kW={kW}", flush=True)

    others_by_f = [[c for c in range(kU) if c != f] for f in range(kU)]
    t0 = time.time(); tested = 0; count = 0; first = None; rankdef_total = 0
    for a2 in range(nmaj):
        Wc = batch_conv(np.repeat(P2[a2:a2+1], nmaj, axis=0), P3, p)   # (nmaj, kW+1)
        c, fw, rd = mitm_chunk(Wc, p, kU, kW, lo, hi, ncond, Ukeys_sorted, hcoef, Umat_sorted,
                               others_by_f, order, nsub_min, submin, submaj, a2, stop_first)
        count += c; rankdef_total += rd
        if fw is not None and first is None:
            first = fw
        tested += nmaj
        if first is not None and stop_first:
            break
        if verbose and (a2 % max(1, nmaj//25) == 0):
            rate = tested/(time.time()-t0+1e-9)
            print(f"    [p={p}] b2 {a2+1}/{nmaj}  tested={tested:,}/{Nmaj:,}  "
                  f"count={count} rankdef={rankdef_total}  rate={rate:,.0f}/s  "
                  f"elapsed={time.time()-t0:.0f}s", flush=True)
    stats = dict(Nmin=Nmin, Nmaj=Nmaj, tested=tested, rankdef=rankdef_total,
                 secs=round(time.time()-t0,1))
    return count, first, stats

def _make_hash(Umat, kU, p):
    """Collision-free int64 hash of the min-U coeff vectors (U_0..U_{kU-1}).  Returns
    (hcoef, Ukeys_sorted, order, Umat_sorted[:, :kU]).  Re-seeds until all keys distinct."""
    N = Umat.shape[0]
    for seed in range(0xF100D + p, 0xF100D + p + 50):
        rng = np.random.default_rng(seed)
        hcoef = rng.integers(2**30, 2**40, size=kU, dtype=np.int64)
        Ukeys = (Umat[:, :kU] * hcoef[None, :]).sum(axis=1)     # < 2^53, exact
        order = np.argsort(Ukeys, kind='stable'); Uk = Ukeys[order]
        if len(np.unique(Uk)) == N:      # distinct -> single-probe lookup is complete
            return hcoef, Uk, order, np.ascontiguousarray(Umat[order][:, :kU])
    raise RuntimeError("could not find collision-free hash seed")

def mitm_chunk(Wc, p, kU, kW, lo, hi, ncond, Ukeys_sorted, hcoef, Umat_sorted, others_by_f,
               order, nsub_min, submin, submaj, a2, stop_first):
    """Count (and optionally return first) realizable (W,U) pairs in this maj chunk.  Uses a
    collision-free hash key + EXACT vector reverification on each hit (no false pos/neg).
    Returns (count, first_witness_or_None, rankdef_count)."""
    nW = Wc.shape[0]; Ns = len(Ukeys_sorted)
    Amat = np.zeros((nW, ncond, kU), dtype=np.int64)
    rhs  = np.zeros((nW, ncond), dtype=np.int64)
    for r in range(ncond):
        i = lo + r
        for a in range(kU):
            idx = i - a
            if 0 <= idx <= kW: Amat[:, r, a] = Wc[:, idx]
        idx8 = i - kU
        if 0 <= idx8 <= kW: rhs[:, r] = (-Wc[:, idx8]) % p
    count = 0; first = None
    remaining = np.arange(nW)
    for fcol in range(kU):
        if remaining.size == 0: break
        others = others_by_f[fcol]
        sub = Amat[np.ix_(remaining, np.arange(ncond), others)]   # (R,ncond,ncond)
        det, invM = batch_inv(sub, p)
        okinv = det != 0
        good = remaining[okinv]
        if good.size:
            invg = invM[okinv]
            Acol = Amat[good][:, :, fcol]           # (G,ncond)
            rg = rhs[good]                           # (G,ncond)
            u0 = np.einsum('gij,gj->gi', invg, rg) % p       # particular (t=0)
            ud = np.einsum('gij,gj->gi', invg, Acol) % p     # slope
            hco = hcoef[others]                      # (ncond,)
            hcf = int(hcoef[fcol])
            oarr = np.array(others)
            for t in range(p):
                uo = (u0 - t*ud) % p                 # (G,ncond)
                key = (uo * hco[None, :]).sum(axis=1) + hcf*t
                pos = np.searchsorted(Ukeys_sorted, key)
                pos = np.clip(pos, 0, Ns-1)
                match = Ukeys_sorted[pos] == key
                if not match.any():
                    continue
                for gi in np.nonzero(match)[0]:
                    sp = int(pos[gi])
                    # EXACT reverify: reconstruct full U* and compare to the stored vector
                    Ustar = np.empty(kU, dtype=np.int64)
                    Ustar[oarr] = uo[gi]; Ustar[fcol] = t
                    if np.array_equal(Umat_sorted[sp], Ustar):
                        count += 1
                        if first is None:
                            minrow = int(order[sp]); i0, i1 = divmod(minrow, nsub_min)
                            first = dict(b0=submin[i0], b1=submin[i1],
                                         b2=submaj[a2], b3=submaj[int(good[gi])])
                        if stop_first:
                            return count, first, 0
        remaining = remaining[~okinv]
    rd = int(remaining.size)
    if remaining.size:
        for w in remaining:
            hit = solve_exact_one(Amat[w], rhs[w], p, kU, hcoef, Ukeys_sorted, Umat_sorted,
                                  order, nsub_min, submin, submaj, a2, w)
            if hit is not None:
                count += hit[0]
                if first is None: first = hit[1]
                if stop_first: return count, first, rd
    return count, first, rd

def batch_inv(M, p):
    """Batched inverse of (B,k,k) matrices mod p via Gauss-Jordan.  Returns (det(B,), inv(B,k,k)).
    det==0 marks singular (inv invalid there)."""
    B, k, _ = M.shape
    A = M.copy() % p
    I = np.zeros((B, k, k), dtype=np.int64)
    for i in range(k): I[:, i, i] = 1
    det = np.ones(B, dtype=np.int64)
    singular = np.zeros(B, dtype=bool)
    for col in range(k):
        # find pivot: first row >= col with nonzero entry
        piv = np.full(B, -1, dtype=np.int64)
        for r in range(col, k):
            need = (piv < 0) & (A[:, r, col] % p != 0)
            piv[need] = r
        newsing = piv < 0
        singular |= newsing
        piv_safe = np.where(piv < 0, col, piv)
        # swap row col and piv
        ar = np.arange(B)
        tmp = A[ar, col, :].copy(); A[ar, col, :] = A[ar, piv_safe, :]; A[ar, piv_safe, :] = tmp
        tmpI = I[ar, col, :].copy(); I[ar, col, :] = I[ar, piv_safe, :]; I[ar, piv_safe, :] = tmpI
        pivval = A[:, col, col] % p
        pivval_safe = np.where(pivval == 0, 1, pivval)
        det = (det * pivval) % p
        inv_piv = pow_batch(pivval_safe, p-2, p)
        A[:, col, :] = (A[:, col, :] * inv_piv[:, None]) % p
        I[:, col, :] = (I[:, col, :] * inv_piv[:, None]) % p
        for r in range(k):
            if r == col: continue
            f = A[:, r, col].copy() % p
            A[:, r, :] = (A[:, r, :] - f[:, None]*A[:, col, :]) % p
            I[:, r, :] = (I[:, r, :] - f[:, None]*I[:, col, :]) % p
    det = np.where(singular, 0, det)
    return det, I

def solve_exact_one(A, rhs, p, kU, hcoef, Ukeys_sorted, Umat_sorted, order,
                    nsub_min, submin, submaj, a2, wrow):
    """RREF of [A|rhs], enumerate full solution space, hash-lookup + EXACT reverify.
    Rank-deficient/inconsistent case.  Returns (nmatches, first_witness) or None."""
    ncond = A.shape[0]
    M = np.concatenate([A % p, rhs.reshape(-1,1) % p], axis=1).astype(np.int64)
    pivcols = []; r = 0
    for c in range(kU):
        pr = None
        for rr in range(r, ncond):
            if M[rr, c] % p != 0: pr = rr; break
        if pr is None: continue
        M[[r, pr]] = M[[pr, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p-2, p)) % p
        for rr in range(ncond):
            if rr != r and M[rr, c] % p != 0:
                M[rr] = (M[rr] - M[rr, c]*M[r]) % p
        pivcols.append(c); r += 1
    for rr in range(r, ncond):
        if M[rr, kU] % p != 0:
            return None
    freecols = [c for c in range(kU) if c not in pivcols]
    import itertools as it
    nmatch = 0; first = None
    for vals in it.product(range(p), repeat=len(freecols)):
        u = np.zeros(kU, dtype=np.int64)
        for c, v in zip(freecols, vals): u[c] = v
        for ri, c in enumerate(pivcols):
            s = int(M[ri, kU])
            for c2 in freecols:
                s = (s - int(M[ri, c2])*int(u[c2])) % p
            u[c] = s % p
        key = int((u * hcoef).sum())
        pos = int(np.searchsorted(Ukeys_sorted, key))
        if pos < len(Ukeys_sorted) and Ukeys_sorted[pos] == key and np.array_equal(Umat_sorted[pos], u):
            nmatch += 1
            if first is None:
                minrow = int(order[pos]); i0, i1 = divmod(minrow, nsub_min)
                first = dict(b0=submin[i0], b1=submin[i1], b2=submaj[a2], b3=submaj[wrow])
    return (nmatch, first) if nmatch else None

def brute_complement_count(p, n):
    """Vectorized full c0=0 count of realizable patterns via the complement-coeff test.
    Enumerates ALL Q_B = U*W (min-U x maj-W) and counts those with [x^i]Q_B=0, i in[lo,hi]."""
    m, agr_min, agr_maj = pattern_params(n)
    kU = 2*(m-agr_min); kW = 2*(m-agr_maj)
    lo, hi = n//8+1, n//4-1
    roots, cls, X = class_root_arrays(p, n)
    ksub_min = m-agr_min; ksub_maj = m-agr_maj
    submin = list(itertools.combinations(range(m), ksub_min))
    R0 = np.array([[roots[0][i] for i in s] for s in submin], dtype=np.int64)
    R1 = np.array([[roots[1][i] for i in s] for s in submin], dtype=np.int64)
    P0 = batch_poly_from_roots(R0,p); P1 = batch_poly_from_roots(R1,p)
    ns = len(submin); ii=np.repeat(np.arange(ns),ns); jj=np.tile(np.arange(ns),ns)
    Umat = batch_conv(P0[ii],P1[jj],p)            # (Nmin,kU+1)
    submaj = list(itertools.combinations(range(m), ksub_maj))
    RM2 = np.array([[roots[2][i] for i in s] for s in submaj], dtype=np.int64)
    RM3 = np.array([[roots[3][i] for i in s] for s in submaj], dtype=np.int64)
    P2 = batch_poly_from_roots(RM2,p); P3 = batch_poly_from_roots(RM3,p)
    nmaj = len(submaj)
    count = 0
    for a2 in range(nmaj):
        Wc = batch_conv(np.repeat(P2[a2:a2+1],nmaj,axis=0), P3, p)   # (nmaj,kW+1)
        # QB = U*W for all pairs (Nmin x nmaj) -- check coeffs lo..hi
        for i in range(lo, hi+1):
            pass
        # compute coeff i of U*W for all (u, w): sum_a U[u,a]*W[w,i-a]
        ok = np.ones((Umat.shape[0], nmaj), dtype=bool)
        for i in range(lo, hi+1):
            acc = np.zeros((Umat.shape[0], nmaj), dtype=np.int64)
            for a in range(0, kU+1):
                b = i-a
                if 0 <= b <= kW:
                    acc = (acc + Umat[:, a:a+1]*Wc[:, b][None,:]) % p
            ok &= (acc % p == 0)
        count += int(ok.sum())
    return count

def cmd_mitmtest(p):
    n = 32
    print(f"== MITM validation at n=32, p={p} ==")
    # (1) residual-vs-complement agreement is checked in `verify`; here compare the MITM count
    #     to an independent vectorized brute complement full-count over the c0=0 family.
    brute = brute_complement_count(p, n)
    count, wit, stats = mitm_decide(p, n, verbose=False, stop_first=False)
    ok = (count == brute)
    print(f"  brute complement c0=0 realizable count = {brute}")
    print(f"  MITM count                             = {count}  (witness={wit})")
    print(f"  stats={stats}")
    print(f"  COUNTS AGREE = {ok}   {'OK' if ok else '*** FAIL ***'}")
    if wit is not None:
        _, X = mu_elems(p, n); cls = classes(n)
        B = sorted([cls[0][i] for i in wit['b0']]+[cls[1][i] for i in wit['b1']]
                   +[cls[2][i] for i in wit['b2']]+[cls[3][i] for i in wit['b3']])
        A = sorted(set(range(n))-set(B))
        print(f"  witness A realizable (residual test) = {realizable_residual(p,n,X,A)}")
    return ok

def cmd_symtest(p):
    """Validate the translation-symmetry-reduced existence decision at n=32 against ground truth."""
    n = 32
    count, wit, stats = mitm_decide_sym(p, n, nproc=1, stop_first=False, verbose=True)
    exp_found = (p == 97)
    ok = ((count > 0) == exp_found)
    print(f"  sym-reduced count(reps)={count} witness={wit} stats={stats}")
    if wit is not None:
        _, X = mu_elems(p, n); cls = classes(n)
        B = sorted([cls[0][i] for i in wit['b0']]+[cls[1][i] for i in wit['b1']]
                   +[cls[2][i] for i in wit['b2']]+[cls[3][i] for i in wit['b3']])
        A = sorted(set(range(n))-set(B))
        print(f"  witness residual-test realizable = {realizable_residual(p,n,X,A)}")
    print(f"  existence matches ground truth (bad iff p=97): {ok}  {'OK' if ok else '*** FAIL ***'}")
    return ok

def cmd_decide64(p, nproc=1, stop_first=True):
    n = 64
    if (p-1) % n or not isprime(p):
        print(f"p={p} not a split prime for n=64"); return
    print(f"== DECIDE floor-bad(64) membership of p={p} via complement MITM ==")
    print(f"   (c0=0 by translation-invariance; b2 over Z/16 rotation reps => COMPLETE for existence)")
    count, wit, stats = mitm_decide_sym(p, n, nproc=nproc, stop_first=stop_first, verbose=True)
    print(f"   stats: {stats}")
    if count > 0:
        print(f"  *** REALIZABLE: p={p} IS in floor-bad(64) ***  count={count} witness={wit}")
        certify64(p, wit)
    else:
        print(f"  NO realizable adjacent-7th-type pattern exists (COMPLETE scan of {stats['pairs']:,} "
              f"maj-reps x full min-set) => p={p} is NOT in floor-bad(64).")
    return count

# ===================== symmetry-reduced (translation-by-4 = Z/(n/4)) + parallel decision =====
def rotation_canonical_reps(m, k):
    """Indices (into itertools.combinations(range(m),k)) of subsets that are the lex-min among
    their m cyclic rotations (rotation r: i -> (i+r)%m).  Translation-by-4 in exponent == +1 in
    class index, so these represent the Z/m orbits of the maj-complement b2."""
    subs = list(itertools.combinations(range(m), k))
    reps = []
    for a, s in enumerate(subs):
        canon = min(tuple(sorted((i+r) % m for i in s)) for r in range(m))
        if tuple(s) == canon:
            reps.append(a)
    return reps, subs

def _mitm_worker(args):
    """Worker: process a subset of canonical b2 indices at (p,n).  Returns (count, witness, nb2)."""
    p, n, b2_reps, stop_first = args
    return _mitm_core(p, n, b2_reps, stop_first)

def _mitm_core(p, n, b2_reps, stop_first):
    m, agr_min, agr_maj = pattern_params(n)
    kU = 2*(m-agr_min); kW = 2*(m-agr_maj); lo, hi = n//8+1, n//4-1; ncond = hi-lo+1
    roots, cls, X = class_root_arrays(p, n)
    ksub_min = m-agr_min; ksub_maj = m-agr_maj
    submin = list(itertools.combinations(range(m), ksub_min))
    R0 = np.array([[roots[0][i] for i in s] for s in submin], dtype=np.int64)
    R1 = np.array([[roots[1][i] for i in s] for s in submin], dtype=np.int64)
    P0 = batch_poly_from_roots(R0, p); P1 = batch_poly_from_roots(R1, p)
    ns = len(submin); ii = np.repeat(np.arange(ns), ns); jj = np.tile(np.arange(ns), ns)
    Umat = batch_conv(P0[ii], P1[jj], p)
    # ROBUST collision-free hash key (avoids the p^kU int64-overflow of base-p packing for p>=236
    # at kU=8): key = sum_a U_a * hcoef_a with hcoef_a in [2^30,2^40) -> term<2^50, sum<2^53<2^63.
    # Re-seed until all stored keys are DISTINCT, so a single searchsorted + exact vector reverify
    # on a hit is complete (no false negatives) and false-positive-free (reverify rejects them).
    hcoef, Ukeys_sorted, order, Umat_sorted = _make_hash(Umat, kU, p)
    submaj = list(itertools.combinations(range(m), ksub_maj))
    RM2 = np.array([[roots[2][i] for i in s] for s in submaj], dtype=np.int64)
    RM3 = np.array([[roots[3][i] for i in s] for s in submaj], dtype=np.int64)
    P2 = batch_poly_from_roots(RM2, p); P3 = batch_poly_from_roots(RM3, p)
    nmaj = len(submaj)
    others_by_f = [[c for c in range(kU) if c != f] for f in range(kU)]
    count = 0; first = None; rd = 0
    for a2 in b2_reps:
        Wc = batch_conv(np.repeat(P2[a2:a2+1], nmaj, axis=0), P3, p)
        c, fw, r = mitm_chunk(Wc, p, kU, kW, lo, hi, ncond, Ukeys_sorted, hcoef, Umat_sorted,
                              others_by_f, order, ns, submin, submaj, a2, stop_first)
        count += c; rd += r
        if fw is not None and first is None: first = fw
        if first is not None and stop_first: break
    return count, first, len(b2_reps)

def mitm_decide_sym(p, n, nproc=1, stop_first=True, verbose=True):
    """Translation-symmetry-reduced existence decision over the c0=0 family.
    Iterate b2 over rotation-canonical reps x all b3 x full min-set (COMPLETE for existence)."""
    m, agr_min, agr_maj = pattern_params(n); ksub_maj = m-agr_maj
    reps, submaj = rotation_canonical_reps(m, ksub_maj)
    nmaj = len(submaj)
    if verbose:
        print(f"  [n={n} p={p}] canonical b2 reps={len(reps)}/{nmaj} (Z/{m} translation); "
              f"pairs scanned = {len(reps)}*{nmaj} = {len(reps)*nmaj:,} (vs full {nmaj*nmaj:,}); "
              f"nproc={nproc}", flush=True)
    t0 = time.time()
    if nproc <= 1:
        count, first, _ = _mitm_core(p, n, reps, stop_first)
    else:
        import multiprocessing as mp
        chunks = [reps[i::nproc] for i in range(nproc)]
        with mp.Pool(nproc) as pool:
            results = pool.map(_mitm_worker, [(p, n, ch, stop_first) for ch in chunks])
        count = sum(r[0] for r in results)
        first = next((r[1] for r in results if r[1] is not None), None)
    secs = round(time.time()-t0, 1)
    return count, first, dict(reps=len(reps), pairs=len(reps)*nmaj, secs=secs)

def certify64(p, wit):
    n = 64; _, X = mu_elems(p, n); cls = classes(n)
    b0 = [cls[0][i] for i in wit['b0']]; b1 = [cls[1][i] for i in wit['b1']]
    b2 = [cls[2][i] for i in wit['b2']]; b3 = [cls[3][i] for i in wit['b3']]
    B = sorted(b0+b1+b2+b3)
    A = sorted(set(range(n)) - set(B))
    ok = realizable_residual(p, n, X, A)
    print(f"    complement B (24) = {B}")
    print(f"    pattern   A (40) = {A}")
    print(f"    INDEPENDENT residual-test realizable = {ok}")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        cmd_verify()
    elif cmd == "mitmtest":
        cmd_mitmtest(int(sys.argv[2]))
    elif cmd == "symtest":
        cmd_symtest(int(sys.argv[2]))
    elif cmd == "decide64":
        nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 1
        sf = (sys.argv[4] != "count") if len(sys.argv) > 4 else True
        cmd_decide64(int(sys.argv[2]), nproc, sf)
    else:
        print(__doc__)
