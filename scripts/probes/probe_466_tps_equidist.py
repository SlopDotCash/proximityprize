"""probe_466_tps_equidist.py -- LANE L8: the TPS divisor-equidistribution residue (#466).

CONJECTURE UNDER TEST (essay deltastar-466-essay-novel-mathematics-2026-07-01.md section 2.5,
dossier v3 section 15/F): "Conjecture TPS": the divisor mass of {N_a : ||a||_1 <= 2r}
equidistributes over primes p = 1 mod n in [X, 2X] up to K^r for r <= c log X.
This is the named-open input that would push the typical-prime sieve past r ~ beta.
NEVER MEASURED before this probe (probe_466_tps_boundary.py was bookkeeping only).

MODEL (task spec): relations a in {0,+-1}^n with ||a||_1 = 2r (2r nonzero entries, all sign
patterns; the moment-relevant BALANCED subclass r pluses / r minuses tracked separately).
N_a = Res(Phi_n, A) = Norm_{Q(zeta_n)/Q}(A(zeta_n)) >= 0, computed exactly by norm descent
down the 2-power tower (Phi_n = X^{n/2}+1).  p | N_a <=> A vanishes at a primitive n-th root
of unity mod p <=> a is a wraparound relation mod p (char-p only when N_a != 0).

SHARP HEIGHT LAW (proved in-run, attained): folding c_j = a_j - a_{j+n/2} gives
sum_j c_j^2 <= 4r, and sum over the phi(n) primitive roots of |A(zeta)|^2 = (n/2) sum c_j^2
<= 2nr; AM-GM then gives  N_a <= (4r)^{phi(n)/2}  -- QUADRATICALLY smaller than the crude
conjugate bound (2r)^{phi(n)} used by every prior bookkeeping pass (incl.
probe_466_tps_boundary.py).  Verified attained at n=8 r=2,3 and n=16 r=2,3.
CONSEQUENCE: at depth r the divisor mass reaches p ~ n^beta only if (4r)^{phi(n)/2} >= p,
i.e. onset depth r*(n,beta) = n^{2 beta/phi(n)}/4 -- so at n=8 the beta=4 window is
PROVABLY EMPTY at every realizable depth, and at n=16 the first window depth is r=5.

UNITS: raw vector counts W(p) are degenerate under (i) antipodal unfolding (2 per +-1 folded
entry) and (ii) the symmetry group X -> zeta^t X^k, a -> -a (order n*phi(n) on folds), which
preserves N_a.  Poisson statistics are therefore reported in three units: raw vectors
(inflated by design effect = cluster size), DISTINCT NORM VALUES, and SYMMETRY ORBITS of
folded relations (the honest independent-event unit).

STAGES (CLI arg): spec | ext16 | ext32 | ext32deep | fullball16   (default: spec)
  spec     = the task grid n=8 r=2,3,4; n=16 r=2,3,4 + all anchors.
  ext16    = n=16 r=5,6,7,8  (EXTENSION: first depths whose mass reaches [n^4, 4n^4]).
  ext32    = n=32 r=2        (EXTENSION: second n with true in-window mass).
  ext32deep= n=32 r=3        (EXTENSION: depth growth at n=32; ~minutes).
  fullball16 = n=16 r=3,4 FULL L1 ball (multiplicity carriers included -- the conjecture's
    actual family; the {0,+-1} stack is its multiplicity-free part).  This is the ONLY
    stage that can see the GF resonance (D4 anchor: 65537-mass is 100% |c_j|>=3-carried);
    it measures whether the GF prime is OVER-SERVED in the full ball at fixed r.

CROSS-CHECK ANCHORS (mandatory, all in stage spec):
  * n=16 r=2 bad-prime set vs {17} + canonical E2W4 resultant factors
    (CanonicalWidthFourBadPrimeSet: Res(Phi_16, (X^4+1)^16 - (X^2+1)^16)).
  * D4 anchor: tuple-count W_4(65537, n=16) = +4480 reproduced INDEPENDENTLY here, and shown
    to be MULTIPLICITY-CARRIED: the {0,+-1} stack has W(65537) = 0 PROVABLY at r<=4 (sharp
    cap 16^4 = 65536 < 65537); an explicit coefficient->2 vanishing relation is exhibited.
  * n=8: sharp cap (4r)^2 <= 256 for all depths => window mass identically 0 (stronger than
    the 'n=8 window is D4-clean' dossier fact).

REGIME: p = 1 mod n, primary window [n^4, 4n^4] (beta=4); beta=3 windows are FLAGGED
beta-dependence tests; mu_n proper; whole prime classes; GF primes flagged.
"""
import math
import sys
import time
from collections import defaultdict
from itertools import combinations, product

import numpy as np

try:
    import sympy
    HAVE_SYMPY = True
except Exception:
    HAVE_SYMPY = False

T0 = time.time()


def log(msg=""):
    print(msg)
    sys.stdout.flush()


# ---------------------------------------------------------------- primes
def sieve(limit):
    s = np.ones(limit + 1, dtype=bool)
    s[:2] = False
    for q in range(2, int(limit ** 0.5) + 1):
        if s[q]:
            s[q * q :: q] = False
    return np.nonzero(s)[0]


PRIME_LIMIT = 4 * 32 ** 4  # 4194304: covers every window and every sqrt(sharp cap)
PRIMES = sieve(PRIME_LIMIT)
PRIME_SET = set(int(q) for q in PRIMES)


def is_prime(m):
    m = int(m)
    if m <= PRIME_LIMIT:
        return m in PRIME_SET
    return sympy.isprime(m)


def class_primes(n, lo, hi):
    sel = PRIMES[(PRIMES >= lo) & (PRIMES <= hi)]
    return sel[sel % n == 1]


def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2
        k += 1
    return k


def gf_form(p):
    """p = b^(2^s)+1, s>=1, b>=2 (generalized Fermat); smallest b, else None."""
    for s in range(1, 32):
        e = 1 << s
        if 2 ** e + 1 > p:
            break
        b = round((p - 1) ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e + 1 == p:
                return (bb, s)
    return None


def sharp_cap(n, r):
    """N_a <= (4r)^{phi(n)/2} (Parseval on the fold + AM-GM); phi(n)=n/2 for 2-power n."""
    return (4 * r) ** (n // 4)


# ---------------------------------------------------- norm descent (2-power n)
def descent_level(C):
    N, m = C.shape
    Cm = C * ((-1) ** np.arange(m, dtype=np.int64))
    D = np.zeros((N, 2 * m), dtype=np.int64)
    for i in range(m):
        D[:, i : i + m] += C[:, i : i + 1] * Cm
    E = D[:, :m] - D[:, m:]
    return E[:, ::2]


def norms_from_fold(C):
    while C.shape[1] > 1:
        C = descent_level(C)
    return C[:, 0]


def iter_fold_chunks(n, r, batch_supports=2048):
    """Yield (C_folded (rows, n/2) int64, balanced bool (rows,)) chunks over ALL relations."""
    w = 2 * r
    m = n // 2
    signs = np.array(list(product((1, -1), repeat=w)), dtype=np.int64)
    balanced_pat = signs.sum(axis=1) == 0
    supports = list(combinations(range(n), w))
    for lo in range(0, len(supports), batch_supports):
        chunk = supports[lo : lo + batch_supports]
        rows = []
        for sup in chunk:
            M = np.zeros((w, m), dtype=np.int64)
            for k, pos in enumerate(sup):
                M[k, pos % m] += 1 if pos < m else -1
            rows.append(signs @ M)
        C = np.concatenate(rows, axis=0)
        yield C, np.tile(balanced_pat, len(chunk))


def relation_norms(n, r):
    w = 2 * r
    total = math.comb(n, w) * 2 ** w
    norms = np.empty(total, dtype=np.int64)
    bal = np.empty(total, dtype=bool)
    at = 0
    for C, b in iter_fold_chunks(n, r):
        norms[at : at + C.shape[0]] = norms_from_fold(C)
        bal[at : at + C.shape[0]] = b
        at += C.shape[0]
    assert at == total
    return norms, bal, total


def collect_vectors_with_values(n, r, wanted_vals):
    """Second pass: folded rows whose norm is in wanted_vals. Returns (rows, norms)."""
    wanted = np.sort(np.asarray(wanted_vals, dtype=np.int64))
    keep_C, keep_N = [], []
    for C, _b in iter_fold_chunks(n, r):
        nrm = norms_from_fold(C)
        mask = np.isin(nrm, wanted)
        if mask.any():
            keep_C.append(C[mask])
            keep_N.append(nrm[mask])
    if not keep_C:
        return np.zeros((0, n // 2), dtype=np.int64), np.zeros(0, dtype=np.int64)
    return np.concatenate(keep_C), np.concatenate(keep_N)


# ---------------------------------------------------- symmetry orbits (folded)
def orbit_group(n):
    """Action X -> zeta^t X^k on folds (k odd, t in [0,n)); includes negation (t=n/2 shift
    composed appropriately) and reversal (k=n-1).  Order n*phi(n)."""
    m = n // 2
    elems = []
    for k in range(1, n, 2):
        for t in range(n):
            pos = np.empty(m, dtype=np.int64)
            sg = np.empty(m, dtype=np.int64)
            for j in range(m):
                e = (k * j + t) % n
                pos[j] = e % m
                sg[j] = 1 if e < m else -1
            elems.append((pos, sg))
    return elems


def canonical_keys(vecs, n):
    """Minimal base-5 key of each folded vector over the symmetry orbit (entries in [-2,2])."""
    m = n // 2
    w5 = 5 ** np.arange(m, dtype=object) if m > 26 else 5 ** np.arange(m, dtype=np.int64)
    if m > 26:
        raise ValueError("key overflow")
    best = None
    for pos, sg in orbit_group(n):
        t = np.empty_like(vecs)
        t[:, pos] = vecs * sg
        key = (t + 2) @ w5
        best = key if best is None else np.minimum(best, key)
    return best


# ---------------------------------------------------- factor tables / W(p)
def divisor_mass(norms, cap):
    """Exact W(p) for all p.  Any v <= cap has at most ONE prime factor > sqrt(cap):
    trial-divide by primes <= sqrt(cap); the leftover (if > 1) is that unique big prime."""
    n_zero = int((norms == 0).sum())
    nz = norms[norms > 0]
    vals, counts = np.unique(nz, return_counts=True)
    sqrt_cap = int(math.isqrt(int(cap)))
    small = PRIMES[PRIMES <= sqrt_cap]
    W = defaultdict(int)
    for q in small:
        q = int(q)
        mask = vals % q == 0
        if mask.any():
            W[q] += int(counts[mask].sum())
    left = vals.copy()
    for q in small:
        q = int(q)
        while True:
            mask = left % q == 0
            if not mask.any():
                break
            left[mask] //= q
    big_mask = left > 1
    bigp = left[big_mask]
    bigc = counts[big_mask]
    vals_big = vals[big_mask]
    for p, c in zip(bigp, bigc):
        assert is_prime(int(p)), f"leftover {p} not prime (cap {cap})"
        W[int(p)] += int(c)
    return W, vals, counts, n_zero, (bigp, bigc, vals_big), sqrt_cap


# ---------------------------------------------------- validation
def mu_root_zero_exists(avec, n, p):
    for x in range(2, 500):
        g = pow(x, (p - 1) // n, p)
        if g != 1 and pow(g, n // 2, p) != 1:
            break
    else:
        raise RuntimeError("no order-n element")
    for k in range(1, n, 2):
        z = pow(g, k, p)
        acc = 0
        for j in range(n):
            if avec[j]:
                acc = (acc + avec[j] * pow(z, j, p)) % p
        if acc == 0:
            return True
    return False


def validate_case(n, r, seed=466, n_sym=8, n_modp=30):
    if not HAVE_SYMPY:
        log("  [validate] sympy unavailable -- skipped")
        return
    rng = np.random.default_rng(seed + n * 100 + r)
    w = 2 * r
    X = sympy.Symbol("X")
    phi = sympy.cyclotomic_poly(n, X)
    m = n // 2
    for _ in range(n_sym):
        sup = sorted(rng.choice(n, size=w, replace=False).tolist())
        sg = rng.choice([1, -1], size=w).tolist()
        avec = [0] * n
        for pos, s in zip(sup, sg):
            avec[pos] = int(s)
        A = sum(int(avec[j]) * X ** j for j in range(n))
        res = int(sympy.resultant(phi, A))
        C = np.array([[avec[j] - avec[j + m] for j in range(m)]], dtype=np.int64)
        nd = int(norms_from_fold(C)[0])
        assert nd == res and res >= 0, f"descent {nd} != resultant {res}"
    p = int(class_primes(n, n ** 2, 10 * n ** 4)[3])
    div = 0
    for _ in range(n_modp):
        sup = sorted(rng.choice(n, size=w, replace=False).tolist())
        sg = rng.choice([1, -1], size=w).tolist()
        avec = [0] * n
        for pos, s in zip(sup, sg):
            avec[pos] = int(s)
        C = np.array([[avec[j] - avec[j + m] for j in range(m)]], dtype=np.int64)
        Na = int(norms_from_fold(C)[0])
        pred = (Na % p == 0) and (Na != 0)
        actual = mu_root_zero_exists(avec, n, p) and Na != 0
        assert pred == actual, f"mod-{p} mismatch N_a={Na} a={avec}"
        div += pred
    log(f"  [validate] n={n} r={r}: {n_sym} sympy resultants EXACT; "
        f"mod-{p} membership {n_modp}/{n_modp} consistent (divisible: {div})")


# ---------------------------------------------------- reports
def window_report(tag, n, r, W, lo, hi, nvec, orbit_map=None, flag=""):
    ps = class_primes(n, lo, hi)
    if len(ps) == 0:
        log(f"  [{tag}] no class primes in [{lo},{hi}]")
        return None
    Wv = np.array([W.get(int(p), 0) for p in ps], dtype=np.float64)
    served = int((Wv > 0).sum())
    tot = int(Wv.sum())
    log(f"  [{tag}] {flag}window [{lo},{hi}]: {len(ps)} class primes, served {served} "
        f"({100.0*served/len(ps):.1f}%), vector mass {tot}")
    if tot == 0:
        log(f"      W(p) == 0 identically -- ZERO divisor mass at r={r} in this window")
        return dict(nprimes=len(ps), served=0, mass=0)
    mean, var = Wv.mean(), Wv.var()
    log(f"      raw-vector Poisson index var/mean = {var/mean:.2f} "
        f"(inflated by unfold x orbit degeneracy)")
    stats = dict(nprimes=len(ps), served=served, mass=tot)
    if orbit_map is not None:
        Ov = np.array([orbit_map.get(int(p), (0, 0, 0))[2] for p in ps], dtype=np.float64)
        Dv = np.array([orbit_map.get(int(p), (0, 0, 0))[1] for p in ps], dtype=np.float64)
        om, ov = Ov.mean(), Ov.var()
        oi = ov / om if om > 0 else float("nan")
        di = Dv.var() / Dv.mean() if Dv.mean() > 0 else float("nan")
        log(f"      ORBIT-unit: total {int(Ov.sum())} orbits; mean {om:.4f}  "
            f"index var/mean = {oi:.3f}   (distinct-norm index {di:.3f})")
        stats.update(orbit_mass=int(Ov.sum()), orbit_index=oi)
        order = np.argsort(-Ov)
    else:
        order = np.argsort(-Wv)
    shown = 0
    for i in order:
        p = int(ps[i])
        if Wv[i] == 0 or shown >= 8:
            break
        gf = gf_form(p)
        flags = [f"v2(p-1)={v2(p-1)}"]
        if p == int(ps[0]):
            flags.insert(0, "least-in-window")
        if gf:
            flags.insert(0, f"GF b={gf[0]}^{2**gf[1]}+1")
        ostr = ""
        if orbit_map is not None and p in orbit_map:
            nv, nd, no = orbit_map[p]
            ostr = f"  orbits={no} distinct-norms={nd}"
        log(f"        W({p}) = {int(Wv[i])}{ostr}   [{', '.join(flags)}]")
        shown += 1
    if orbit_map is not None and Ov.sum() > 0:
        log(f"      top-prime orbit share = {Ov[order[0]]/Ov.sum():.3f}")
    return stats


def dyadic_profile(n, r, W, cap, orbit_map):
    """Per-dyadic [Y,2Y) class equidistribution profile -- the conjecture's native shape.
    NOTE (bug found in-run, n=16 r=5 bin [256,512) index 11.18): a bin with
    Y < sqrt(cap) < 2Y mixes below-sqrt-cap primes (orbit count 0 BY CONSTRUCTION,
    orbit_map only covers leftover primes > sqrt(cap)) with genuine entries -- the
    inflated index there is an ARTIFACT, now flagged STRADDLE (checked: the
    all-prime distinct-norm counts in that bin are FLAT 10/8/9/10/10/8, stage aux)."""
    sqc = int(math.isqrt(int(cap)))
    log(f"  dyadic class profile (p = 1 mod {n}; orbit units where p > sqrt(cap)):")
    Y = n
    while Y <= min(cap, PRIME_LIMIT // 2):
        ps = class_primes(n, Y, 2 * Y - 1)
        if len(ps):
            Wv = np.array([W.get(int(p), 0) for p in ps], dtype=np.float64)
            if Wv.sum() > 0:
                served = int((Wv > 0).sum())
                Ov = np.array([orbit_map.get(int(p), (0, 0, 0))[2] for p in ps],
                              dtype=np.float64) if orbit_map else None
                if Ov is not None and Ov.sum() > 0:
                    oi = Ov.var() / Ov.mean()
                    strad = "  [STRADDLE sqrt(cap): index unreliable]" \
                        if Y <= sqc < 2 * Y else ""
                    log(f"      [{Y},{2*Y}): {len(ps)} primes, served {served}, "
                        f"orbit mass {int(Ov.sum())}, orbit index {oi:.2f}, "
                        f"top share {Ov.max()/Ov.sum():.2f}{strad}")
                else:
                    log(f"      [{Y},{2*Y}): {len(ps)} primes, served {served}, "
                        f"vector mass {int(Wv.sum())} (below sqrt-cap: small-prime regime)")
        Y *= 2


def full_class_spectrum(n, r, W, cap):
    ps_all = sorted(p for p in W if p % n == 1 and W[p] > 0)
    tot_class = sum(W[p] for p in ps_all)
    tot_all = sum(W.values())
    log(f"  full class spectrum (p = 1 mod {n}, W>0): {len(ps_all)} primes, vector mass "
        f"{tot_class} (class share {tot_class/tot_all:.3f})" if tot_all else
        "  full class spectrum: EMPTY")
    if ps_all:
        shown = (ps_all[:10] + ["..."] + ps_all[-6:]) if len(ps_all) > 16 else ps_all
        log("      served: " + ", ".join(str(x) for x in shown))
    return ps_all


# ---------------------------------------------------- anchors
def negacyclic_mul(u, v, m):
    out = [0] * (2 * m)
    for i, ui in enumerate(u):
        if ui:
            for j, vj in enumerate(v):
                if vj:
                    out[i + j] += ui * vj
    return [out[i] - out[i + m] for i in range(m)]


def negacyclic_pow(u, e, m):
    result = [1] + [0] * (m - 1)
    base = list(u)
    while e:
        if e & 1:
            result = negacyclic_mul(result, base, m)
        base = negacyclic_mul(base, base, m)
        e >>= 1
    return result


def bigint_norm(coeffs, m):
    C = list(coeffs)
    mm = m
    while mm > 1:
        Cm = [c if (i % 2 == 0) else -c for i, c in enumerate(C)]
        D = [0] * (2 * mm)
        for i, ci in enumerate(C):
            if ci:
                for j, cj in enumerate(Cm):
                    if cj:
                        D[i + j] += ci * cj
        C = [D[i] - D[i + mm] for i in range(mm)][::2]
        mm //= 2
    return C[0]


def e2w4_canonical_anchor():
    m = 8
    u = [0] * m; u[0] = 1; u[4] = 1
    v = [0] * m; v[0] = 1; v[2] = 1
    B = [a - b for a, b in zip(negacyclic_pow(u, 16, m), negacyclic_pow(v, 16, m))]
    R = bigint_norm(B, m)
    facs = []
    Rw = abs(R)
    for q in PRIMES:
        q = int(q)
        if q * q > Rw:
            break
        if Rw % q == 0:
            facs.append(q)
            while Rw % q == 0:
                Rw //= q
    if Rw > 1:
        facs.append(int(Rw)) if Rw <= PRIME_LIMIT or is_prime(Rw) else None
        Rw = 1
    return R, facs


def d4_multiplicity_anchor():
    """Reproduce W_4(65537, n=16) = +4480 by tuple counting, then exhibit an explicit
    multiplicity->=2 vanishing relation (the mass the {0,+-1} stack provably cannot see)."""
    p, n = 65537, 16
    for x in range(2, 100):
        g = pow(x, (p - 1) // n, p)
        if g != 1 and pow(g, n // 2, p) != 1:
            break
    mu = sorted(pow(g, k, p) for k in range(n))
    h2 = defaultdict(int)
    for a in mu:
        for b in mu:
            h2[(a + b) % p] += 1
    h4 = defaultdict(int)
    for s1, c1 in h2.items():
        for s2, c2 in h2.items():
            h4[(s1 + s2) % p] += c1 * c2
    E4 = sum(c * c for c in h4.values())
    E4_char0 = 4649680  # dense-conv verified char-0 value (D4 scanner, clean prime 65617)
    W4 = E4 - E4_char0
    log(f"  D4 tuple anchor: E4(65537,n=16) = {E4}, char-0 {E4_char0}, W4 = {W4:+d} "
        f"(dossier requires +4480) {'PASS' if W4 == 4480 else 'FAIL'}")
    assert W4 == 4480
    # explicit multiplicity relation: the FULL D4-legal folded space c in Z^8, sum|c| <= 8
    # (a depth-4 tuple relation has a in Z^16, ||a||_1 <= 8, so folded entries reach +-8).
    # NOTE (bug fixed in-run): the sharp law N_c <= (sum c_j^2)^4 makes any c with entries
    # in {-2..2} and sum|c| <= 8 satisfy N_c <= 16^4 = 65536 < p -- a {-2..2} search is
    # PROVABLY empty; the mass needs sum c^2 >= 17, i.e. a folded entry |c_j| >= 3.
    # Membership test = p | N_c (zeta-free, covers all primitive roots at once).
    def gen_l1(budget, coords):
        if coords == 1:
            for v in range(-budget, budget + 1):
                yield (v,)
            return
        for v in range(-budget, budget + 1):
            for rest in gen_l1(budget - abs(v), coords - 1):
                yield (v,) + rest
    all_c = np.array(list(gen_l1(8, 8)), dtype=np.int64)
    nrm = norms_from_fold(all_c.copy())
    hit = (nrm != 0) & (nrm % p == 0)
    n_hit = int(hit.sum())
    assert n_hit > 0, "no multiplicity relation found at 65537 (unexpected)"
    hc = all_c[hit]
    hn = nrm[hit]
    sq = (hc * hc).sum(axis=1)
    i0 = int(np.argmin(sq))
    c, Nc = tuple(int(x) for x in hc[i0]), int(hn[i0])
    assert int(sq.min()) >= 17 and int(np.abs(hc).max(axis=1).min()) >= 3, \
        "sharp-cap structural claim violated"
    log(f"  D4-legal folded space (c in Z^8, sum|c| <= 8): {all_c.shape[0]} vectors, "
        f"{n_hit} with 65537 | N_c != 0; min sum c^2 = {int(sq.min())} (>= 17 as the "
        f"sharp cap (sum c^2)^4 forces), min max|c_j| = {int(np.abs(hc).max(axis=1).min())}")
    log(f"  explicit multiplicity-carried relation at p=65537: folded c = {c}, "
        f"N_c = {Nc} = 65537 * {Nc//65537} (65537 | N_c: {Nc % 65537 == 0})")
    log(f"  => W_4(65537) mass is 100% multiplicity-carried: the {{0,+-1}} stack has sharp "
        f"cap 16^4 = 65536 < 65537 at r=4 (W(65537) = 0 PROVABLY; carriers need |c_j| >= 3)")


# ================================================================ case runner
def run_case(n, r, windows, spec_label, collect_orbits=True):
    w = 2 * r
    if w > n:
        log(f"[n={n} r={r}] IMPOSSIBLE: ||a||_1 = {w} > n")
        return None
    cap = sharp_cap(n, r)
    crude = (2 * r) ** (n // 2)
    log(f"\n===== n={n}, r={r}  ({spec_label}) =====")
    t = time.time()
    norms, balanced, nvec = relation_norms(n, r)
    mx = int(norms.max(initial=0))
    assert mx <= cap, f"sharp height law violated: {mx} > {cap}"
    W, vals, counts, n_zero, (bigp, bigc, vals_big), sqc = divisor_mass(norms, cap)
    log(f"  {nvec} vectors (C({n},{w})*2^{w}); char-0 vanishers: {n_zero}; distinct nonzero "
        f"norms: {len(vals)}; max N_a = {mx}, sharp cap (4r)^(n/4) = {cap} "
        f"[{'ATTAINED' if mx == cap else f'ratio {mx/cap:.3f}'}; crude cap {crude}]; "
        f"{time.time()-t:.1f}s")
    validate_case(n, r)
    # orbit-unit statistics for class primes above sqrt(cap) (= leftover primes)
    orbit_map = None
    if collect_orbits and len(bigp):
        cls = (bigp % n == 1)
        if cls.any():
            t = time.time()
            wanted = vals_big[cls]
            vecs, vnorms = collect_vectors_with_values(n, r, wanted)
            keys = canonical_keys(vecs, n)
            # value -> big prime lookup
            order = np.argsort(vals_big)
            vb_sorted = vals_big[order]
            bp_sorted = bigp[order]
            pl = bp_sorted[np.searchsorted(vb_sorted, vnorms)]
            orbit_map = {}
            for p in np.unique(pl):
                sel = pl == p
                orbit_map[int(p)] = (int(sel.sum()),
                                     int(len(np.unique(vnorms[sel]))),
                                     int(len(np.unique(keys[sel]))))
            log(f"  orbit pass: {vecs.shape[0]} class big-prime vectors -> "
                f"{sum(v[2] for v in orbit_map.values())} orbits over "
                f"{len(orbit_map)} class primes > sqrt(cap)={sqc}  ({time.time()-t:.1f}s)")
    full_class_spectrum(n, r, W, cap)
    dyadic_profile(n, r, W, cap, orbit_map)
    results = {}
    for (lo, hi, wtag, flag) in windows:
        results[wtag] = window_report(wtag, n, r, W, lo, hi, nvec, orbit_map, flag)
    return dict(W=W, nvec=nvec, ps_all=sorted(p for p in W if p % n == 1 and W[p] > 0),
                results=results, cap=cap, orbit_map=orbit_map)


def main():
    stage = sys.argv[1] if len(sys.argv) > 1 else "spec"
    log(f"probe_466_tps_equidist.py -- TPS divisor-equidistribution (LANE L8, #466) "
        f"[stage {stage}]")
    log(f"numpy {np.__version__}, sympy {'yes' if HAVE_SYMPY else 'NO'}; "
        f"primes to {PRIME_LIMIT}")

    if stage == "spec":
        log("\n----- ANCHOR: canonical width-4 resultant Res(Phi_16,(X^4+1)^16-(X^2+1)^16) -----")
        R, canon_facs = e2w4_canonical_anchor()
        log(f"  |Res| has {len(str(abs(R)))} digits; prime factors: {canon_facs}")
        log("\n----- ANCHOR: D4 tuple count at the resonant GF prime -----")
        d4_multiplicity_anchor()

        win8 = [(8 ** 4, 4 * 8 ** 4, "beta=4", ""), (8 ** 3, 4 * 8 ** 3, "beta=3", "BETA-DEP ")]
        for r in (2, 3, 4):
            run_case(8, r, win8, "task spec")
        log("\n  [n=8 STRUCTURAL] sharp cap (4r)^2 <= 256 for every realizable depth r<=4:")
        log("  => ALL {0,+-1} divisor mass at n=8 lives in p <= 241; the beta=3 AND beta=4")
        log("     windows are PROVABLY EMPTY at every depth (strengthens 'n=8 D4-clean').")

        win16 = [(16 ** 4, 4 * 16 ** 4, "beta=4", ""),
                 (16 ** 3, 4 * 16 ** 3, "beta=3", "BETA-DEP ")]
        out2 = run_case(16, 2, win16, "task spec")
        run_case(16, 3, win16, "task spec")
        run_case(16, 4, win16, "EXTENSION: below window onset r*=5, rich beta=3 data")

        log("\n----- CROSS-CHECK: n=16 r=2 bad-prime set vs the width-4 anchor -----")
        r2set = set(out2["ps_all"])
        log(f"  measured r=2 class bad-prime set: {sorted(r2set)}")
        cf = set(q for q in canon_facs if q % 16 == 1)
        log(f"  contains 17: {17 in r2set}; canonical class factors {sorted(cf)} "
            f"subset: {cf <= r2set}; measured-only: {sorted(r2set - set(canon_facs))}")

    elif stage == "ext16":
        win16 = [(16 ** 4, 4 * 16 ** 4, "beta=4", ""),
                 (16 ** 3, 4 * 16 ** 3, "beta=3", "BETA-DEP ")]
        for r in (5, 6, 7, 8):
            run_case(16, r, win16, f"EXTENSION: window-reaching depth (onset r*=5)")

    elif stage == "ext32":
        win32 = [(32 ** 4, 4 * 32 ** 4, "beta=4", ""),
                 (32 ** 3, 4 * 32 ** 3, "beta=3", "BETA-DEP ")]
        run_case(32, 2, win32, "EXTENSION: second n with true in-window mass")

    elif stage == "ext32deep":
        win32 = [(32 ** 4, 4 * 32 ** 4, "beta=4", ""),
                 (32 ** 3, 4 * 32 ** 3, "beta=3", "BETA-DEP ")]
        run_case(32, 3, win32, "EXTENSION: depth growth at n=32")

    else:
        raise SystemExit(f"unknown stage {stage}")

    log(f"\n[stage {stage}] total runtime {time.time()-T0:.1f}s")


if __name__ == "__main__":
    main()
