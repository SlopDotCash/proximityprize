#!/usr/bin/env python3
"""
probe_466_sst_sections.py  --  LANE R2, Conjecture SST (essay sec 2.3, sparse-section
transference) for issue #466.

Setup: L_p = ker( Z[x]/(x^n - 1) -> F_p, x -> h ), h of multiplicative order exactly n
mod p (p = 1 mod n, p >= n^4).  For a 2r-subset S = {s_0 < ... < s_{2r-1}} of Z/n the
section L_p cap Z^S is the rank-2r lattice

    L_S = { c in Z^{2r} : sum_i c_i h^{s_i} = 0 mod p }.

(a) covolume of the section = p iff the restricted map Z^S -> F_p is surjective; since
    every h^{s_i} is a unit the map is ALWAYS surjective, so covolume = p always.
    We verify this via an explicit triangular basis (det = p, rows in kernel; the basis
    lattice has index p in Z^{2r} and is contained in the kernel of index p, so equal).
(b) exact {0,+-1}-vector counts (brute force over all 3^{2r} candidates), exact shortest
    vector (lambda1) and exact dual shortest vector (lambda1*) via LLL + full
    Schnorr-Euchner enumeration (dim <= 6, exact within the enumeration radius).
    Dual: L_S^* = Z^{2r} + Z*(v/p) with v = (h^{s_i})_i, so p*L_S^* has basis
    {w, p e_1, ..., p e_{2r-1}} where w = (h^{-s_0} v mod p) has w_0 = 1.
(c) statistics vs the DC/Gaussian prediction: expected nonzero {0,+-1}-count per section
    = (3^{2r}-1)/p; bad-section (tail) rate vs the pair-corrected union bound
    (3^{2r}-1)/(2p); implied K via bad_rate = K^r/(2p).
    STRUCTURAL SPLIT: n is a 2-power so h^{n/2} = -1 mod p; every section containing an
    antipodal pair {s, s+n/2} carries a deterministic char-0 sparse vector
    (e_s + e_{s+n/2}).  These are the correlated X^{n/2} directions -> flagged and
    separated.  Sporadic bad = antipodal-free section with a sparse vector (char-p
    defect); this is what the K^r control is about.
(d) SHIFT-ORBIT test: S -> S+1 sends the defining form sum c_i h^{s_i} to
    h * (sum c_i h^{s_i}) -- a UNIT multiple -- so the section lattice is literally the
    same subgroup of Z^{2r} up to the coordinate re-sorting permutation.  Hence sparse
    counts, lambda1, lambda1* must be EXACTLY constant on shift orbits (provable, not
    just empirical).  We verify this numerically on full orbits.
(e) REVERSAL test S -> -S: values become h^{-s_i}; this is the section of the
    Galois-conjugate prime (h -> h^{-1}), NOT a unit multiple of the same form, so
    equality of invariants is not forced.  Tested numerically.

Regime: n in {16, 32}, two primes each with p = 1 mod n, p >= n^4 (beta >= 4),
mu_n a PROPER subgroup (n < p-1).
"""

import itertools, math, random, sys, time
from collections import Counter, defaultdict

random.seed(466)

# ----------------------------------------------------------------------------
# small number theory helpers
# ----------------------------------------------------------------------------

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    f = {}
    d = 2
    while d*d <= m:
        while m % d == 0: f[d] = f.get(d,0)+1; m //= d
        d += 1
    if m > 1: f[m] = f.get(m,0)+1
    return f

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def find_primes(n, count=2):
    """first `count` primes p = 1 mod n with p >= n^4"""
    out = []
    p = n**4 + 1
    p += (-(p-1)) % n           # make p = 1 mod n
    while len(out) < count:
        if is_prime(p) and p-1 != n:   # never n = p-1 (automatic here)
            out.append(p)
        p += n
    return out

# ----------------------------------------------------------------------------
# exact SVP in small dimension: LLL + Schnorr-Euchner enumeration
# ----------------------------------------------------------------------------

def _gso(B):
    d = len(B); m = len(B[0])
    mu = [[0.0]*d for _ in range(d)]
    c  = [0.0]*d
    Bs = [[0.0]*m for _ in range(d)]
    for i in range(d):
        Bs[i] = [float(x) for x in B[i]]
        for j in range(i):
            s = 0.0
            for k in range(m): s += B[i][k]*Bs[j][k]
            mu[i][j] = s / c[j]
            for k in range(m): Bs[i][k] -= mu[i][j]*Bs[j][k]
        c[i] = sum(x*x for x in Bs[i])
    return mu, c

def lll(B, delta=0.99):
    B = [row[:] for row in B]
    d = len(B)
    mu, c = _gso(B)
    k = 1
    while k < d:
        # size-reduce row k
        for j in range(k-1, -1, -1):
            q = round(mu[k][j])
            if q != 0:
                for t in range(len(B[k])): B[k][t] -= q*B[j][t]
                mu, c = _gso(B)
        if c[k] >= (delta - mu[k][k-1]**2) * c[k-1]:
            k += 1
        else:
            B[k], B[k-1] = B[k-1], B[k]
            mu, c = _gso(B)
            k = max(k-1, 1)
    return B

def svp_norm2(B):
    """exact lambda1^2 of the lattice with basis B (integer rows), full enumeration."""
    B = lll(B)
    d = len(B)
    mu, c = _gso(B)
    best = min(sum(x*x for x in row) for row in B)  # integer upper bound
    x = [0]*d

    def rec(i, partial):
        nonlocal best
        # center for level i given x[i+1..d-1]
        center = -sum(mu[j][i]*x[j] for j in range(i+1, d))
        x0 = round(center)
        # zigzag around center
        for step in range(0, 64):
            for xi in ({x0} if step == 0 else {x0-step, x0+step}):
                y = xi - center
                contrib = y*y*c[i]
                if partial + contrib >= best: continue
                x[i] = xi
                if i == 0:
                    if any(x):  # exclude zero vector
                        # exact integer norm of the found vector
                        v = [0]*len(B[0])
                        for j in range(d):
                            if x[j]:
                                for t in range(len(v)): v[t] += x[j]*B[j][t]
                        n2 = sum(t*t for t in v)
                        if 0 < n2 < best: best = n2
                else:
                    rec(i-1, partial + contrib)
            # stop zigzag when both sides exceed radius
            lo = (x0-step) - center; hi = (x0+step) - center
            if partial + min(lo*lo, hi*hi)*c[i] >= best and step > 0:
                break
        x[i] = 0

    rec(d-1, 0.0)
    return best

# ----------------------------------------------------------------------------
# section machinery
# ----------------------------------------------------------------------------

def primal_basis(vals, p):
    """basis of {c : sum c_i vals_i = 0 mod p};  vals[0] must be a unit."""
    d = len(vals)
    inv0 = pow(vals[0], p-2, p)
    B = [[0]*d for _ in range(d)]
    B[0][0] = p
    for j in range(1, d):
        t = (vals[j]*inv0) % p
        if t > p//2: t -= p          # center for milder entries
        B[j][0] = -t; B[j][j] = 1
    return B

def dual_scaled_basis(vals, p):
    """basis of p * L_S^*  =  p Z^d + Z w,  w = vals * vals[0]^{-1} mod p (w_0 = 1)."""
    d = len(vals)
    inv0 = pow(vals[0], p-2, p)
    w = [(v*inv0) % p for v in vals]
    B = [w[:]]
    for j in range(1, d):
        row = [0]*d; row[j] = p
        B.append(row)
    return B

def sparse_count(vals, p, half_patterns):
    """exact number of NONZERO {0,+-1} vectors in the section (counted with both signs)."""
    cnt = 0
    for pat in half_patterns:
        s = 0
        for c, v in zip(pat, vals): s += c*v
        if s % p == 0: cnt += 1
    return 2*cnt

def dual_min_scan(vals, p):
    """O(p) exact dual minimum cross-check: lambda1(pL*)^2 = min over k of
       sum centered(k*w_i mod p)^2  (k=0 contributes p^2 via p*e_i)."""
    d = len(vals)
    inv0 = pow(vals[0], p-2, p)
    w = [(v*inv0) % p for v in vals]
    best = p*p
    for k in range(1, (p-1)//2 + 1):
        s = 0
        for wi in w:
            t = (k*wi) % p
            if t > p//2: t -= p
            s += t*t
            if s >= best: break
        if s < best: best = s
    return best

def gauss_l1(d, covol):
    return math.sqrt(d/(2*math.pi*math.e)) * covol**(1.0/d)

def orbit_canonical(S, n):
    """canonical representative of the shift orbit of frozenset S."""
    best = None
    for t in range(n):
        cand = tuple(sorted((s+t) % n for s in S))
        if best is None or cand < best: best = cand
    return best

def has_antipodal(S, n):
    Sset = set(S)
    return any((s + n//2) % n in Sset for s in Sset)

def antipodal_pairs(S, n):
    """number k of full antipodal pairs {s, s+n/2} inside S; the section then has
    EXACTLY 3^k - 1 forced char-0 sparse vectors (signed disjoint pair sums --
    the complete dyadic Lam-Leung classification of {0,+-1} vanishing sums for n=2^mu)."""
    Sset = set(S)
    return sum(1 for s in S if (s + n//2) % n in Sset) // 2

# ----------------------------------------------------------------------------
# main experiment
# ----------------------------------------------------------------------------

OUT = []
def log(msg=""):
    print(msg); OUT.append(str(msg))

def run(n, p, r, sections, svp_sections, half_patterns, do_full_orbit_check,
        orbit_sample_orbits=None):
    d = 2*r
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    # order check: h has order exactly n
    assert pow(h, n, p) == 1
    for q in factorize(n):
        assert pow(h, n//q, p) != 1, "h order not exactly n"
    a = [pow(h, i, p) for i in range(n)]
    assert len(set(a)) == n and (p-1) % n == 0 and n < p-1

    log(f"--- n={n} p={p} r={r} (d={d})  h={h}  beta=log_n(p)={math.log(p)/math.log(n):.3f} ---")

    # (a) section structure spot check on 5 random sections
    for S in random.sample(sections, min(5, len(sections))):
        vals = [a[s] for s in S]
        B = primal_basis(vals, p)
        det = 1
        for i in range(d): det *= B[i][i] if i == 0 else 1
        det = abs(B[0][0])  # triangular: |det| = p * 1 * ... * 1
        assert det == p
        for row in B:
            assert sum(c*v for c, v in zip(row, vals)) % p == 0
        assert all(v % p != 0 for v in vals)   # restricted map surjective (units)
    log(f"(a) section structure OK on spot checks: triangular basis det = p = {p}, "
        f"rows in kernel, all h^s units => restricted map surjective => covolume = p ALWAYS.")

    # (b)+(c) sparse counts for ALL listed sections
    t0 = time.time()
    counts = {}
    for S in sections:
        vals = [a[s] for s in S]
        counts[S] = sparse_count(vals, p, half_patterns)
    t_counts = time.time() - t0

    anti  = [S for S in sections if has_antipodal(S, n)]
    free  = [S for S in sections if not has_antipodal(S, n)]
    bad_all   = [S for S in sections if counts[S] > 0]
    bad_free  = [S for S in free if counts[S] > 0]
    # sanity: every antipodal section is bad (e_s + e_{s+n/2} in kernel)
    assert all(counts[S] > 0 for S in anti)
    # EXACT char-0 accounting: k antipodal pairs => exactly 3^k - 1 forced solutions;
    # char-p defect(S) = count - (3^k - 1) must be >= 0 (every pair-combination IS a solution)
    forced = {S: 3**antipodal_pairs(S, n) - 1 for S in sections}
    defect = {S: counts[S] - forced[S] for S in sections}
    assert all(v >= 0 for v in defect.values()), "count < forced char-0 count: classification bug"
    anti_defective = [S for S in anti if defect[S] > 0]

    N = len(sections)
    exp_count = (3**d - 1) / p
    mean_all  = sum(counts.values()) / N
    mean_free = (sum(counts[S] for S in free) / len(free)) if free else float('nan')
    union_rate = (3**d - 1) / (2*p)
    bad_free_rate = len(bad_free)/len(free) if free else float('nan')
    K_impl = (bad_free_rate * 2 * p) ** (1.0/r) if bad_free else 0.0

    log(f"(b/c) sections={N}  antipodal-containing={len(anti)}  antipodal-free={len(free)}")
    log(f"      sparse-count time {t_counts:.1f}s; distribution over ALL sections: "
        f"{dict(sorted(Counter(counts.values()).items()))}")
    log(f"      distribution over ANTIPODAL-FREE sections: "
        f"{dict(sorted(Counter(counts[S] for S in free).items()))}")
    log(f"      mean count ALL  = {mean_all:.6f}   (prediction (3^{d}-1)/p = {exp_count:.6f} "
        f"applies to generic sections)")
    log(f"      mean count FREE = {mean_free:.6f}  ratio to prediction = {mean_free/exp_count:.3f}")
    log(f"      bad sections: ALL {len(bad_all)}/{N} = {len(bad_all)/N:.5f}; "
        f"FREE {len(bad_free)}/{len(free)} = {bad_free_rate:.6f} "
        f"vs union-bound rate (3^{d}-1)/(2p) = {union_rate:.6f}  "
        f"(expected #bad among free = {union_rate*len(free):.2f})")
    log(f"      implied K (bad_free_rate = K^r/(2p)):  K = {K_impl:.3f}   [prediction K=9 i.e. 3^2]")
    tot_defect_free = sum(defect[S] for S in free)
    tot_defect_anti = sum(defect[S] for S in anti)
    pred_defect_anti = sum((3**d - 3**antipodal_pairs(S, n))/p for S in anti)
    log(f"      char-p DEFECT (count - forced 3^k-1):  FREE total = {tot_defect_free};  "
        f"ANTIPODAL total = {tot_defect_anti} over {len(anti_defective)} defective sections "
        f"(DC prediction {pred_defect_anti:.2f})")

    # (b) exact SVP + dual SVP on svp_sections
    # ALWAYS include the sporadic char-p bad sections (bad FREE + defective antipodal):
    # a random subsample would miss exactly the sections the conjecture is about.
    svp_sections = sorted(set(svp_sections) | set(bad_free) | set(anti_defective))
    t0 = time.time()
    l1 = {}; l1d = {}
    for S in svp_sections:
        vals = [a[s] for s in S]
        l1[S]  = math.sqrt(svp_norm2(primal_basis(vals, p)))
        l1d[S] = math.sqrt(svp_norm2(dual_scaled_basis(vals, p))) / p
    t_svp = time.time() - t0
    gh_p = gauss_l1(d, p)          # primal gaussian
    gh_d = gauss_l1(d, 1.0/p)      # dual gaussian
    ratios_d = sorted(l1d[S]/gh_d for S in svp_sections)
    ratios_p = sorted(l1[S]/gh_p for S in svp_sections)
    m = len(svp_sections)
    def q(lst, x): return lst[min(int(x*len(lst)), len(lst)-1)]
    log(f"(b) exact SVP on {m} sections in {t_svp:.1f}s;  gaussian lambda1 = {gh_p:.3f}, "
        f"gaussian lambda1* = {gh_d:.6f}")
    log(f"      lambda1 /gauss quantiles  1%={q(ratios_p,0.01):.3f} 10%={q(ratios_p,0.10):.3f} "
        f"50%={q(ratios_p,0.50):.3f} 90%={q(ratios_p,0.90):.3f}")
    log(f"      lambda1*/gauss quantiles  1%={q(ratios_d,0.01):.3f} 10%={q(ratios_d,0.10):.3f} "
        f"50%={q(ratios_d,0.50):.3f} 90%={q(ratios_d,0.90):.3f}")
    for thr in (0.5, 0.75, 1.0):
        frac = sum(1 for x in ratios_d if x < thr)/m
        log(f"      fraction with lambda1* < {thr}*gauss : {frac:.5f}")
    # transference correlation: dual minima on bad vs good sections
    svp_bad  = [S for S in svp_sections if counts[S] > 0]
    svp_free = [S for S in svp_sections if not has_antipodal(S, n)]
    svp_bad_free = [S for S in svp_free if counts[S] > 0]
    if svp_bad:
        mb = sum(l1d[S] for S in svp_bad)/len(svp_bad)
        mg = sum(l1d[S] for S in svp_sections if counts[S] == 0)/max(1, m-len(svp_bad))
        log(f"      mean lambda1*: bad sections {mb:.6f} vs good {mg:.6f} (gauss {gh_d:.6f}); "
            f"bad(free/sporadic) n={len(svp_bad_free)}"
            + (f" mean {sum(l1d[S] for S in svp_bad_free)/len(svp_bad_free):.6f}" if svp_bad_free else ""))
    # sanity: sections with sparse vector have lambda1 <= sqrt(2r)
    for S in svp_bad:
        assert l1[S] <= math.sqrt(d) + 1e-9

    # cross-check dual enumeration against O(p) scan on 3 sections (n=16 only: p small)
    if p < 10**5:
        for S in random.sample(svp_sections, 3):
            vals = [a[s] for s in S]
            exact = math.sqrt(dual_min_scan(vals, p))/p
            assert abs(exact - l1d[S]) < 1e-9, (S, exact, l1d[S])
        log(f"      cross-check: dual enumeration == O(p) exhaustive scan on 3 sections OK")

    # (d) shift-orbit constancy
    if do_full_orbit_check:
        orbits = defaultdict(list)
        for S in sections: orbits[orbit_canonical(S, n)].append(S)
        cviol = sum(1 for o in orbits.values() if len({counts[S] for S in o}) > 1)
        # dual-min constancy over orbits fully contained in svp_sections
        svpset = set(svp_sections)
        dviol = ncheck = 0
        for o in orbits.values():
            if all(S in svpset for S in o):
                ncheck += 1
                if max(l1d[S] for S in o) - min(l1d[S] for S in o) > 1e-9: dviol += 1
        log(f"(d) shift orbits: {len(orbits)} orbits over {N} sections "
            f"(compression factor {N/len(orbits):.2f}, max possible {n}); "
            f"count-constancy violations {cviol}/{len(orbits)}; "
            f"dual-min-constancy violations {dviol}/{ncheck} (orbits fully SVP'd)")
    elif orbit_sample_orbits:
        cviol = dviol = 0
        for o in orbit_sample_orbits:
            cs = {sparse_count([a[s] for s in S], p, half_patterns) for S in o}
            if len(cs) > 1: cviol += 1
            ds = [math.sqrt(svp_norm2(dual_scaled_basis([a[s] for s in S], p)))/p for S in o]
            if max(ds) - min(ds) > 1e-9: dviol += 1
        log(f"(d) shift orbits (sampled, fully expanded): {len(orbit_sample_orbits)} orbits; "
            f"count-constancy violations {cviol}; dual-min-constancy violations {dviol}")

    # (e) reversal S -> -S
    rev_pairs = 0; rev_cnt_eq = 0; rev_dual_eq = 0; rev_dual_pairs = 0
    svpset = set(svp_sections)
    seen = set()
    for S in sections:
        Srev = tuple(sorted((-s) % n for s in S))
        if Srev in counts and S not in seen:
            seen.add(S); seen.add(Srev)
            rev_pairs += 1
            if counts[S] == counts[Srev]: rev_cnt_eq += 1
            if S in svpset and Srev in svpset:
                rev_dual_pairs += 1
                if abs(l1d[S] - l1d[Srev]) < 1e-9: rev_dual_eq += 1
    log(f"(e) reversal S -> -S: {rev_pairs} comparable pairs; sparse-count equal on "
        f"{rev_cnt_eq}/{rev_pairs}; dual-min equal on {rev_dual_eq}/{rev_dual_pairs} SVP'd pairs")

    log()
    return dict(n=n, p=p, r=r, N=N, n_free=len(free), bad_all=len(bad_all),
                bad_free=len(bad_free), union_exp=union_rate*len(free),
                K_impl=K_impl, mean_free=mean_free, exp_count=exp_count,
                def_free=tot_defect_free, def_anti=tot_defect_anti,
                n_anti_def=len(anti_defective))


def main():
    t_start = time.time()
    log("=" * 88)
    log("probe_466_sst_sections.py  --  Conjecture SST (sparse-section transference), lane R2")
    log("=" * 88)
    log()
    log("THEORY NOTE (exact, not empirical): the shift S -> S+1 multiplies the defining")
    log("linear form sum c_i h^{s_i} by the UNIT h, so the section lattice is the same")
    log("subgroup of Z^{2r} up to the sorting permutation of coordinates.  Sparse counts,")
    log("lambda1, lambda1* are therefore EXACTLY constant on shift orbits.  (d) verifies.")
    log("STRUCTURAL sparse vectors: n = 2^k => h^{n/2} = -1 => every section containing an")
    log("antipodal pair {s, s+n/2} has the char-0 vector e_s + e_{s+n/2}.  For n a 2-power")
    log("ALL char-0 vanishing {0,+-1} sums of n-th roots of unity decompose into antipodal")
    log("pairs, so: bad section is CHAR-0/structural iff it contains an antipodal pair;")
    log("bad ANTIPODAL-FREE sections are the sporadic char-p defect (the K^r question).")
    log()

    results = []

    # ---------------- n = 16 : full enumeration ----------------
    n = 16
    primes16 = find_primes(16, 3)
    log(f"n=16 primes: {primes16}  (p = 1 mod 16, p >= 16^4 = 65536)")
    log(f"REGIME FLAG: 65537 = 2^16+1 is the FERMAT prime: mu_16 = +-<4> is a geometric")
    log(f"progression of 2-powers (maximally structured/correlated instance). Kept for")
    log(f"contrast but statistics are read off the two generic primes 65617, 65633.")
    for r in (2, 3):
        d = 2*r
        pats = [pat for pat in itertools.product((-1,0,1), repeat=d) if any(pat)]
        half = [pat for pat in pats if next(x for x in pat if x) == 1]
        sections = [tuple(S) for S in itertools.combinations(range(16), d)]
        for p in primes16:
            results.append(run(16, p, r, sections, sections, half,
                               do_full_orbit_check=True))

    # ---------------- n = 32 : sampled ----------------
    n = 32
    primes32 = find_primes(32, 2)
    log(f"n=32 primes: {primes32}  (p = 1 mod 32, p >= 32^4 = 1048576)")
    NSAMP = 20000
    NSVP  = 4000     # exact SVP subsample (per (r,p)); sparse counts on all NSAMP
    NORB  = 30       # fully expanded shift orbits for (d)
    for r in (2, 3):
        d = 2*r
        pats = [pat for pat in itertools.product((-1,0,1), repeat=d) if any(pat)]
        half = [pat for pat in pats if next(x for x in pat if x) == 1]
        all_idx = list(range(32))
        samp = set()
        while len(samp) < NSAMP:
            samp.add(tuple(sorted(random.sample(all_idx, d))))
        sections = sorted(samp)
        # make the sample reversal-closed for (e)
        for S in list(sections):
            Srev = tuple(sorted((-s) % 32 for s in S))
            if Srev not in samp: samp.add(Srev)
        sections = sorted(samp)
        svp_sections = random.sample(sections, NSVP)
        # sampled full orbits for (d)
        orbit_reps = random.sample(sections, NORB)
        orbs = []
        for S in orbit_reps:
            orb = sorted({tuple(sorted((s+t) % 32 for s in S)) for t in range(32)})
            orbs.append(orb)
        for p in primes32:
            results.append(run(32, p, r, sections, svp_sections, half,
                               do_full_orbit_check=False, orbit_sample_orbits=orbs))

    # ---------------- verdict ----------------
    log("=" * 88)
    log("SUMMARY TABLE (bad = has >= 1 nonzero {0,+-1} vector; FREE = antipodal-free)")
    log(f"{'n':>3} {'p':>9} {'r':>2} {'#sect':>7} {'#free':>7} {'badALL':>7} {'badFREE':>8} "
        f"{'exp(union)':>10} {'K_impl':>7} {'meanFREE/pred':>13} {'defF':>5} {'defA':>5} {'#Adef':>5}")
    for R in results:
        log(f"{R['n']:>3} {R['p']:>9} {R['r']:>2} {R['N']:>7} {R['n_free']:>7} "
            f"{R['bad_all']:>7} {R['bad_free']:>8} {R['union_exp']:>10.2f} "
            f"{R['K_impl']:>7.2f} {R['mean_free']/R['exp_count']:>13.3f} "
            f"{R['def_free']:>5} {R['def_anti']:>5} {R['n_anti_def']:>5}")
    log()
    log(f"total time {time.time()-t_start:.1f}s")

    with open("scripts/probes/_out_466_sst_sections.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")

if __name__ == "__main__":
    main()
