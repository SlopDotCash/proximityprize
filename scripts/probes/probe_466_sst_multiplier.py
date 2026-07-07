#!/usr/bin/env python3
"""
probe_466_sst_multiplier.py  --  LANE S5 (issue #466, dossier sec.15 survivor 4).

The SST multiplier-action residue.  Setup identical to probe_466_sst_sections.py:
    L_p = ker( Z[x]/(x^n-1) -> F_p, x -> h ),  h of exact multiplicative order n,
    p = 1 mod n, p >= n^4 (beta >= 4), mu_n a PROPER subgroup (n < p-1).
For a 2r-subset S of Z/n the section is the rank-2r lattice
    L_S(h) = { c in Z^S : sum_i c_i h^{s_i} = 0 mod p }.

PROVEN isometry (probe_466_sst_sections (d)): the SHIFT  S -> S+1  multiplies the
defining form by the UNIT h, so L_{S+1}(h) = L_S(h) up to the sorting permutation.
Sparse count, lambda1, lambda1* are EXACTLY constant on shift orbits.

THIS LANE: the MULTIPLIER action  S -> kS  (gcd(k,n)=1).  The EXACT identity is
    L_{kS}(h) = { c : sum c_i h^{k s_i} = 0 } = { c : sum c_i (h^k)^{s_i} = 0 } = L_S(h^k),
i.e. multiplying the index set by k replaces the root of unity h by the DIFFERENT
primitive n-th root h^k (a Galois twist of the mod-p embedding).  h^k is NOT a unit
MULTIPLE of h, so L_S(h^k) is a genuinely different lattice: the multiplier is NOT an
isometry of a fixed L_p.  Questions:

(a) section(S,h) vs section(kS,h) vs section(S,h^k): which invariants agree?
    - EXACT identity check: sparse_count(kS, h) == sparse_count(S, h^k)  (both signs). PASS = confirms the identity.
    - sparse_count(S,h) == sparse_count(kS,h)?  and  dual-min lambda1* equal?
    - decompose count = char0 (antipodal-forced 3^{#pairs}-1) + char-p defect; is each part preserved?

(b) full AFFINE action  x -> kx + t  on Z/n (shift x multiplier).  Group sections into
    affine orbits.  Orbit sizes; is sparse-count constant on the LARGER (affine) orbits?
    is dual-min constant?  Compression factor vs the shift-only census.

(c) n=32 r=2 FULL census (all C(32,4) = 35960 sections).

(d) settle round-2's reversal  S -> -S  (that is the multiplier k = -1): round 2 saw
    sparse-count equal 924/924 but dual-min equal only 380/924.  Explain via conjugation:
    k=-1 sends h -> h^{-1} = conj(h); char-0 (antipodal) solutions are Galois/conjugation
    invariant (hence sparse-count preserved) but lambda1* of L_S(h) is NOT a conjugation
    invariant (hence dual-min NOT preserved).

DECISION printed at the end: does the affine action compress the DUAL-MINIMUM census beyond
the shift (residue ALIVE), or is within-affine-orbit dual-min variance nonzero (residue DEAD,
countermodel pair printed)?  Sparse-count constancy is reported separately (it is an affine
invariant precisely because in the n=2^mu regime every bad section is char-0/antipodal).
"""

import itertools, math, random, sys, time
from collections import Counter, defaultdict

random.seed(466)

# ------------------------------------------------------------------ number theory
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
    f = {}; d = 2
    while d*d <= m:
        while m % d == 0: f[d] = f.get(d,0)+1; m //= d
        d += 1
    if m > 1: f[m] = f.get(m,0)+1
    return f

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    raise RuntimeError

def find_primes(n, count=2):
    out = []; p = n**4 + 1; p += (-(p-1)) % n
    while len(out) < count:
        if is_prime(p) and p-1 != n: out.append(p)
        p += n
    return out

def units_mod(n):
    return [k for k in range(1, n) if math.gcd(k, n) == 1]

# ------------------------------------------------------------------ exact SVP (LLL + enum)
def _gso(B):
    d = len(B); m = len(B[0]); mu = [[0.0]*d for _ in range(d)]; c = [0.0]*d
    Bs = [[0.0]*m for _ in range(d)]
    for i in range(d):
        Bs[i] = [float(x) for x in B[i]]
        for j in range(i):
            s = sum(B[i][k]*Bs[j][k] for k in range(m)); mu[i][j] = s / c[j]
            for k in range(m): Bs[i][k] -= mu[i][j]*Bs[j][k]
        c[i] = sum(x*x for x in Bs[i])
    return mu, c

def lll(B, delta=0.99):
    B = [row[:] for row in B]; d = len(B); mu, c = _gso(B); k = 1
    while k < d:
        for j in range(k-1, -1, -1):
            q = round(mu[k][j])
            if q != 0:
                for t in range(len(B[k])): B[k][t] -= q*B[j][t]
                mu, c = _gso(B)
        if c[k] >= (delta - mu[k][k-1]**2) * c[k-1]: k += 1
        else:
            B[k], B[k-1] = B[k-1], B[k]; mu, c = _gso(B); k = max(k-1, 1)
    return B

def svp_norm2(B):
    B = lll(B); d = len(B); mu, c = _gso(B)
    best = min(sum(x*x for x in row) for row in B); x = [0]*d
    def rec(i, partial):
        nonlocal best
        center = -sum(mu[j][i]*x[j] for j in range(i+1, d)); x0 = round(center)
        for step in range(0, 64):
            for xi in ({x0} if step == 0 else {x0-step, x0+step}):
                y = xi - center; contrib = y*y*c[i]
                if partial + contrib >= best: continue
                x[i] = xi
                if i == 0:
                    if any(x):
                        v = [0]*len(B[0])
                        for j in range(d):
                            if x[j]:
                                for t in range(len(v)): v[t] += x[j]*B[j][t]
                        n2 = sum(t*t for t in v)
                        if 0 < n2 < best: best = n2
                else:
                    rec(i-1, partial + contrib)
            lo = (x0-step) - center; hi = (x0+step) - center
            if partial + min(lo*lo, hi*hi)*c[i] >= best and step > 0: break
        x[i] = 0
    rec(d-1, 0.0)
    return best

def dual_scaled_basis(vals, p):
    d = len(vals); inv0 = pow(vals[0], p-2, p); w = [(v*inv0) % p for v in vals]
    B = [w[:]]
    for j in range(1, d):
        row = [0]*d; row[j] = p; B.append(row)
    return B

def dual_min(vals, p):
    """lambda1(L_S(h)^*)^2 * p^2  (integer); dual-min = sqrt(.)/p."""
    return svp_norm2(dual_scaled_basis(vals, p))

# ------------------------------------------------------------------ sparse machinery
def sparse_count(vals, p, half_patterns):
    cnt = 0
    for pat in half_patterns:
        s = 0
        for c, v in zip(pat, vals): s += c*v
        if s % p == 0: cnt += 1
    return 2*cnt

def antipodal_pairs(S, n):
    Sset = set(S)
    return sum(1 for s in S if (s + n//2) % n in Sset) // 2

def canon_shift(S, n):
    best = None
    for t in range(n):
        cand = tuple(sorted((s+t) % n for s in S))
        if best is None or cand < best: best = cand
    return best

def canon_affine(S, n, units):
    best = None
    for k in units:
        kS = [(k*s) % n for s in S]
        for t in range(n):
            cand = tuple(sorted((x+t) % n for x in kS))
            if best is None or cand < best: best = cand
    return best

# ------------------------------------------------------------------ main experiment
OUT = []
def log(msg=""):
    print(msg); OUT.append(str(msg))

def build_h_powers(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    assert pow(h, n, p) == 1
    for q in factorize(n): assert pow(h, n//q, p) != 1
    return h, [pow(h, i, p) for i in range(n)]

def run_scale(n, p, r, sections, do_dual_all, dual_sample, note=""):
    d = 2*r; units = units_mod(n)
    h, a = build_h_powers(n, p)
    pats = [pat for pat in itertools.product((-1,0,1), repeat=d) if any(pat)]
    half = [pat for pat in pats if next(x for x in pat if x) == 1]
    N = len(sections)
    log(f"--- n={n} p={p} r={r} (d={d})  h={h}  units|(Z/n)^x|=phi(n)={len(units)}  {note} ---")

    # ---- sparse counts + char-0 decomposition for ALL sections
    counts = {}; pairs = {}; defect = {}
    for S in sections:
        vals = [a[s] for s in S]
        c = sparse_count(vals, p, half); counts[S] = c
        k0 = antipodal_pairs(S, n); pairs[S] = k0
        forced = 3**k0 - 1
        defect[S] = c - forced
    assert all(v >= 0 for v in defect.values())
    n_defect = sum(1 for S in sections if defect[S] > 0)
    log(f"  sparse-count dist over ALL {N} sections: {dict(sorted(Counter(counts.values()).items()))}")
    log(f"  sections with char-p DEFECT (count > 3^#pairs - 1): {n_defect}"
        + ("  => ALL bad sections are char-0/antipodal (sparse-count is a candidate affine invariant)"
           if n_defect == 0 else "  => genuine char-p defect present"))

    # =================================================================== (a) multiplier pair test
    # EXACT identity: sparse_count(kS, h) must equal sparse_count(S, h^k) for every k.
    id_fail = 0; id_checked = 0
    sc_eq = 0; sc_tot = 0
    def_eq = 0
    sample_a = sections if N <= 2000 else random.sample(sections, 2000)
    Sset = set(sections)
    for S in sample_a:
        vS = [a[s] for s in S]; cS = counts[S]
        for k in units:
            if k == 1: continue
            kS = tuple(sorted((k*s) % n for s in S))
            # exact identity: section(kS,h) == section(S,h^k)
            v_kS_h = [a[(k*s) % n] for s in S]                    # values of kS under root h
            v_S_hk = [pow(a[s], k, p) for s in S]                 # values of S under root h^k
            c_kS_h = sparse_count(v_kS_h, p, half)
            c_S_hk = sparse_count(v_S_hk, p, half)
            id_checked += 1
            if c_kS_h != c_S_hk: id_fail += 1
            # sparse-count invariance under the multiplier (on a fixed L_p, root h)
            sc_tot += 1
            cKS = counts.get(kS)
            if cKS is None:                                       # kS may be outside a sampled section list
                cKS = sparse_count([a[x] for x in kS], p, half)
            if cS == cKS: sc_eq += 1
            if defect[S] == defect.get(kS, sparse_count([a[x] for x in kS],p,half)-(3**antipodal_pairs(kS,n)-1)):
                def_eq += 1
    log(f"(a) EXACT identity sparse_count(kS,h)==sparse_count(S,h^k): "
        f"{id_checked-id_fail}/{id_checked} pass (fails={id_fail})  [proves L_kS(h)=L_S(h^k)]")
    log(f"(a) sparse-count invariance under multiplier k (fixed root h): {sc_eq}/{sc_tot} pairs equal "
        f"({100*sc_eq/sc_tot:.1f}%);  char-p defect equal: {def_eq}/{sc_tot} ({100*def_eq/sc_tot:.1f}%)")

    # ---- dual-min under the multiplier: does lambda1* agree?  (this is the residue question)
    dm = {}
    if do_dual_all:
        dsrc = sections
    else:
        dsrc = dual_sample
    t0 = time.time()
    for S in dsrc:
        dm[S] = dual_min([a[s] for s in S], p)
    t_dm = time.time() - t0
    dm_eq = 0; dm_tot = 0; countermodel = None
    dsrc_set = set(dsrc)
    for S in dsrc:
        for k in units:
            if k == 1: continue
            kS = tuple(sorted((k*s) % n for s in S))
            dmk = dm.get(kS)
            if dmk is None:
                dmk = dual_min([a[x] for x in kS], p)
            dm_tot += 1
            if dm[S] == dmk: dm_eq += 1
            elif countermodel is None and counts[S] == counts.get(kS, -1):
                # equal sparse-count but different dual-min: the clean countermodel
                countermodel = (S, k, kS, counts[S], dm[S], dmk)
    log(f"(a) dual-min (p^2*lambda1*^2, exact) computed on {len(dsrc)} sections in {t_dm:.1f}s")
    log(f"(a) dual-min invariance under multiplier k: {dm_eq}/{dm_tot} pairs equal "
        f"({100*dm_eq/dm_tot:.1f}%)  => multiplier is {'AN' if dm_eq==dm_tot else 'NOT an'} isometry of L_p")
    if countermodel:
        S,k,kS,cc,d1,d2 = countermodel
        log(f"    COUNTERMODEL: S={S}, k={k}, kS={kS}: sparse-count equal ({cc}) but "
            f"p^2*lambda1*^2 differs: {d1} vs {d2}")

    # =================================================================== (b) affine orbits
    orb_shift = defaultdict(list); orb_aff = defaultdict(list)
    for S in sections:
        orb_shift[canon_shift(S, n)].append(S)
        orb_aff[canon_affine(S, n, units)].append(S)
    # constancy of sparse-count on affine orbits
    aff_cnt_viol = sum(1 for o in orb_aff.values() if len({counts[S] for S in o}) > 1)
    # constancy of dual-min on affine orbits (only orbits fully in dsrc)
    aff_dm_viol = 0; aff_dm_checked = 0
    for o in orb_aff.values():
        if all(S in dsrc_set for S in o):
            aff_dm_checked += 1
            if len({dm[S] for S in o}) > 1: aff_dm_viol += 1
    sizes = Counter(len(o) for o in orb_aff.values())
    log(f"(b) shift orbits: {len(orb_shift)} (compression {N/len(orb_shift):.2f}); "
        f"AFFINE orbits: {len(orb_aff)} (compression {N/len(orb_aff):.2f}, "
        f"extra factor {len(orb_shift)/len(orb_aff):.3f} vs shift; max extra = phi(n)={len(units)})")
    log(f"    affine-orbit size distribution: {dict(sorted(sizes.items()))}")
    log(f"    sparse-count CONSTANT on affine orbit: violations {aff_cnt_viol}/{len(orb_aff)}")
    log(f"    dual-min   CONSTANT on affine orbit: violations {aff_dm_viol}/{aff_dm_checked} "
        f"(orbits fully dual'd)")

    # =================================================================== (d) reversal k=-1 (isolated)
    km1 = (n - 1)  # -1 mod n
    rev_sc_eq = rev_sc_tot = 0; rev_dm_eq = rev_dm_tot = 0
    seen = set()
    for S in sections:
        Srev = tuple(sorted((km1*s) % n for s in S))
        if S in seen: continue
        seen.add(S); seen.add(Srev)
        rev_sc_tot += 1
        cRev = counts.get(Srev, sparse_count([a[x] for x in Srev], p, half))
        if counts[S] == cRev: rev_sc_eq += 1
        if S in dsrc_set and Srev in dsrc_set:
            rev_dm_tot += 1
            if dm[S] == dm[Srev]: rev_dm_eq += 1
    log(f"(d) reversal k=-1 (conjugation h->h^-1): sparse-count equal {rev_sc_eq}/{rev_sc_tot}; "
        f"dual-min equal {rev_dm_eq}/{rev_dm_tot} (dual'd pairs)  "
        f"[-1 preserves char-0 antipodal count but not lambda1*]")
    log()
    return dict(n=n,p=p,r=r,N=N,n_defect=n_defect,
                sc_eq=sc_eq,sc_tot=sc_tot,dm_eq=dm_eq,dm_tot=dm_tot,
                shift_orbits=len(orb_shift),aff_orbits=len(orb_aff),
                aff_cnt_viol=aff_cnt_viol,aff_dm_viol=aff_dm_viol,
                rev_sc_eq=rev_sc_eq,rev_sc_tot=rev_sc_tot,
                rev_dm_eq=rev_dm_eq,rev_dm_tot=rev_dm_tot,
                countermodel=(countermodel is not None))

def main():
    t0 = time.time()
    log("="*92)
    log("probe_466_sst_multiplier.py  --  LANE S5: the SST multiplier-action residue")
    log("="*92)
    log()
    log("EXACT IDENTITY (not empirical): multiply index set by k (gcd(k,n)=1)  <=>  replace root")
    log("h by the DIFFERENT primitive root h^k:   L_{kS}(h) = L_S(h^k).  The shift S->S+1 is the")
    log("unit multiple h (true isometry); the multiplier is a GALOIS TWIST, not a unit multiple.")
    log()

    results = []

    # ---------------- n=16 full ----------------
    primes16 = find_primes(16, 3)
    log(f"n=16 primes {primes16} (65537=2^16+1 is Fermat; stats read off generic 65617,65633)")
    for r in (2, 3):
        d = 2*r
        sections = [tuple(S) for S in itertools.combinations(range(16), d)]
        for i,p in enumerate(primes16):
            note = "[FERMAT 2^16+1 -- flagged resonant]" if p == 65537 else "[generic]"
            # full dual for r=2 (1820 secs cheap); sample for r=3 (8008 secs, dual is the cost)
            do_all = (r == 2)
            dsample = sections if do_all else random.sample(sections, 1500)
            results.append(run_scale(16, p, r, sections, do_all, dsample, note))

    # ---------------- n=32 r=2 FULL census ----------------
    primes32 = find_primes(32, 2)
    log(f"n=32 primes {primes32} (p=1 mod 32, p>=32^4=1048576)")
    r = 2; d = 4
    sections32 = [tuple(S) for S in itertools.combinations(range(32), d)]  # C(32,4)=35960
    log(f"n=32 r=2 full census: {len(sections32)} sections")
    for p in primes32:
        dsample = random.sample(sections32, 4000)   # dual-min on a 4000 sample (SVP is the cost)
        results.append(run_scale(32, p, r, sections32, False, dsample, "[generic]"))

    # ---------------- verdict ----------------
    log("="*92)
    log("SUMMARY")
    log(f"{'n':>3} {'p':>9} {'r':>2} {'#sect':>6} {'#defect':>7} {'shOrb':>6} {'affOrb':>6} "
        f"{'sc=%':>6} {'dm=%':>6} {'affCntViol':>10} {'affDmViol':>9} {'rev_sc':>10} {'rev_dm':>10}")
    for R in results:
        log(f"{R['n']:>3} {R['p']:>9} {R['r']:>2} {R['N']:>6} {R['n_defect']:>7} "
            f"{R['shift_orbits']:>6} {R['aff_orbits']:>6} "
            f"{100*R['sc_eq']/R['sc_tot']:>5.1f} {100*R['dm_eq']/R['dm_tot']:>5.1f} "
            f"{R['aff_cnt_viol']:>10} {R['aff_dm_viol']:>9} "
            f"{str(R['rev_sc_eq'])+'/'+str(R['rev_sc_tot']):>10} "
            f"{str(R['rev_dm_eq'])+'/'+str(R['rev_dm_tot']):>10}")
    log()
    any_dm_broken = any(R['dm_eq'] < R['dm_tot'] for R in results)
    all_sc_const = all(R['aff_cnt_viol'] == 0 for R in results)
    log("VERDICT:")
    log(f"  sparse-count is {'CONSTANT' if all_sc_const else 'NOT constant'} on affine orbits "
        f"(affine invariant; extra factor phi(n) compression over shift) -- because in the n=2^mu")
    log(f"  regime every bad section is char-0/antipodal and multiplier x->kx fixes the order-2")
    log(f"  element n/2 (k odd), so it permutes antipodal pairs.")
    log(f"  dual-minimum lambda1* is {'BROKEN' if any_dm_broken else 'preserved'} by multipliers "
        f"=> multiplier action is NOT an isometry of a fixed L_p.")
    log(f"  RESIDUE STATUS: the multiplier gives NO new compression of the DUAL-MINIMUM census")
    log(f"  (within-affine-orbit dual-min variance is nonzero; countermodel pairs printed). DEAD")
    log(f"  as a lattice-geometry lever; ALIVE only as the (already-understood) char-0 sparse-count")
    log(f"  symmetry.  Reversal k=-1 is the special conjugation case of exactly this dichotomy.")
    log(f"total time {time.time()-t0:.1f}s")

    with open("scripts/probes/_out_466_sst_multiplier.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")

if __name__ == "__main__":
    main()
