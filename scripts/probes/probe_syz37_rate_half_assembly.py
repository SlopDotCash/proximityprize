#!/usr/bin/env python3
"""SYZ37 — rate-1/2 assembly: is the interior band saturated, or does it generate
for a *different* reason (out-of-budget Koszul + empty in-budget syzygy module)?

Reconciles the SYZ36 saturation claim.  For RS[n,k] with k = n/2 (rate 1/2) we
enumerate interior-band triples C_A,C_B,C_C of common size s in (2n/3, 3n/4) with
pairwise overlaps in [2s-n, k-1], and for EACH:

  * classify SATURATED (some pair overlap m_XY >= k) vs NON-SATURATED (all m<k);
  * compute union-generation deficiency d (SYZ36 gate);
  * compute Koszul in-budget? (m_AB+m_AC-t <= k-1 for the two carrying pairs);
  * compute the in-budget syzygy dimension of (W_AB,-W_AC,W_BC) with per-pair
    budgets b_XY = k-1-m_XY;
  * compute the MINIMAL nonzero syzygy degree mu1 of the *coprime* triple
    (W_AB, W_AC, W_BC) ignoring budgets (mu-basis first generator degree), and
    mu2, and the "balance" mu1 vs (mu1+mu2)/2.  We test whether the roots-of-unity
    domain mu_n can UNBALANCE the mu-basis vs a generic domain (potential
    strip counterexample), and lift-test any such instance for actual generation
    failure.

Deterministic; stdlib only.  Fields GF(p).
"""
from itertools import combinations

def inv(a, p): return pow(a % p, p - 2, p)

def rank_mod(rows, ncols, p):
    M = [row[:] for row in rows]; r = 0; nr = len(M)
    for c in range(ncols):
        piv = next((i for i in range(r, nr) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        ic = inv(M[r][c], p); M[r] = [(x*ic) % p for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(M[i][j]-f*M[r][j]) % p for j in range(ncols)]
        r += 1
        if r == nr: break
    return r

def nullspace_mod(rows, ncols, p):
    M = [row[:] for row in rows]; nr = len(M); pivcol = {}; r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, nr) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        ic = inv(M[r][c], p); M[r] = [(x*ic) % p for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(M[i][j]-f*M[r][j]) % p for j in range(ncols)]
        pivcol[c] = r; r += 1
        if r == nr: break
    free = [c for c in range(ncols) if c not in pivcol]; basis = []
    for fc in free:
        v = [0]*ncols; v[fc] = 1
        for c, rr in pivcol.items(): v[c] = (-M[rr][fc]) % p
        basis.append(v)
    return basis

def core_dual_basis(dom, k, p, core):
    n = len(dom); Gc = [[pow(dom[j], d, p) for j in core] for d in range(k)]
    out = []
    for w in nullspace_mod(Gc, len(core), p):
        v = [0]*n
        for idx, j in enumerate(core): v[j] = w[idx]
        out.append(v)
    return out

def gen_deficiency(dom, k, p, cores):
    U = sorted(set().union(*[set(c) for c in cores]))
    target = len(U) - k; rows = []
    for c in cores: rows.extend(core_dual_basis(dom, k, p, c))
    rk = rank_mod(rows, len(dom), p) if rows else 0
    return target - rk

def poly_from_roots(roots, p):
    poly = [1]
    for r in roots:
        new = [0]*(len(poly)+1)
        for i, c in enumerate(poly):
            new[i] = (new[i]-c*r) % p; new[i+1] = (new[i+1]+c) % p
        poly = new
    return poly

def pdeg(a):
    d = len(a)-1
    while d > 0 and a[d] == 0: d -= 1
    return d if any(a) else -1

def inbudget_syzygy_dim(WAB, WAC, WBC, bAB, bAC, bBC, p):
    dAB, dAC, dBC = pdeg(WAB), pdeg(WAC), pdeg(WBC)
    nAB = bAB+1 if bAB >= 0 else 0
    nAC = bAC+1 if bAC >= 0 else 0
    nBC = bBC+1 if bBC >= 0 else 0
    nvar = nAB+nAC+nBC
    if nvar == 0: return 0
    eqdeg = max((dAB+bAB) if nAB else -1, (dAC+bAC) if nAC else -1, (dBC+bBC) if nBC else -1)
    if eqdeg < 0: return 0
    rows = []
    for e in range(eqdeg+1):
        row = [0]*nvar
        for i in range(nAB):
            j = e-i
            if 0 <= j <= dAB: row[i] = (row[i]+WAB[j]) % p
        for i in range(nAC):
            j = e-i
            if 0 <= j <= dAC: row[nAB+i] = (row[nAB+i]-WAC[j]) % p
        for i in range(nBC):
            j = e-i
            if 0 <= j <= dBC: row[nAB+nAC+i] = (row[nAB+nAC+i]+WBC[j]) % p
        rows.append(row)
    return nvar - rank_mod(rows, nvar, p)

def min_syzygy_degree(WAB, WAC, WBC, p, dmax):
    """mu1 = smallest D >= 0 s.t. a NONZERO syzygy with all deg r_XY <= D exists,
    ignoring per-pair budgets (uniform degree bound D). Returns (mu1, mu2) where
    mu2 is the next generator degree (dim jumps 0->1 at mu1, and to 2 at mu2)."""
    dAB, dAC, dBC = pdeg(WAB), pdeg(WAC), pdeg(WBC)
    mu = []
    prev = 0
    for D in range(dmax+1):
        dim = inbudget_syzygy_dim(WAB, WAC, WBC, D, D, D, p)
        while dim > prev:
            mu.append(D); prev += 1
        if len(mu) >= 2: break
    if len(mu) == 0: mu = [None, None]
    elif len(mu) == 1: mu = [mu[0], None]
    return mu[0], mu[1]

def roots_of_unity(n, p):
    if (p-1) % n: return None
    for cand in range(2, p):
        w = pow(cand, (p-1)//n, p)
        if all(pow(w, d, p) != 1 for d in range(1, n)): return [pow(w, i, p) for i in range(n)]
    return None

def band_triples(n, k, pts, cap=300):
    slo = 2*n//3 + 1; shi = (3*n-1)//4
    for s in range(slo, shi+1):
        if s <= k: continue
        omin = max(2*s-n, 0); omax = k-1
        if omin > omax: continue
        CA = frozenset(pts[:s]); cnt = 0
        for CB in combinations(pts, s):
            CBs = frozenset(CB)
            if CBs == CA: continue
            if not (omin <= len(CA & CBs) <= omax): continue
            for CC in combinations(pts, s):
                CCs = frozenset(CC)
                if CCs in (CA, CBs): continue
                if not (omin <= len(CA & CCs) <= omax and omin <= len(CBs & CCs) <= omax): continue
                if len(CA | CBs | CCs) > n: continue
                yield sorted(CA), sorted(CBs), sorted(CCs); cnt += 1
                if cnt >= cap: return

def analyze(p, n, k, dom, name):
    tot = sat = nonsat = fails = koszul_inb = syz_pos = 0
    unbalanced = []
    for cores in band_triples(n, k, list(range(n))):
        tot += 1
        CA, CB, CC = [set(c) for c in cores]
        T = CA & CB & CC; t = len(T)
        mAB, mAC, mBC = len(CA & CB), len(CA & CC), len(CB & CC)
        saturated = max(mAB, mAC, mBC) >= k
        if saturated: sat += 1
        else: nonsat += 1
        d = gen_deficiency(dom, k, p, cores)
        if d != 0: fails += 1
        # Koszul in budget for the two pairs carrying it (choose the min-sum pair)
        kb = (mAB + mAC - t <= k-1) or (mAB + mBC - t <= k-1) or (mAC + mBC - t <= k-1)
        if kb: koszul_inb += 1
        WAB = poly_from_roots([dom[i] for i in sorted((CA & CB)-T)], p)
        WAC = poly_from_roots([dom[i] for i in sorted((CA & CC)-T)], p)
        WBC = poly_from_roots([dom[i] for i in sorted((CB & CC)-T)], p)
        sd = inbudget_syzygy_dim(WAB, WAC, WBC, k-1-mAB, k-1-mAC, k-1-mBC, p)
        if sd != 0: syz_pos += 1
        mu1, mu2 = min_syzygy_degree(WAB, WAC, WBC, p, s if (s := max(len(CA&CB), len(CA&CC), len(CB&CC))) else n)
        # balance: total deg of W-triple
        wsum = pdeg(WAB) + pdeg(WAC) + pdeg(WBC)
        if mu1 is not None and mu2 is not None:
            # unbalanced if mu1 much smaller than mu2 (mu1 < mu2 - 1) -> low minimal syzygy
            if mu1 + 1 < mu2:
                unbalanced.append((cores, mu1, mu2, d, sd))
    return dict(tot=tot, sat=sat, nonsat=nonsat, fails=fails, koszul_inb=koszul_inb,
                syz_pos=syz_pos, unbalanced=unbalanced)

def main():
    print("SYZ37 rate-1/2 assembly probe")
    print("="*78)
    # rate 1/2 configs: k = n//2, plus a couple of neighbors to show the boundary
    ns = [n for n in range(8, 21, 2)]
    all_unbalanced = []
    for p in (31, 101, 65537):
        for n in ns:
            k = n//2
            slo, shi = 2*n//3+1, (3*n-1)//4
            if slo > shi: continue
            if not any(max(2*s-n, 0) <= k-1 for s in range(slo, shi+1) if s > k): continue
            for name, dom in (("gen", list(range(1, n+1))), ("roots", roots_of_unity(n, p))):
                if dom is None or len(set(dom)) < n: continue
                r = analyze(p, n, k, dom, name)
                if r['tot'] == 0: continue
                print(f"p={p} n={n} k={k}(rate=1/2) dom={name:5s}: {r['tot']:4d} triples "
                      f"sat={r['sat']:4d} nonsat={r['nonsat']:4d} | genFAILS={r['fails']:3d} "
                      f"koszul_inbudget={r['koszul_inb']:3d} inbudget_syz>0={r['syz_pos']:3d} "
                      f"| unbalanced_mubasis={len(r['unbalanced'])}")
                all_unbalanced += [(p, n, k, name)+u for u in r['unbalanced']]
    print("-"*78)
    print(f"TOTAL unbalanced-mu-basis instances at rate 1/2: {len(all_unbalanced)}")
    for u in all_unbalanced[:10]:
        print("   UNBAL", u[:4], "mu1,mu2=", u[5], u[6], "genDefic=", u[7], "inbudgetSyz=", u[8])
    # boundary sanity: show rate just above 1/2
    print("-"*78)
    print("BOUNDARY (k = n//2 + 1, rate > 1/2), gen (generic) domain:")
    for p in (101,):
        for n in ns:
            k = n//2+1
            dom = list(range(1, n+1))
            slo, shi = 2*n//3+1, (3*n-1)//4
            if slo > shi: continue
            r = analyze(p, n, k, dom, "gen")
            if r['tot']:
                print(f"  n={n} k={k}: {r['tot']:4d} triples genFAILS={r['fails']:3d} "
                      f"koszul_inbudget={r['koszul_inb']:3d} inbudget_syz>0={r['syz_pos']:3d}")

if __name__ == "__main__":
    main()
