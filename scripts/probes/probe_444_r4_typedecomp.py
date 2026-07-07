"""
probe_444_r4_typedecomp.py  (#444 -- WHY is r=3 clean and r>=4 not? per-antipodal-type decomposition)

TASK: Diagnose precisely why r=3 has O_P(3)=C(n/4,2) (clean) but r>=4 has no clean form.
Candidate causes:
  (a) resonant maximizer line changes character with r (leading-exponent order != 2)
  (b) MULTIPLE antipodal types contribute incommensurate counts (r=3 has effectively ONE type)
  (c) genuine additive-energy coincidences enter even in char 0.

STRATEGY: For the TRUE maximizer line of each r, decompose #bad AND O_P by antipodal type
(p pairs, j singletons; 2p+j=a0=r+1). Check whether EACH type alone has a clean per-type O_P
that fits a closed form across n. A per-type law (even if total is messy) => <= K by summation.

We:
  1. CALIBRATE r=3 digit-for-digit (O_P=C(n/4,2), #bad=n*C(n/4,2)+1).
  2. For the r=3 maximizer, confirm it lives in essentially ONE antipodal type (the descent type).
  3. For the r=4 TRUE maximizer (family (x^{n/2+2},x^{n/4+1}); known O_P=9,97,897 @ n=16,32,64),
     decompose by type, compute per-type #bad and per-type O_P, fit per-type closed forms in q=n/4.
  4. Report the precise diagnosis.

p = BabyBear 2013265921 (char-0 worst case). NEVER n=q-1.
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict

p = 2013265921  # BabyBear, 2^27 | p-1

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 1000):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no w of order n=%d" % n)

def band_gamma_idx(Sidx, pe, pf, mu, k, a0):
    """S given by indices into mu. Interpolate x^e (vals pe) and x^f (vals pf) on the points;
    return pinned gamma (0 or nonzero) if S is bad, else None."""
    pts = [mu[i] for i in Sidx]
    m = len(pts)
    def interp(vals):
        A = [[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
        M = [A[i][:] + [vals[i] % p] for i in range(m)]
        for col in range(m):
            piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            inv = pow(M[col][col], p - 2, p)
            M[col] = [(v * inv) % p for v in M[col]]
            for rr in range(m):
                if rr != col and M[rr][col] % p != 0:
                    c = M[rr][col]
                    M[rr] = [(M[rr][t] - c * M[col][t]) % p for t in range(m + 1)]
        return [M[i][m] % p for i in range(m)]
    c0 = interp([pe[i] for i in Sidx])
    c1 = interp([pf[i] for i in Sidx])
    if c0 is None or c1 is None:
        return None
    gam = None
    nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None
    return gam if nd else None

def antipodal_type(Sidx, n):
    """Return (pairs, singles): #antipodal pairs {j, j+n/2} both in S, and #singletons."""
    h = n // 2
    Sset = set(Sidx)
    pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
    singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
    return (pairs, singles)

def census_with_type(n, r, e, f, mu):
    """Full census of one line. Returns dict:
       total_bad_nz, has_zero, total_OP, K,
       per_type: {(pairs,singles): {'subsets': cnt, 'bad_nz_gammas': set, 'OP': int, 'zero': bool}}
       Also tracks gamma -> set of types that PRODUCE it (to see if a gamma is multi-type)."""
    k = r - 1; a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    pe = [pow(x, e, p) for x in mu]
    pf = [pow(x, f, p) for x in mu]
    mult = pow(mu[1], (e - f) % n, p)  # dilation factor w^{e-f}

    all_bad = {}          # gamma -> first Sidx
    zero_bad = False
    type_bad_gammas = defaultdict(set)   # type -> set of nonzero gammas arising from THAT type
    type_subset_cnt = Counter()          # type -> #(bad subsets, counting multiplicity)
    type_zero = defaultdict(bool)
    gamma_types = defaultdict(set)       # gamma -> set of types producing it

    for Sidx in itertools.combinations(range(n), a0):
        gv = band_gamma_idx(Sidx, pe, pf, mu, k, a0)
        if gv is None:
            continue
        t = antipodal_type(Sidx, n)
        if gv % p == 0:
            zero_bad = True
            type_zero[t] = True
            type_subset_cnt[t] += 1
            continue
        type_subset_cnt[t] += 1
        type_bad_gammas[t].add(gv)
        gamma_types[gv].add(t)
        if gv not in all_bad:
            all_bad[gv] = Sidx

    nz = list(all_bad.keys())

    def count_orbits(gset):
        rem = set(gset); orbs = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; o = set()
            for _ in range(n):
                o.add(cur); cur = cur * mult % p
            orbs += 1; rem -= o
        return orbs

    total_OP = count_orbits(nz)
    per_type = {}
    for t, gset in type_bad_gammas.items():
        per_type[t] = {
            'subsets': type_subset_cnt[t],
            'bad_nz': len(gset),
            'OP': count_orbits(gset),
            'zero': type_zero[t],
            'gammas': gset,
        }
    # also record types with only zero-bad
    for t in type_zero:
        if t not in per_type:
            per_type[t] = {'subsets': type_subset_cnt[t], 'bad_nz': 0, 'OP': 0,
                           'zero': True, 'gammas': set()}

    # multi-type gammas: gammas produced by more than one antipodal type
    multi = {g: ts for g, ts in gamma_types.items() if len(ts) > 1}

    return {
        'n': n, 'r': r, 'e': e, 'f': f,
        'total_bad_nz': len(nz), 'has_zero': zero_bad, 'total_OP': total_OP, 'K': K,
        'per_type': per_type, 'multi_type_gammas': multi,
        'gamma_types': gamma_types,
    }

def print_census(res):
    n, r, e, f = res['n'], res['r'], res['e'], res['f']
    print(f"\n--- n={n} r={r} line (x^{e},x^{f}) d=gcd(e-f,n)={gcd((e-f)%n,n)} ---")
    print(f"    TOTAL #bad_nz={res['total_bad_nz']} (+{int(res['has_zero'])} zero) "
          f"O_P={res['total_OP']} K={res['K']} bad/K={res['total_bad_nz']/res['K']:.4f}")
    print(f"    per antipodal type (pairs,singles) -> #subsets / distinct nonzero gamma / O_P / zero?:")
    # SUM of per-type O_P vs total O_P tells us if types share gammas
    sum_type_OP = sum(d['OP'] for d in res['per_type'].values())
    sum_type_bad = sum(d['bad_nz'] for d in res['per_type'].values())
    for t in sorted(res['per_type']):
        d = res['per_type'][t]
        print(f"      type {t}: subsets={d['subsets']:6d}  bad_nz={d['bad_nz']:5d}  "
              f"O_P_type={d['OP']:4d}  zero={d['zero']}")
    print(f"    SUM(per-type bad_nz)={sum_type_bad} vs TOTAL bad_nz={res['total_bad_nz']} "
          f"(diff={sum_type_bad-res['total_bad_nz']} => # of gammas shared across types' multiplicity)")
    print(f"    SUM(per-type O_P)={sum_type_OP} vs TOTAL O_P={res['total_OP']}")
    nmulti = len(res['multi_type_gammas'])
    print(f"    # gammas produced by >1 antipodal type = {nmulti} "
          f"({'TYPES OVERLAP => incommensurate' if nmulti else 'TYPES DISJOINT in gamma-space'})")

def calibrate_r3():
    print("="*90)
    print("CALIBRATION r=3 (anti-fabrication): expect O_P=C(n/4,2)=6,28; #bad_total=n*C(n/4,2)+1")
    print("="*90)
    out = {}
    for n in [16, 32]:
        mu = [pow(w_of_order(n), i, p) for i in range(n)]
        e, f = n // 2, n // 2 - 1
        res = census_with_type(n, 3, e, f, mu)
        exp_op = comb(n // 4, 2)
        exp_bad = n * comb(n // 4, 2) + 1
        tot = res['total_bad_nz'] + int(res['has_zero'])
        ok = (res['total_OP'] == exp_op) and (tot == exp_bad)
        print(f"  n={n}: O_P={res['total_OP']} (expect {exp_op})  #bad_total={tot} "
              f"(expect {exp_bad})  => {'PASS' if ok else 'FAIL'}")
        print_census(res)
        out[n] = res
    return out

def diagnose_r4():
    print("\n" + "="*90)
    print("r=4 TRUE maximizer family (x^{n/2+2}, x^{n/4+1}); known O_P=9,97,897 @ n=16,32,(64)")
    print("="*90)
    out = {}
    for n in [16, 32]:
        mu = [pow(w_of_order(n), i, p) for i in range(n)]
        e, f = n // 2 + 2, n // 4 + 1
        res = census_with_type(n, 4, e, f, mu)
        print_census(res)
        out[n] = res
    return out

def fit_per_type(r3, r4):
    """Try clean per-type closed forms in q=n/4 for each antipodal type, across n=16,32."""
    print("\n" + "="*90)
    print("PER-TYPE CLOSED-FORM ATTEMPT (q=n/4; n=16->q=4, n=32->q=8)")
    print("="*90)
    for label, data in [("r=3", r3), ("r=4", r4)]:
        print(f"\n  {label}:")
        # collect union of types
        types = set()
        for n in data:
            types |= set(data[n]['per_type'].keys())
        for t in sorted(types):
            vals = {}
            for n in data:
                d = data[n]['per_type'].get(t)
                vals[n] = (d['OP'] if d else 0)
            q16 = 4; q32 = 8
            v16 = vals.get(16, 0); v32 = vals.get(32, 0)
            # candidate clean forms in q
            cands = []
            for name, fn in [
                ("C(q,2)", lambda q: comb(q, 2)),
                ("C(q,3)", lambda q: comb(q, 3)),
                ("q*C(q,2)", lambda q: q * comb(q, 2)),
                ("C(q,2)^? n/d", lambda q: comb(q, 2)),
                ("C(2q,2)", lambda q: comb(2 * q, 2)),
                ("C(q,2)+C(q,3)", lambda q: comb(q, 2) + comb(q, 3)),
                ("q^2", lambda q: q * q),
                ("q*(q-1)", lambda q: q * (q - 1)),
            ]:
                if fn(q16) == v16 and fn(q32) == v32:
                    cands.append(name)
            print(f"    type {t}: O_P_type n16={v16} n32={v32}  matches: "
                  f"{cands if cands else 'NONE of the small library'}")

if __name__ == "__main__":
    r3 = calibrate_r3()
    r4 = diagnose_r4()
    fit_per_type(r3, r4)
