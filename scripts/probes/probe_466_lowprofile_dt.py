#!/usr/bin/env python3
"""probe_466_lowprofile_dt.py — LANE W2 (#466): the low-profile D(t) fiber theorem.

Objects (matching ArkLib/Data/CodingTheory/ProximityGap/LineListReduction.lean +
LineListAppearanceFiber.lean):
  * RS code C = rsCode(dom, k), dom = mu_n (multiplicative subgroup of order n, p = 1 mod n).
  * Line w_gamma = u0 + gamma*u1; Z = directionZeroSet(u1), supp = complement, s = |supp|.
  * lineBadScalars   = {gamma : exists codeword with agreement >= a with w_gamma}   (Lambda_b)
  * lineAppearing    = {codewords appearing at some gamma with agreement >= a}      (Lambda)
  * plain fiber D(t) = |lineAppearing  cap  {c : c|S = u0|S}|,  S subset Z, |S| = t
  * exact fiber      = |{c in lineAppearing : zeroAgreementSet(c) = S}|
  * per-gamma plain fiber(gamma, S)  = {c in C : c|S = u0|S, agree(c, w_gamma) >= a}
  * per-gamma exact fiber(gamma, S)  = same but zeroAgreementSet(c) = S exactly

Claims tested:
  (N) NAIVE (the task's key-observation reading): a >= k  ==>  per-gamma PLAIN fiber <= 1.
      Expected FALSE; we search for countermodels and also build one constructively.
  (T) THEOREM candidate: k + s + t <= 2a  ==>  per-gamma EXACT fiber <= 1.
      (support-localized union bound; s = |supp(u1)|, t = |S|). Expected TRUE (0 violations).
  (A) AMBIENT: 2a >= n + k ==> per-gamma PLAIN fiber <= 1 (unique decoding). Expected TRUE
      wherever the premise holds (rarely at our params).
  (C) CIRCULARITY data: D(t), D_exact(t) vs Lambda_b (bad count) and the weld coefficient
      K = sum_{t<a} C(z,t) * floor(s/(a-t))  (always >= 1 => the self-referential
      fixed point is vicious).

Regime: multiple primes per n with different v2(p-1); dom = proper subgroup mu_n where
possible; large-zero-safe lines only (z >= a and no codeword with >= a zero-agreements).
This is a coding/counting probe (no character sums), so beta >= 4 is spot-checked only via
the fiber-side theorem check (claim T/N) at p = 4129, n = 8 (fiber enumeration, k - t = 1).
"""
import itertools, random, sys
from collections import defaultdict

random.seed(466)
OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v

def primitive_root(p):
    fac = []
    m = p - 1; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    dom = [pow(h, i, p) for i in range(n)]
    assert len(set(dom)) == n
    return dom

def all_codewords(p, k, dom):
    """list of (coeff_tuple, eval_tuple) for all polys of degree < k."""
    words = []
    for coeffs in itertools.product(range(p), repeat=k):
        ev = tuple(sum(coeffs[j] * pow(x, j, p) for j in range(k)) % p for x in dom)
        words.append(ev)
    return words

def line_data(p, n, k, a, dom, words, Z, u0, u1):
    """Return per-codeword (zeroagr_set, votes dict gamma->count) + appearing/bad sets."""
    supp = [i for i in range(n) if i not in Z]
    inv_u1 = {i: pow(u1[i], p - 2, p) for i in supp}
    appearing = []   # (idx, zset frozenset, gammas set of gamma where agreement >= a)
    bad = set()
    for idx, c in enumerate(words):
        zset = frozenset(i for i in Z if c[i] == u0[i])
        votes = defaultdict(int)
        for i in supp:
            g = ((c[i] - u0[i]) * inv_u1[i]) % p
            votes[g] += 1
        zc = len(zset)
        gammas = {g for g, v in votes.items() if zc + v >= a}
        if gammas:
            appearing.append((idx, zset, gammas))
            bad |= gammas
    return appearing, bad, supp

def safe_line(p, n, k, a, words, Z, u0):
    """ZeroDirectionSafeLine: every codeword has < a zero-agreements with u0 on Z."""
    for c in words:
        if sum(1 for i in Z if c[i] == u0[i]) >= a:
            return False
    return True

def scan_config(p, n, k, a, z, n_lines=4, n_subsets=25):
    dom = mu_n(p, n)
    words = all_codewords(p, k, dom)
    s = n - z
    res = dict(naive_viol=0, thmT_viol=0, ambient_viol=0, rows=[], cm=None)
    lines_done = 0
    tries = 0
    while lines_done < n_lines and tries < 60:
        tries += 1
        Z = frozenset(random.sample(range(n), z))
        u0 = [random.randrange(p) for _ in range(n)]
        u1 = [0 if i in Z else random.randrange(1, p) for i in range(n)]
        if not safe_line(p, n, k, a, words, Z, u0):
            continue
        appearing, bad, supp = line_data(p, n, k, a, dom, words, Z, u0, u1)
        lines_done += 1
        Lb = len(bad)
        Lam = len(appearing)
        K = sum(comb(z, t) * (s // (a - t)) for t in range(a))
        for t in range(min(a, z + 1)):
            Zl = sorted(Z)
            subsets = [frozenset(c) for c in itertools.combinations(Zl, t)]
            if len(subsets) > n_subsets:
                subsets = random.sample(subsets, n_subsets)
            for S in subsets:
                plainD = [ap for ap in appearing if all(words[ap[0]][i] == u0[i] for i in S)]
                exactD = [ap for ap in appearing if ap[1] == S]
                # per-gamma counts
                pg_plain = defaultdict(int); pg_exact = defaultdict(int)
                for ap in plainD:
                    for g in ap[2]: pg_plain[g] += 1
                for ap in exactD:
                    for g in ap[2]: pg_exact[g] += 1
                mx_plain = max(pg_plain.values(), default=0)
                mx_exact = max(pg_exact.values(), default=0)
                # (N) naive: a >= k so claim says mx_plain <= 1
                if a >= k and mx_plain > 1:
                    res['naive_viol'] += 1
                    if res['cm'] is None:
                        res['cm'] = (p, n, k, a, z, t, sorted(S), mx_plain)
                # (T) support-localized exact-fiber uniqueness
                if k + s + t <= 2 * a and mx_exact > 1:
                    res['thmT_viol'] += 1
                    log(f"  !! THEOREM T VIOLATION p={p} n={n} k={k} a={a} z={z} t={t} mx={mx_exact}")
                # (A) ambient unique decoding
                if 2 * a >= n + k and mx_plain > 1:
                    res['ambient_viol'] += 1
                    log(f"  !! AMBIENT VIOLATION p={p} n={n} k={k} a={a} t={t}")
                res['rows'].append((t, len(plainD), len(exactD), mx_plain, mx_exact, Lb, Lam, K,
                                    k + s + t <= 2 * a))
    return res, lines_done

from math import comb

def summarize(tag, res, lines_done, p, n, k, a, z):
    s = n - z
    rows = res['rows']
    if not rows:
        log(f"[{tag}] p={p} n={n} k={k} a={a} z={z}: no safe lines found"); return
    byt = defaultdict(list)
    for r in rows: byt[r[0]].append(r)
    log(f"[{tag}] p={p} (v2={v2(p-1)}) n={n} k={k} a={a} z={z} s={s} "
        f"lines={lines_done} naive_viol={res['naive_viol']} thmT_viol={res['thmT_viol']} "
        f"ambient_viol={res['ambient_viol']}")
    for t in sorted(byt):
        rs = byt[t]
        Dmax = max(r[1] for r in rs); Dexmax = max(r[2] for r in rs)
        mxp = max(r[3] for r in rs); mxe = max(r[4] for r in rs)
        Lb = max(r[5] for r in rs); K = rs[0][7]; thr = rs[0][8]
        log(f"   t={t}: D(t)max={Dmax} Dexact_max={Dexmax} perG_plain_max={mxp} "
            f"perG_exact_max={mxe} Lambda_b_max={Lb} K={K} thrT(k+s+t<=2a)={thr}")
    if res['cm']:
        log(f"   NAIVE COUNTERMODEL (random scan): p,n,k,a,z,t,S,mx = {res['cm']}")

def constructive_countermodel(p, n=8, k=2, a=4, t=1):
    """Explicit refutation of (N): two distinct codewords in the same per-gamma PLAIN fiber.
    Construction (see lane analysis): z = a = 4, s = 4, S = one zero coord;
    c = P with a-1 zero-agreements + 1 moving vote for gamma;
    c' = P' (= P exactly on S) with t zero-agreements + (a-t) moving votes for gamma."""
    dom = mu_n(p, n)
    # coordinates 0..3 zero-set Z, 4..7 support
    Z = [0, 1, 2, 3]; supp = [4, 5, 6, 7]
    S = [0]
    # P and P' distinct deg<2 polys agreeing exactly on dom[0]
    P  = lambda x: (3 + 5 * x) % p
    x0 = dom[0]
    # P' = P + (X - x0)  => agrees with P exactly at x0 (deg 1, both in code k=2)
    Pp = lambda x: (P(x) + (x - x0)) % p
    c  = tuple(P(dom[i]) % p for i in range(n))
    cp = tuple(Pp(dom[i]) % p for i in range(n))
    assert c != cp and sum(1 for i in range(n) if c[i] == cp[i]) == 1  # pairwise agr = |S| = 1
    # u0 on Z: equal to P on S u E (E = {1,2}, so c has a-1 = 3 zero-agreements);
    # differ from BOTH P and P' on Z \ (S u E) = {3}
    u0 = [0] * n
    for i in [0, 1, 2]:
        u0[i] = c[i]
    u0[3] = (c[3] + 1) % p
    if u0[3] == cp[3]:
        u0[3] = (c[3] + 2) % p
        assert u0[3] != cp[3] and u0[3] != c[3]
    gamma = 1
    # moving: coord 4 votes for gamma from c;  coords 5,6,7 vote for gamma from c'
    u1 = [0] * n
    for i, w in [(4, c)] + [(i, cp) for i in [5, 6, 7]]:
        u0[i] = (w[i] + random.randrange(1, p)) % p          # ensure u0 != w there
        u1[i] = ((w[i] - u0[i]) * pow(gamma, p - 2, p)) % p  # w_i = u0_i + gamma*u1_i
        assert u1[i] != 0
    words = all_codewords(p, k, dom)
    assert safe_line(p, n, k, a, words, frozenset(Z), u0), "line not zero-direction safe"
    wg = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    agr  = sum(1 for i in range(n) if c[i] == wg[i])
    agrp = sum(1 for i in range(n) if cp[i] == wg[i])
    inS  = all(c[i] == u0[i] for i in S) and all(cp[i] == u0[i] for i in S)
    zc   = sum(1 for i in Z if c[i]  == u0[i])
    zcp  = sum(1 for i in Z if cp[i] == u0[i])
    ok = (agr >= a and agrp >= a and inS and c != cp)
    log(f"[constructive countermodel to NAIVE] p={p} n={n} k={k} a={a} t={t}: "
        f"agree(c,w_g)={agr} agree(c',w_g)={agrp} both>={a}: {ok}; "
        f"zero-agr(c)={zc} zero-agr(c')={zcp} (different strata; exact-fiber thm unharmed); "
        f"pairwise agr(c,c')=1 <= k-1={k-1}")
    assert ok
    # check the support-localized threshold correctly EXCLUDES this pair:
    s = n - len(Z)
    log(f"   threshold check: plain-fiber pair has k+s+t = {k+s+t} vs 2a = {2*a} "
        f"(<= means exact-thm applies; the two words sit in exact strata t'={zc} and t'={zcp})")
    return True

def beta4_spotcheck(p=4129, n=8, k=2, a=4, t=1, n_lines=3, n_gamma=200):
    """beta >= 4 spot check (p >= n^4): fiber-side only (enumerate the p^{k-t} = p fiber
    completions through S; cannot enumerate p^2 codewords). Checks (N) and (T) per gamma."""
    assert p >= n ** 4 and (p - 1) % n == 0
    dom = mu_n(p, n)
    z = a
    naive_viol = 0; thmT_viol = 0
    s = n - z
    for _ in range(n_lines):
        Z = sorted(random.sample(range(n), z))
        supp = [i for i in range(n) if i not in Z]
        u0 = [random.randrange(p) for _ in range(n)]
        u1 = [0] * n
        for i in supp: u1[i] = random.randrange(1, p)
        S = Z[:t]
        i0 = S[0]
        x0 = dom[i0]
        # fiber(S): deg<2 polys P with P(x0) = u0[i0]:  P = u0[i0] + m*(X - x0), m in F_p
        for gcount, gamma in enumerate(random.sample(range(p), n_gamma)):
            wg = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
            hits = []
            for m in range(p):
                cw = tuple((u0[i0] + m * (dom[i] - x0)) % p for i in range(n))
                agr = sum(1 for i in range(n) if cw[i] == wg[i])
                if agr >= a:
                    zc = frozenset(i for i in Z if cw[i] == u0[i])
                    hits.append((m, zc))
            if len(hits) > 1:
                naive_viol += 1
            exact_ct = defaultdict(int)
            for m, zc in hits:
                if zc == frozenset(S): exact_ct['x'] += 1
            if k + s + t <= 2 * a and exact_ct.get('x', 0) > 1:
                thmT_viol += 1
    log(f"[beta>=4 spot] p={p} n={n} k={k} a={a} z={z} t={t}: naive per-gamma>1 events="
        f"{naive_viol} (claim N false OK), thmT violations={thmT_viol} (must be 0; "
        f"threshold k+s+t={k+s+t} <= 2a={2*a}: {k+s+t <= 2*a})")
    return thmT_viol

def main():
    log("=== probe_466_lowprofile_dt: low-profile D(t) fiber scanner (lane W2) ===")
    log("")
    # constructive countermodel to the naive claim at >= 2 primes
    for p in [17, 41, 97]:
        constructive_countermodel(p)
    log("")
    total_T_viol = 0
    configs = [
        # (p, n, k, a, z)   a = k+2 typical; z >= a (large-zero branch)
        (17, 8, 2, 4, 4), (41, 8, 2, 4, 4), (97, 8, 2, 4, 4),
        (17, 8, 2, 4, 5), (41, 8, 2, 4, 5),
        (17, 8, 3, 5, 5), (17, 8, 3, 5, 6),
        (13, 12, 2, 4, 6), (73, 12, 2, 4, 6),
        (13, 12, 2, 4, 8), (73, 12, 2, 4, 8),
        (13, 12, 3, 5, 6), (13, 12, 3, 5, 8),
        (97, 16, 2, 4, 8), (193, 16, 2, 4, 8),
        (97, 16, 2, 4, 12), (193, 16, 2, 4, 12),
        # higher a: cross the k+s+t <= 2a threshold with room (test T on both sides)
        (17, 8, 2, 5, 5), (41, 8, 2, 5, 5),
        (13, 12, 2, 6, 8), (73, 12, 2, 6, 8),
        (97, 16, 3, 8, 10), (193, 16, 3, 8, 10),
    ]
    for (p, n, k, a, z) in configs:
        if (p - 1) % n != 0: continue
        res, ld = scan_config(p, n, k, a, z)
        summarize("scan", res, ld, p, n, k, a, z)
        total_T_viol += res['thmT_viol'] + res['ambient_viol']
    log("")
    total_T_viol += beta4_spotcheck()
    log("")
    log(f"=== VERDICT: theorem-T (k+s+t<=2a => per-gamma exact fiber <=1) violations: "
        f"{total_T_viol} (0 expected) ===")
    log("=== naive claim (a>=k => per-gamma plain fiber <=1): REFUTED constructively at "
        "p=17,41,97 ===")
    with open("scripts/probes/_out_466_lowprofile_dt.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")

if __name__ == "__main__":
    main()
