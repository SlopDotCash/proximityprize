#!/usr/bin/env python3
"""probe_466_lowprofile_coupled.py — LANE S1 (#466): the z-COUPLED low-profile sum.

The weld's `hlow` provable upper bound on the bad-scalar count on a large-zero-safe line is
(LineListMCAWeld / _R2B_LargeZeroWitnessSplit / _LowProfileFiberBound):

    #bad  <=  weight  =  Σ_{t<a} #stratum(t) * floor(s/(a-t))                      (EXACT, layer 3)

where #stratum(t) = # appearing codewords with EXACTLY t zero-agreements.  The ONLY provable
per-stratum cap available (per-fiber uniqueness, _LowProfileFiberBound §3-6) is the z-COUPLED
decomposition

    #stratum(t)  <=  choose(z, t) * D(t),   D(t) := max_{S in C(Z,t)} #{appearing c : zeroAgrSet(c)=S}

giving the COUPLED weld bound the consumer must fit into <= 2B:

    W_coup  =  Σ_{t<a} choose(z,t) * D(t) * floor(s/(a-t)).

Round-4 L1 killed the UNCOUPLED envelope  W_unc = (max_t D(t)) * Σ_t choose(z,t) floor(s/(a-t)).
THIS probe answers the surviving question (dossier §15 survivor 1):

  ==> With the z-coupling (coefficients choose(z,t) depend on t), is W_coup sub-q / poly,
      where the uncoupled W_unc was not?

Decisive measurements on large-zero-SAFE lines (z >= a, no codeword with >= a zero-agreements):
  * W_true  = Σ_t #stratum(t)*floor(s/(a-t))          -- the ACTUAL weld weight (what we need small)
  * W_coup  = Σ_t choose(z,t)*D(t)*floor(s/(a-t))     -- the provable coupled bound
  * W_unc   = (max_t D(t)) * Σ_t choose(z,t)*floor(s/(a-t))  -- the dead uncoupled envelope
  * Lambda  = total # appearing codewords (= Σ_t #stratum(t)); Lambda_b = # bad scalars
  * occupancy(t) = (# t-subsets S of Z with nonempty EXACT fiber) / choose(z,t)
  * the "coupling gap"  G(t) = choose(z,t)*D(t) / #stratum(t)  (>1 => choose-decomposition lossy)

Verdict logic:
  - If  W_coup  tracks a POLY budget (~ n) while W_unc explodes  => coupling RESCUES => try to PROVE.
  - If  W_coup  ALSO explodes (>> W_true ~ Lambda, grows binomially in n) => coupling does NOT
    rescue: the choose(z,t) factor injects a q-power because D(t)>=1 is realized at high t while
    most t-subsets are EMPTY (occupancy -> 0).  Then the sub-q object is the TRUE stratum
    Σ_S D_exact(S) = punctured list size (Johnson-equivalent-hard, hlow-map §3) => REFUTE, name split.

Regime: p = 1 mod n, proper subgroup mu_n; multiple primes with different v2(p-1); flag the
generalized-Fermat resonant family (p=17=2^4+1, p=257=2^8+1) vs generic primes.  k=2 (full enum);
n=8,16.  This is a pure coding/counting probe (no character sums).
"""
import itertools, random, sys
from math import comb
from collections import defaultdict

random.seed(4660)
OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v

def primitive_root(p):
    fac = []; m = p - 1; d = 2
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
    words = []
    for coeffs in itertools.product(range(p), repeat=k):
        ev = tuple(sum(coeffs[j] * pow(x, j, p) for j in range(k)) % p for x in dom)
        words.append(ev)
    return words

def line_appearing(p, n, k, a, dom, words, Z, u0, u1):
    """Return appearing list as (eval_tuple, zeroAgrSet frozenset, bad-gammas set); bad set."""
    supp = [i for i in range(n) if i not in Z]
    inv_u1 = {i: pow(u1[i], p - 2, p) for i in supp}
    appearing = []; bad = set()
    for c in words:
        zset = frozenset(i for i in Z if c[i] == u0[i])
        votes = defaultdict(int)
        for i in supp:
            g = ((c[i] - u0[i]) * inv_u1[i]) % p
            votes[g] += 1
        zc = len(zset)
        gammas = {g for g, v in votes.items() if zc + v >= a}
        if gammas:
            appearing.append((c, zset, gammas))
            bad |= gammas
    return appearing, bad

def safe_line(p, n, k, a, words, Z, u0):
    for c in words:
        if sum(1 for i in Z if c[i] == u0[i]) >= a:
            return False
    return True

def coupled_measure(p, n, k, a, z, n_lines=6, n_tries=400, fermat=False):
    dom = mu_n(p, n)
    words = all_codewords(p, k, dom)
    s = n - z
    rows = []   # per safe line: dict of measurements
    tries = 0
    while len(rows) < n_lines and tries < n_tries:
        tries += 1
        Z = frozenset(random.sample(range(n), z))
        u0 = [random.randrange(p) for _ in range(n)]
        u1 = [0 if i in Z else random.randrange(1, p) for i in range(n)]
        if not safe_line(p, n, k, a, words, Z, u0):
            continue
        appearing, bad = line_appearing(p, n, k, a, dom, words, Z, u0, u1)
        Lam = len(appearing); Lb = len(bad)
        # per-stratum & per-subset exact fiber
        stratum = defaultdict(int)                 # t -> #stratum(t)
        subset_fiber = defaultdict(lambda: defaultdict(int))  # t -> {S: count}
        for (c, zset, gammas) in appearing:
            t = len(zset)
            stratum[t] += 1
            subset_fiber[t][zset] += 1
        Dmax = {}; occ = {}
        for t in range(a):
            fibers = subset_fiber.get(t, {})
            Dmax[t] = max(fibers.values(), default=0)
            occ[t] = (len(fibers), comb(z, t))
        def fl(t): return s // (a - t)
        W_true = sum(stratum.get(t, 0) * fl(t) for t in range(a))
        W_coup = sum(comb(z, t) * Dmax[t] * fl(t) for t in range(a))
        maxD = max(Dmax.values(), default=0)
        W_unc = maxD * sum(comb(z, t) * fl(t) for t in range(a))
        # realized top stratum (largest t with an appearing codeword)
        t_top = max((t for t in range(a) if stratum.get(t, 0) > 0), default=-1)
        rows.append(dict(Z=Z, Lam=Lam, Lb=Lb, stratum=dict(stratum), Dmax=Dmax, occ=occ,
                         W_true=W_true, W_coup=W_coup, W_unc=W_unc, t_top=t_top, maxD=maxD))
    return rows, s

def summarize(p, n, k, a, z, rows, s, fermat):
    tag = "FERMAT" if fermat else "generic"
    if not rows:
        log(f"[{tag}] p={p} n={n} k={k} a={a} z={z}: NO safe lines"); return None
    # aggregate worst-case
    worst = max(rows, key=lambda r: r['W_coup'])
    Lam_max = max(r['Lam'] for r in rows)
    Lb_max = max(r['Lb'] for r in rows)
    Wtrue_max = max(r['W_true'] for r in rows)
    Wcoup_max = max(r['W_coup'] for r in rows)
    Wunc_max = max(r['W_unc'] for r in rows)
    vlz = (k + s <= a)   # very-large-zero (choose-cap branch) vs mid-band
    band = "vLZ(k+s<=a)" if vlz else "MID(a<k+s)"
    log(f"[{tag}] p={p}(v2={v2(p-1)}) n={n} k={k} a={a} z={z} s={s} {band} "
        f"lines={len(rows)}: Lambda<= {Lam_max} Lb<= {Lb_max} | "
        f"W_true<= {Wtrue_max}  W_coup<= {Wcoup_max}  W_unc<= {Wunc_max}")
    # per-t detail on the worst coupled line
    log(f"    worst-coupled line: Lambda={worst['Lam']} t_top={worst['t_top']} "
        f"W_true={worst['W_true']} W_coup={worst['W_coup']} (ratio {worst['W_coup']/max(1,worst['W_true']):.1f}x)")
    for t in range(a):
        st = worst['stratum'].get(t, 0); D = worst['Dmax'][t]; (nz, tot) = worst['occ'][t]
        cz = comb(z, t)
        if st == 0 and cz*D == 0:
            continue
        coup_t = cz * D * (s // (a - t))
        log(f"      t={t}: stratum={st}  D(t)={D}  choose(z,t)={cz}  occ={nz}/{tot}"
            f"  choose*D={cz*D} (vs stratum {st}; loss x{(cz*D/max(1,st)):.0f})  coupTerm={coup_t}")
    return dict(Wtrue_max=Wtrue_max, Wcoup_max=Wcoup_max, Wunc_max=Wunc_max,
                Lam_max=Lam_max, vlz=vlz)

def main():
    log("=== probe_466_lowprofile_coupled: z-COUPLED low-profile sum W_coup vs W_true vs W_unc ===")
    log("Question: does the z-coupling (choose(z,t) coeffs) keep W_coup sub-q where W_unc blew up?")
    log("")
    # (p, n, k, a, z, fermat?)  — a in-window (k < a < sqrt(nk)); z>=a large-zero branch.
    # n=8 k=2: sqrt(nk)=4, so a=4 is the Johnson boundary; a=4 is the smallest in-branch value.
    #   Use a=4 (boundary) and a=5 (needs z>=5). Primes: 17=Fermat(2^4+1), 41, 97 (generic).
    # n=16 k=2: sqrt(nk)=~5.66 -> a in {4,5}; z>=a. Primes: 97,193,257=Fermat(2^8+1),241.
    configs = [
        (17, 8, 2, 4, 4, True), (41, 8, 2, 4, 4, False), (97, 8, 2, 4, 4, False),
        (17, 8, 2, 4, 6, True), (97, 8, 2, 4, 6, False),
        (17, 8, 2, 5, 5, True), (41, 8, 2, 5, 5, False),
        (17, 8, 2, 5, 7, True), (97, 8, 2, 5, 7, False),
        (97, 16, 2, 4, 8, False), (193, 16, 2, 4, 8, False), (257, 16, 2, 4, 8, True),
        (97, 16, 2, 5, 10, False), (257, 16, 2, 5, 10, True),
        (97, 16, 2, 5, 13, False), (193, 16, 2, 5, 13, False),
        (97, 16, 2, 6, 12, False), (257, 16, 2, 6, 12, True),
    ]
    stats = []
    for (p, n, k, a, z, fermat) in configs:
        if (p - 1) % n != 0:
            log(f"  (skip p={p} n={n}: n does not divide p-1)"); continue
        rows, s = coupled_measure(p, n, k, a, z, fermat=fermat)
        r = summarize(p, n, k, a, z, rows, s, fermat)
        if r: stats.append((p, n, k, a, z, r))
        log("")
    # scaling verdict: W_coup/W_true growth vs n on comparable (k,a/z) rows
    log("=== SCALING (W_coup vs W_true) — is the coupling lossy (choose injects a q-power)? ===")
    for (p, n, k, a, z, r) in stats:
        ratio = r['Wcoup_max'] / max(1, r['Wtrue_max'])
        polyref = n * n   # a generous poly(n) budget reference (2B with B~n^2/2)
        flag_coup = "EXCEEDS poly n^2" if r['Wcoup_max'] > polyref else "within n^2"
        flag_true = "EXCEEDS poly n^2" if r['Wtrue_max'] > polyref else "within n^2"
        log(f"  n={n} a={a} z={z} {'vLZ' if r['vlz'] else 'MID'}: "
            f"W_true={r['Wtrue_max']} ({flag_true})  W_coup={r['Wcoup_max']} ({flag_coup})  "
            f"coup/true={ratio:.0f}x  Lambda<= {r['Lam_max']}")
    log("")
    log("VERDICT: see coup/true ratio growth and occupancy loss above. If W_coup >> W_true ~ Lambda")
    log("and grows binomially while W_true stays poly, the z-coupling does NOT rescue the sum:")
    log("choose(z,t) injects a q-power (D(t)>=1 realized at high t, most t-subsets empty).")
    with open("scripts/probes/_out_466_lowprofile_coupled.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")

if __name__ == "__main__":
    main()
