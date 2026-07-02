#!/usr/bin/env python3
"""
probe_466_ca_vs_mca.py -- #466 Lane W3 / B4: the CA => MCA collapse at LINES, measured exactly.

QUESTION (dossier v3 sec 6, Crites-Stewart flag): does a good correlated-agreement (CA) bound
imply a good mutual-correlated-agreement (MCA) bound, for affine lines (m=2)?  Open even for
lines; never attacked in this campaign.

OBJECTS (matching ArkLib/Data/CodingTheory/ProximityGap/Errors.lean):
  * CA-bad scalar (per stack u=(u0,u1), radius delta = (n-a)/n):
      gamma such that the line u0 + gamma*u1 is delta-close to RS_k, i.e. SOME codeword agrees
      with it on >= a of the n domain points.  (epsCA zeroes the whole stack if u is JOINTLY
      delta-close -- the if-branch in epsCA.)
  * MCA-bad scalar (mcaEvent, Errors.lean:216):
      exists S, |S| >= a, some codeword agrees with the line on S, AND no joint codeword pair
      (v0,v1) agrees with (u0,u1) on S  (pairJointAgreesOn splits row-wise).

KEY STRUCTURAL FACTS the probe exploits (each is a small lemma, checked by brute force below):
  (F1) mcaEvent(gamma) => line delta-close at gamma  (in-tree: mcaEvent_imp_relCloseToCode).
       So per-gamma, MCAbad subset-of CAbad on every stack.  The per-stack Pr bound
       Pr[mca] <= epsCA is ALREADY proven in-tree for non-jointly-close stacks
       (mcaEvent_probability_le_epsCA_of_not_jointProximity).  Hence the ONLY channel through
       which the collapse can fail is JOINTLY-close stacks (epsCA body = 0 there).
  (F2) not-pairJointAgreesOn is monotone UP in S, codeword-agreement is monotone DOWN, so
       mcaEvent fires at gamma iff SOME near-codeword w (agreement >= a) has NO joint pair on
       its MAXIMAL agreement set S_w.
  (F3) every near-codeword w at gamma is the interpolation P^T_gamma = P0^T + gamma*P1^T of the
       line through a k-subset T of S_w, where P0^T interpolates u0|T and P1^T interpolates
       u1|T (linearity of interpolation in the line parameter).  Agreement of P^T_gamma at
       j not in T happens at ONE critical gamma_j(T) (or always, or never).  Hence both bad
       sets are computable EXACTLY by enumerating (T, j) critical pairs -- no loop over F_p.
  (F4) a fire needs at least one strictly-critical point: if S_w = T union always(T), the pair
       (P0^T, P1^T) is itself a joint pair on S_w, so mcaEvent cannot fire there.

REGIME DISCIPLINE: mu_n = PROPER subgroup (m=(p-1)/n >= n^3), p = 1 mod n, p >= n^4,
never n = p-1, TWO primes per n, generalized-Fermat p (m a 2-power) excluded/flagged,
correlated direction X^{n/2} flagged in the monomial family.

Usage:  python probe_466_ca_vs_mca.py [--fast]
Output: scripts/probes/_out_466_ca_vs_mca.txt
"""

import sys, random, itertools, time
from collections import defaultdict

random.seed(466)

OUT = []
def log(s=""):
    print(s, flush=True)
    OUT.append(s)

# ---------------------------------------------------------------- primality
def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def is_pow2(m):
    return m > 0 and (m & (m-1)) == 0

def find_primes(n, count=2):
    """primes p = 1 mod n, p >= n^4, m=(p-1)/n not a 2-power (gen-Fermat trap excluded)."""
    ps, p = [], ((n**4)//n)*n + 1
    while len(ps) < count:
        if p >= n**4 and is_prime(p):
            m = (p-1)//n
            if not is_pow2(m):          # exclude generalized-Fermat structure
                ps.append(p)
            else:
                log(f"    [flag] skipping generalized-Fermat-structured prime p={p} (m=2^t)")
        p += n
    return ps

# ---------------------------------------------------------------- field/poly kit
class Kit:
    """RS_k on mu_n inside F_p: exact CA/MCA bad-set computation for 2-stacks."""
    def __init__(self, p, n, k):
        self.p, self.n, self.k = p, n, k
        # find generator of F_p^*
        fac = self._factor(p-1)
        g = 2
        while any(pow(g, (p-1)//q, p) == 1 for q in fac): g += 1
        self.h = pow(g, (p-1)//n, p)                    # generator of mu_n
        self.xs = [pow(self.h, j, p) for j in range(n)] # the domain (proper subgroup)
        assert len(set(self.xs)) == n and n < p-1
        self.Ts = list(itertools.combinations(range(n), k))
        self._inv = {}

    @staticmethod
    def _factor(m):
        fs, d = set(), 2
        while d*d <= m:
            while m % d == 0: fs.add(d); m //= d
            d += 1
        if m > 1: fs.add(m)
        return fs

    def inv(self, x):
        x %= self.p
        r = self._inv.get(x)
        if r is None:
            r = pow(x, self.p-2, self.p); self._inv[x] = r
        return r

    def interp_evals(self, pts_x, pts_y):
        """Newton interpolation through k points, evaluated at all n domain points."""
        p, k = self.p, len(pts_x)
        coef = list(pts_y)
        for j in range(1, k):
            for i in range(k-1, j-1, -1):
                coef[i] = (coef[i]-coef[i-1]) * self.inv(pts_x[i]-pts_x[i-j]) % p
        out = []
        for x in self.xs:
            acc = coef[-1]
            for i in range(k-2, -1, -1):
                acc = (acc*(x-pts_x[i]) + coef[i]) % p
            out.append(acc)
        return out

    def row_codeword_on(self, row, S):
        """Does SOME codeword agree with `row` on ALL of S (|S| >= k)? Return evals or None."""
        Sl = sorted(S)
        T = Sl[:self.k]
        ev = self.interp_evals([self.xs[i] for i in T], [row[i] for i in T])
        for j in Sl[self.k:]:
            if ev[j] != row[j]: return None
        return tuple(ev)

class StackAnalysis:
    """Exact CA/MCA analysis of one stack for all agreement thresholds a."""
    def __init__(self, kit, u0, u1):
        self.kit, self.u0, self.u1 = kit, tuple(u0), tuple(u1)
        p, n, k = kit.p, kit.n, kit.k
        self.tables = []      # per T: (base frozenset, {gamma: [j...]})
        self.maxbase = 0
        for T in kit.Ts:
            A = kit.interp_evals([kit.xs[i] for i in T], [u0[i] for i in T])
            B = kit.interp_evals([kit.xs[i] for i in T], [u1[i] for i in T])
            base = set(T); crit = defaultdict(list)
            for j in range(n):
                if j in base: continue
                dB = (B[j]-u1[j]) % p
                dA = (u0[j]-A[j]) % p
                if dB == 0:
                    if dA == 0: base.add(j)      # always-agree point
                else:
                    crit[dA * kit.inv(dB) % p].append(j)
            self.tables.append((frozenset(base), dict(crit)))
            if len(base) > self.maxbase: self.maxbase = len(base)
        self._rowmemo = {}

    def joint_on(self, S):
        """pairJointAgreesOn(S): both rows individually codeword-explained on S."""
        r = self._rowmemo.get(S)
        if r is None:
            r = (self.kit.row_codeword_on(self.u0, S) is not None
                 and self.kit.row_codeword_on(self.u1, S) is not None)
            self._rowmemo[S] = r
        return r

    def analyze(self, a):
        """Exact bad sets at agreement threshold a.  Returns dict of results."""
        joint = self.maxbase >= a           # jointProximity at delta=(n-a)/n
        CA = set(); MCA = set()
        witnesses = defaultdict(set)        # gamma -> set of S_w that qualify (fire or not)
        fired = defaultdict(set)            # gamma -> set of S_w that FIRE
        seen = set()
        for base, crit in self.tables:
            lb = len(base)
            for g, js in crit.items():
                if lb + len(js) >= a:
                    CA.add(g)
                    Sw = frozenset(base | set(js))
                    key = (g, Sw)
                    if key in seen: continue
                    seen.add(key)
                    witnesses[g].add(Sw)
                    if not self.joint_on(Sw):
                        MCA.add(g); fired[g].add(Sw)
        return dict(joint=joint, CA=CA, MCA=MCA, witnesses=witnesses, fired=fired)

    def witness_word(self, g, Sw):
        """The unique codeword agreeing with the line at gamma=g on Sw, as eval tuple."""
        p = self.kit.p
        y = [(self.u0[i] + g*self.u1[i]) % p for i in range(self.kit.n)]
        return self.kit.row_codeword_on(y, Sw)

# ---------------------------------------------------------------- brute-force validator
def brute_force(kit, u0, u1, a):
    """Independent per-gamma list-decode over ALL of F_p (slow; n=8 only)."""
    p, n, k = kit.p, kit.n, kit.k
    ana = StackAnalysis(kit, u0, u1)   # only for joint_on memo reuse
    CA, MCA = set(), set()
    for g in range(p):
        y = [(u0[i] + g*u1[i]) % p for i in range(n)]
        words = {}
        for T in kit.Ts:
            ev = kit.interp_evals([kit.xs[i] for i in T], [y[i] for i in T])
            S = frozenset(j for j in range(n) if ev[j] == y[j])
            if len(S) >= a: words[S] = ev
        if words: CA.add(g)
        for S in words:
            if not ana.joint_on(S): MCA.add(g); break
    return CA, MCA

# ---------------------------------------------------------------- stack families
def random_stack(kit):
    p, n = kit.p, kit.n
    return ([random.randrange(p) for _ in range(n)],
            [random.randrange(p) for _ in range(n)])

def monomial_stack(kit, j0, j1):
    return ([pow(x, j0, kit.p) for x in kit.xs], [pow(x, j1, kit.p) for x in kit.xs])

def sparse_random_stack(kit, e):
    """double support of size e, random values (rows vanish on n-e >= a points)."""
    p, n = kit.p, kit.n
    E = random.sample(range(n), e)
    u0, u1 = [0]*n, [0]*n
    for i in E:
        u0[i] = random.randrange(1, p); u1[i] = random.randrange(1, p)
    return u0, u1, sorted(E)

def sparse_designed_stack(kit, e):
    """double support, all ratios -u0_i/u1_i distinct => >= e zero-witness fires predicted."""
    p, n = kit.p, kit.n
    E = random.sample(range(n), e)
    ratios = random.sample(range(1, p), e)
    u0, u1 = [0]*n, [0]*n
    for i, r in zip(E, ratios):
        u1[i] = random.randrange(1, p)
        u0[i] = (p - r) * u1[i] % p       # fire at gamma = -u0_i/u1_i = r
    return u0, u1, sorted(E)

def sparse_monomial_stack(kit, e, j0, j1):
    """structured sparse: monomial values restricted to a support window."""
    n = kit.n
    E = list(range(n-e, n))
    u0, u1 = [0]*n, [0]*n
    for i in E:
        u0[i] = pow(kit.xs[i], j0, kit.p); u1[i] = pow(kit.xs[i], j1, kit.p)
    return u0, u1, E

# ---------------------------------------------------------------- per-config driver
def classify_gap(ana, res, sample=3):
    """For CA-bad-not-MCA-bad scalars: are all witnesses explained by ONE global pair?"""
    out = []
    gaps = sorted(res['CA'] - res['MCA'])
    for g in gaps[:sample]:
        Ws = sorted(res['witnesses'][g], key=len, reverse=True)
        pairs = set()
        for S in Ws:
            v0 = ana.kit.row_codeword_on(ana.u0, S)
            v1 = ana.kit.row_codeword_on(ana.u1, S)
            pairs.add((v0, v1))
        out.append((g, len(Ws), len(pairs)))
    return len(gaps), out

def excess_fires(ana, res, vstar):
    """Fires whose witness word differs from the joint explainer line v0*+g*v1*.
    vstar=(v0evals,v1evals) or None.  Returns (n_zero_type, n_excess, excess_gammas)."""
    p = ana.kit.p
    nz, ne, eg = 0, 0, []
    for g, Ss in res['fired'].items():
        is_excess = False
        for S in Ss:
            w = ana.witness_word(g, S)
            if vstar is None:
                base = None
            else:
                base = tuple((vstar[0][j] + g*vstar[1][j]) % p for j in range(ana.kit.n))
            if w != base:
                is_excess = True
        if is_excess: ne += 1; eg.append(g)
        else: nz += 1
    return nz, ne, sorted(eg)

def run_config(p, n, k, a_list, fast=False):
    kit = Kit(p, n, k)
    e_of = {a: n - a for a in a_list}
    m = (p-1)//n
    log(f"\n=== n={n} k={k} p={p} (m=(p-1)/n={m}, proper={n < p-1})  a in {a_list} "
        f"(e=n-a: { {a: e_of[a] for a in a_list} }) ===")
    # UDR / window landmarks
    d = n - k + 1
    log(f"    rate rho={k}/{n}; Johnson agreement sqrt(kn)={ (k*n)**0.5 :.2f}; "
        f"UDR needs a >= {n - (d-1)//2} (d={d});  window-interior a: {k+1}..{int((k*n)**0.5)}")

    results = defaultdict(list)   # (family, a) -> list of dict
    t0 = time.time()

    def handle(name, u0, u1, vstar=None, note=""):
        ana = StackAnalysis(kit, u0, u1)
        for a in a_list:
            res = ana.analyze(a)
            ca = p if res['joint'] else len(res['CA'])
            mca = len(res['MCA'])
            assert res['MCA'] <= res['CA'] or res['joint']
            ngap, gapinfo = classify_gap(ana, res)
            nz = nex = 0; eg = []
            if res['joint']:
                nz, nex, eg = excess_fires(ana, res, vstar)
            results[(name, a)].append(dict(joint=res['joint'], ca=ca, mca=mca,
                    ca_crit=len(res['CA']), gap=ngap, gapinfo=gapinfo,
                    zero_fires=nz, excess_fires=nex, excess_g=eg, note=note))
        return ana

    # --- family 1: random dense stacks
    R = 6 if fast else (10 if (n == 16 and min(a_list) <= 5) else 40)
    for _ in range(R):
        u0, u1 = random_stack(kit)
        handle("random", u0, u1)

    # --- family 2: monomial stacks (the take-over/KKH26-adjacent structured adversary)
    js = [j for j in range(k, n)]
    pairs = [(j0, j1) for j0 in js for j1 in js if j0 < j1] if (n == 16) else \
            [(j0, j1) for j0 in js for j1 in js if j0 != j1]
    if fast: pairs = pairs[:12]
    for j0, j1 in pairs:
        note = "CORRELATED-X^(n/2)" if (j0 == n//2 or j1 == n//2) else ""
        u0, u1 = monomial_stack(kit, j0, j1)
        ana = handle(f"monomial", u0, u1, note=note)
        # record identity for extremes
        results[("monomial_ids", 0)].append((j0, j1, note))

    # --- family 3: sparse stacks (JOINT: the actual B4 obstruction channel), per a
    for a in a_list:
        e = e_of[a]
        if e < 1: continue
        Rs = 4 if fast else (10 if (n == 16 and a <= 5) else 30)
        vstar = ([0]*n, [0]*n)
        for _ in range(Rs):
            u0, u1, E = sparse_random_stack(kit, e)
            ana = StackAnalysis(kit, u0, u1)
            res = ana.analyze(a)
            assert res['joint'], "sparse stack must be jointly close"
            nz, nex, eg = excess_fires(ana, res, vstar)
            results[("sparse_random", a)].append(dict(joint=True, ca=p, mca=len(res['MCA']),
                    ca_crit=len(res['CA']), gap=p-len(res['MCA']), gapinfo=[],
                    zero_fires=nz, excess_fires=nex, excess_g=eg, note=f"|E|={e}"))
        for _ in range(Rs):
            u0, u1, E = sparse_designed_stack(kit, e)
            ana = StackAnalysis(kit, u0, u1)
            res = ana.analyze(a)
            nz, nex, eg = excess_fires(ana, res, vstar)
            mca = len(res['MCA'])
            assert mca >= min(e, p), f"designed sparse stack must have >= e fires, got {mca} < {e}"
            results[("sparse_designed", a)].append(dict(joint=True, ca=p, mca=mca,
                    ca_crit=len(res['CA']), gap=p-mca, gapinfo=[],
                    zero_fires=nz, excess_fires=nex, excess_g=eg, note=f"|E|={e}"))
        # structured sparse monomial
        for (j0, j1) in [(k, k+1), (n-1, n-2), (n//2, k)][: (1 if fast else 3)]:
            u0, u1, E = sparse_monomial_stack(kit, e, j0, j1)
            if all(v == 0 for v in u0) or all(v == 0 for v in u1): continue
            ana = StackAnalysis(kit, u0, u1)
            res = ana.analyze(a)
            nz, nex, eg = excess_fires(ana, res, vstar)
            results[("sparse_monomial", a)].append(dict(joint=res['joint'], ca=p,
                    mca=len(res['MCA']), ca_crit=len(res['CA']), gap=p-len(res['MCA']),
                    gapinfo=[], zero_fires=nz, excess_fires=nex, excess_g=eg,
                    note=f"X^{j0},X^{j1}|E|={e}"))

    # --- family 4: hill-climb sparse for MAX MCA (the B4 quantity J(n,k,a)), per a
    for a in a_list:
        e = e_of[a]
        if e < 1: continue
        steps = 0 if (n == 16 and a <= 5 and not fast) else (30 if fast else 150)
        u0, u1, E = sparse_designed_stack(kit, e)
        best = StackAnalysis(kit, u0, u1).analyze(a)
        bmca, bu0, bu1 = len(best['MCA']), u0[:], u1[:]
        for _ in range(steps):
            v0, v1 = bu0[:], bu1[:]
            i = random.choice(E)
            v0[i] = random.randrange(1, p); v1[i] = random.randrange(1, p)
            r = StackAnalysis(kit, v0, v1).analyze(a)
            if len(r['MCA']) > bmca:
                bmca, bu0, bu1 = len(r['MCA']), v0, v1
        ana = StackAnalysis(kit, bu0, bu1)
        res = ana.analyze(a)
        nz, nex, eg = excess_fires(ana, res, ([0]*n, [0]*n))
        results[("sparse_climb", a)].append(dict(joint=True, ca=p, mca=bmca,
                ca_crit=len(res['CA']), gap=p-bmca, gapinfo=[],
                zero_fires=nz, excess_fires=nex, excess_g=eg, note=f"|E|={e} steps={steps}"))

    # --- brute-force cross-validation (n=8 only): independent per-gamma list decode
    if n == 8 and not fast:
        log("    [validate] brute-force per-gamma cross-check (independent algorithm):")
        for label, mk in [("random", lambda: random_stack(kit)),
                          ("sparse", lambda: sparse_designed_stack(kit, n - a_list[0])[:2])]:
            u0, u1 = mk()
            ana = StackAnalysis(kit, u0, u1)
            for a in a_list[:2]:
                res = ana.analyze(a)
                bCA, bMCA = brute_force(kit, u0, u1, a)
                fastCA = set(range(p)) if res['joint'] else res['CA']
                okCA = (fastCA == bCA); okMCA = (res['MCA'] == bMCA)
                log(f"      {label} a={a}: CA fast={'ALL' if res['joint'] else len(res['CA'])} "
                    f"brute={len(bCA)} match={okCA} | MCA fast={len(res['MCA'])} "
                    f"brute={len(bMCA)} match={okMCA}")
                assert okCA and okMCA, "ENUMERATION BUG: fast path disagrees with brute force"

    # ------------------------------------------------------------ report
    for a in a_list:
        e = e_of[a]
        log(f"\n  --- a={a} (delta={n-a}/{n}, e={e}) ---")
        # non-joint reference: worst CA among non-joint stacks (the epsCA side)
        best_ca_nj, best_mca_nj, worst_gap = 0, 0, (0, None)
        for (fam, aa), lst in results.items():
            if aa != a or fam.startswith("sparse"): continue
            for r in lst:
                if isinstance(r, tuple) or r['joint']: continue
                best_ca_nj = max(best_ca_nj, r['ca'])
                best_mca_nj = max(best_mca_nj, r['mca'])
                if r['gap'] > worst_gap[0]: worst_gap = (r['gap'], r)
        # joint side: the B4 quantity
        J, Jrec = 0, None
        tot_excess = 0; any_excess = []
        for (fam, aa), lst in results.items():
            if aa != a: continue
            for r in lst:
                if isinstance(r, tuple) or not (isinstance(r, dict) and r.get('joint')): continue
                if r['mca'] > J: J, Jrec = r['mca'], (fam, r)
                if r.get('excess_fires', 0) > 0:
                    tot_excess += 1; any_excess.append((fam, r['excess_fires'], r['note']))
        log(f"    NON-JOINT stacks: max #CA-bad = {best_ca_nj}, max #MCA-bad = {best_mca_nj} "
            f"(per-gamma MCA subset-of CA verified on every stack)")
        if worst_gap[1] is not None:
            r = worst_gap[1]
            log(f"    largest CA-minus-MCA gap on a non-joint stack: {r['gap']} "
                f"(ca={r['ca']}, mca={r['mca']}); gap-scalar structure (g, #witnessSets, "
                f"#distinct explaining pairs): {r['gapinfo']}")
        log(f"    JOINT stacks (B4 channel; epsCA body = 0 here): "
            f"max #MCA-bad J = {J}  vs  e = {e}  vs  non-joint max CA = {best_ca_nj}")
        if Jrec: log(f"      attained by family={Jrec[0]} note={Jrec[1]['note']} "
                     f"zero-type fires={Jrec[1]['zero_fires']} excess fires={Jrec[1]['excess_fires']}")
        if any_excess:
            log(f"      EXCESS (nonzero-witness) fires seen on {tot_excess} joint stacks: "
                f"{any_excess[:6]}")
        else:
            log(f"      NO excess (nonzero-witness) fires found on any joint stack at a={a}")
        # per-family summary
        for fam in ("random", "monomial", "sparse_random", "sparse_designed",
                    "sparse_monomial", "sparse_climb"):
            lst = [r for r in results.get((fam, a), []) if isinstance(r, dict)]
            if not lst: continue
            cas = [r['ca'] for r in lst if not r['joint']]
            mcas = [r['mca'] for r in lst]
            jn = sum(1 for r in lst if r['joint'])
            log(f"      {fam:16s} N={len(lst):3d} joint={jn:3d} "
                f"CA(nonjoint) max={max(cas) if cas else '-'} "
                f"MCA max={max(mcas)} mean={sum(mcas)/len(mcas):.2f}")
        # monomial extremes
        mono = [(r, mid) for r, mid in zip(results.get(("monomial", a), []),
                results.get(("monomial_ids", 0), [])) if isinstance(r, dict)]
        mono.sort(key=lambda t: -(t[0]['mca']))
        if mono:
            top = [(mid, r['ca'] if not r['joint'] else 'ALL', r['mca'], r['gap'])
                   for r, mid in mono[:5]]
            log(f"      monomial top-5 by MCA [(j0,j1,flag), CA, MCA, gap]: {top}")
    log(f"    [config time {time.time()-t0:.1f}s]")
    return results

# ---------------------------------------------------------------- main
def main():
    fast = "--fast" in sys.argv
    log("#466 W3/B4 probe: CA vs MCA bad-scalar counts at lines, exact, window-interior a")
    log(f"fast={fast}")

    all_res = {}
    # n=8, k=2 (rho=1/4): interior a=3; a=4 Johnson edge; a=5 below-Johnson (toward UDR a>=5)
    for p in find_primes(8, 2):
        all_res[(8, 2, p)] = run_config(p, 8, 2, [3, 4, 5], fast)
    # n=8, k=3 (rho=3/8): interior a=4; a=5 below-Johnson
    for p in find_primes(8, 2):
        all_res[(8, 3, p)] = run_config(p, 8, 3, [4, 5], fast)
    # n=16, k=4 (rho=1/4): interior a in {5,6,7}
    for p in find_primes(16, 2):
        all_res[(16, 4, p)] = run_config(p, 16, 4, [5, 6, 7], fast)

    log("\n=== O147 cross-check: take-over stack (X^9, X^8) on mu_16, k=4, a=7 ===")
    p = find_primes(16, 1)[0]
    kit = Kit(p, 16, 4)
    u0, u1 = monomial_stack(kit, 9, 8)
    ana = StackAnalysis(kit, u0, u1)
    res = ana.analyze(7)
    log(f"    joint={res['joint']} (O147: parity-class witnesses make the stack jointly "
        f"explainable)  #critical-CA={len(res['CA'])}  #MCA={len(res['MCA'])} "
        f"[X^8 = X^(n/2): CORRELATED direction, flagged]")

    with open("scripts/probes/_out_466_ca_vs_mca.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")
    log("\nwritten: scripts/probes/_out_466_ca_vs_mca.txt")

if __name__ == "__main__":
    main()
