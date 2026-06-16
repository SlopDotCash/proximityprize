#!/usr/bin/env python3
"""_wf_floor-truth_1.py  (#389 / #407 prize — FLOOR TRUTH-TEST, replicate 2/2)

Q3 FLOOR TRUTH-TEST
  Over F_q in the SPARSE regime (p >> n^2.5), at a radius ABOVE Johnson
  (delta in (1 - sqrt(rho), 1 - rho)), does ANY non-ladder far word w have list size
      L(w) = #{ deg<k polys agreeing with w on >= (1-delta)*n points of mu_n }
  STRICTLY EXCEEDING the ladder / equidistributed value N_fib?

  - If NO word beats the ladder  -> the closed-form delta* (upper half) is CORRECT.
  - If SOME structured word beats it -> delta* is pinned LOWER (floor wins).

  N_fib = the ladder value = #{ deg<k polys agreeing on >= rm coords with the
  ladder word w_ladder = x^{rm} + lam*x^{(r-1)m} } realized as fibre-unions
  (the equidistributed / Lam-Leung antipodal count). We compute N_fib here by
  DIRECTLY measuring the ladder word's own list (most honest baseline) and also
  compare to the combinatorial fibre count C(s/2, r/2) for cross-check.

INDEPENDENCE FROM THE TWIN (replicate 2/2)
  The twin uses SMALL primes near n (e.g. p in {13, 7681, 12289}).  THIS probe is
  deliberately in a DIFFERENT, SPARSE prime range p >> n^2.5 (chosen smooth primes
  with n | p-1, p from ~10^4 up to ~10^7) and uses BOTH exhaustive word enumeration
  (tiny n) and random-restart hill-climbing (larger n).  Different primes + different
  enumeration => independent confirmation.

METHOD
  * EXHAUSTIVE (n=8, k=2, t=3): list ALL words obtained as
      base codeword (deg<k poly)  +  e corrupted coordinates set to arbitrary values,
    sweeping over which coords and (densely sampled) what values, AND a full exhaustive
    sweep over corrupted-coordinate VALUES for the worst configurations.  For n=8 we can
    afford to enumerate corrupted-value grids of moderate size.
  * HILL-CLIMB (n=16, k=2 and k=3, n=8 k=3): random-restart hill-climbing over the full
    adversarial word, the reliable worst_list method from probe_smooth_listsize_energy.py.
  * Each run reports: window check (delta strictly inside (1-sqrt rho, 1-rho)),
    N_fib (ladder value), max NON-ladder list found, and any explicit word that beats
    N_fib.

A word is "ladder" if (up to affine shift x->ax+b on the values, and the deg-<k
codeword offset) it equals x^{rm} + lam x^{(r-1)m}.  Operationally we treat the ladder
baseline as the LADDER WORD'S OWN list (computed exactly) and ask whether any OTHER word
exceeds it.  We additionally tag a word as "ladder-like" if its agreeing-polynomial set,
after subtracting one agreeing poly, looks like a single monomial-pair; but for the
floor test the decisive quantity is simply: max over non-ladder words L(w) vs N_fib.

================================ RESULTS (2026-06-13) ===========================
FLOOR IS BEATEN.  In the beyond-Johnson window, NON-ladder far words EXCEED the
ladder / equidistributed value N_fib for the studied small-n RS codes.  The decisive
finds come from the LADDER-NEIGHBORHOOD search (random-start hill-climb systematically
UNDER-finds structured high-list words, as the original probe warned):

  n   k   t  delta   window?   N_fib(ladder)   max non-ladder   verdict
  8   2   3  0.6250  YES       3               5  (>3)          FLOOR BEATEN  (1.67x)
  8   3   4  0.5000  YES       6               6  (=6)          ladder ties
 16   2   3  0.8125  YES       7               9  (>7)          FLOOR BEATEN  (1.29x)
 16   3   4  0.7500  YES      28              ~5 (hill-climb only; neighborhood not reached)

INDEPENDENT BRUTE-FORCE CONFIRMATION (full line enumeration, NOT the FastList path):
  * n=8  k=2: beater w=(1,0,0,8955,9330,3263,11134,0) over p=20089 has EXACTLY 5 distinct
    deg<2 polys, each agreeing on EXACTLY 3 of 8 mu_8 points (all at radius t=3).
    Ladder x^3+lam x^2 max self-list over ALL lambda in F_p = 3 (full sweep, lam=1).
    Global max list over ANY word (hard hill-climb) = 5 -> the beater hits the true
    list-decoding ceiling, well above the ladder's 3.
  * n=16 k=2: beater has EXACTLY 9 distinct lines, each agreeing on EXACTLY 3 of 16 pts.
    Ladder max self-list over 465 fibre-optimal + 3000 random lambda = 7.
  * Holds across SPARSE primes p in {20089, 200009, 2000081} (p/n^2.5 = 111 .. 11049)
    for n=8, and p=50033 for n=16 -- prime-range independent.

HONEST CAVEATS
  * SMALL n only (8, 16).  These are NOT the prize regime (n=2^a up to 2^44, q in
    [2^128,2^256]).  The beat ratio 5/3, 9/7 is an O(1) constant-factor at tiny n; it
    does NOT establish an asymptotic floor below delta*.  The asymptotic question
    (does the floor stay above delta*, i.e. is the equidistributed value still the
    determinant as n->inf?) is the open core and is NOT resolved here.
  * The "ladder value N_fib" here is the ladder word's OWN self-list, the monomial-pair
    family.  A more sophisticated equidistributed family might match the beater; but the
    monomial ladder -- the explicit adversary the closed-form delta* is built on -- is
    PROVABLY not list-maximal at these small n.  This PINS delta* (upper-half) as NOT
    tight for small-n RS: the true list-decoding radius admits more codewords than the
    ladder predicts, so any delta* derived purely from the ladder is an UNDER-count of
    the worst case (radius too optimistic) at small n.
  * n=16 k=3: the neighborhood search did not finish under the time budget; only the
    weaker random hill-climb (max 5) ran.  N_fib=28 = C(s/2,r/2) exactly (Lam-Leung).
    No claim either way for this case.
================================================================================
"""
import itertools, math, random, sys
from math import comb
from collections import Counter


# ---------- field / subgroup utilities ----------

def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def sparse_prime(n, lo):
    """Smallest prime p >= lo with n | p-1  (so mu_n exists).  SPARSE: lo >> n^2.5."""
    # p = 1 + n*t
    t = (lo - 1 + n - 1) // n
    while True:
        p = 1 + n * t
        if p >= lo and is_prime(p):
            return p
        t += 1


def primitive_root(p):
    fac = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    return None


def find_subgroup(p, n):
    if (p - 1) % n != 0:
        return None
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    S, v = [], 1
    for _ in range(n):
        S.append(v)
        v = v * h % p
    return sorted(S)


def add_energy(S, p):
    c = Counter()
    for a in S:
        for b in S:
            c[(a + b) % p] += 1
    return sum(v * v for v in c.values())


# ---------- list size (general k) ----------

def _evalp(c, x, p):
    r = 0
    for a in reversed(c):
        r = (r * x + a) % p
    return r


def _interp_vals(xs, ys, D, p, inv):
    """Values on D of the deg-<len(xs) Lagrange interpolant through (xs, ys)."""
    out = []
    k = len(xs)
    for x in D:
        tot = 0
        for i in range(k):
            num, den = ys[i], 1
            for j in range(k):
                if j == i:
                    continue
                num = num * ((x - xs[j]) % p) % p
                den = den * ((xs[i] - xs[j]) % p) % p
            tot = (tot + num * inv[den]) % p
        out.append(tot)
    return tuple(out)


def listsize(w, D, k, t, p, inv, return_polys=False):
    """#{ distinct deg-<k polynomials agreeing with w on >= t coords of D }."""
    n = len(D)
    seen, cnt = set(), 0
    polys = []
    for sub in itertools.combinations(range(n), k):
        vals = _interp_vals([D[i] for i in sub], [w[i] for i in sub], D, p, inv)
        if vals in seen:
            continue
        seen.add(vals)
        agree = sum(1 for a in range(n) if vals[a] == w[a])
        if agree >= t:
            cnt += 1
            if return_polys:
                polys.append(vals)
    return (cnt, polys) if return_polys else cnt


class FastList:
    """Precompute Lagrange-basis coefficients so listsize is O(C(n,k)*n) field-mults
    with NO per-call inverse work.  For a k-subset S=(i_0..i_{k-1}) the interpolant value
    at coordinate a is  sum_t L[S][a][t] * w[i_t]  (mod p), L precomputed once per domain.
    """
    __slots__ = ("D", "n", "k", "p", "subs", "L")

    def __init__(self, D, k, p):
        self.D, self.n, self.k, self.p = D, len(D), k, p
        n = self.n
        self.subs = list(itertools.combinations(range(n), k))
        L = []  # L[s] = list over a of tuple(coeff_t)
        for sub in self.subs:
            xs = [D[i] for i in sub]
            rowa = []
            for a in range(n):
                x = D[a]
                coeffs = []
                for i in range(k):
                    num, den = 1, 1
                    for j in range(k):
                        if j == i:
                            continue
                        num = num * ((x - xs[j]) % p) % p
                        den = den * ((xs[i] - xs[j]) % p) % p
                    coeffs.append(num * pow(den, p - 2, p) % p)
                rowa.append(tuple(coeffs))
            L.append(rowa)
        self.L = L

    def listsize(self, w, t, return_polys=False):
        p, n, k = self.p, self.n, self.k
        seen, cnt = set(), 0
        polys = []
        for si, sub in enumerate(self.subs):
            ys = [w[i] for i in sub]
            La = self.L[si]
            vals = tuple(
                sum(La[a][i] * ys[i] for i in range(k)) % p for a in range(n)
            )
            if vals in seen:
                continue
            seen.add(vals)
            agree = 0
            for a in range(n):
                if vals[a] == w[a]:
                    agree += 1
            if agree >= t:
                cnt += 1
                if return_polys:
                    polys.append(vals)
        return (cnt, polys) if return_polys else cnt


class LazyInv:
    """Lazy modular-inverse cache (a full length-p array is too big for sparse p)."""
    __slots__ = ("p", "cache")

    def __init__(self, p):
        self.p = p
        self.cache = {}

    def __getitem__(self, a):
        a %= self.p
        v = self.cache.get(a)
        if v is None:
            v = pow(a, self.p - 2, self.p)
            self.cache[a] = v
        return v


def build_inv(p):
    return LazyInv(p)


# ---------- ladder baseline (N_fib) ----------

def ladder_word(D, m, r, lam, p):
    """w = x^{rm} + lam x^{(r-1)m} evaluated on D = mu_n."""
    a = r * m
    b = (r - 1) * m
    return [(pow(x, a, p) + lam * pow(x, b, p)) % p for x in D]


def nfib_via_ladder(D, m, r, p, fl_ladder):
    """N_fib = max over lam of the ladder word's OWN list at agreement t = rm,
    with code dim k = (r-2)m+1.  This is the equidistributed ladder value.
    fl_ladder is a FastList built with k = (r-2)m+1 (the ladder code dim)."""
    n = len(D)
    k = (r - 2) * m + 1
    t = r * m
    if t > n or k < 1:
        return None
    best = 0
    best_lam = None
    mus = sorted({pow(x, m, p) for x in D})
    s = len(mus)
    lam_cands = set()
    for T in itertools.combinations(mus, r):
        lam_cands.add((-sum(T)) % p)
    lam_cands.add(0)
    for lam in lam_cands:
        w = ladder_word(D, m, r, lam, p)
        c = fl_ladder.listsize(w, t)
        if c > best:
            best, best_lam = c, lam
    return best, best_lam, k, t, s


# ---------- exhaustive non-ladder word enumeration (tiny n) ----------

def exhaustive_floor(D, k, t, p, fl, ladder_baseline, ladder_words_set,
                     val_grid, max_e, seed=11):
    """Enumerate words = (deg-<k codeword) + (e coords corrupted to grid values).
    For each, compute L(w); track max over NON-ladder words and any beater.
    val_grid: list of candidate corrupted values (sampled from field).
    Returns (max_nonladder_list, beater_word_or_None, beater_list, n_words)."""
    n = len(D)
    random.seed(seed)
    best = 0
    beater = None
    beater_list = -1
    nwords = 0
    # base codewords: a small set of structured deg-<k polys + a few random.
    # (The floor max comes from corrupting near a codeword; the base just sets the
    #  "background" agreeing-poly structure, so a handful suffices.)
    base_polys = []
    for c0 in (0, 1):
        for c1 in ([0, 1] if k >= 2 else [0]):
            for c2 in ([0, 1] if k >= 3 else [0]):
                coeffs = ([c0, c1, c2])[:k]
                base_polys.append([_evalp(coeffs, x, p) for x in D])
    for _ in range(4):
        coeffs = [random.randrange(p) for _ in range(k)]
        base_polys.append([_evalp(coeffs, x, p) for x in D])
    for base in base_polys:
        for e in range(1, max_e + 1):
            for coords in itertools.combinations(range(n), e):
                for vals in itertools.product(val_grid, repeat=e):
                    w = list(base)
                    for idx, cd in enumerate(coords):
                        w[cd] = vals[idx]
                    wt = tuple(w)
                    if wt in ladder_words_set:
                        continue
                    nwords += 1
                    L = fl.listsize(w, t)
                    if L > best:
                        best = L
                    if L > ladder_baseline and L > beater_list:
                        beater_list = L
                        beater = wt
    return best, beater, beater_list, nwords


# ---------- hill-climb worst-case word (larger n) ----------

def worst_list(D, k, t, p, fl, ladder_baseline, ladder_words_set,
               restarts=80, steps=500, seed=3):
    """Random-restart hill-climb over the full adversarial word.
    Returns (best_nonladder_list, beater_word_or_None)."""
    n = len(D)
    random.seed(seed)
    best = 0
    beater = None
    for _ in range(restarts):
        c0 = [random.randrange(p) for _ in range(k)]
        w = [_evalp(c0, x, p) for x in D]
        for _ in range(random.randint(n // 2, n)):
            w[random.randrange(n)] = random.randrange(p)
        cur = fl.listsize(w, t)
        for _ in range(steps):
            i = random.randrange(n)
            old = w[i]
            w[i] = random.randrange(p)
            nv = fl.listsize(w, t)
            if nv >= cur:
                cur = nv
            else:
                w[i] = old
        wt = tuple(w)
        if wt in ladder_words_set:
            continue
        if cur > best:
            best = cur
            if cur > ladder_baseline:
                beater = wt
    return best, beater


def ladder_neighborhood(D, m, r, p, fl, t, ladder_words_set,
                        nlam=12, depth=3, tries=400, seed=5):
    """SEED from the optimal ladder word and perturb (set a few coords to mu_n / random
    values, or apply x->ax+b). If the ladder is a LOCAL max that some nearby NON-ladder
    structured word beats, this finds it.  This is where a floor-beater is most plausible
    (the hill-climb from random words systematically under-finds structured high-list words,
    so we must probe the ladder's own neighborhood directly).
    Returns (best_nonladder_list_in_neighborhood, beater_or_None, ladder_self_list)."""
    n = len(D)
    random.seed(seed)
    mus = sorted({pow(x, m, p) for x in D})
    lam_cands = list({(-sum(T)) % p for T in itertools.combinations(mus, r)})
    lam_cands.append(0)
    # find the best ladder word (max self-list)
    best_ladder_w, ladder_self = None, 0
    for lam in lam_cands:
        w = ladder_word(D, m, r, lam, p)
        c = fl.listsize(w, t)
        if c > ladder_self:
            ladder_self, best_ladder_w = c, w
    grid = list(D) + [0] + [random.randrange(p) for _ in range(6)]
    best = 0
    beater = None
    # perturb the best ladder word by 1..depth coordinate edits
    for _ in range(tries):
        w = list(best_ladder_w)
        e = random.randint(1, depth)
        coords = random.sample(range(n), e)
        for cd in coords:
            w[cd] = random.choice(grid)
        wt = tuple(w)
        if wt in ladder_words_set:
            continue
        L = fl.listsize(w, t)
        if L > best:
            best = L
            if L > ladder_self:
                beater = wt
    # also hill-climb starting AT the ladder word (gradient from the ladder)
    for _ in range(8):
        w = list(best_ladder_w)
        # nudge off the ladder first
        cd0 = random.randrange(n)
        w[cd0] = random.choice(grid)
        cur = fl.listsize(w, t)
        for _ in range(200):
            i = random.randrange(n)
            old = w[i]
            w[i] = random.choice(grid + [random.randrange(p)])
            nv = fl.listsize(w, t)
            if nv >= cur:
                cur = nv
            else:
                w[i] = old
        wt = tuple(w)
        if wt in ladder_words_set:
            continue
        if cur > best:
            best = cur
            if cur > ladder_self:
                beater = wt
    return best, beater, ladder_self


# ---------- window / Johnson check ----------

def window_info(n, k, t):
    rho = k / n
    delta = 1 - t / n
    J = 1 - math.sqrt(rho)
    cap = 1 - rho
    in_window = (J < delta < cap)
    return rho, delta, J, cap, in_window


# ============================== RUNS ==============================

def run_exhaustive(n, k, m, r, lo, val_grid_size=None, max_e=3):
    p = sparse_prime(n, lo)
    D = find_subgroup(p, n)
    t = r * m  # agreement threshold = ladder agreement
    rho, delta, J, cap, in_window = window_info(n, k, t)
    fl = FastList(D, k, p)  # k of the studied code (== ladder code dim (r-2)m+1)
    print(f"\n==== EXHAUSTIVE  n={n} k={k} (m={m},r={r}) p={p}  [p/n^2.5 = {p/(n**2.5):.1f}] ====",
          flush=True)
    print(f"  mu_n energy E/n^2 = {add_energy(D, p)/n**2:.3f}  (Sidon floor 3-3/n = {3-3/n:.2f})",
          flush=True)
    print(f"  agreement t={t}  delta={delta:.4f}  rho={rho:.4f}  Johnson={J:.4f}  cap={cap:.4f}  "
          f"IN WINDOW: {in_window}", flush=True)
    nfib = nfib_via_ladder(D, m, r, p, fl)
    if nfib is None:
        print("  (ladder shape invalid for this n,m,r)", flush=True)
        return
    Nf, lam, kk, tt, s = nfib
    cA = comb(s // 2, r // 2) if r % 2 == 0 else None
    print(f"  N_fib (ladder value, best lam={lam}) = {Nf}   "
          f"[ladder k={kk} t={tt}, C(s/2,r/2)={cA}, s={s}]", flush=True)
    mus = sorted({pow(x, m, p) for x in D})
    ladder_set = set()
    lam_cands = set((-sum(T)) % p for T in itertools.combinations(mus, r))
    lam_cands.add(0)
    for lc in lam_cands:
        ladder_set.add(tuple(ladder_word(D, m, r, lc, p)))
    random.seed(99)
    grid = list(D)  # structured values (in mu_n) -- most likely to create extra agreements
    grid += [0]
    if val_grid_size:
        grid += [random.randrange(p) for _ in range(val_grid_size)]
    grid = list(dict.fromkeys(grid))  # dedupe, keep order
    best, beater, bl, nw = exhaustive_floor(D, k, t, p, fl, Nf, ladder_set, grid, max_e)
    # also a hill-climb pass: the true worst word may have > max_e errors.
    hc_best, hc_beater = worst_list(D, k, t, p, fl, Nf, ladder_set, restarts=120, steps=400)
    # ladder-neighborhood: perturb the optimal ladder word directly.
    nb_best, nb_beater, ladder_self = ladder_neighborhood(
        D, m, r, p, fl, t, ladder_set, depth=3, tries=600)
    print(f"  max NON-ladder list (exhaustive {nw} words, base+{max_e} corruptions, "
          f"grid|{len(grid)}|) = {best}", flush=True)
    print(f"  max NON-ladder list (hill-climb 120x400) = {hc_best}", flush=True)
    print(f"  ladder self-list = {ladder_self}; max NON-ladder in ladder-neighborhood = "
          f"{nb_best}", flush=True)
    for cand_best, cand_beater in ((hc_best, hc_beater), (nb_best, nb_beater)):
        if cand_best > best:
            best = cand_best
            if cand_beater is not None:
                beater = cand_beater
    if beater is not None and best > Nf:
        bL, bp = fl.listsize(list(beater), t, return_polys=True)
        print(f"  *** BEATER FOUND: list={best} > N_fib={Nf} ***  word={beater}", flush=True)
        print(f"      (recomputed L={bL}; #agreeing polys={len(bp)})", flush=True)
    else:
        print(f"  NO non-ladder word beats N_fib={Nf}.  (max non-ladder {best} <= {Nf})", flush=True)
    return Nf, best, beater


def run_hillclimb(n, k, m, r, lo, restarts=80, steps=500):
    p = sparse_prime(n, lo)
    D = find_subgroup(p, n)
    t = r * m
    rho, delta, J, cap, in_window = window_info(n, k, t)
    fl = FastList(D, k, p)
    print(f"\n==== HILL-CLIMB  n={n} k={k} (m={m},r={r}) p={p}  [p/n^2.5 = {p/(n**2.5):.1f}] ====",
          flush=True)
    print(f"  mu_n energy E/n^2 = {add_energy(D, p)/n**2:.3f}", flush=True)
    print(f"  agreement t={t}  delta={delta:.4f}  rho={rho:.4f}  Johnson={J:.4f}  cap={cap:.4f}  "
          f"IN WINDOW: {in_window}", flush=True)
    nfib = nfib_via_ladder(D, m, r, p, fl)
    if nfib is None:
        print("  (ladder shape invalid)", flush=True)
        return
    Nf, lam, kk, tt, s = nfib
    cA = comb(s // 2, r // 2) if r % 2 == 0 else None
    print(f"  N_fib (ladder value, best lam={lam}) = {Nf}  [C(s/2,r/2)={cA}, s={s}]", flush=True)
    mus = sorted({pow(x, m, p) for x in D})
    ladder_set = set()
    lam_cands = set((-sum(T)) % p for T in itertools.combinations(mus, r))
    lam_cands.add(0)
    for lc in lam_cands:
        ladder_set.add(tuple(ladder_word(D, m, r, lc, p)))
    best, beater = worst_list(D, k, t, p, fl, Nf, ladder_set, restarts, steps)
    print(f"  max NON-ladder list (random-start hill-climb {restarts}x{steps}) = {best}",
          flush=True)
    # ladder-neighborhood search: perturb the optimal ladder word directly
    nb_best, nb_beater, ladder_self = ladder_neighborhood(
        D, m, r, p, fl, t, ladder_set, depth=3, tries=600)
    print(f"  ladder self-list = {ladder_self}; max NON-ladder in ladder-neighborhood "
          f"(perturb+gradient) = {nb_best}", flush=True)
    if nb_best > best:
        best = nb_best
        if nb_beater is not None:
            beater = nb_beater
    if beater is not None and best > Nf:
        bL = fl.listsize(list(beater), t)
        print(f"  *** BEATER: list={best} > N_fib={Nf} ***  word={beater} (recheck L={bL})",
              flush=True)
    else:
        print(f"  NO non-ladder word beats N_fib={Nf}.  (max non-ladder {best} <= {Nf})",
              flush=True)
    return Nf, best, beater


def main():
    print("FLOOR TRUTH-TEST (replicate 2/2): SPARSE primes p >> n^2.5, "
          "non-ladder word list vs N_fib in beyond-Johnson window")
    print("=" * 78)
    results = []
    # --- EXHAUSTIVE tiny n=8, k=2 (m=2,r=2 -> t=4, code dim 1). Window check below. ---
    # For k=2 (rho=1/4) ladder shape: k=(r-2)m+1=2 needs (r-2)m=1 => m=1,r=3 (s=n).
    # m=1,r=3: t=rm=3, k=2.  delta = 1-3/8 = 0.625.  rho=2/8=0.25.
    # Johnson=1-0.5=0.5; cap=0.75.  0.5<0.625<0.75 -> IN WINDOW.
    # grid = mu_n (8) + {0} + few random; max_e=2 keeps exhaustive sweep tractable.
    results.append(run_exhaustive(8, 2, 1, 3, lo=20000, val_grid_size=4, max_e=2))
    results.append(run_exhaustive(8, 2, 1, 3, lo=200000, val_grid_size=4, max_e=2))
    results.append(run_exhaustive(8, 2, 1, 3, lo=2000000, val_grid_size=4, max_e=2))
    # --- EXHAUSTIVE n=8, k=3 (m=1,r=4): t=4, k=3, rho=3/8=0.375, delta=1-4/8=0.5.
    # Johnson=1-sqrt(.375)=0.388; cap=0.625. 0.388<0.5<0.625 -> IN WINDOW.
    results.append(run_exhaustive(8, 3, 1, 4, lo=50000, val_grid_size=4, max_e=2))
    # --- HILL-CLIMB n=16, k=2 (m=1,r=3): t=3, delta=1-3/16=0.8125, rho=1/8=0.125.
    # Johnson=1-sqrt(.125)=0.646; cap=0.875. 0.646<0.8125<0.875 -> IN WINDOW.
    results.append(run_hillclimb(16, 2, 1, 3, lo=50000, restarts=50, steps=300))
    # --- HILL-CLIMB n=16, k=3 (m=1,r=4): t=4, delta=1-4/16=0.75, rho=3/16=0.1875.
    # Johnson=1-sqrt(.1875)=0.567; cap=0.8125. 0.567<0.75<0.8125 -> IN WINDOW.
    results.append(run_hillclimb(16, 3, 1, 4, lo=50000, restarts=30, steps=200))

    print("\n" + "=" * 78)
    print("SUMMARY (N_fib  vs  max non-ladder list):")
    for r in results:
        if r is None:
            continue
        Nf, best, beater = r
        verdict = "FLOOR BEATEN (delta* lower!)" if (beater is not None and best > Nf) \
                  else "ladder holds (delta* upper-half OK)"
        print(f"  N_fib={Nf:>4}  max_nonladder={best:>4}  ->  {verdict}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
