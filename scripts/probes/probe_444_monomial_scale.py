#!/usr/bin/env python3
"""
probe_444_monomial_scale.py  (#444 SEAM A -- Refuter C: monomial base case at SCALE)

TASK: verify (or BREAK) monomial-word window-list CONSTANCY at N=64 and N=128, with
k'=2,3 only (C(128,2)=8128, C(128,3)=341700 feasible), across >=4 primes including a
NON-Fermat / small-v2 prime (m=(p-1)/N ODD => v2(p-1) minimal = mu) and a LARGE prime.
Word = monomial y^j on mu_N, for j in {N/2-1, N/2+1, 3N/4, N-3}.

QUESTION 1: does any monomial list exceed the n=16,32 value (which was <=2)?
QUESTION 2: does it stay constant as eta -> 0 (deeper window)?

Report: max monomial list over all (N, j, prime, eta), and whether it GROWS with N.

NOTE on "non-Fermat prime": mu_N subgroup forces p == 1 (mod N=2^mu) => v2(p-1) >= mu
ALWAYS. The honest analogue of "small v2(p-1)" is m=(p-1)/N ODD (v2 minimal); deep-2adic
is m even. We sample both, plus a large prime (beta high). All proper subgroups (m>=2),
exact arithmetic, never n=p-1.

A monomial list that GROWS with N, or exceeds 2, is a REFUTATION (a win). Do not fabricate.
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

# ---------------------------------------------------------------- prime selection
def primes_for(N, want=4):
    """Return a curated list of dicts {p, m, v2, kind} for proper subgroup mu_N.
       Includes: small-v2 (m odd), deep-v2 (m even, high 2-adic), and a large prime."""
    out = []
    seen = set()

    def add(p, kind):
        if p in seen or not isprime(p):
            return False
        if (p - 1) % N != 0:
            return False
        m = (p - 1) // N
        if m < 2:   # proper subgroup only
            return False
        v2 = bin(p - 1).count('0') if False else _v2(p - 1)
        out.append({'p': p, 'm': m, 'v2': v2, 'kind': kind})
        seen.add(p)
        return True

    def _v2(x):
        c = 0
        while x % 2 == 0:
            x //= 2; c += 1
        return c

    mu = N.bit_length() - 1

    # (1) smallest prime with m ODD (v2(p-1) == mu exactly) -- the "non-Fermat"/small-v2 case
    # p = m*N + 1 with m odd, smallest such prime above ~ small beta.
    m = 3
    while len([o for o in out if o['kind'] == 'small-v2']) < 1:
        p = m * N + 1
        if isprime(p):
            add(p, 'small-v2')
        m += 2
        if m * N + 1 > 10**9:
            break

    # (2) a prime with HIGH 2-adic valuation: m even, ideally m a multiple of a large 2-power
    # search p = m*N+1 with v2(m) maximal among a window
    best = None
    m = 2
    while m * N + 1 < 200000 + (10 * N):
        p = m * N + 1
        if isprime(p):
            vv = _v2(p - 1)
            if best is None or vv > best[1]:
                best = (p, vv)
        m += 1
    if best:
        add(best[0], 'deep-v2')

    # (3) a "prize-shaped" beta~4 prime (smallest p >= N^4, p==1 mod N, m>=2)
    target = int(N ** 4)
    p = target - (target % N) + 1
    while True:
        if p > N and isprime(p) and (p - 1) % N == 0 and (p - 1) // N >= 2:
            add(p, 'beta4')
            break
        p += N

    # (4) a LARGE prime (beta ~ 5)
    target = int(N ** 5)
    p = target - (target % N) + 1
    while True:
        if p > N and isprime(p) and (p - 1) % N == 0 and (p - 1) // N >= 2:
            add(p, 'large-beta5')
            break
        p += N

    # top up with a couple more smallest proper-subgroup primes for redundancy
    m = 2
    while len(out) < want and m * N + 1 < 10**7:
        p = m * N + 1
        if isprime(p):
            add(p, 'aux')
        m += 1

    return out

def subgroup(N, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // N, p)
    elts, x = [], 1
    for _ in range(N):
        elts.append(x); x = (x * zeta) % p
    assert len(set(elts)) == N, "subgroup degenerate"
    return elts

# ---------------------------------------------------------------- interpolation
def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i:
                continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)):
            c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)

def peval(c, x, p):
    r = 0
    for a in reversed(c):
        r = (r * x + a) % p
    return r

def full_list(uvals, elts, k, s, p):
    """all distinct deg<k polys agreeing with u on >= s points of mu_N.
       returns dict {coeffs: agreement_size}. EXACT enumeration over all k-subsets."""
    N = len(elts)
    seen = {}
    for T in itertools.combinations(range(N), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen:
            continue
        ag = 0
        for i in range(N):
            if peval(c, elts[i], p) == uvals[i]:
                ag += 1
        if ag >= s:
            seen[c] = ag
    return seen

# ---------------------------------------------------------------- the experiment
def run(Ns=(64, 128), kps=(2, 3), etas=(0.25, 0.125, 0.0625, 0.03125, 0.0)):
    GLOBAL_MAX = -1
    GLOBAL_MAX_CTX = None
    per_N_max = {}
    # collect (N, kp, j, eta) -> max list over primes, to test growth
    table = {}
    for N in Ns:
        ps = primes_for(N)
        mu = N.bit_length() - 1
        print(f"\n===== N={N} (mu={mu}); primes: " +
              ", ".join(f"{d['p']}(m={d['m']},v2={d['v2']},{d['kind']})" for d in ps) + " =====")
        per_N_max[N] = -1
        # precompute subgroups
        sub = {d['p']: subgroup(N, d['p']) for d in ps}
        for kp in kps:
            csz = comb(N, kp)
            if csz > 3_000_000:
                print(f"  kp={kp}: SKIP C(N,kp)={csz} too large")
                continue
            rho = kp / N
            js = sorted(set([N // 2 - 1, N // 2 + 1, 3 * N // 4, N - 3]))
            js = [j for j in js if 0 < j < N and j != N // 2]  # exclude correlated x^{n/2}
            for j in js:
                for eta in etas:
                    # window threshold: s = round((rho+eta)*N), clamp to [kp+1, N-1]
                    s = round((rho + eta) * N)
                    s = max(s, kp + 1)      # must beat exact codeword (a deg<kp poly hits exactly kp generic; monomial y^j is NOT deg<kp so genuine word)
                    s = min(s, N - 1)
                    row_vals = []
                    for d in ps:
                        p = d['p']; elts = sub[p]
                        uv = [pow(x, j, p) for x in elts]
                        lst = full_list(uv, elts, kp, s, p)
                        L = len(lst)
                        row_vals.append((p, L, d['kind']))
                        if L > GLOBAL_MAX:
                            GLOBAL_MAX = L
                            GLOBAL_MAX_CTX = (N, kp, j, eta, s, p, d['kind'])
                        if L > per_N_max[N]:
                            per_N_max[N] = L
                    maxL = max(v[1] for v in row_vals)
                    table[(N, kp, j, eta)] = maxL
                    flag = "  <-- EXCEEDS 2!" if maxL > 2 else ""
                    print(f"  kp={kp} j={j:3d} (j/N={j/N:.3f}) eta={eta:.4f} s={s:3d}: "
                          f"L over primes = {[v[1] for v in row_vals]} (max {maxL}){flag}")
    # ---- growth analysis: compare matching (kp, j-fraction, eta) across N
    print("\n===== GROWTH ANALYSIS (N=64 vs N=128, matched kp / j-role / eta) =====")
    roles = {'N/2-1': lambda N: N // 2 - 1, 'N/2+1': lambda N: N // 2 + 1,
             '3N/4': lambda N: 3 * N // 4, 'N-3': lambda N: N - 3}
    grew = False
    for kp in kps:
        if comb(128, kp) > 3_000_000:
            continue
        for rname, rf in roles.items():
            for eta in etas:
                a = table.get((64, kp, rf(64), eta))
                b = table.get((128, kp, rf(128), eta))
                if a is None or b is None:
                    continue
                tag = ""
                if b > a:
                    tag = "  GROWS"; grew = True
                elif b < a:
                    tag = "  shrinks"
                print(f"  kp={kp} role={rname:6s} eta={eta:.4f}: N=64 -> {a}, N=128 -> {b}{tag}")
    print(f"\n  any GROWTH 64->128 ? {grew}")
    print(f"  per-N max list: {per_N_max}")
    print(f"\n##### GLOBAL MAX MONOMIAL LIST = {GLOBAL_MAX} at "
          f"(N,kp,j,eta,s,p,kind)={GLOBAL_MAX_CTX} #####")
    print(f"##### exceeds n=16,32 baseline (<=2)? {GLOBAL_MAX > 2} #####")

if __name__ == "__main__":
    run()
