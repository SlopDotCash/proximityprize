#!/usr/bin/env python3
"""
C033 probe (v2): "The char-p transfer of #lacBad (COUNT) and of E_r (ENERGY) are the
IDENTICAL {-1,0,1}-lattice-relation-mod-q question, ONE threshold s*."

v2 fixes: measure the GENUINE relation height = a {-1,0,1} (or signed) relation of
2^mu-th roots that vanishes mod q but NOT in characteristic 0 (i.e. its Z[zeta_n]
value is nonzero).  Trivial char-0 relations (e.g. zeta^0 + zeta^{n/2} = 1 + (-1) = 0)
must be EXCLUDED -- they are not defect carriers.

Exact integer arithmetic over dyadic mu_n of F_q* in the PRIZE regime (n=2^mu PROPER
subgroup, q prime = 1 mod n, multiple primes per n).

Two faces, measured independently:

(I) COUNT face: minimal-support nonzero {-1,0,1}-vector c whose  sum_j c_j zeta^j = 0
    mod q  AND  sum_j c_j zeta_C^j != 0 in C  (genuine char-p relation).  By
    LamLeungAntipodalTightness this is the antipodal-violation source.  We ALSO report
    the minimal non-antipodal subset (the actual #lacBad defect carrier).

(II) ENERGY face: the additive energy E_r^{Fp}(mu_n) = #{2r-tuples in mu_n summing to 0
     mod q}, vs the char-0 / char-p comparison.  The defect = signed 2r-relations that
     vanish mod q beyond the Wick (negation-pairing) collisions.  We report the minimal
     r at which a NON-Wick collision appears mod q (the energy-defect relation length 2r).

We then COMPARE the two minimal relation lengths.  Unification (one s*) requires they
agree (same threshold).  If COUNT defects appear at support s_count while ENERGY needs
2r ~ 2 log q >> s_count, the "one s*" is FALSE (faces share the OBJECT not the SCALE).
"""
import itertools, math, sys
_p = __builtins__.print if hasattr(__builtins__, 'print') else print
def print(*a, **k):
    k.setdefault('flush', True); _p(*a, **k)
from math import comb, log2, log

# ---- char-0 cyclotomic value of a {-1,0,1} (or integer) combo of zeta_n powers ----
# zeta_n primitive n-th root; n=2^mu so minimal poly is X^{n/2}+1 over Q.
# A combo sum_j c_j zeta^j (0<=j<n) reduces mod (X^{n/2}+1): X^{j} for j>=n/2 -> -X^{j-n/2}.
def char0_reduce(coeffs, n):
    """coeffs: list length n of integers. Return reduced coeff vector length n/2
    in basis {1,zeta,...,zeta^{n/2-1}} (since zeta^{n/2}=-1)."""
    half = n//2
    red = [0]*half
    for j, c in enumerate(coeffs):
        if c == 0: continue
        jj = j % n
        sign = 1
        while jj >= half:
            jj -= half; sign = -sign
        red[jj] += sign*c
    return red

def char0_is_zero(coeffs, n):
    return all(v == 0 for v in char0_reduce(coeffs, n))

def factorize(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def isprime(m):
    if m < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m % p == 0: return m == p
    d = m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x%m
            if x==m-1: break
        else: return False
    return True

def primitive_root(q):
    facs = factorize(q-1)
    for g in range(2, q):
        if all(pow(g, (q-1)//p, q) != 1 for p in facs):
            return g
    raise RuntimeError("no primitive root")

def mu_subgroup(q, n):
    assert (q-1) % n == 0
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)
    P = []; x = 1
    for _ in range(n):
        P.append(x); x = (x*h) % q
    assert len(set(P)) == n
    return P

def find_prize_prime(n, beta=4.5):
    target = int(n**beta)
    q = ((target // n) + 1) * n + 1
    for _ in range(500000):
        if isprime(q): return q
        q += n
    return None

def H(rho):
    if rho<=0 or rho>=1: return 0.0
    return -rho*log2(rho)-(1-rho)*log2(1-rho)

# -------- COUNT face: minimal GENUINE {-1,0,1} relation (vanishes mod q, not in C) ----
def min_genuine_pm1_relation(P, q, n, max_s=8):
    """minimal support s of a nonzero {-1,0,1} combo of zeta^j (j in 0..n-1) with
    sum=0 mod q AND char-0 value != 0.  Returns (s, relation) or (None,None)."""
    for s in range(2, max_s+1):
        for positions in itertools.combinations(range(n), s):
            for signs_rest in itertools.product((1,-1), repeat=s-1):
                signs = (1,) + signs_rest
                val = 0
                for pos, sg in zip(positions, signs):
                    val = (val + sg*P[pos]) % q
                if val % q == 0:
                    coeffs = [0]*n
                    for pos, sg in zip(positions, signs):
                        coeffs[pos] = sg
                    if not char0_is_zero(coeffs, n):
                        return s, list(zip(positions, signs))
    return None, None

def is_antipodal(idx_set, n):
    N = n//2
    return all(((j+N) % n in idx_set) for j in idx_set)

def min_nonantipodal_e1zero(P, q, n, max_a=8):
    """smallest |S| with sum(S)=0 mod q (e_1=0) that is NOT antipodal (count defect)."""
    for a in range(2, max_a+1):
        for combo in itertools.combinations(range(n), a):
            if sum(P[j] for j in combo) % q == 0 and not is_antipodal(set(combo), n):
                return a, combo
    return None, None

# -------- ENERGY face: char-0 vs char-p additive energy of mu_n ----------------------
def E_r_modq(P, q, r):
    from collections import Counter
    base = Counter(P)
    dist = Counter({0: 1})
    for _ in range(2*r):
        nd = Counter()
        for s, c in dist.items():
            for v, cv in base.items():
                nd[(s+v) % q] += c*cv
        dist = nd
    return dist[0]

def E_r_char0(n, r):
    """char-0 additive energy of mu_{2^mu}: #{2r-tuples of 2^mu-th roots summing to 0}.
    EXACT closed form: each root zeta^a = +-zeta^{a mod (n/2)} (sign by carry). The
    sum over C vanishes iff, in each of the n/2 residue classes mod n/2, the number of
    '+' picks equals the number of '-' picks (the half-basis {1,..,zeta^{n/2-1}} is a
    Q-basis of the 2^mu-cyclotomic field). For each class with k_c picks the number of
    sign-balanced assignments is 0 if k_c odd else C(k_c, k_c/2). And the multinomial
    distributes 2r positions into classes with given per-class counts and per-position
    sign already fixed by which of the 2 roots (zeta^{c} or zeta^{c+n/2}) is chosen.
    Equivalently: E_r = #{(eps_i, c_i)_{i<2r}: eps_i in {+,-}, c_i in [n/2],
    and for each class +count == -count}. Count = sum over (k_c) composition of 2r
    into n/2 parts, multinomial(2r; k_c) * prod_c [k_c even] C(k_c, k_c/2]."""
    half = n // 2
    m = 2*r
    # DP over classes: f[j] = sum over ways to fill processed classes using j positions
    # of  (multinomial partial) * prod balanced-sign factor.  Track as: number of
    # tuples (positions assigned to classes, with signs balanced per class).
    # Use generating function per class: g(x) = sum_{k>=0} [k even] C(k,k/2) x^k / k!
    # then E_r = (2r)! * [x^{2r}] g(x)^{half}.  Compute via convolution of per-class
    # coefficient arrays a_k = ([k even] C(k,k/2))/k!  -- but keep integer by working
    # with b_k = [k even] C(k,k/2) * C(remaining...). Simpler: integer DP.
    from math import comb, factorial
    # per-class integer weight w_k = [k even] * C(k, k/2)  (sign-balanced assignments
    # for k positions in this class, signs being the only freedom; positions already
    # labelled). Then E_r = sum over (k_1+...+k_half = 2r) multinomial(2r;k_*) prod w_{k_c}.
    # DP: dp[used] aggregated over classes, dp_new[used+k] += dp[used]*C(2r-used,k? ) ...
    # We fold multinomial via binomial choices.
    w = [0]*(m+1)
    for k in range(0, m+1):
        if k % 2 == 0:
            w[k] = comb(k, k//2)
    dp = [0]*(m+1)
    dp[0] = 1
    for _c in range(half):
        nd = [0]*(m+1)
        for used in range(m+1):
            if dp[used] == 0: continue
            for k in range(0, m-used+1):
                if w[k] == 0 and k != 0: continue
                # choose which k of the remaining (m-used) positions go to this class
                nd[used+k] += dp[used] * comb(m-used, k) * w[k]
        dp = nd
    return dp[m]

def energy_defect_onset(P, q, n, max_r=4):
    """minimal r with E_r^{Fp} > E_r^{char0} (a non-char-0 collision appears mod q)."""
    for r in range(1, max_r+1):
        Efp = E_r_modq(P, q, r)
        E0 = E_r_char0(n, r)
        if Efp > E0:
            return r, Efp, E0
    return None, None, None

def run():
    print("="*104)
    print("C033 UNIFICATION TEST v2: GENUINE char-p relation height, COUNT vs ENERGY face")
    print("="*104)
    eps_exp = 128
    for n in [8, 16, 32]:
        mu = int(round(log2(n)))
        primes = []
        q1 = find_prize_prime(n, 4.5)
        if q1: primes.append(q1)
        # small proper-subgroup prime for exact energy DP
        cand = ((int(n**3)//n)+1)*n+1
        while cand < int(n**3.2):
            if isprime(cand): primes.append(cand); break
            cand += n
        for q in primes:
            P = mu_subgroup(q, n)
            beta = log(q)/log(n)
            print(f"\n--- n={n} (mu={mu}), q={q} (q~n^{beta:.2f}), PROPER subgroup, large prime ---")
            # genuine count-face relation height (cap support by feasibility)
            cap_s = 8 if n <= 16 else 7
            sc, rel = min_genuine_pm1_relation(P, q, n, max_s=min(cap_s, n))
            print(f"  [COUNT] min GENUINE +-1 relation support (vanish mod q, !=0 in C): {sc}"
                  f"   (searched up to {min(cap_s,n)})   rel: {rel}")
            cap_a = 8 if n <= 16 else 7
            ma, combo = min_nonantipodal_e1zero(P, q, n, max_a=min(cap_a, n))
            print(f"  [COUNT] min non-antipodal |S| with e_1=0 mod q (true #lacBad defect): {ma}"
                  f"   (searched up to {min(cap_a,n)})")
            # energy-face defect
            if q <= 60000:
                er, Efp, E0 = energy_defect_onset(P, q, n, max_r=4)
                print(f"  [ENERGY] min r with E_r^Fp > E_r^char0: r={er}  (E_r^Fp={Efp}, "
                      f"E_r^char0={E0});  signed relation length 2r={2*er if er else None}")
            else:
                print(f"  [ENERGY] q={q} too large for exact DP; energy NEEDS r~log2 q={log2(q):.1f}, "
                      f"length 2r~{2*log2(q):.0f} (BGK depth)")
    print("\n" + "="*104)
    print("KEY COMPARISON: does COUNT min-relation-support == ENERGY 2r-onset == s*?")
    print(" s* = 2 log2(q eps*)/H(rho). In TRUE prize regime q*eps* ~ n  =>  s* ~ 2 log2(n)/H(rho)")
    for n in [8,16,32, 2**30, 2**32]:
        s_star = 2*log2(n)/H(0.25)  # q eps* ~ n
        print(f"   n={n}: s* (q eps*~n, rho=1/4) = {s_star:.2f}   |   energy depth 2 log2 q "
              f"(q~n^4.5) = {2*4.5*log2(n):.1f}")
    print("="*104)

if __name__ == "__main__":
    run()
