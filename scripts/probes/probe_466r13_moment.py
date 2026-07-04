#!/usr/bin/env python3
"""
#466 Round 13 -- LANE M probe: validate the moment-order optimization

  WallHolds  ==>  M = max_{b!=0} ||eta_b|| <= C * sqrt(n * log(p/n))   (and <= C' sqrt(n log q))

Chain being validated (all pieces in-tree/elementary):
  (i)  DC-subtracted moment identity: sum_{b!=0} ||eta_b||^{2r} = q*E_r - n^{2r}   (sum_nonzero_moment)
  (ii) hence  M^{2r} <= q*E_r - n^{2r}  =: A_r  (single term <= sum)
  (iii) the WALL (DCEnergyBound at rung r):  A_r <= q * (2r-1)!! * n^r  =: q*Wick_r
  (iv) so  M <= (q * (2r-1)!! * n^r)^{1/2r}  for every r; minimize over r.

We compute, for concrete (n, p) in-regime:
  * the ACTUAL min_r (q*E_r - n^{2r})^{1/2r}  (the true moment-optimized sup-norm proxy;
    q*E_r - n^{2r} = sum over nonzero freqs of ||eta_b||^{2r}, an UPPER proxy for M^{2r}),
  * the actual argmin r*,
  * the WICK RHS min_r (q*(2r-1)!!*n^r)^{1/2r}  (what WallHolds delivers),
  * compare both to sqrt(n log(p/n)) and sqrt(n log q), and to the closed form sqrt(2e n (ln q +1)).

Regime rules: p == 1 mod n, p >= n^4, proper mu_n, >= 2 primes distinct v2(p-1),
exclude X^{n/2} = +/-1 degenerate.  We use small n (8,16,32) so E_r is computable exactly
by brute enumeration of mu_n^{2r} wraparound counts... but that is q-independent only via the
character-sum second-moment.  Instead we compute ||eta_b|| DIRECTLY from the Gauss periods
eta_b = sum_{y in mu_n} zeta_p^{b*y}, exactly (complex), and form the moments.
"""
import cmath, math
from math import gcd

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2; k += 1
    return k

def find_primes(n, count, min_ratio_pow=4):
    """primes p == 1 mod n, p >= n^min_ratio_pow, distinct v2(p-1)."""
    out = []
    seen_v2 = set()
    p = 1
    lo = n**min_ratio_pow
    k = max(1, lo // n)
    while len(out) < count and k < 10**7:
        p = k*n + 1
        k += 1
        if p < lo: continue
        if not is_prime(p): continue
        vv = v2(p-1)
        if vv in seen_v2: continue
        # find a generator g of F_p^*, then mu_n = <g^{(p-1)/n}>
        seen_v2.add(vv)
        out.append(p)
    return out

def mu_n_elements(n, p):
    """the n-th roots of unity in F_p (as integers mod p): elements x with x^n=1."""
    # find an element of order exactly n
    # p-1 divisible by n
    # take a generator
    def order(a):
        o = 1; cur = a % p
        while cur != 1:
            cur = (cur*a) % p; o += 1
        return o
    # find primitive root
    g = None
    for cand in range(2, p):
        if order(cand) == p-1:
            g = cand; break
    h = pow(g, (p-1)//n, p)   # order n
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur)
        cur = (cur*h) % p
    return elts, g

def eta_norms(n, p):
    """||eta_b|| = |sum_{y in mu_n} exp(2 pi i b y / p)| for all b != 0, exact-ish (float)."""
    mu, g = mu_n_elements(n, p)
    norms = []
    twopi_over_p = 2*math.pi/p
    for b in range(1, p):
        s = 0j
        for y in mu:
            s += cmath.exp(1j*twopi_over_p*(b*y % p))
        norms.append(abs(s))
    return norms, mu

def doublefact_odd(r):
    """(2r-1)!! = prod_{i<r}(2i+1) = 1*3*5*...*(2r-1)."""
    v = 1
    for i in range(r):
        v *= (2*i+1)
    return v

def analyze(n, p, max_r=None):
    q = p
    norms, mu = eta_norms(n, p)
    # verify DC: eta_0 = n (not in norms since b starts at 1)
    M = max(norms)  # the true sup-norm over b != 0
    # A_r = sum_{b!=0} ||eta_b||^{2r}  (= q*E_r - n^{2r})
    if max_r is None:
        max_r = max(2, int(math.log(q)) + 3)
    results = []
    for r in range(1, max_r+1):
        A_r = sum(x**(2*r) for x in norms)
        moment_bound = A_r**(1.0/(2*r))          # (q E_r - n^{2r})^{1/2r}  >= M
        wick = q * doublefact_odd(r) * (n**r)     # q*(2r-1)!!*n^r
        wick_bound = wick**(1.0/(2*r))            # what WallHolds gives
        wall_holds_r = (A_r <= wick + 1e-6)       # is DCEnergyBound satisfied at this r?
        results.append((r, moment_bound, wick_bound, wall_holds_r, A_r, wick))
    # find argmin of each
    r_star_mom = min(results, key=lambda t: t[1])
    r_star_wick = min(results, key=lambda t: t[2])
    logq = math.log(q)
    log_p_over_n = math.log(p/n)
    scale_pn = math.sqrt(n*log_p_over_n)
    scale_q = math.sqrt(n*logq)
    closed = math.sqrt(2*math.e*n*(logq+1))
    print(f"\n===== n={n}, p={p} (p/n={p/n:.1f}, beta=log_n(p)={math.log(p)/math.log(n):.2f}, v2(p-1)={v2(p-1)}) =====")
    print(f"  q=p={q}, log q={logq:.3f}, log(p/n)={log_p_over_n:.3f}")
    print(f"  TRUE sup-norm M = max_b!=0 ||eta_b|| = {M:.4f}")
    print(f"  sqrt(n log(p/n)) = {scale_pn:.4f}   sqrt(n log q) = {scale_q:.4f}")
    print(f"  M / sqrt(n log(p/n)) = {M/scale_pn:.4f}    M / sqrt(n log q) = {M/scale_q:.4f}")
    print(f"  closed form sqrt(2e n (ln q +1)) = {closed:.4f}  (M/closed = {M/closed:.4f})")
    r_opt_theory = 0.5*logq
    print(f"  theory optimal r ~ (1/2) ln q = {r_opt_theory:.2f}")
    print(f"  --- moment-bound (q E_r - n^{{2r}})^(1/2r) [proxy >= M] : argmin r*={r_star_mom[0]}, value={r_star_mom[1]:.4f} ---")
    print(f"  --- WICK bound   (q (2r-1)!! n^r)^(1/2r) [WallHolds]  : argmin r*={r_star_wick[0]}, value={r_star_wick[2]:.4f} ---")
    print(f"    moment argmin/(0.5 ln q) = {r_star_mom[0]/r_opt_theory:.3f}   wick argmin/(0.5 ln q) = {r_star_wick[0]/r_opt_theory:.3f}")
    print(f"    wick-min / sqrt(n log q) = {r_star_wick[2]/scale_q:.4f}   (theory C=sqrt(2e)={math.sqrt(2*math.e):.4f})")
    print(f"    ceil(ln q)={math.ceil(logq)}: at r=ceil(ln q), wick bound=", end="")
    rr = min(math.ceil(logq), max_r)
    row = results[rr-1]
    print(f"{row[2]:.4f}  (/sqrt(n log q)={row[2]/scale_q:.4f})")
    print("   r |  moment^(1/2r) |  wick^(1/2r) | DCEnergyBound(r) holds?")
    for (r, mb, wb, wh, A_r, wick) in results:
        star_m = " <-mom*" if r==r_star_mom[0] else ""
        star_w = " <-wick*" if r==r_star_wick[0] else ""
        print(f"  {r:2d} | {mb:12.4f} | {wb:12.4f} | {str(wh):5s}{star_m}{star_w}")
    return M, r_star_wick, scale_q

def main():
    print("#466 R13 LANE M -- moment-order optimization validation")
    print("Validating: WallHolds => M <= C sqrt(n log q), optimal r ~ (1/2) ln q, C ~ sqrt(2e)~2.33")
    for n in (8, 16, 32):
        primes = find_primes(n, 2, min_ratio_pow=4)
        for p in primes:
            try:
                analyze(n, p)
            except Exception as ex:
                print(f"  n={n} p={p}: ERROR {ex}")

if __name__ == "__main__":
    main()
