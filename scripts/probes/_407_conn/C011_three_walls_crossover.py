"""
C011 probe: do the THREE deep-moment walls share ONE root crossover depth r*?

Claim (C011): all three walls cross over at r* ~= beta = log_n q, deficit = a/2
where a = log2(n) = tower height, beta = log_n q.

Three crossover depths to compute exactly (prize regime: n=2^mu proper dyadic
subgroup, q = n^beta prime, beta in {4,5}, n << sqrt(q)):

(i)  W-anomaly (CharSumMomentDeepWall):
     char-0 moment value E_r valid only for r <= r_max = 2*log_n(p) - 3 = 2*beta - 3.
     moment optimum needs r_opt ~= log q = a * log_n p = a*beta  (a = log2 n).
     => reliable-depth crossover r*_anom = r_max = 2*beta - 3.

(ii) W-largesieve (ManyTermResultantBound):
     char-0 energy E_r valid when q > (2r)^{phi(n)} = (2r)^{n/2}.
     Solve largest r with (2r)^{n/2} < q:
         (n/2)*log2(2r) < log2(q)  =>  log2(2r) < 2*log2(q)/n  =>  2r < q^{2/n}.
     => r*_ls = floor( (q^{2/n})/2 ).  [the connection says this -> beta at "production index"]

(iii) W-Betti / Kowalski-Untrau (KowalskiUntrauBarrier):
     non-vacuous when (d-1)*(12 + 2*log2 d) < log2 q, d = subgroup size = n.
     For a FIXED subgroup the relevant "depth" is d=n; but the connection reads it as
     a ceiling d <= log q / log log q. We compute the max d that is non-vacuous,
     d*_ku = max d with (d-1)*(12+2 log2 d) < log2 q, and compare to beta.

We tabulate all three and test the assertion "all three ~ beta +- 1".
Exact integer / mpmath arithmetic; real prime q ~ n^beta with q == 1 mod n.
"""
import math
from sympy import nextprime, isprime

def log_n(x, n):
    return math.log(x) / math.log(n)

def find_prime_q(n, beta):
    """smallest prime q >= n^beta with q == 1 mod n (NTT prime, proper subgroup mu_n)."""
    target = n**beta
    # search q = 1 + k*n >= target
    k = (target - 1 + n - 1)//n  # ceil((target-1)/n)
    while True:
        q = 1 + k*n
        if q >= target and isprime(q):
            return q
        k += 1

def r_anom(beta):
    # r_max = 2*beta - 3 ; r_opt = a*beta  (a=log2 n) -- we return r_max (reliable crossover)
    return 2.0*beta - 3.0

def r_largesieve(n, q):
    # largest r with (2r)^{n/2} < q   <=>  2r < q^{2/n}
    # q^{2/n} = exp( (2/n)*ln q )
    cap_2r = math.exp((2.0/n)*math.log(q))
    r = math.floor(cap_2r/2.0)
    return r, cap_2r

def d_ku_max(q):
    # max d (>=2) with (d-1)*(12+2*log2 d) < log2 q
    log2q = math.log2(q)
    d = 2
    last = None
    while True:
        lhs = (d-1)*(12 + 2*math.log2(d))
        if lhs < log2q:
            last = d
            d += 1
        else:
            break
        if d > 10**6:
            break
    return last

print(f"{'mu':>3} {'n':>10} {'beta':>4} {'q~n^b':>22} {'logn q':>8} "
      f"{'r*_anom':>8} {'r*_ls':>8} {'cap2r_ls':>10} {'d*_ku':>8} {'beta?':>6}")
print("-"*110)

rows = []
for mu in [8, 12, 16, 20, 24, 28, 32]:
    n = 2**mu
    for beta in [4, 5]:
        q = find_prime_q(n, beta)
        bq = log_n(q, n)
        ra = r_anom(beta)
        rls, cap2r = r_largesieve(n, q)
        dku = d_ku_max(q)
        rows.append((mu, n, beta, q, bq, ra, rls, cap2r, dku))
        print(f"{mu:>3} {n:>10} {beta:>4} {q:>22} {bq:>8.3f} "
              f"{ra:>8.2f} {rls:>8} {cap2r:>10.4f} {str(dku):>8} {beta:>6}")

print()
print("=== INTERPRETATION ===")
print("beta = log_n q is the production index (n << sqrt q means beta > 2, prize beta~4-5).")
print()
print("(i)  W-anomaly r*_anom = 2*beta-3 :  for beta=4 -> 5,  beta=5 -> 7.  ~ 2*beta, NOT beta.")
print("(ii) W-largesieve: cap on 2r is q^{2/n} -> 1 as n grows (n>>log q). So r*_ls collapses to")
print("     ZERO/ONE for ALL prize n, regardless of beta. cap_2r = q^{2/n}: at n=2^32, q~n^5,")
print("     2*log2 q/n = 2*5*32/2^32 = 320/2^32 ~ 7.5e-8, so q^{2/n}=2^{7.5e-8}~1.00000005.")
print("     => r*_ls = 0. It does NOT land at beta.")
print("(iii) W-KU: d*_ku = max non-vacuous subgroup ~ log q/loglog q, a SIZE not a moment depth;")
print("     and the prize uses a FIXED d=n=2^mu >> d*_ku, so KU is vacuous (depth concept N/A).")
print()
print("Check: is r*_anom ~ beta +- 1 ?  (connection's central coincidence claim)")
for (mu,n,beta,q,bq,ra,rls,cap2r,dku) in rows:
    ok_anom = abs(ra - beta) <= 1.0
    ok_ls   = abs(rls - beta) <= 1.0
    print(f"  n=2^{mu:<2} beta={beta}: r*_anom={ra:.1f} (|-beta|={abs(ra-beta):.1f}, within1={ok_anom}); "
          f"r*_ls={rls} (within1={ok_ls}); d*_ku={dku}")
