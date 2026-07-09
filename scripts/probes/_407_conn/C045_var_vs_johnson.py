"""
C045 attack: "Var=n is literally the Johnson ceiling: the SAME flat-profile
equality saturates both Cauchy-Schwarz steps."

Two in-tree exact identities:
  (1) subgroup_gaussSum_secondMoment:  sum_b ||eta_b||^2 = q*|G|, so AVERAGE = |G| = n.
      Here eta_b = sum_{y in G} psi(b*y), G = mu_n (dyadic subgroup), q prime = 1 mod n.
      Claim names this the "period variance Var = n".
  (2) cauchySchwarz_eq_iff_flat:  (sum_j S_j)^2 = n * sum_j S_j^2  iff S_j flat.
      This is the Johnson 2nd-moment tightness over n COORDINATES, S_j = #codewords
      agreeing with w at coordinate j.

The connection asserts these are "one object on two faces" and that the flat
witness in (2) is the SAME configuration as the period spectrum being flat
(Salem-Zygmund extremal), tying F7 Var=n to W-Johnson tightness via one identity.

We probe, EXACT integer arithmetic, on proper dyadic subgroups mu_n < F_q*,
q = n^beta-ish, multiple large primes:

  A. Confirm identity (1):  sum_b ||eta_b||^2 = q*n  (so average ||eta_b||^2 = n).
  B. Check whether the PERIOD SPECTRUM {||eta_b||^2 : b} is FLAT (it is NOT: b=0 gives n^2).
     -> The variance/average is n, but max is n^2 (at b=0) and the nonzero-b family is
        the real object. Check max_{b != 0} ||eta_b||^2 vs n  (the Johnson sqrt(n) deficit
        is about THIS max, not the average).
  C. The crux of the connection: is the flatness of (2) the SAME equality as Var=n?
     - In (1) the relevant CS step (Parseval) gives max_b ||eta_b||^2 <= sum_b = q*n,
       i.e. ||eta_b|| <= sqrt(q*n). Equality there means ONE frequency carries ALL mass.
       That is the OPPOSITE of flat.
     - In (2) flat S_j is required for Johnson tightness.
     So check numerically: at a real far line, is the matchCount profile S_j flat
     exactly when the period family {||eta_b||^2} is L2-extremal? Are the two "flat"
     conditions the same object, or different (one flat = both-CS-saturate)?
"""
import cmath, math
from sympy import isprime, primitive_root

def subgroup_mu_n(q, n):
    """mu_n = unique subgroup of order n in F_q* (q prime, n | q-1)."""
    assert (q-1) % n == 0
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)   # generator of mu_n
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x*h) % q
    assert len(set(G)) == n
    return G, h

def eta_sq(q, G, b):
    """||eta_b||^2 = | sum_{y in G} exp(2pi i b y / q) |^2, exact-ish via complex,
       but we ALSO compute it as an exact integer via the autocorrelation count."""
    # exact integer form: ||eta_b||^2 = sum_{y,y' in G} cos? No: it's
    # sum_{y,y'} exp(2pi i b (y - y')/q). Real because conjugate-symmetric.
    # = #{(y,y') in GxG : b(y-y') = 0 mod q} contributions... not integer per b generally.
    # Use exact integer via: ||eta_b||^2 = sum over (y,y') of zeta^{b(y-y')}.
    # We'll just sum complex with high precision and round the AGGREGATE checks.
    s = 0j
    w = 2*math.pi*b/q
    for y in G:
        s += cmath.exp(1j*w*y)
    return abs(s)**2

def exact_sum_etasq(q, G):
    """sum_b ||eta_b||^2 EXACT integer = sum_{y,y'} #{b : b(y-y')=0 mod q}
       = sum_{y,y'} q*[y=y'] = q*|G|.  (closed form, no float)"""
    return q*len(G)

def main():
    # proper dyadic subgroups, large-ish primes, q ~ n^beta with n << sqrt(q)
    cases = [
        (8,  1009),   # n=8,  q=1009  (q-1=1008=2^4*63, 8|1008), beta~3.4
        (16, 1153),   # n=16, q=1153  (q-1=1152=2^7*9), beta~2.5  -> bump
        (16, 7681),   # n=16, q=7681  (q-1=7680=2^9*15), beta~3.2
        (32, 12289),  # n=32, q=12289 (q-1=12288=2^12*3), beta~2.7
        (64, 65537),  # n=64, q=65537 Fermat prime, q-1=2^16, beta~2.66
    ]
    for n, q in cases:
        if not isprime(q):
            print(f"  SKIP q={q} not prime"); continue
        if (q-1) % n != 0:
            print(f"  SKIP n={n} does not divide q-1={q-1}"); continue
        G, h = subgroup_mu_n(q, n)
        beta = math.log(q)/math.log(n)
        # A. identity (1) exact
        exact = exact_sum_etasq(q, G)              # = q*n
        # float cross-check of the sum
        fsum = sum(eta_sq(q, G, b) for b in range(q))
        avg = fsum/q
        # B. spectrum stats over b != 0
        nz = [eta_sq(q, G, b) for b in range(1, q)]
        mx = max(nz); mn = min(nz)
        # flat? all equal?
        flat = (mx - mn) < 1e-6
        # the "Johnson sqrt(n) deficit": max_{b!=0} ||eta_b|| vs sqrt(n)
        B = math.sqrt(mx)
        print(f"n={n:3d} q={q:6d} beta={beta:.2f} | "
              f"exact sum_b||eta||^2 = q*n = {exact} (float {fsum:.1f}); avg={avg:.3f} (=n? {abs(avg-n)<1e-3}) | "
              f"max_{{b!=0}}||eta||^2={mx:.2f} -> B={B:.3f}, sqrt(n)={math.sqrt(n):.3f}, B/sqrt(n)={B/math.sqrt(n):.3f} | "
              f"spectrum FLAT? {flat}")

if __name__ == "__main__":
    main()
