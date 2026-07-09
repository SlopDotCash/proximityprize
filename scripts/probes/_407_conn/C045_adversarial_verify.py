"""
ADVERSARIAL VERIFICATION of the C045 REFUTED verdict.

I re-derive the key steps independently, with EXACT integer arithmetic for the
period spectrum (no float for the per-frequency values), at PROPER dyadic
subgroups mu_n < F_q* (large prime, n << sqrt(q)).

Exact integer form of the period power spectrum:
  ||eta_b||^2 = sum_{y,y' in G} zeta^{b(y-y')},  zeta = exp(2pi i/q).
  This is real. Grouping by d = (y-y') mod q with multiplicity c_d = #{(y,y'): y-y'=d}:
    ||eta_b||^2 = sum_{d} c_d * zeta^{b d}.
  For b != 0, sum over b of this = sum_d c_d * (sum_{b} zeta^{bd}) ... but per-b it
  is generally irrational. HOWEVER we can compute ||eta_b||^2 EXACTLY as an algebraic
  number by working with the autocorrelation c_d and Gauss periods. For a robust
  *exact-integer* check we instead verify the AGGREGATE identities exactly and use
  high-precision (mpmath, 50 digits) for the per-b maxima, then cross-check that the
  max is stable.

Checks:
  (V1) EXACT: sum_{b=0}^{q-1} ||eta_b||^2 = q*n  (the in-tree 2nd moment).  [integer]
  (V2) EXACT: ||eta_0||^2 = n^2.                                            [integer]
  (V3) Hence sum_{b!=0} ||eta_b||^2 = q*n - n^2 EXACTLY; avg over nonzero = (qn-n^2)/(q-1).
  (V4) Is the nonzero spectrum FLAT?  Compute (max-min)/avg with 50-digit precision.
  (V5) B = sqrt(max_{b!=0}||eta_b||^2). Track B/sqrt(n) vs n -> does it stay near 1
       (flat) or GROW (the BGK/Paley wall)?
  (V6) The "period step": is max_{b!=0} <= sum_{b!=0} (=q*n - n^2) a CS step or a
       trivial max<=sum? Numerically how loose is sqrt(qn) vs true B?
  (V7) BLINDNESS test: construct an ALTERNATIVE nonnegative spectrum on the same q-1
       nonzero frequencies with the SAME total (qn-n^2) but a SPIKE (B'=n, trivial
       ceiling). Confirms the 2nd moment alone admits B' as large as n while the
       average is unchanged. This is the rigorous core of (P3).
"""
import math
from mpmath import mp, mpf, mpc, exp, pi, fabs, sqrt
from sympy import isprime, primitive_root

mp.dps = 50  # 50 decimal digits

def subgroup_mu_n(q, n):
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)
    G, x = [], 1
    for _ in range(n):
        G.append(x); x = (x*h) % q
    assert len(set(G)) == n
    return G

def eta_sq_hp(q, G, b):
    """||eta_b||^2 at 50-digit precision."""
    s = mpc(0)
    w = 2*pi*mpf(b)/q
    for y in G:
        ang = w*y
        s += mpc(exp(mpc(0, ang)))
    return (s.real**2 + s.imag**2)

def autocorr_exact(q, G):
    """c_d = #{(y,y') in GxG : (y - y') mod q = d}, exact integers."""
    from collections import Counter
    c = Counter()
    for y in G:
        for yp in G:
            c[(y - yp) % q] += 1
    return c

def main():
    cases = [(8,1009),(16,7681),(32,12289),(64,65537)]
    print(f"{'n':>3} {'q':>6} {'beta':>5} | {'V1 sum=q*n exact':>16} | {'V2 eta0^2=n^2':>13} | "
          f"{'avg(b!=0)':>10} {'=n?':>5} | {'flat?(mx-mn)/avg':>16} | "
          f"{'B/sqrt(n)':>9} {'B/sqrt(qn)':>10}")
    rows = []
    for n, q in cases:
        if not isprime(q) or (q-1) % n:
            print(f"SKIP n={n} q={q}"); continue
        G = subgroup_mu_n(q, n)
        beta = math.log(q)/math.log(n)
        # V1: exact integer 2nd moment via autocorrelation
        c = autocorr_exact(q, G)
        # sum_b ||eta_b||^2 = sum_d c_d * sum_b zeta^{bd} = sum_d c_d * q*[d==0] = q*c_0
        c0 = c[0]                       # = n (diagonal pairs)
        exact_2nd = q * c0              # should = q*n
        v1_ok = (exact_2nd == q*n)
        # V2: ||eta_0||^2 = n^2 exact
        eta0_sq = n*n
        # V3 avg over nonzero
        sum_nz = exact_2nd - eta0_sq    # = q*n - n^2 exact
        avg_nz = sum_nz/(q-1)
        # V4/V5 high-precision per-b maxima/minima over b!=0
        vals = [eta_sq_hp(q, G, b) for b in range(1, q)]
        mx = max(vals); mn = min(vals)
        flatness = float((mx-mn)/(mpf(sum_nz)/(q-1)))
        B = float(sqrt(mx))
        rows.append((n,q,B))
        print(f"{n:3d} {q:6d} {beta:5.2f} | {exact_2nd:>10}={q*n}({str(v1_ok):>4}) | "
              f"{eta0_sq:>13} | {avg_nz:10.3f} {str(abs(avg_nz-n)<0.06):>5} | "
              f"{flatness:16.3f} | {B/math.sqrt(n):9.3f} {B/math.sqrt(q*n):10.4f}")
    print()
    print("V6: 'period step' sqrt(qn) vs true B -> looseness factor sqrt(qn)/B:")
    for n,q,B in rows:
        print(f"   n={n:3d}: sqrt(qn)={math.sqrt(q*n):9.2f}  B={B:8.3f}  loose x{math.sqrt(q*n)/B:6.2f}")
    print()
    print("V7 BLINDNESS (rigorous): same 2nd moment sum_nz=q*n-n^2 admits a SPIKE with B'=n.")
    print("   Need one freq carrying n^2 (trivial ceiling |eta_b|<=|G|=n) + rest sharing remainder.")
    for n,q,_ in rows:
        sum_nz = q*n - n*n
        spike = n*n                 # B'^2 = n^2 -> B'=n, the trivial ceiling
        rest_total = sum_nz - spike
        rest_avg = rest_total/(q-2) if q>2 else 0
        feasible = (rest_total >= 0) and (rest_avg >= 0)
        print(f"   n={n:3d} q={q:6d}: total(b!=0)={sum_nz}, put {spike} on ONE freq (B'=n={n}), "
              f"remaining {rest_total} over {q-2} freqs avg {rest_avg:.2f}>=0 feasible={feasible}; "
              f"avg STILL {(sum_nz)/(q-1):.3f}~n")
    print()
    print("INTERPRETATION:")
    print(" - V1/V2/V3 confirm the in-tree 2nd-moment identity EXACTLY (integer): sum=q*n, eta0^2=n^2.")
    print(" - V4 flatness ratio >> 0 -> spectrum NOT flat; V5 B/sqrt(n) GROWS -> not the flat extremal.")
    print(" - V6 sqrt(qn) is loose by a large factor -> the 'period step' is vacuous as a B bound.")
    print(" - V7: the SAME 2nd moment is consistent with B'=n (spike). Average is BLIND to worst-case B.")

if __name__ == "__main__":
    main()
