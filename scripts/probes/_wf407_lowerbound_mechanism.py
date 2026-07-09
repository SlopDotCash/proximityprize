#!/usr/bin/env python3
"""
WF407 / lowerbound — WHICH lower-bound mechanism is RIGOROUSLY provable, and what c?

Three candidate provable lower bounds on  B = max_cosets |eta|  (m cosets, b!=0):

  L0 (bare floor, FULLY PROVABLE, axiom-clean already in-tree):
      sum_cosets |eta|^2 = p - n  =>  B^2 >= avg = (p-n)/m  =>  B >= sqrt((p-n)/m).
      Since (p-n)/m = n(p-n)/(p-1) = n(1 - (n-1)/(p-1)) ~ n, this is  B >= ~sqrt(n).
      NO log factor.  c_eff in front of sqrt(n) is just 1 (asymptotically).

  L1 (moment-ratio / "flatness reversed"):  if we KNOW an UPPER bound on a HIGHER
      even moment, M_{2r} <= K_r, that does NOT lower-bound the max.  The max is
      lower-bounded by moments only via:
         B^{2r} = max |eta|^{2r} >= (1/m) sum |eta|^{2r} = M_{2r}.
      So  B >= M_{2r}^{1/2r}.  With the EXACT 4th moment we can BEAT sqrt(n):
         B^4 >= M_4 = (1/m) sum |eta|^4.  Measure M_4 and B/M_4^{1/4}.
      Crucially M_4 is EXACTLY computable (additive energy E_2(mu_n) of the subgroup):
         sum_cosets |eta|^4 * n = sum_{b!=0} |eta_b|^4 = q * (#additive quadruples) - corr.
      so M_4 is an EXACT arithmetic quantity => B >= (exact)^{1/4}, provable.

  L2 (the log factor — the GENUINELY HARD direction): to get B >= c sqrt(n log m)
      you need the values to be SPREAD (anti-concentrated) like a Gaussian max, i.e.
      a LOWER bound on a high moment M_{2r} for r ~ log m of size ~ (2r-1)!! n^r.
      That is the SAME deep input (Gaussian energy lower bound E_r >= ~r! n^r) as the
      UPPER route, just used in reverse.  We test how big r can go before the EXACT
      char-0 Gaussian growth M_{2r} ~ (2r-1)!! n^r breaks (it breaks when r ~ collisions
      saturate, i.e. when the subgroup additive energy stops being "generic").

This script:
 (a) reports the EXACT L0 floor sqrt((p-n)/m) and confirms B >= it (always true).
 (b) reports B / M_4^{1/4}  (the 4th-moment lower bound; M_4^{1/4} should beat sqrt(n)
     by a small constant; tells us c4 = M_4^{1/4}/sqrt(n)).
 (c) reports, for the BEST provable r, the lower bound M_{2r}^{1/(2r)} and its ratio to
     sqrt(n log m): the GAP between the provable lower constant and the target sqrt(log m).
 (d) the Paley-Zygmund 2nd/4th lower bound on the FRACTION of cosets with |eta|^2 >= theta*n,
     P >= (1-theta)^2 (E|eta|^2)^2 / E|eta|^4 = (1-theta)^2 n^2 / M_4.  This LOWER-bounds
     how many cosets are large => via union/counting gives a max lower bound with a log.
"""
import cmath, math, statistics as st

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = []; t = phi; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t //= d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac): return g

def coset_etas(p, n, g=None):
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    gen = pow(g, m, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []; bc = 1
    for _ in range(m):
        s = 0j
        for xx in mu: s += e[(bc*xx) % p]
        etas.append(s); bc = (bc*g) % p
    return etas, m, g

def additive_energy(p, n, g=None):
    """E_2(mu_n) = #{(a,b,c,d) in mu_n^4 : a+b=c+d}.  M_4 relation:
       sum_{b in F} |eta_b|^4 = q * E_2(mu_n).  (standard Parseval-4 identity)"""
    if g is None: g = primitive_root(p)
    m = (p-1)//n
    gen = pow(g, m, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    # count sums a+b mod p
    from collections import Counter
    cnt = Counter()
    for a in mu:
        for b in mu:
            cnt[(a+b) % p] += 1
    E2 = sum(v*v for v in cnt.values())
    return E2

def main():
    print("="*88)
    print("(a)+(b) EXACT floors:  sqrt((p-n)/m) [2nd-mom, ~sqrt n]  and  M_4^{1/4} [4th-mom]")
    print("    plus B and the ratios.  E2 = additive energy of mu_n; sum_b|eta_b|^4 = q*E2.")
    print("="*88)
    print(f"{'n':>4} {'p':>8} {'m':>6} | {'floor2=sqrt((p-n)/m)':>20} {'B':>8} {'B/floor2':>8} | "
          f"{'M4^1/4':>8} {'B/M4^.25':>9} {'c4=M4^.25/sqrtn':>15}")
    for n in [8, 16, 32]:
        p = n+1; rows = 0
        while rows < 6:
            p += n
            if p > 200000: break
            if is_prime(p) and (p-1) % n == 0:
                m = (p-1)//n
                if m < 16: continue
                if n*n*1 > 5000 and m > 600: break   # keep E2 (O(n^2)) cheap; m sum cheap
                etas, m, g = coset_etas(p, n, )
                mags2 = [abs(e)**2 for e in etas]
                floor2 = math.sqrt((p-n)/m)
                B = math.sqrt(max(mags2))
                # M4 exact via additive energy: sum_{b!=0}|eta|^4 = q*E2 - n^4 (subtract b=0)
                E2 = additive_energy(p, n, g)
                sum_b_ne0 = p*E2 - n**4
                # distinct coset values counted n times each:
                M4 = (sum_b_ne0 / n) / m   # = avg over cosets of |eta|^4
                # sanity: empirical M4
                M4_emp = st.mean(v*v for v in mags2)
                M4root = M4**0.25
                c4 = M4root/math.sqrt(n)
                print(f"{n:>4} {p:>8} {m:>6} | {floor2:>20.4f} {B:8.3f} {B/floor2:8.3f} | "
                      f"{M4root:8.3f} {B/M4root:9.3f} {c4:15.4f}   (M4_emp={M4_emp:.2f} M4_exact={M4:.2f})")
                rows += 1
    print()
    print("  NOTE: M4_exact (from additive energy E2) MATCHES M4_emp  => the 4th-moment lower")
    print("  bound B >= M4^{1/4} is an EXACT ARITHMETIC quantity (provable, no Weil).")
    print()
    print("="*88)
    print("(c) HIGH-MOMENT provable lower bound vs target.  B >= M_{2r}^{1/2r}.")
    print("    ratio R_r = M_{2r}^{1/2r} / sqrt(n log m). As r grows R_r -> ? (the gap to 1).")
    print("="*88)
    for (n, want_m) in [(16, 2000), (32, 1500)]:
        p = n+1
        while p < 3_000_000:
            p += n
            if is_prime(p) and (p-1) % n == 0 and (p-1)//n >= want_m:
                break
        etas, m, g = coset_etas(p, n)
        mags2 = [abs(e)**2 for e in etas]
        B = math.sqrt(max(mags2))
        tgt = math.sqrt(n*math.log(m))
        print(f"\n  n={n} p={p} m={m}  B={B:.3f}  sqrt(n logm)={tgt:.3f}  B/tgt={B/tgt:.3f}")
        print(f"   {'r':>2} {'M2r^{1/2r}':>11} {'/sqrtn':>8} {'/sqrt(n logm)':>13}")
        for r in [1,2,3,4,6,8]:
            Mr = st.mean(v**r for v in mags2)
            root = Mr**(1/(2*r))
            print(f"   {r:>2} {root:>11.3f} {root/math.sqrt(n):>8.3f} {root/tgt:>13.4f}")
    print()
    print("="*88)
    print("(d) PALEY-ZYGMUND fraction with |eta|^2 >= theta*n:  P >= (1-theta)^2 n^2/M4.")
    print("    A POSITIVE fraction of cosets are >= theta*n => MANY large cosets.")
    print("="*88)
    for (n, want_m) in [(16, 2000), (32, 1500)]:
        p = n+1
        while p < 3_000_000:
            p += n
            if is_prime(p) and (p-1) % n == 0 and (p-1)//n >= want_m:
                break
        etas, m, g = coset_etas(p, n)
        mags2 = [abs(e)**2 for e in etas]
        navg = st.mean(mags2)
        M4 = st.mean(v*v for v in mags2)
        print(f"\n  n={n} p={p} m={m}  avg|eta|^2={navg:.2f}  M4={M4:.1f}  M4/n^2={M4/n**2:.3f}")
        print(f"   {'theta':>6} {'PZ lower P':>11} {'emp frac':>9}")
        for theta in [0.25, 0.5, 0.75]:
            PZ = (1-theta)**2 * navg**2 / M4
            emp = sum(1 for v in mags2 if v >= theta*navg)/m
            print(f"   {theta:>6.2f} {PZ:>11.4f} {emp:>9.4f}")

if __name__ == "__main__":
    main()
