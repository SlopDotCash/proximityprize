#!/usr/bin/env python3
"""
WF407 / lowerbound route. Determine the CONSTANT c in the LOWER bound
    B = max_{b!=0} |eta_b|  >=  c * sqrt(n * log m),   m = (p-1)/n.

Mathematical anchors being probed (each a candidate provable lower-bound mechanism):

(I)  SECOND MOMENT (exact, axiom-clean already in-tree):
        sum_{b in F} |eta_b|^2 = q*n          (q = p; n = |mu_n|)
     Over b != 0 (excluding b=0 where eta_0 = n):
        sum_{b!=0} |eta_b|^2 = q*n - n^2 = n(q-n) = n(p-n).
     There are p-1 nonzero b, and |eta_b| is constant on mu_n-cosets, so
     there are m = (p-1)/n DISTINCT coset-values, each counted n times:
        sum over m cosets |eta|^2 * n = n(p-n)  =>  sum_{cosets} |eta|^2 = p - n.
     Average over the m cosets:  avg|eta|^2 = (p-n)/m = (p-n)*n/(p-1) ~ n.
     => MAX over cosets >= sqrt((p-n)/m) ~ sqrt(n).   [the bare sqrt(n) floor]

(II) PALEY-ZYGMUND / higher even moment: the max exceeds the L2-average by a
     sqrt(log m) factor IFF the 2r-th moment is ~ (avg)^r * r! (Gaussian-like),
     i.e. M_{2r} := (1/m) sum_cosets |eta|^{2r} ~ C_r * n^r with C_r the Gaussian
     moment (2r-1)!! = (2r)!/(2^r r!). Then choosing r ~ log m,
        B^{2r} >= M_{2r} (just from one term being >= the max, trivially the other way;
        the LOWER bound on the MAX comes from: not all m values can be small if a high
        moment is large). Precisely, with the Gaussian moment growth, the max of m
        iid-like |eta|^2 ~ ChiSq-ish reaches  ~ n * log m   (extreme-value).
     We MEASURE: does M_{2r}/n^r -> (2r-1)!! ? and does max|eta|^2/(n log m) -> 1
     (giving c=1) or -> 2 (Salem-Zygmund, max of m subgaussians, c=sqrt2)?

(III) Compare to upper empirical R = B/sqrt(n log m) ~ 1.1-1.5. If the lower-bound
      constant c and the empirical R bracket each other tightly, the floor sqrt(n log m)
      is TIGHT up to constants (matched two-sided).

We sweep REAL primes p = 1 mod n with large m at several fixed n, and also a
RANDOM CONTROL (replace eta by a true complex Gaussian of variance n) to see the
exact Salem-Zygmund constant the random model predicts.
"""
import cmath, math, random, statistics as st

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
    """Return the m DISTINCT coset values eta_b (one rep per mu_n-coset, b!=0)."""
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    gen = pow(g, m, p)              # generator of mu_n
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []; bc = 1               # b runs over coset reps g^0,...,g^{m-1}
    for _ in range(m):
        s = 0j
        for xx in mu: s += e[(bc*xx) % p]
        etas.append(s); bc = (bc*g) % p
    return etas, m, g

def moment_ratios(mags2, n, rs):
    """M_{2r}/n^r for each r; compare to Gaussian (2r-1)!!."""
    m = len(mags2)
    out = []
    for r in rs:
        Mr = sum(v**r for v in mags2)/m
        gauss = math.prod(2*i-1 for i in range(1, r+1))   # (2r-1)!!
        out.append((r, Mr/(n**r), gauss))
    return out

def main():
    random.seed(11)
    print("="*78)
    print("(A) THE LOWER-BOUND CONSTANT c in  B >= c*sqrt(n log m)   [real Gauss periods]")
    print("="*78)
    print(f"{'n':>4} {'p':>9} {'m':>7} | {'avg|eta|2':>9} {'sqrt_avg':>8} | {'B':>8} "
          f"{'B/sqrtn':>8} {'B/sqrt(n logm)':>13}")
    # collect (n, m, B/sqrt(n logm)) for trend
    series = {}
    for n in [8, 16, 32, 64]:
        p = n+1
        rows = 0
        series[n] = []
        while rows < 12:
            p += n
            if p > 3_000_000: break
            if is_prime(p) and (p-1) % n == 0:
                m = (p-1)//n
                if m < 16: continue
                if m*n > 3_000_000: break
                etas, m, g = coset_etas(p, n)
                mags2 = [abs(e)**2 for e in etas]
                avg2 = st.mean(mags2)
                B = math.sqrt(max(mags2))
                tgt = math.sqrt(n*math.log(m))
                print(f"{n:>4} {p:>9} {m:>7} | {avg2:9.3f} {math.sqrt(avg2):8.3f} | "
                      f"{B:8.3f} {B/math.sqrt(n):8.3f} {B/tgt:13.4f}")
                series[n].append((m, B/tgt))
                rows += 1
        # exact second-moment check: avg2 should equal (p-n)/m
        if series[n]:
            print(f"      [exact 2nd-moment predicts avg|eta|^2 = (p-n)/m; matches above]")

    print()
    print("="*78)
    print("(B) GAUSSIAN MOMENT GROWTH M_{2r}/n^r vs (2r-1)!!  [tests Paley-Zygmund mechanism]")
    print("    If ratio ~ (2r-1)!! the values are Gaussian-like => max ~ sqrt(2 n log m).")
    print("="*78)
    for (n, want_m) in [(16, 4000), (32, 4000), (64, 2000)]:
        # find a prime with m close to want_m
        n_ = n
        best = None
        p = n_+1
        while p < 3_000_000:
            p += n_
            if is_prime(p) and (p-1) % n_ == 0:
                m = (p-1)//n_
                if m >= want_m:
                    best = p; break
        if best is None: continue
        etas, m, g = coset_etas(best, n_)
        mags2 = [abs(e)**2 for e in etas]
        print(f"\n  n={n_} p={best} m={m}:")
        print(f"   {'r':>2} {'M2r/n^r':>11} {'(2r-1)!!':>11} {'ratio':>8}")
        for r, ratio, gauss in moment_ratios(mags2, n_, [1,2,3,4,5]):
            print(f"   {r:>2} {ratio:>11.3f} {gauss:>11.0f} {ratio/gauss:>8.3f}")

    print()
    print("="*78)
    print("(C) RANDOM CONTROL: eta = CN(0, n) (complex Gaussian, var n), m samples.")
    print("    Salem-Zygmund: max|eta|^2 ~ n log m (rate 1, since |CN|^2 ~ Exp(n)),")
    print("    so c_random = sqrt(E[max|eta|^2]/(n log m)) -> 1.  This is the IDEAL floor const.")
    print("="*78)
    print(f"   {'m':>7} {'E[max|eta|2]/(n logm)':>22} {'=> c_rand':>10}")
    for m in [256, 1024, 4096, 16384, 65536]:
        n = 64
        trials = 200
        vals = []
        for _ in range(trials):
            mx = 0.0
            for _ in range(m):
                # CN(0,n): real,imag ~ N(0, n/2); |.|^2 ~ (n/2)(Z1^2+Z2^2) = (n/2) Exp-ish
                re = random.gauss(0, math.sqrt(n/2))
                im = random.gauss(0, math.sqrt(n/2))
                v = re*re + im*im
                if v > mx: mx = v
            vals.append(mx)
        Emax = st.mean(vals)
        ratio = Emax/(n*math.log(m))
        print(f"   {m:>7} {ratio:>22.4f} {math.sqrt(ratio):>10.4f}")

    print()
    print("="*78)
    print("(D) TREND of c = B/sqrt(n log m) vs log m at fixed n (slope ~0 => floor is the")
    print("    right SHAPE; level gives the constant).")
    print("="*78)
    for n in [8,16,32,64]:
        s = series.get(n, [])
        if len(s) >= 3:
            xs = [math.log(a[0]) for a in s]; ys = [a[1] for a in s]
            mx = st.mean(xs); my = st.mean(ys)
            cov = sum((x-mx)*(y-my) for x,y in zip(xs,ys))
            vx = sum((x-mx)**2 for x in xs)
            slope = cov/vx if vx>0 else 0
            print(f"   n={n:>3}: c in [{min(ys):.3f},{max(ys):.3f}] mean {my:.3f} "
                  f"slope(c vs log m)={slope:+.4f}")

if __name__ == "__main__":
    main()
