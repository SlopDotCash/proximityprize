#!/usr/bin/env python3
"""
C019 attack: "The Bessel coefficient bound IS the Salem-Zygmund sub-Gaussian MGF —
char-0 closes the chaining input, leaving only the char-p defect."

CLAIM (from C019.json):
  bessel_energy_le_gaussian proves E_r^inf(mu_n) <= (2r-1)!! n^r for ALL r (char 0, axiom-clean).
  Generating-function-wise this IS the per-period sub-Gaussian MGF with sigma^2 = n.
  Feeding chernoff_max_re_le gives B <= sqrt(2 n log m), the prize floor.
  ONLY residual: the char-p defect E_r - E_r^(0) > 0 at r ~ beta.

WHAT I TEST (exact integer arithmetic, PROPER subgroups, large prizelike primes):

  (T1) Quantify the char-0 chain itself.  If E_r <= (2r-1)!! n^r held for ALL r at the
       prize prime, the moment transport B^{2r} <= q E_r, optimized over r, gives what?
       Compute B_bound(r) = (q (2r-1)!! n^r)^{1/2r} and minimize over r in [1, r_max].
       Compare to sqrt(2 n log m).  KEY: is the char-0 chain valid up to r ~ log q?

  (T2) Measure the EXACT char-p energy E_r^{F_p}(mu_n) = #{(x,y) in mu_n^{2r}: sum x = sum y mod p}
       by exact integer arithmetic at proper subgroups, and compare to the char-0 bound
       (2r-1)!! n^r.  Find r_break = smallest r where E_r^{F_p} > (2r-1)!! n^r (the wall onset).
       The C019 claim that the defect is "only at r ~ beta" -- check r_break vs beta = log_n p
       and vs r_opt = log q needed for the prize.

  (T3) The DECISIVE structural point.  The chain B <= sqrt(2n log m) requires the char-0 bound
       to hold at r_opt ~ log q.  But there is NO char-0 Gauss period: eta_b is defined mod p.
       The object the MGF/chernoff consumes is the REAL eta_b^{F_p}, whose moments are E_r^{F_p},
       NOT E_r^inf.  So "char-0 closes the input" only if E_r^{F_p} = E_r^inf up to r_opt.
       Check directly: does B_actual <= sqrt(2 n log m), and is the moment bound using char-0
       E_r ever <= sqrt(2n log m) at any single r at these primes?
"""
import cmath, math

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
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    return None

def double_factorial_odd(twoR):
    # (2r-1)!! = product of odd numbers up to 2r-1
    r = 1; k = twoR-1
    while k > 1:
        r *= k; k -= 2
    return r

def subgroup(p, n, g):
    m = (p-1)//n
    gen = pow(g, m, p)
    H = []; x = 1
    for _ in range(n):
        H.append(x); x = (x*gen) % p
    return H

def exact_energy_charp(p, H, r):
    """E_r^{F_p} = #{(x_1..x_r, y_1..y_r) in H^{2r}: sum x = sum y mod p}.
    Compute via convolution of the r-fold sumset distribution mod p.  Exact integers."""
    n = len(H)
    # distribution of sum of r elements of H mod p
    from collections import defaultdict
    dist = {0: 1}  # sum of 0 elements
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for h in H:
                nd[(s+h) % p] += c
        dist = nd
    # E_r = sum_s dist[s]^2
    return sum(c*c for c in dist.values())

def exact_charp_B(p, n, g):
    """B = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x).  Use exact period structure:
    eta_b only depends on coset of b in F_p* / mu_n, so m = (p-1)/n distinct values."""
    H = subgroup(p, n, g)
    m = (p-1)//n
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    Bmax = 0.0
    bc = g  # b ranges over coset reps; b=1 too. Use g^0..g^{m-1}
    b = 1
    for c in range(m):
        s = sum(e[(b*x) % p] for x in H)
        Bmax = max(Bmax, abs(s))
        b = (b*g) % p
    return Bmax, m

def main():
    print("# C019: Does char-0 Bessel bound E_r<=(2r-1)!!n^r discharge the sub-Gaussian MGF -> B<=sqrt(2n log m)?")
    print("# Proper subgroups, prizelike beta=log_n(p). EXACT integer energies for the char-p defect.\n")

    # Pick proper-subgroup cases with growing beta. Keep p small enough for exact E_r at modest r.
    cases = []
    for n in [8, 16, 32]:
        targets = []  # several primes spanning beta
        p = n+1
        found = 0
        while p < 60000 and found < 3:
            if p % n == 1 and is_prime(p):
                m = (p-1)//n
                if m >= 8:
                    targets.append(p)
                    found += 1
                    # skip ahead to spread beta
                    p = int(p*3)
            p += 1
        for p in targets:
            cases.append((n, p))

    for (n, p) in cases:
        g = primitive_root(p)
        m = (p-1)//n
        beta = math.log(p)/math.log(n)
        logm = math.log(m)
        H = subgroup(p, n, g)
        Bact, _ = exact_charp_B(p, n, g)
        target = math.sqrt(2*n*logm)
        print(f"=== n={n} p={p} m={m} beta={beta:.2f} | B_actual={Bact:.3f}  sqrt(2n log m)={target:.3f}  ratio={Bact/target:.3f}")

        # T1+T2: char-0 vs char-p energy, and the moment-transport bound at each r
        print(f"   {'r':>2} {'E_r^Fp(exact)':>16} {'(2r-1)!!n^r=E0':>16} {'defect>0?':>9} "
              f"{'(qE0)^1/2r':>11} {'(qEp)^1/2r':>11} {'<=tgt?':>7}")
        r_break = None
        char0_ever_beats = False
        charp_ever_beats = False
        rmax_exact = 5 if p > 5000 else 6
        for r in range(1, rmax_exact+1):
            Ep = exact_energy_charp(p, H, r)
            E0 = double_factorial_odd(2*r) * (n**r)
            defect = Ep > E0
            if defect and r_break is None:
                r_break = r
            b0 = (p * E0) ** (1.0/(2*r))
            bp = (p * Ep) ** (1.0/(2*r))
            ok0 = b0 <= target
            okp = bp <= target
            if ok0: char0_ever_beats = True
            if okp: charp_ever_beats = True
            mark = ("c0" if ok0 else "..") + ("/cp" if okp else "/..")
            print(f"   {r:>2} {Ep:>16d} {E0:>16d} {str(defect):>9} {b0:>11.3f} {bp:>11.3f} {mark:>7}")

        # r needed for q^{1/2r} ~ O(1):  r_opt ~ 0.5 log q / log(target-ish); report log q and r_max
        r_opt = 0.5*math.log(p)  # rough: q^{1/2r}=e <=> r=log q /2
        r_max = 2*beta - 3
        print(f"   -> r_break(char-p defect onset) = {r_break};  r_opt~log(q)/2 = {r_opt:.1f};  "
              f"r_max(char-0 valid ~2beta-3) = {r_max:.1f}")
        print(f"   -> char-0 moment bound EVER beats sqrt(2n log m) at a single r in [1,{rmax_exact}]? {char0_ever_beats}")
        print(f"   -> char-p moment bound EVER beats sqrt(2n log m) at a single r in [1,{rmax_exact}]? {charp_ever_beats}\n")

    print("# INTERPRETATION:")
    print("#  - If char-0 (qE0)^{1/2r} only beats sqrt(2n log m) for r >> r_max (i.e. NOT in [1,r_max]),")
    print("#    then even GRANTING E_r=E0 for all r, a SINGLE moment never reaches the prize; you need")
    print("#    the FULL MGF assembly across ALL r (Carleman), which needs E0 valid up to r~log q.")
    print("#  - r_break is where char-p energy EXCEEDS the char-0 Bessel bound: the defect is NOT")
    print("#    confined to r~beta if r_break is small/grows slowly. The Bessel bound is a CHAR-0")
    print("#    statement; the object the MGF consumes is the char-p eta_b. So 'char-0 closes the input'")
    print("#    is only true if E_r^{Fp}=E0 up to r~log q, which the r_break data tests directly.")

if __name__ == "__main__":
    main()
