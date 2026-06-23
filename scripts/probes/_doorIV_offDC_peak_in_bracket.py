#!/usr/bin/env python3
"""Door-(iv) Lane-1 probe: where does the ACTUAL off-DC peak M(mu_n) sit inside the
proven exact bracket  sqrt((N*d - d^2)/(N-1)) <= M <= sqrt(N*d - d^2) ?

For thin 2-power multiplicative subgroups mu_n (n = 2^a) of F_p* in the prize regime
(p prime, n | p-1, p ~ n^beta), compute exactly:

  M           = max_{b != 0} | sum_{x in mu_n} e_p(b*x) |      (the prize object, off-DC peak)
  floor       = sqrt((N*d - d^2)/(N-1))   with N=p, d=n         (Plancherel floor, _DoorIVSubgroupOffDCPeakFloor)
  ceil        = sqrt(N*d - d^2)                                 (l2-completion ceiling, _DoorIVSubgroupOffDCPeakBracket)
  prize       = sqrt(n*log(p/n))                                (the CORE target, up to abs constant C)

Report M/floor, M/ceil, M/prize, and M/sqrt(n) across instances.  Question the brief asks:
is the actual peak HUGGING the floor (slack a non-sum-product method could exploit -> crack)
or is it up near the ceiling (no slack, wall confirmed)?  And how does M track the prize sqrt(n*log)?

NO claim is formalized from this; it is an empirical Lane-1 characterization.  Probe-first.
"""
import cmath
import math


def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True


def subgroup_of_order_n(p, n):
    """Return the multiplicative subgroup mu_n of F_p* of order n (n | p-1), as a list of ints."""
    # find a generator g of F_p*
    # factor p-1
    def factorize(m):
        fac = {}
        d = 2
        while d * d <= m:
            while m % d == 0:
                fac[d] = fac.get(d, 0) + 1
                m //= d
            d += 1
        if m > 1:
            fac[m] = fac.get(m, 0) + 1
        return fac

    order = p - 1
    fac = factorize(order)
    g = 2
    while g < p:
        ok = True
        for q in fac:
            if pow(g, order // q, p) == 1:
                ok = False
                break
        if ok:
            break
        g += 1
    # generator of mu_n: g^((p-1)/n)
    h = pow(g, (p - 1) // n, p)
    sub = []
    cur = 1
    for _ in range(n):
        sub.append(cur)
        cur = (cur * h) % p
    return sub


def offDC_peak(p, sub):
    """M = max_{b=1..p-1} | sum_{x in sub} e_p(b*x) |, computed exactly via complex exp."""
    n = len(sub)
    best = 0.0
    twopi_over_p = 2.0 * math.pi / p
    for b in range(1, p):
        s = 0j
        for x in sub:
            s += cmath.exp(1j * twopi_over_p * ((b * x) % p))
        m = abs(s)
        if m > best:
            best = m
    return best


def main():
    # prize-regime instances: n = 2^a, find prime p with n | p-1, p ~ n^beta (beta ~ 2..4)
    print(f"{'n':>5} {'p':>9} {'beta':>5} {'M':>9} {'floor':>9} {'ceil':>9} "
          f"{'M/floor':>8} {'M/ceil':>8} {'M/sqrt(n)':>10} {'prize':>9} {'M/prize':>8}")
    results = []
    for a in range(3, 8):  # n = 8 .. 128
        n = 2 ** a
        for beta_target in (2.0, 2.5, 3.0):
            target_p = int(n ** beta_target)
            # find smallest prime p >= target_p with n | p-1
            # p = 1 + k*n
            k = (target_p - 1 + n - 1) // n
            if k < 1:
                k = 1
            p = 1 + k * n
            tries = 0
            while not is_prime(p) and tries < 20000:
                p += n
                tries += 1
            if not is_prime(p):
                continue
            if p > 80000:  # keep the exact O(p*n) peak scan affordable
                continue
            sub = subgroup_of_order_n(p, n)
            M = offDC_peak(p, sub)
            N = p
            d = n
            floor = math.sqrt((N * d - d * d) / (N - 1))
            ceil = math.sqrt(N * d - d * d)
            beta = math.log(p) / math.log(n)
            prize = math.sqrt(n * max(math.log(p / n), 1e-9))
            row = (n, p, beta, M, floor, ceil, M / floor, M / ceil,
                   M / math.sqrt(n), prize, M / prize)
            results.append(row)
            print(f"{n:>5} {p:>9} {beta:>5.2f} {M:>9.3f} {floor:>9.3f} {ceil:>9.3f} "
                  f"{M/floor:>8.3f} {M/ceil:>8.3f} {M/math.sqrt(n):>10.3f} "
                  f"{prize:>9.3f} {M/prize:>8.3f}")

    if results:
        import statistics
        print("\nSUMMARY (over instances):")
        mf = [r[6] for r in results]
        mc = [r[7] for r in results]
        msn = [r[8] for r in results]
        mp = [r[10] for r in results]
        print(f"  M/floor   : min={min(mf):.3f} max={max(mf):.3f} mean={statistics.mean(mf):.3f}")
        print(f"  M/ceil    : min={min(mc):.3f} max={max(mc):.3f} mean={statistics.mean(mc):.3f}")
        print(f"  M/sqrt(n) : min={min(msn):.3f} max={max(msn):.3f} mean={statistics.mean(msn):.3f}")
        print(f"  M/prize   : min={min(mp):.3f} max={max(mp):.3f} mean={statistics.mean(mp):.3f}")
        print("\nINTERPRETATION:")
        print("  M/floor near 1  => peak HUGS the Plancherel floor (potential door-iv slack to exploit).")
        print("  M/ceil near 1   => peak near l2-completion ceiling (no slack, wall confirmed).")
        print("  M/prize bounded => CORE-consistent on these (small) instances; NOT a proof (n small,")
        print("                     beta below prize beta~4-5, and abs constant C absorbs O(1)).")


if __name__ == "__main__":
    main()
