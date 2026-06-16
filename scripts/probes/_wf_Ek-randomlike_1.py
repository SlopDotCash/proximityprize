#!/usr/bin/env python3
"""_wf_Ek-randomlike_1.py  (#407 prize -- Ek-randomlike replicate 2/2, INDEPENDENT method)

QUESTION (settle the swarm back-and-forth):
  Is the 2r-th additive energy E_r(mu_n) RANDOM-LIKE in the prize CONSTANT-INDEX regime?
  Concretely, with the MEAN (b=0) term removed:
        Eex_r := E_r(mu_n) - n^{2r}/p          (the off-mean / "noise" energy)
  is it bounded by the char-0 Gaussian diagonal  C^r * r! * n^r  with C BOUNDED as n grows
  at FIXED index m = (p-1)/n?

  If yes (sub-Gaussian to depth r~log q), the moment arrow  B <= (q E_r)^{1/2r}  closes the prize
  bound B <= sqrt(n log q).  If C grows in n or r, the moment route provably overshoots.

WHY n^{2r}/p AND NOT (2r-1)!! n^r AS BASELINE:
  E_r = (1/p) sum_b |S(b)|^{2r}.  The b=0 term is S(0)=n so contributes n^{2r}/p EXACTLY.
  That is the "mean/diagonal" mass and is NOT noise -- a truly random S would have E[|S|^2]~n off-0.
  The off-mean energy  Eex_r = E_r - n^{2r}/p = (1/p) sum_{b!=0} |S(b)|^{2r}  is what the moment
  method actually controls (B = max_{b!=0}|S(b)|).  The random-like target for THIS is
  Eex_r ~ c^r r! n^r  (Gaussian moments of a complex sub-Gaussian of variance ~n).
  We report  ratio_r := Eex_r / (r! n^r)   and  c_r := ratio_r^{1/r}  (per-moment constant).

INDEPENDENT METHOD (differs from twin probe_moment_growth_law_407.py):
  - twin uses prime_1_mod_n_near(n^3) (SPARSE p~n^3) and FFT-of-indicator.
  - THIS probe FIXES the index m=(p-1)/n to a small constant {8,16,32} (the structural prize
    feature: m large there, but the random-like LAW is index-driven, so small fixed m is the
    clean stress test) and uses TWO independent energy engines:
       (A) exact integer convolution via repeated np.convolve of the count-vector over Z_p
           (E_r = sum of squared r-fold convolution counts), NO floating FFT -- exact integers;
       (B) FFT-of-indicator (float) cross-check.
    Agreement of (A) and (B) certifies the numbers.  We push n as far as p (~m*n) FFT allows.
"""
import numpy as np
import sympy
import math

def subgroup_fixed_index(n, m_target):
    """smallest prime p = m*n+1 with m >= m_target; return (p, m, sorted mu_n as list)."""
    m = m_target
    while True:
        p = m * n + 1
        if sympy.isprime(p):
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            H = sorted(pow(z, j, p) for j in range(n))
            assert len(set(H)) == n
            return p, m, H
        m += 1

def energy_exact_convolve(p, H, rmax):
    """EXACT E_r for r=1..rmax via repeated cyclic convolution mod p, NO float cancellation.
       cur[b] = #{r-tuples of mu_n summing to b mod p}; E_r = sum_b cur[b]^2.
       The COUNTS cur[b] stay within int64 (max ~ n^r/p * O(1), << 9.2e18 in our range),
       so np.convolve(int64) is exact and fast.  Only the SUM OF SQUARES is promoted to
       Python big-int (sum cur[b]^2 reaches ~10^34 at r=7) -- done by summing int(v)*int(v)
       over the int64 array.  We assert no int64 overflow occurred in the convolution.
       This avoids the catastrophic float cancellation of E_r - n^{2r}/p (both ~10^23, diff ~10^12)."""
    n = len(H)
    INT64MAX = int(np.iinfo(np.int64).max)
    base = np.zeros(p, dtype=np.int64)
    for x in H:
        base[x] += 1
    res = {}
    cur = base.copy()
    for r in range(1, rmax + 1):
        # exact big-int sum of squares from the int64 count vector
        res[r] = sum(int(v) * int(v) for v in cur.tolist())
        # SANITY: total mass must equal n^r EXACTLY -- catches any silent int64 wrap (overflow)
        total = sum(int(v) for v in cur.tolist())
        if total != n ** r:
            # the int64 convolution overflowed at this depth; drop the corrupted r and stop.
            del res[r]
            break
        if r < rmax:
            # will the NEXT convolution overflow int64? max linear-conv term <= n^{r+1} (mass bound).
            if n ** (r + 1) >= INT64MAX:
                break
            lin = np.convolve(cur, base)          # int64 linear convolution (exact while in range)
            wrap = lin[:p].copy()
            wrap[:p-1] += lin[p:]                  # fold the cyclic wrap-around (exact int64)
            cur = wrap
    return res

def energy_fft(p, H, rmax):
    """float E_r via FFT-of-indicator cross-check."""
    f = np.zeros(p)
    for x in H:
        f[x] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S) ** 2
    res = {}
    for r in range(1, rmax + 1):
        res[r] = float(np.sum(a2 ** r))   # = sum_b |S(b)|^{2r}; E_r = this / p
    # B (max off-0)
    a2b = a2.copy(); a2b[0] = 0.0
    B = float(np.sqrt(np.max(a2b)))
    return res, B

def energy_bruteforce(p, H, rmax):
    """O(n^r) ground-truth: E_r = #{(x_1..x_r,y_1..y_r) in mu^2r : sum x = sum y}
       = sum_b count_r(b)^2 with count_r built by exhaustive product (tiny n only)."""
    from itertools import product
    from collections import Counter
    res = {}
    for r in range(1, rmax + 1):
        c = Counter()
        for tup in product(H, repeat=r):
            c[sum(tup) % p] += 1
        res[r] = sum(v * v for v in c.values())
    return res

def main():
    fac = [math.factorial(r) for r in range(0, 14)]

    # ---- ground-truth certification: exact-convolve == brute-force product count ----
    print("="*100)
    print("ENGINE CERTIFICATION (exact-convolve vs O(n^r) brute-force product count):")
    print("="*100)
    for (n, mt) in ((8, 9), (16, 12)):
        p, m, H = subgroup_fixed_index(n, mt)
        ec = energy_exact_convolve(p, H, 4)
        bf = energy_bruteforce(p, H, 4)
        ok = all(ec[r] == bf[r] for r in range(1, 5))
        print(f" n={n} p={p}: convolve {[ec[r] for r in range(1,5)]}")
        print(f"          brute    {[bf[r] for r in range(1,5)]}  -> EXACT MATCH: {ok}")
    print()

    print("="*100)
    print("CONSTANT-INDEX random-like test.  Eex_r = E_r - n^{2r}/p (off-mean energy);")
    print("  ratio_r = Eex_r/(r! n^r),  c_r = ratio_r^{1/r}  (bounded c_r in n AND r => random-like).")
    print("="*100)

    for m_target in (8, 16, 32):
        print(f"\n############### FIXED INDEX  m >= {m_target}  (p = m*n + 1) ###############")
        header = f"{'n':>5} {'m':>5} {'p':>10} | " + " ".join(f"c_{r}".rjust(7) for r in range(2, 6)) \
                 + " | " + f"{'B':>9} {'B/sqrtn':>8} {'B/sqrt(nLogq)':>12} {'AB-agree':>9}"
        print(header)
        # push n: FFT/conv length p ~ m*n; keep p under ~ 12M for memory/speed
        for a in range(3, 11):       # n = 8 .. 1024
            n = 1 << a
            if m_target * n > 13_000_000:   # cap p length
                break
            p, m, H = subgroup_fixed_index(n, m_target)
            if p > 13_000_000:
                break
            rmax = 5
            # exact integer engine
            raw_exact = energy_exact_convolve(p, H, rmax)   # raw_exact[r] = sum cur^2 = E_r (already, since E_r=sum counts^2)
            # NOTE: E_r as defined = (1/p) sum_b |S(b)|^{2r} = sum_b (#r-tuples to b)^2  -- these are EQUAL (Parseval).
            E_exact = raw_exact
            # fft engine
            raw_fft, B = energy_fft(p, H, rmax)
            E_fft = {r: raw_fft[r] / p for r in raw_fft}
            # agreement on E_2 (relative)
            agree = abs(E_exact[2] - E_fft[2]) / max(1.0, E_exact[2])
            cs = []
            for r in range(2, 6):
                Er = E_exact[r]                       # exact big int
                # Eex_r = E_r - n^{2r}/p, computed EXACTLY as (p*E_r - n^{2r})/p to dodge float cancel
                Eex_num = p * Er - n ** (2 * r)        # exact big int
                Eex = Eex_num / p                      # float of an exact rational, no cancellation
                if Eex <= 0:
                    cs.append(float('nan')); continue
                ratio = Eex / (fac[r] * n ** r)
                c_r = ratio ** (1.0 / r)
                cs.append(c_r)
            logq = math.log2(p)
            bsn = B / math.sqrt(n)
            bsl = B / math.sqrt(n * math.log2(p / n)) if p > n else float('nan')
            print(f"{n:>5} {m:>5} {p:>10} | " + " ".join(f"{c:7.3f}" for c in cs) +
                  f" | {B:9.2f} {bsn:8.3f} {bsl:12.3f} {agree:9.1e}")

    print("\n" + "="*100)
    print("GROWTH IN r AT LARGE FIXED-INDEX n (does c_r grow with r at one n? deep-moment test):")
    print("="*100)
    # push n to 1024/2048/4096 at small fixed index so p~m*n stays FFT/conv-feasible
    for (m_target, n) in ((8, 1024), (8, 2048), (8, 4096), (16, 1024), (16, 2048)):
        p, m, H = subgroup_fixed_index(n, m_target)
        if p > 80_000_000:
            continue
        rmax = 8
        if n ** rmax > 0:  # convolution cost is ~ rmax * p, fine
            pass
        E_exact = energy_exact_convolve(p, H, rmax)
        print(f"\n m>={m_target}: n={n} p={p} (logq={math.log2(p):.2f})")
        print(f"   {'r':>3} {'E_r':>20} {'n^{2r}/p':>20} {'Eex_r(EXACT)':>20} {'ratio=Eex/(r!n^r)':>20} {'c_r':>8}")
        for r in range(2, rmax + 1):
            if r not in E_exact:
                print(f"   {r:>3}  (int64 conv limit reached -- exact only to r={max(E_exact)})")
                break
            Er = E_exact[r]                          # exact big int
            mean_term_f = (n ** (2 * r)) / p         # for display only
            Eex_num = p * Er - n ** (2 * r)          # EXACT integer numerator of Eex*p
            Eex = Eex_num / p                         # float of exact rational (no cancellation)
            if Eex <= 0:
                ratio = float('nan'); c_r = float('nan')
            else:
                ratio = Eex / (fac[r] * n ** r)
                c_r = ratio ** (1.0 / r)
            print(f"   {r:>3} {float(Er):>20.3e} {mean_term_f:>20.3e} {Eex:>20.3e} {ratio:>20.4f} {c_r:>8.4f}")

    print("\n" + "="*100)
    print("DEEP r AT SMALL FIXED-INDEX n (exact BIG-INT convolution, reach r ~ log q to probe the")
    print("actual moment-arrow depth; does c_r stay bounded all the way to depth ~ log q?):")
    print("="*100)
    for (m_target, n, rmax) in ((8, 16, 12), (8, 32, 11), (16, 32, 11)):
        p, m, H = subgroup_fixed_index(n, m_target)
        # exact big-int convolution engine (object dtype) -- affordable since p ~ m*n is small
        base = np.zeros(p, dtype=object)
        for x in H:
            base[x] = int(base[x]) + 1
        cur = base.copy()
        rows = []
        for r in range(1, rmax + 1):
            Er = sum(int(v) * int(v) for v in cur)              # exact
            assert sum(int(v) for v in cur) == n ** r           # mass check
            rows.append((r, Er))
            if r < rmax:
                lin = np.convolve(cur, base)                    # exact bigint conv
                wrap = lin[:p].copy(); wrap[:p-1] = wrap[:p-1] + lin[p:]
                cur = wrap
        print(f"\n m>={m_target}: n={n} p={p} (log2 q={math.log2(p):.2f}, target depth r~log2 q={math.log2(p):.0f})")
        print(f"   {'r':>3} {'Eex_r(EXACT)':>22} {'ratio=Eex/(r!n^r)':>20} {'c_r':>8}")
        for (r, Er) in rows:
            if r < 2:
                continue
            Eex = (p * Er - n ** (2 * r)) / p
            if Eex <= 0:
                print(f"   {r:>3} {Eex:>22.3e}  (Eex<=0: subgroup MORE concentrated than uniform here)")
                continue
            ratio = Eex / (fac[r] * n ** r)
            c_r = ratio ** (1.0 / r)
            print(f"   {r:>3} {Eex:>22.3e} {ratio:>20.4f} {c_r:>8.4f}")

    print("\n" + "="*100)
    print("MOMENT-ARROW REALITY CHECK (the actual gate): does  min_r (p*E_r)^{1/2r}  reach the")
    print("clean law sqrt(n*log2(p/n)) using these EXACT moments?  This is what random-like must buy.")
    print("="*100)
    print(f"{'n':>5} {'m':>4} {'p':>8} | {'trueB':>7} {'sqrt(nLogq)':>11} | {'arrowmin':>8} {'@r':>3} {'arrow/trueB':>11} {'arrow/sqrtnLogq':>14}")
    for (m_target, n) in ((8, 16), (8, 32), (16, 32), (8, 64), (8, 128), (8, 256), (8, 512)):
        p, m, H = subgroup_fixed_index(n, m_target)
        # true B
        f = np.zeros(p);
        for x in H: f[x] = 1.0
        a2 = np.abs(np.fft.fft(f)) ** 2; a2[0] = 0.0
        B = float(np.sqrt(np.max(a2)))
        # exact moments via int64 conv (stops where it must)
        rmax_try = 14
        E = energy_exact_convolve(p, H, rmax_try)
        L = math.log2(p / n); snl = math.sqrt(n * L)
        best = None; bestr = None
        for r in sorted(E):
            bound = (p * E[r]) ** (1.0 / (2 * r))
            if best is None or bound < best:
                best, bestr = bound, r
        print(f"{n:>5} {m:>4} {p:>8} | {B:7.2f} {snl:11.2f} | {best:8.2f} {bestr:3d} {best/B:11.3f} {best/snl:14.3f}")

    print("\n" + "="*100)
    print("READ:")
    print(" - c_r BOUNDED across BOTH growing n (fixed m) and growing r => RANDOM-LIKE structure of E_r.")
    print(" - BUT the moment ARROW (p*E_r)^{1/2r} is what gates the prize: if arrow/sqrt(nLogq) ~ const")
    print("   it closes; if arrow/sqrt(nLogq) GROWS in n the moment method overshoots despite random-like E_r.")
    print(" - c_r grows in n => sqrt(log n) overshoot in B.   c_r grows in r => deep-moment wall stands.")
    print("="*100)

if __name__ == "__main__":
    main()
