"""
C038 attack: "Folding buys an additive-energy reduction — the (d+1)-orbit fold is
the multiplicative analogue of the 2-adic char-sum descent M(n)^2 <= 2 M(n/2)^2;
W-subspace (list) and W-BGK (char-sum) may SHARE one deflation mechanism."

attack_plan (verbatim from C038.json): compute
  (i)  the orbit-fold deflation factor (PROVEN in tree = exactly d+1, lossless), and
  (ii) the char-sum 2-adic descent ratio R = M(n)^2 / M(n/2)^2,
across proper-subgroup primes (mu_n a PROPER subgroup, n << sqrt q, q ~ n^beta, beta~4-5),
and test whether both 'track (d+1)=2 with the SAME sub-maximal correction'.
 - corrections coincide  -> ONE deflation mechanism.
 - corrections diverge    -> 'two walls' framing CONFIRMED.

M(n) := max_{b!=0} |sum_{y in mu_n} e_q(b y)|  (Gauss-period sup-norm = non-principal Paley eigenvalue).
The fold x->x^2 maps mu_n -> mu_{n/2} two-to-one; its orbit size is 2 = d+1.

Implementation: exact subgroup, numpy for the period max. We use proper-subgroup primes
that keep q (=> work ~ q) tractable while still having n << sqrt q (q >> n^2).
"""
import math
import numpy as np

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def prime_factors(m):
    fac = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fac.add(d); m //= d
        d += 1
    if m > 1: fac.add(m)
    return fac

def find_primes(n, q_lo, q_hi, count):
    """proper-subgroup primes q = 1 mod n in [q_lo, q_hi] (need q >> n^2 for n<<sqrt q)."""
    out = []
    k0 = (q_lo - 1)//n + 1
    q = k0*n + 1
    while q <= q_hi and len(out) < count:
        if is_prime(q):
            out.append(q)
        q += n
    return out

def subgroup_generator(q, n):
    # generator g of F_q^*
    m = q-1
    fac = prime_factors(m)
    g = 2
    while True:
        if all(pow(g, m//p, q) != 1 for p in fac):
            break
        g += 1
    return pow(g, (q-1)//n, q)   # generator of mu_n

def gauss_period_supnorm(q, n):
    """M(n) = max_{b!=0} |sum_{y in mu_n} e_q(b y)|.
    Period(b) only depends on coset b*mu_n; but enumerating ALL b in 1..q-1 and taking
    the max is correct and simplest (the max over reps = max over all b). Work ~ q*... ;
    we vectorize with numpy: for each b, sum exp(2pi i b*mu/q). We loop b but vectorize over mu."""
    h = subgroup_generator(q, n)
    mu = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        mu[i] = x
        x = (x*h) % q
    w = 2*math.pi/q
    best = 0.0
    # iterate b over 1..q-1 but only need one per coset; cosets = (q-1)/n of them.
    # To avoid building a size-q 'seen' set, just iterate all b (correct, max unaffected).
    # vectorize: process b in chunks
    chunk = 200000
    b = 1
    while b < q:
        bs = np.arange(b, min(b+chunk, q), dtype=np.int64)
        # phases[k, j] = (bs[k]*mu[j]) % q
        ph = (np.outer(bs, mu) % q).astype(np.float64) * w
        s = np.exp(1j*ph).sum(axis=1)
        m = np.abs(s).max()
        if m > best: best = m
        b += chunk
    return best

def main():
    print("="*108)
    print("C038: orbit-fold deflation (EXACT factor d+1=2, lossless) vs char-sum 2-adic descent R=M(n)^2/M(n/2)^2")
    print("="*108)
    # proper-subgroup primes; keep q tractable (work ~ q). n<<sqrt q means q >> n^2.
    # use q ~ a few * n^3 .. n^4 so still PROPER subgroup with n<<sqrt q, but q small enough to run.
    plan = {
        8:   (8000,   40000,  3),
        16:  (70000,  200000, 3),
        32:  (1_000_000, 2_500_000, 2),
        64:  (16_000_000, 30_000_000, 1),
    }
    print(f"\n{'n':>5} {'q':>11} {'beta':>6} {'M(n)':>9} {'M(n/2)':>9} {'R=Mn^2/Mn2^2':>13} "
          f"{'orbit':>6} {'R/orbit':>8} {'2*log(q/n)/log(2q/n)':>20} {'M/sqrt(n*log(q/n))':>18}")
    rows = []
    for n, (qlo, qhi, cnt) in plan.items():
        for q in find_primes(n, qlo, qhi, cnt):
            beta = math.log(q)/math.log(n)
            if q < 4*n*n:   # enforce n << sqrt q
                continue
            Mn  = gauss_period_supnorm(q, n)
            Mn2 = gauss_period_supnorm(q, n//2)
            R = (Mn*Mn)/(Mn2*Mn2)
            orbit = 2
            bgk_pred = 2*math.log(q/n)/math.log(2*q/n)
            bgk_norm = Mn/math.sqrt(n*math.log(q/n))
            rows.append((n,q,beta,Mn,Mn2,R,bgk_pred,bgk_norm))
            print(f"{n:>5} {q:>11} {beta:>6.2f} {Mn:>9.3f} {Mn2:>9.3f} {R:>13.4f} "
                  f"{orbit:>6} {R/orbit:>8.4f} {bgk_pred:>20.4f} {bgk_norm:>18.4f}")

    print("\n" + "-"*108)
    print("ANALYSIS")
    print("-"*108)
    print("Folding side (FoldingTransferNoGo.lean, PROVEN axiom-clean): the deflation factor is")
    print("EXACTLY d+1 = 2 (the orbit size), a LOSSLESS combinatorial inequality")
    print("  (d+1)*foldedAgree <= plainAgree,  converse fails MAXIMALLY")
    print("  (one corruption/orbit: plainAgree = N*d, foldedAgree = 0).")
    print("So on the folding side, R_orbit = 2 EXACTLY and the 'slack' is purely structural/integer.")
    print()
    print("Char-sum side: R = M(n)^2/M(n/2)^2 measured above. Two competing predictions:")
    print("  * C038 claim:  R = 2 (orbit) +/- a 'matching sub-maximal correction'.")
    print("  * BGK/Paley:   M(n) ~ sqrt(n*log(q/n)) (the open square-root cancellation),")
    print("                 so R ~ 2*log(q/n)/log(2q/n)  -- an ANALYTIC log-ratio, NOT 2,")
    print("                 q- and n-DEPENDENT, with NO relation to the integer orbit factor.")
    print()
    # Decisive comparison: which prediction does R match?
    print("Match test (smaller |R - pred| wins):")
    print(f"{'n':>5} {'q':>11} {'R':>9} {'|R-2| (orbit)':>14} {'|R-BGK|':>10} {'winner':>10}")
    orbit_wins = bgk_wins = 0
    for (n,q,beta,Mn,Mn2,R,bgk_pred,bgk_norm) in rows:
        d_orbit = abs(R-2.0)
        d_bgk = abs(R-bgk_pred)
        win = "ORBIT" if d_orbit < d_bgk else "BGK"
        if d_orbit < d_bgk: orbit_wins += 1
        else: bgk_wins += 1
        print(f"{n:>5} {q:>11} {R:>9.4f} {d_orbit:>14.4f} {d_bgk:>10.4f} {win:>10}")
    print(f"\nORBIT-prediction wins: {orbit_wins}   BGK-prediction wins: {bgk_wins}")
    print()
    print("Also report M(n)/sqrt(n log(q/n)): if STABLE across n (not -> 1, not growing as M/sqrt(n)),")
    print("M(n) lives on the BGK sqrt(n log) law, i.e. the char-sum 'descent' is the open BGK")
    print("cancellation, NOT a lossless orbit fold.")

if __name__ == "__main__":
    main()
