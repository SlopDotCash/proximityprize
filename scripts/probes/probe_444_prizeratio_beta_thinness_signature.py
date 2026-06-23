#!/usr/bin/env python3
# DOOR-IV Lane-1 thinness-signature follow-up to the creep-saturation probe (push 6f2e557a2).
# The creep probe FIXED beta~4 and found R(n)=M/sqrt(2n log p) saturates ~0.78. The prize bound is
# M <= C*sqrt(n*log(p/n)); its NATURAL normalization is R'(n) = M/sqrt(n*log(p/n)) (NOT sqrt(2n log p)).
# QUESTION (thinness-essential, per HARD RULE 3): at FIXED n, as beta = log_n(p) grows (the subgroup gets
# THINNER relative to F_p*), does the prize-normalized ratio R'(n,beta) stay BOUNDED (prize-consistent,
# the sqrt(log(p/n)) denominator absorbs the growth) or BLOW UP (thinness defeats the bound)?
# If R' is FLAT/bounded across the thin beta window while a thickness-monotone proxy is not, that is the
# thinness signature the prize needs. Probe-first; reproducible; PROPER thin mu_n < F_p*, NEVER n=q-1.
import math, numpy as np

def isp(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def proot(p):
    m = p-1; fs = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    g = 2
    while not all(pow(g, (p-1)//f, p) != 1 for f in fs): g += 1
    return g

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def good_prime_near(n, target, cap):
    mu2 = int(round(math.log2(n)))
    p = target + ((1 + n - target % n) % n)
    while p < cap:
        if p % n == 1 and isp(p) and v2(p-1) == mu2:
            return p
        p += n
    return None

def M_of_n(n, p):
    # M = max over coset transversal t_k=(g^n)^k of |sum_{x in mu_n} e_p(t*x)|, vectorized exact.
    g = proot(p); gn = pow(g, n, p); m = (p-1)//n
    z = pow(g, m, p)
    mu = []
    v = 1
    for _ in range(n):
        mu.append(v); v = (v*z) % p
    muu = np.array(mu, dtype=object)
    w = 2.0*math.pi/p
    best = 0.0
    cur = 1
    CH = 200000
    k = 0
    while k < m:
        sz = min(CH, m-k)
        ts = np.empty(sz, dtype=object)
        c = cur
        for i in range(sz):
            ts[i] = c; c = (c*gn) % p
        cur = c
        ph = (ts[:, None] * muu[None, :]) % p
        ang = w * ph.astype(np.float64)
        re = np.cos(ang).sum(axis=1); im = np.sin(ang).sum(axis=1)
        mag = np.sqrt(re*re + im*im)
        j = int(mag.argmax())
        if mag[j] > best: best = float(mag[j])
        k += sz
    return best, m

def main():
    print("# DOOR-IV thinness signature: prize-normalized R'(n,beta)=M/sqrt(n*log(p/n)) vs beta")
    print("# thin mu_n < F_p*, good prime p==1 mod n, v2(p-1)=log2 n, NEVER n=q-1")
    print(f"# {'n':>4} {'beta':>5} {'p':>11} {'M':>9} {'M/sqrt(n)':>10} {'Rprime':>8} {'sqrt(log(p/n))':>14}")
    cap = 1 << 32
    for n in (16, 32, 64):
        rows = []
        for beta in (3.0, 3.5, 4.0, 4.5, 5.0):
            target = int(round(n ** beta))
            if target >= cap:  # keep p < 2^32 for exact uint64; skip too-thin at large n
                continue
            p = good_prime_near(n, target, cap)
            if p is None:
                continue
            b = math.log(p)/math.log(n)
            M, m = M_of_n(n, p)
            lr = math.log(p/n)
            Rp = M/math.sqrt(n*lr)
            rows.append((n, b, p, M, M/math.sqrt(n), Rp, math.sqrt(lr)))
            print(f"  {n:>4} {b:>5.2f} {p:>11} {M:>9.3f} {M/math.sqrt(n):>10.3f} {Rp:>8.4f} {math.sqrt(lr):>14.4f}", flush=True)
        if len(rows) >= 3:
            Rp = [r[5] for r in rows]
            print(f"    -> n={n}: R' range [{min(Rp):.4f}, {max(Rp):.4f}], spread {max(Rp)-min(Rp):.4f}; "
                  f"M/sqrt(n) range [{min(r[4] for r in rows):.3f}, {max(r[4] for r in rows):.3f}]")
        print()
    print("READ: if R'(n,beta)=M/sqrt(n*log(p/n)) stays in a NARROW bounded band as beta grows (thinner)")
    print("      while the bare M/sqrt(n) GROWS, the sqrt(log(p/n)) denominator absorbs the thinness =>")
    print("      prize-consistent thinness-essential normalization. CAVEAT: finite n<=64, p<2^32 caps the")
    print("      thin window; MEASURE not proof; CORE stays OPEN.")

if __name__ == '__main__':
    main()
