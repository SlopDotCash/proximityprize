#!/usr/bin/env python3
"""
S6 bounded-Betti Deligne route probe (#444).

Object: V_r = { x in (mu_n)^{2r} : sum_{i} eps_i x_i = 0 },  eps_i = +-1.
E_r(mu_n) = #{ (a_1..a_r, b_1..b_r) in mu_n^{2r} : sum a = sum b }
          = #{ x in mu_n^{2r} : sum_{i<=r} x_i - sum_{i>r} x_i = 0 }   (one sign pattern)
This is the additive energy of order r of the multiplicative subgroup mu_n of F_p*.

Wick = (2r-1)!! * n^r   (char-0 Gaussian / Lam-Leung ceiling, the target form).

We compute, EXACTLY (full enumeration is too big for big n; we use the FFT/convolution
count over the additive group F_p, which is exact):
  E_r^{Fp}(n) = (1/p) * sum_{b in F_p} |S_b|^{2r},   S_b = sum_{x in mu_n} e_p(b x)
            ... NO. The exact identity is:
  E_r = #{x in mu_n^{2r}: sum eps_i x_i = 0 in F_p}
      = (1/p) sum_{b=0}^{p-1} ( sum_{x in mu_n} e_p(b x) )^r * conj(...)^r
  with the r/r sign split:
  E_r = (1/p) sum_b |T_b|^{2r}, where T_b = sum_{x in mu_n} e_p(b x).   (exact, T_0 = n)

The char-0 ("ideal Gaussian / Lam-Leung") value E_r^{c0} is the SAME count but in char 0,
i.e. solutions to sum eps_i z_i = 0 with z_i ranging over the COMPLEX n-th roots of unity.
We compute E_r^{c0} by the same FFT identity over a LARGE prime P >> n^{2r} (so no wraparound
== char-0 count), OR directly by combinatorial recursion. We use a huge prime as ground truth.

spur_r(p) = E_r^{Fp} - E_r^{c0}  >= 0  (one-sided inflation; char-p has EXTRA solutions
            from sparse relations that vanish only mod p).

K_eff vs Wick     = (E_r^{Fp} / Wick)^{1/r}
K_eff vs char-0   = (E_r^{Fp} / E_r^{c0})^{1/r}

S6 CLAIM to test:
 (a) spur_r(p) = 0 EXACTLY at generic prize-shaped p (beta = log_n p ~ 4), for r up to ~ln p.
 (b) the Betti/Deligne main-term + error: E_r = E_r^{c0} + (error <= TotalBetti * p^{power}),
     TotalBetti <= C(2r,r) <= 4^r INDEPENDENT of n. If TRUE, spur <= 4^r * p^{power} and
     when divided into Wick gives K = O(1).
 The CRUX: does spur, when nonzero, scale like 4^r (n-independent) or like a power of n
     (= the wall hiding in the Betti number)?
"""

import cmath
import math
from itertools import product

def primitive_root(p):
    # find a generator of F_p^*
    phi = p - 1
    factors = []
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")

def mu_n(p, n):
    """The order-n subgroup of F_p^* (n | p-1). Returns sorted list of residues."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # element of order n
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x * h) % p
    assert len(S) == n, (p, n, len(S))
    return sorted(S)

def energy_r_charp(p, S, r):
    """E_r(S) over F_p, exact, via additive-character FFT:
       E_r = (1/p) sum_b |T_b|^{2r}, T_b = sum_{x in S} e_p(b x).
       Exact in integer arithmetic is hard with complex; use float but it IS exact-valued
       (E_r is an integer; we round). For correctness check we also do direct count for small."""
    twopi_over_p = 2.0 * math.pi / p
    total = 0.0
    for b in range(p):
        T = 0.0 + 0.0j
        ang0 = twopi_over_p * b
        for x in S:
            T += cmath.exp(1j * ang0 * x)
        total += (abs(T) ** 2) ** r
    return total / p

def energy_r_direct(p, S, r):
    """Direct exact count for small cases: #{a in S^r, b in S^r: sum a == sum b mod p}.
       Uses convolution of the r-fold sumset distribution."""
    # distribution of sum of r elements of S mod p
    from collections import defaultdict
    dist = defaultdict(int)
    dist[0] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for x in S:
                nd[(s + x) % p] += c
        dist = nd
    # E_r = sum_s dist[s]^2
    return sum(c * c for c in dist.values())

def energy_r_char0(n, r):
    """Char-0 order-r additive energy of the n-th roots of unity (complex), EXACT integer.
       = #{ a in mu_n^r, b in mu_n^r : sum a = sum b in C }.
       mu_n complex roots: e^{2pi i k/n}. Sum equality in C is a Z-linear relation.
       We compute it via FFT over a prime P >> n^{2r} so NO wraparound -> equals char-0 count.
       But that's circular. Instead: char-0 count = exact integer; for moderate n,r we use a
       large prime ground truth and verify stability across two large primes."""
    raise NotImplementedError

def energy_r_char0_via_bigprime(n, r, bigprimes):
    """Ground-truth char-0 E_r: compute over several primes P with P > (n)^{?} huge and
       P = 1 mod n (so mu_n exists), and confirm the count is STABLE (no mod-P collisions).
       The stable value = the char-0 count."""
    vals = []
    for P in bigprimes:
        S = mu_n(P, n)
        # direct count (exact integer) via convolution
        v = energy_r_direct(P, S, r)
        vals.append(v)
    return vals

def find_prime_1_mod_n(n, lo):
    """smallest prime >= lo with p = 1 mod n."""
    p = lo + ((1 - lo) % n)
    if p < lo:
        p += n
    while True:
        if is_prime(p):
            return p
        p += n

def is_prime(m):
    if m < 2:
        return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0:
            return m == q
    d = m - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x == 1 or x == m - 1:
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True

def wick(n, r):
    # (2r-1)!! * n^r
    dd = 1
    for k in range(1, 2*r, 2):
        dd *= k
    return dd * (n ** r)

def beta_of(p, n):
    return math.log(p) / math.log(n)

print("="*100)
print("S6 PROBE: bounded-Betti Deligne route for E_r(mu_n) <= K^r * Wick")
print("="*100)

# ground-truth char-0 E_r: use two huge primes p = 1 mod n, p >> n^{2r}, confirm stable.
def char0_energy(n, r):
    # need P > n^{2r} roughly (max possible sum coincidence magnitude); use P > n^{2r+2}
    target = (n ** (2*r)) * 100 + 10**6
    P1 = find_prime_1_mod_n(n, target)
    P2 = find_prime_1_mod_n(n, P1 + 1)
    v1 = energy_r_direct(P1, mu_n(P1, n), r)
    v2 = energy_r_direct(P2, mu_n(P2, n), r)
    if v1 != v2:
        return None, (P1, v1, P2, v2)  # not stable => char-0 not yet captured
    return v1, (P1, P2)

print("\n--- Part A: char-0 ground truth (stability across two huge primes p>>n^{2r}) ---")
for n in (8, 16):
    for r in (2, 3, 4):
        v, info = char0_energy(n, r)
        w = wick(n, r)
        if v is None:
            print(f"  n={n} r={r}: char-0 UNSTABLE {info}")
        else:
            ratio = v / w
            keff = ratio ** (1.0/r)
            print(f"  n={n:3d} r={r}: E_r^c0={v:>12d}  Wick={w:>14d}  E/Wick={ratio:.4f}  K_eff(c0/Wick)={keff:.4f}")

print("\n--- Part B: spur_r(p) = E_r^{Fp} - E_r^{c0} at GENERIC prize-shaped p (beta~4) and STRUCTURED p ---")
print("    (generic: smallest p=1 mod n with p ~ n^4 ;  structured: Fermat-like / small p=1 mod n)")

def smallest_prime_1modn_above(n, lo):
    return find_prime_1_mod_n(n, lo)

for n in (16, 32):
    print(f"\n  n = {n}:")
    # char-0 baseline
    # generic prize-shaped prime: p ~ n^4
    p_gen = smallest_prime_1modn_above(n, n**4)
    # structured-ish: a smaller p = 1 mod n (beta ~ 2-3), to expose sub-prize artifact
    p_str = smallest_prime_1modn_above(n, n**2)
    for label, p in (("beta~2 (structured/sub-prize)", p_str), ("beta~4 (generic prize)", p_gen)):
        S = mu_n(p, n)
        b = beta_of(p, n)
        print(f"    p={p}  ({label}, beta={b:.2f})")
        for r in (2, 3, 4):
            Ep = energy_r_direct(p, S, r)
            c0, _ = char0_energy(n, r)
            spur = Ep - c0 if c0 is not None else None
            w = wick(n, r)
            kfp = (Ep / w) ** (1.0/r)
            if c0 is not None and c0 > 0:
                kc0 = (Ep / c0) ** (1.0/r)
                print(f"       r={r}: E_Fp={Ep:>12d}  E_c0={c0:>12d}  spur={spur:>10d}  "
                      f"spur/E_c0={spur/c0:8.5f}  K(Fp/Wick)={kfp:.4f}  K(Fp/c0)={kc0:.4f}")
            else:
                print(f"       r={r}: E_Fp={Ep:>12d}  K(Fp/Wick)={kfp:.4f}")
