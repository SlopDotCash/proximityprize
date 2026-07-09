#!/usr/bin/env python3
"""
probe_444_fkm_conductor_gauss.py -- pin the conductor / Gauss-sum decomposition that decides the
FKM Fourier-stability lead for #444.  (CORRECTED character identity.)

CORRECT identity:  1_{mu_n}(x) = (n/(p-1)) * sum_{chi : chi|_{mu_n} = 1} chi(x)   for x != 0,
where the sum is over the m=(p-1)/n multiplicative characters TRIVIAL on mu_n (the dual of the
quotient F_p^*/mu_n).  [Orthogonality: (1/|mu_n|) sum_{chi triv on mu_n}... no -- 1_{mu_n}(x) =
(|mu_n|/(p-1)) sum_{chi: mu_n <= ker chi} chi(x), since these chi are exactly the characters of the
quotient group of order m, and they detect membership in mu_n.]  Then
  eta_b = sum_{x in mu_n} e_p(bx) = (n/(p-1)) sum_{chi triv on mu_n} sum_{x!=0} chi(x) e_p(bx)
        = (n/(p-1)) sum_{chi triv on mu_n} conj(chi(b)) G(chi),
a SUM OF m=(p-1)/n GAUSS SUMS (each |G(chi)|=sqrt(p) for chi nontrivial, G(chi_0)=-1).

So the l-adic FT of 1_{mu_n} is a sum of m Kummer sheaves -> conductor Theta(m), m=2^128 at prize:
NOT bounded.  FKM/Weil give each |G|=sqrt(p); the sum of m of them must cancel by sqrt(m) to reach
the period scale.  That cancellation IS the Paley/BGK wall; FKM bounded-conductor does not supply it.

Tests (exact, PROPER mu_n):
  (A) verify eta_b = (n/(p-1)) sum_{chi triv on mu_n} conj(chi(b)) G(chi).
  (B) trivial no-cancellation bound: (n/(p-1)) * [ |G(chi_0)|=1  +  (m-1)*sqrt(p) ]
      = (n/(p-1))(1 + (m-1)sqrt(p)) ~ n*sqrt(p)/... ~ n/sqrt(p)*... actually ~ (n/(p-1))*m*sqrt(p)
      = n*m*sqrt(p)/(p-1) = sqrt(p)  (since n*m = p-1).  So the TRIVIAL bound is exactly sqrt(p):
      the m Gauss sums must cancel from sqrt(p) DOWN to the period ~sqrt(n)..n. That is the wall.
  (C) FKM correlation sum (autocorrelation) is self-similar: A_h = p*eta_{-h} (period -> itself).
"""
import math, cmath
from sympy import isprime, primitive_root

def odd_part(m):
    while m % 2 == 0 and m > 0:
        m //= 2
    return m

def prize_prime(n, beta, pmax=10**6):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if isprime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None

def main():
    print("=" * 100)
    print(" #444 FKM conductor test: eta_b = SUM of m=(p-1)/n Gauss sums (conductor Theta(m), m=2^128)")
    print("=" * 100)
    for n, beta in [(4, 4.0), (8, 4.0), (16, 4.0)]:
        p = prize_prime(n, beta, pmax=120000)
        if p is None:
            continue
        g = primitive_root(p)
        m = (p - 1) // n
        dlog = {}
        acc = 1
        for a in range(p - 1):
            dlog[acc] = a; acc = (acc * g) % p
        # characters trivial on mu_n: chi_k(g^a) = exp(2pi i k a / (p-1)) with k a multiple of n
        # (so chi_k(mu_n elt = g^{a*(p-1)/n}) = exp(2pi i k a/n) = 1 iff n | k).  k = n*j, j=0..m-1.
        def chi(j, t):
            k = n * j
            return cmath.exp(2j * math.pi * k * dlog[t % p] / (p - 1))
        def gauss(j):
            return sum(chi(j, t) * cmath.exp(2j * math.pi * t / p) for t in range(1, p))
        G = [gauss(j) for j in range(m)]
        mu = []
        x = 1
        z = pow(g, (p - 1) // n, p)
        for _ in range(n):
            mu.append(x); x = (x * z) % p
        def eta_direct(b):
            return sum(cmath.exp(2j * math.pi * (b * e % p) / p) for e in mu)
        def eta_gauss(b):
            return (n / (p - 1)) * sum(chi(j, b).conjugate() * G[j] for j in range(m))
        maxerr = 0.0; bestM = 0.0
        for b in range(1, min(p, 400)):
            ed = eta_direct(b); eg = eta_gauss(b)
            maxerr = max(maxerr, abs(ed - eg)); bestM = max(bestM, abs(ed))
        gmag = [abs(G[j]) for j in range(1, m)]
        triv = (n / (p - 1)) * (1 + (m - 1) * math.sqrt(p))
        print(f"\nn={n} p={p} m=(p-1)/n={m}: |eta_b = sum-of-{m}-Gauss-sums| max err over b = {maxerr:.2e}")
        if gmag:
            print(f"   each |G(chi_j)| (j>=1) in [{min(gmag):.3f},{max(gmag):.3f}], sqrt(p)={math.sqrt(p):.3f}"
                  f"  (Weil: nontrivial = sqrt(p) EXACT)")
        print(f"   trivial NO-cancellation bound (n/(p-1))(1+(m-1)sqrt(p)) = {triv:.3f}  ~ sqrt(p)={math.sqrt(p):.3f}")
        print(f"   actual M ~ {bestM:.3f}   sqrt(n)={math.sqrt(n):.3f}")
        print(f"   => the {m} Gauss sums must CANCEL from ~sqrt(p)={math.sqrt(p):.1f} down to ~{bestM:.1f}")
        print(f"      (a sqrt(m)-type cancellation among m phases). THAT is Paley/BGK, NOT FKM.")

    print("\n" + "=" * 100)
    print(" (C) AUTOCORRELATION self-reduction (the FKM-controllable correlation sum):")
    print("=" * 100)
    for n, beta in [(8, 4.0), (16, 4.0)]:
        p = prize_prime(n, beta, pmax=120000)
        if p is None:
            continue
        g = primitive_root(p); z = pow(g, (p - 1) // n, p)
        mu = []; x = 1
        for _ in range(n):
            mu.append(x); x = (x * z) % p
        def eta(b):
            return sum(cmath.exp(2j * math.pi * (b * e % p) / p) for e in mu)
        h = mu[1]
        Ah = sum(eta(b) * eta((b + h) % p).conjugate() for b in range(p))
        pred = p * eta((-h) % p)
        print(f"n={n} p={p}: A_h = {Ah:.2f};  p*eta_(-h) = {pred:.2f};  match={abs(Ah-pred)<1e-3*abs(pred)+1e-6}")
    print("\n  READING (C): the FKM-controllable correlation sum maps the period sequence to ITSELF")
    print("  (A_h = p*eta_{-h}). 'bound the dual, transport back' is a FIXED-POINT: dual = period.")

if __name__ == "__main__":
    main()
