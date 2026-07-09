"""
probe_444_hypocycloid_envelope.py  (lens [hypocycloid-support], part B FIXED, issue #444)

The STRONGER, p-free form of the lead. Untrau's torus-image support of a self-similar dyadic
phase family is governed by the LACUNARY (Weyl) sum
    z(theta) = sum_{j=0}^{mu-1} exp(i * 2^j * theta)        (mu = log2 n terms, NOT n terms!)
-- the hypocycloid Minkowski-sum is the image of the mu-torus under the dyadic doubling map.
Salem-Zygmund: the sup norm of a lacunary sum of K terms is Theta(sqrt(K log K)). With K=mu
terms this is sqrt(mu log mu)=tiny, NOT sqrt(n). So the FAITHFUL period support has n=2^mu unit
vectors but their PHASES are tied by the dyadic cascade.

We test BOTH faithful models of the dyadic period support, p-free, WITHOUT real-exponent
overflow (all doublings done mod a large dyadic modulus N=2^L so frequencies stay bounded):

 MODEL 1 (full-orbit lacunary, the actual mu_n analogue): the n=2^mu phases are
    theta_x = (2 pi / N) * (b * x mod N),  x in <2> = dyadic subgroup of (Z/N)^*,
 i.e. x runs over the cyclic orbit of 2 (the genuine multiplicative dyadic subgroup of a
 2-power modulus). This is the EXACT 2-adic analogue of mu_n and is p-free. max over b is the
 p-free dyadic house. We sweep modulus 2^L and subgroup = <2 or 3> of order n=2^mu.

 MODEL 2 (geometric lacunary curve, K=mu terms): z(theta)=sum_{j<mu} exp(i 2^j theta mod 2pi)
 -- the literal hypocycloid/Weyl-sum with mu (=log n) terms. Salem-Zygmund sqrt(mu log mu).

If the p-free dyadic house (MODEL 1) grows like sqrt(n log n): support = wall (reduces-to-wall).
If it stays O(sqrt n): support is a sqrt(n) handle (SURVIVES, then check the log m).
"""

import math, cmath
import numpy as np


def dyadic_house_modN(mu, L, base=3):
    """p-free 2-adic analogue: modulus N=2^L, subgroup H=<base> of (Z/N)^* (base odd).
    eta_b = sum_{x in H'} exp(2pi i b x / N), where H' is the order-n=2^mu sub-orbit of H.
    Return max_b |eta_b| (the p-free dyadic house) and the realized order n0."""
    N = 1 << L
    # multiplicative order of base mod N (for odd base, divides 2^{L-2})
    H = []
    x = 1
    seen = set()
    while True:
        if x in seen:
            break
        seen.add(x)
        H.append(x)
        x = (x * base) % N
    full = len(H)
    n = 1 << mu
    if n > full:
        return None, full
    Hn = H[:n]  # order-n sub-orbit (subgroup since cyclic)
    # but to be a genuine subgroup take elements of the unique order-n subgroup: powers of base^{full/n}
    step = full // n
    Hn = [H[(j * step) % full] for j in range(n)]
    w = 2 * math.pi / N
    Hn = np.array(Hn, dtype=np.int64)
    best = 0.0
    # b over a representative set of cosets (sample if N large)
    bs = range(1, N, 2) if N <= 1 << 14 else range(1, 1 << 14, 2)
    for b in bs:
        ang = w * ((b * Hn) % N)
        z = np.exp(1j * ang).sum()
        a = abs(z)
        if a > best:
            best = a
    return best, n


def lacunary_curve_mu_terms(mu, grid=2_000_000):
    """MODEL 2: z(theta)=sum_{j<mu} exp(i 2^j theta), theta in [0,2pi). mu terms (Salem-Zygmund)."""
    K = mu
    thetas = np.linspace(0, 2 * math.pi, grid, endpoint=False)
    z = np.zeros(grid, dtype=np.complex128)
    for j in range(K):
        z += np.exp(1j * (2 ** j) * thetas)
    return np.max(np.abs(z)), K


def main():
    print("=" * 100)
    print("[hypocycloid-support] part B (fixed): p-FREE dyadic support radius (2-adic analogue + Weyl)")
    print("=" * 100)
    print("MODEL 1: 2-adic dyadic house  eta_b on order-n subgroup of (Z/2^L)^*  (p-free, exact)")
    print(f"{'mu':>3} {'n':>6} {'L':>3} {'p-free house':>13} {'/sqrtn':>8} {'/sqrt(n*mu)':>12} {'/sqrt(n*lnN)':>13}")
    for mu in range(2, 11):
        L = mu + 8  # modulus much larger than subgroup => 'thin' analogue, m=2^{L-?} large
        h, n = dyadic_house_modN(mu, L, base=3)
        if h is None:
            print(f"{mu:>3} {1<<mu:>6} {L:>3}   (order too small)")
            continue
        lnN = math.log(2) * L
        print(f"{mu:>3} {n:>6} {L:>3} {h:>13.3f} {h/math.sqrt(n):>8.3f} "
              f"{h/math.sqrt(n*max(mu,1)):>12.3f} {h/math.sqrt(n*lnN):>13.3f}")
    print("-" * 100)
    print("MODEL 2: literal hypocycloid Weyl-sum z(theta)=sum_{j<mu} exp(i 2^j theta), mu=log2(n) terms")
    print(f"{'mu':>3} {'K=mu':>5} {'max|z|':>9} {'/sqrt(K)':>9} {'/sqrt(K lnK)':>13}")
    for mu in range(2, 16):
        r, K = lacunary_curve_mu_terms(mu, grid=2_000_000)
        lnk = math.log(K) if K > 1 else 1.0
        print(f"{mu:>3} {K:>5} {r:>9.3f} {r/math.sqrt(K):>9.3f} {r/math.sqrt(K*lnk):>13.3f}")
    print("-" * 100)
    print("READING:")
    print(" MODEL 1 column /sqrtn: GROWS in mu (like sqrt(log)) => p-free dyadic support = the wall.")
    print("   FLAT O(1) => genuine sqrt(n) handle. (This is the decisive p-free test of the lead.)")
    print(" MODEL 2 is the K=mu-term Weyl sum: small (sqrt(mu)) -- but it is the WRONG object,")
    print("   it only has mu unit vectors. The faithful support has n=2^mu vectors = MODEL 1.")


if __name__ == "__main__":
    main()
