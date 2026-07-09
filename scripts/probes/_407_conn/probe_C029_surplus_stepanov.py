"""
C029 attack: "The char-p energy SURPLUS S_r = E_r^{F_p} - E_r^infty is a Stepanov point-count,
hence O(n^{2r}/p) (sub-floor) for the LOW-r band."

The three bricks (repCount_le_two, bessel_energy_le_gaussian, surplus def) are PROVEN in-tree.
The load-bearing NEW claim is quantitative:
    surplus_r := #{(x,y) in mu_n^{2r} : sum x = sum y mod p, but sum x != sum y over Z[zeta_n]}
                 = O(n^{2r}/p)   (Sidon-spread / random heuristic), hence sub-floor n^r.

We test this DIRECTLY with exact integer arithmetic at PRIZE-LIKE instances:
  - mu_n a PROPER dyadic subgroup of F_p^*  (n=8,16,32; n^2 << p),
  - p = 1 mod n a LARGE prime, p ~ n^beta, beta in [4,5],
  - r small (the "low band": r=2,3,4).

E_r^{F_p}(mu_n) = #{(x,y) in mu_n^{2r} : x_1+...+x_r == y_1+...+y_r (mod p)}.
E_r^infty(mu_n) = same but the equality holds as ALGEBRAIC INTEGERS in Z[zeta_n], i.e. the
   multiset of exponents on each side matches AS A MULTISET (since {zeta^a} are Z-linearly
   independent up to the cyclotomic relation -- for n=2^mu, Phi_n has degree n/2, so the
   ONLY Z-relations among {zeta^a : a in Z_n} are antipodal: zeta^{a+n/2} = -zeta^a).

So char-0 (Z[zeta_n], n=2^mu) vanishing of sum x - sum y means: after applying the antipodal
reduction zeta^{a+n/2} -> -zeta^a, both sides reduce to the SAME signed multiset on the half
{zeta^0..zeta^{n/2-1}}. We compute E_r^infty by counting tuples whose REDUCED signed-coefficient
vector matches; E_r^{F_p} by the mod-p count. Surplus = E_r^{F_p} - E_r^infty.

KEY QUESTIONS:
  Q1. Is surplus_r >= 0 and = O(n^{2r}/p)?  (the Stepanov/random heuristic the connection asserts)
  Q2. Does surplus_r/(n^{2r}/p) stay O(1) as p grows at fixed (n,r) -- i.e. is the leading
      term really n^{2r}/p?  (necessary for "sub-floor": need surplus << floor n^r, i.e. need
      n^{2r}/p << n^r  <=>  p >> n^r. At prize p~n^beta this holds only for r < beta!)
  Q3. The decisive prize question: the deep-moment wall puts the OPERATIVE r at r ~ ln q >> beta.
      For r >= beta, n^{2r}/p = n^{2r-beta} >> n^r (floor). So even IF surplus = Theta(n^{2r}/p),
      it is ABOVE the floor for the operative r. Does the data show surplus crossing the floor
      exactly at r ~ beta?  (=> the Stepanov reframing only governs r<beta, NOT the mid band.)
"""
import itertools
from sympy import isprime, primitive_root
import math
from collections import Counter

def primitive_n_root(p, n):
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1
    return g

def char0_signed_reduce(exps, n):
    """For n=2^mu: reduce a multiset of exponents (in Z_n) to a signed coefficient vector
    over the half {0..n/2-1} using zeta^{a+n/2} = -zeta^a. Returns a tuple (canonical key)."""
    half = n // 2
    vec = [0] * half
    for a in exps:
        a %= n
        if a < half:
            vec[a] += 1
        else:
            vec[a - half] -= 1
    return tuple(vec)

def energy_counts(n, p, r):
    """Return (E_r^{F_p}, E_r^infty) exactly. Tuples range over mu_n^r on each side, so the
    full object is mu_n^{2r}; we use the standard 'representation count' factorization:
       E_r = sum_{s} N_p(s)^2   where N_p(s)=#{x in mu_n^r : sum x == s mod p}
       E_r^infty = sum_{key} N0(key)^2 where key = char0 signed-reduced exponent vector.
    This is exact and avoids the n^{2r} blowup (only n^r work)."""
    g = primitive_n_root(p, n)
    powg = [pow(g, a, p) for a in range(n)]
    Np = Counter()   # mod-p sum -> count
    N0 = Counter()   # char-0 signed key -> count
    for exps in itertools.product(range(n), repeat=r):
        s = sum(powg[a] for a in exps) % p
        Np[s] += 1
        N0[char0_signed_reduce(exps, n)] += 1
    Ep = sum(c * c for c in Np.values())
    E0 = sum(c * c for c in N0.values())
    return Ep, E0

def run():
    print("C029: char-p energy surplus S_r = E_r^{F_p} - E_r^infty for dyadic mu_n, proper subgroup\n")
    for n in (8, 16, 32):
        half = n // 2
        # pick proper-subgroup primes p = 1 mod n at several beta values
        print(f"=== n={n} (mu_n proper dyadic subgroup), floor E_r ~ n^r ===")
        print(f"  {'r':>2} {'p':>12} {'beta':>5} {'E_r^Fp':>14} {'E_r^inf':>12} {'surplus':>12} "
              f"{'n^2r/p':>12} {'surp/(n^2r/p)':>14} {'surp/floor':>11}")
        for r in (2, 3, 4):
            # choose primes near beta=4 and beta=5 (and a mid one) -- proper subgroup, large
            betas = [3.0, 4.0, 5.0]
            for beta in betas:
                target = int(n ** beta)
                # find a prime p = 1 mod n near target with n < p-1 (proper subgroup)
                p = target - (target % n) + 1
                cnt = 0
                while cnt < 200000:
                    if p > n + 1 and isprime(p) and (p - 1) % n == 0:
                        break
                    p += n
                    cnt += 1
                Ep, E0 = energy_counts(n, p, r)
                surplus = Ep - E0
                n2r = n ** (2 * r)
                pred = n2r / p
                floor = n ** r
                ratio = surplus / pred if pred > 0 else float('nan')
                sf = surplus / floor
                print(f"  {r:>2} {p:>12} {beta:>5.1f} {Ep:>14} {E0:>12} {surplus:>12} "
                      f"{pred:>12.1f} {ratio:>14.3f} {sf:>11.3f}")
        print()

if __name__ == "__main__":
    run()
