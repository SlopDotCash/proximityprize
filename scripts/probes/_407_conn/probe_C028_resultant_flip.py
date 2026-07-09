# -*- coding: utf-8 -*-
import sys, functools
print = functools.partial(print, flush=True)
"""
Probe for connection C028 (#407 proximity-gap prize attack).

CLAIM (C028): The KKH26 resultant threshold p > s^{s/2} is the SINGLE shared
injectivity boundary controlling BOTH:
  (F4) the covering count / list explosion: needs short signed R = P - Q with R(g) != 0
       (distinct signed sums), guaranteed when ||R||_1^{n/2} < p  (i.e. p > s^{s/2});
  (F10) the DyadicLacunaryFloor cleanliness: "needs bad relations to VANISH R(g)=0".
And these are "the SAME resultant-nonvanishing inequality with the inequality flipped:
exact complements gated by p <=> s^{s/2}".

We test the precise logical content with EXACT integer arithmetic at PROPER dyadic
subgroups mu_n of large prime fields F_q, q ~ n^beta (beta ~ 4), the prize regime.

What we measure (exact, q-independent where stated):

(A) F4 object: collision polynomials R = P_{d1} - P_{d2}, P signed sum-poly, deg < n/2,
    coeffs in {-2,-1,0,1,2}. F4 wants R(g) != 0 (distinctness). Threshold p > s^{s/2}.

(B) F10 object: vanishingVariety(mu_n, a, t) = subsets S of mu_n, |S|=a, with
    e_1(S)=...=e_{t-1}(S)=0; lacBad = image of e_t. F10 wants #lacBad <= C*n.
    This is a CHAR-0 / large-p combinatorial count (in mu_n over Q(zeta_n) / over F_q).

We test four sub-claims:
  (1) DIRECTION: is F10 cleanliness really "R(g)=0" (vanishing) while F4 is "R(g)!=0"?
      i.e. are the two faces literally the same R with the inequality flipped?
  (2) Is the SAME polynomial R the controlling object on both sides?
  (3) THRESHOLD location: at prize p ~ n^beta, where do s^{s/2} and the actual
      char-p collision behaviour sit? Is the prize "in the crossover where (2r)^{n/2}
      vs p is delicate" (C028) or massively on one side?
  (4) Does flipping the inequality (p <= s^{s/2}) actually GIVE the floor? i.e. below
      threshold do the F10 bad relations vanish (clean floor), as C028 asserts?
"""

import itertools, math
from sympy import primerange, isprime, nextprime

# ---------------------------------------------------------------------------
# subgroup machinery in F_q : mu_n = the order-n multiplicative subgroup.
# ---------------------------------------------------------------------------
def find_prize_prime(n, beta=4, start_mult=None):
    """Smallest prime q = 1 mod n with q >= n^beta, ensuring mu_n is a PROPER
    subgroup (q-1 has order-n subgroup, q large)."""
    lo = int(n**beta)
    # find prime q ≡ 1 mod n, q >= lo
    q = lo - (lo % n) + 1
    if q < lo: q += n
    while True:
        if isprime(q):
            return q
        q += n

def primitive_nth_root(q, n):
    """A generator g of mu_n in F_q (order exactly n)."""
    # find a generator of F_q^*  then raise to (q-1)/n
    # quick: try small bases
    e = (q - 1) // n
    for base in range(2, q):
        g = pow(base, e, q)
        if g == 1: continue
        # check order exactly n
        ok = True
        # order divides n; check it is not a proper divisor
        good = True
        for p in set(prime_factors(n)):
            if pow(g, n // p, q) == 1:
                good = False; break
        if good:
            return g
    raise RuntimeError("no primitive root found")

def prime_factors(n):
    f = []
    d = 2
    while d*d <= n:
        while n % d == 0:
            f.append(d); n//=d
        d += 1
    if n>1: f.append(n)
    return f

# ---------------------------------------------------------------------------
# (1)+(2): F4 collision polynomials vs F10 vanishing-variety objects.
# Are they the same family?
# ---------------------------------------------------------------------------
def f4_collision_polys(half, r):
    """F4 / KKH26 objects: R = P - Q where P,Q are signed sum-polys of r distinct
    exponents in [0,half) with +-1 coeffs. R has degree < half, coeffs in [-2,2],
    and ||R||_1 <= 2r. (We return coefficient dicts {exp: coeff}.)"""
    polys = []
    sigs = []
    exps_all = range(half)
    for U in itertools.combinations(exps_all, r):
        for signs in itertools.product([1,-1], repeat=r):
            p = {}
            for e,s in zip(U, signs):
                p[e] = p.get(e,0)+s
            sigs.append(p)
    # collision polys = pairwise differences
    seen=set()
    for i in range(len(sigs)):
        for j in range(len(sigs)):
            if i==j: continue
            R={}
            for e in set(sigs[i])|set(sigs[j]):
                c = sigs[i].get(e,0)-sigs[j].get(e,0)
                if c: R[e]=c
            if not R: continue
            key=tuple(sorted(R.items()))
            if key in seen: continue
            seen.add(key)
            polys.append(R)
    return polys

def esymm(vals, t, q):
    """e_t of a list of field elements mod q, computed exactly via Newton/DP."""
    # DP: coefficients of prod (x + v)  -> elementary symmetric
    e = [0]*(t+1); e[0]=1
    for v in vals:
        for k in range(min(t,len(e)-1),0,-1):
            e[k] = (e[k] + v*e[k-1]) % q
    return e[t] % q

def f10_vanishing_variety(g, n, q, a, t):
    """F10 object in F_q : subsets S of mu_n, |S|=a, with e_1=..=e_{t-1}=0 mod q;
    return the set of e_t(S) values (= lacBad up to sign)."""
    mu = [pow(g, i, q) for i in range(n)]
    lac = set()
    cnt = 0
    for S in itertools.combinations(mu, a):
        ok = True
        for j in range(1, t):
            if esymm(S, j, q) != 0:
                ok=False; break
        if ok:
            cnt += 1
            lac.add(esymm(S, t, q))
    return lac, cnt

# ---------------------------------------------------------------------------
# (3): threshold location: s^{s/2} vs prize p = n^beta.
# ---------------------------------------------------------------------------
def threshold_report():
    print("=== (3) THRESHOLD LOCATION: s^{s/2}  vs  prize p ~ n^beta ===")
    print(f"{'n':>5} {'log2(s^(s/2))':>16} {'log2(prize p)':>14} {'ratio thr/p (log2)':>20}")
    for mu in [3,4,5,6,8,10,20,30]:
        n = 2**mu
        log2_thr = n * mu / 2.0            # log2( (2^mu)^(2^{mu-1}) ) = mu * 2^{mu-1}
        # actually s^{s/2} = (2^mu)^{2^{mu-1}} => log2 = mu * 2^{mu-1}
        log2_thr = mu * (2**(mu-1))
        for beta in [4,5]:
            log2_p = beta*mu
            print(f"{n:>5} {log2_thr:>16.1f} {log2_p:>14.1f}   beta={beta}: thr is 2^{log2_thr-log2_p:.0f}x p")
    print()

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    threshold_report()

    print("=== (1)+(2) Are the F4 and F10 controlling objects the SAME R? ===")
    # F10 vanishing variety members S give a polynomial prod_{x in S}(X - x)
    #   = X^a + (deg<=a-t terms) with e_1..e_{t-1}=0  -> LACUNARY  X^a + (-1)^t e_t X^{a-t} + ...
    # F4 collision R = P - Q : a DIFFERENCE of two signed sum-polys, coeffs in {-2..2},
    #   support arbitrary in [0,half), NO splitting / no vanishing-e constraint.
    # They live in different ambient sets. Show concretely for small n.
    n = 8; half = n//2  # =4
    f4 = f4_collision_polys(half, r=2)
    print(f"n={n}: F4 collision polys R=P-Q (r=2): count={len(f4)}; sample coeffs:")
    for R in f4[:4]:
        print("   ", dict(sorted(R.items())), " ||R||_1 =", sum(abs(c) for c in R.values()))
    print("   -> F4 R: degree<half, coeffs in {-2..2}, arbitrary support, NO split constraint.")
    print("   -> F10 object: monic deg-a poly that SPLITS over mu_n with e_1..e_{t-1}=0.")
    print("   => DIFFERENT object families (difference-of-signed-sums vs splitting-with-vanishing).")
    print()

    print("=== (4) Does p <= s^{s/2} (flip) give the F10 floor / vanishing? ===")
    print("Test at PROPER dyadic subgroups, prize prime q ~ n^4, exact char-p count.")
    print(f"{'n':>4} {'q':>10} {'a':>3} {'t':>3} {'#var':>6} {'#lacBad':>8} {'<=C*n? (C=4)':>14}")
    for mu in [3, 4]:
        n = 2**mu; half = n//2
        q = find_prize_prime(n, beta=4)
        g = primitive_nth_root(q, n)
        # check g has order n
        assert pow(g, n, q) == 1 and all(pow(g, n//p, q)!=1 for p in set(prime_factors(n)))
        # keep a small enough to ENUMERATE C(n,a) exactly; vary gap t
        cand = [(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)]
        for (a, t) in cand:
            if a > n or t > a or t < 1 or math.comb(n,a) > 3_000_000: continue
            lac, cnt = f10_vanishing_variety(g, n, q, a, t)
            Cn = 4*n
            print(f"{n:>4} {q:>10} {a:>3} {t:>3} {cnt:>6} {len(lac):>8} {str(len(lac)<=Cn):>14}")
    print()
    print("Interpretation printed by analysis section in the verdict.")

if __name__ == "__main__":
    main()
