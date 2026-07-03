#!/usr/bin/env python3
"""
probe_466_wall_newenergy.py  --  LANE W2 (#466, dossier v3 §3/§6): the exact-energy
exponent landscape, ONE MORE audit, against THREE candidate inputs the campaign's
additive-energy sweep (probe_466_dibenedetto_half.py) does NOT isolate:

  (C1) the MULTIPLICATIVE energy of mu_n:  E_x(mu_n) = n^3 EXACTLY and UNCONDITIONALLY
       (subgroup fact, char-free).  Question: does a mixed additive-multiplicative /
       sum-product transfer feed a char-sum bound past BGK n^{1-o(1)} UNCONDITIONALLY?
  (C2) the exact 4th/6th ADDITIVE energies T_4, T_6 (char-0 Wick, good-prime) as inputs
       to a Rudnev-style point-line / point-plane incidence finisher.  Question: does a
       higher exact energy + incidence beat the landed 8/9 (T_3, bilinear-(3,3))?
  (C3) the exact CHARACTER-SUM SECOND MOMENT  sum_{b!=0}|eta_b|^2 = pn - n^2.  Question:
       does the exact 2nd moment give a sup-norm UPPER bound better than trivial?

OBJECT.  M(n,p) = max_{a!=0} |sum_{y in mu_n} e_p(a y)|,  p = 1 mod n,  p ~ n^beta,
beta = 4 the prize aspect ratio.  Landed SOTA (this repo):
  * good-prime-conditional : M <= n^{8/9+o(1)}  (bilinear (3,3)+sqrt(p)-DFT, _BilinearDFTBeat)
  * di Benedetto family infimum (all LEGAL additive inputs) : 1 - 1/(2 beta) = 7/8 at beta=4,
    binding = CS mass floor T_k >= n^{2k}/p at depth k=beta (probe_466_dibenedetto_half.py)
  * unconditional : BGK n^{1-o(1)} ; sharpest EFFECTIVE unconditional = di Benedetto
    2849/2880 = 0.98924 (generic sum-product energies t2=49/20, t3=4)

The moment identity that pins WHY the multiplicative energy cannot enter the ADDITIVE
sup-norm directly:
  sum_{a in F_p} |S(a)|^{2r} = p * T_r(mu_n),   T_r = #{ y_1+..+y_r = z_1+..+z_r }  (ADDITIVE),
so every 2r-th-moment bound on the ADDITIVE character sum routes through the ADDITIVE
energy T_r.  The multiplicative energy enters ONLY through a sum-product/incidence transfer
E_x -> (bound on) T_r, whose sharpest unconditional output for a subgroup is the SAME
t2 = 49/20 / t3 = 4 that already sits in the 'generic' menu.  This probe makes that
concrete and prices each candidate exactly.
"""

from fractions import Fraction as F
import math, cmath, sys

LINE = "-" * 78


def is_prime(m):
    if m < 2:
        return False
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if m % a == 0:
            return m == a
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def primes_1modn(n, count=2):
    out, p = [], n ** 4 + 1
    while len(out) < count:
        if p % n == 1 and is_prime(p) and p - 1 != n:
            out.append(p)
        p += n
    return out


def mun(n, p):
    g = None
    for cand in range(2, p):
        h = pow(cand, (p - 1) // n, p)
        if h != 1 and pow(h, n // 2, p) != 1:
            g = h
            break
    H, x = [], 1
    for _ in range(n):
        H.append(x)
        x = x * g % p
    assert len(set(H)) == n
    return H


# ---------------------------------------------------------------------------
# (C1) MULTIPLICATIVE ENERGY: exact, unconditional; the transfer it powers
# ---------------------------------------------------------------------------
print(LINE)
print("(C1) MULTIPLICATIVE ENERGY  E_x(mu_n) = #{(a,b,c,d) in mu_n^4 : ab=cd}")
print(LINE)


def mult_energy(H, p):
    from collections import defaultdict
    P = defaultdict(int)
    for a in H:
        for b in H:
            P[(a * b) % p] += 1
    return sum(v * v for v in P.values())


for n in [8, 16, 32]:
    ps = primes_1modn(n)
    for p in ps:
        H = mun(n, p)
        Ex = mult_energy(H, p)
        print(f"  n={n:2d} p={p}: E_x = {Ex}   n^3 = {n**3}   match={Ex == n**3}   "
              f"(char-free: E_x = n^3 EXACTLY for any subgroup)")

print("""
  READING.  E_x(mu_n) = n^3 is MAXIMAL (a group has the largest possible mult. energy)
  and UNCONDITIONAL.  But the ADDITIVE character sum's 2r-th moment identity
    sum_a |S(a)|^{2r} = p * T_r(mu_n)   (T_r = ADDITIVE energy)
  contains NO multiplicative energy.  E_x enters a sup-norm bound ONLY via a sum-product
  transfer  E_x = n^3  ==>  T_2(mu_n) <= (unconditional bound).  The sharpest such
  UNCONDITIONAL subgroup transfers:
    * Heath-Brown-Konyagin (Stepanov), single application:  T_2 <= n^{5/2}   (t2 = 5/2)
    * MRSS 2017 / Rudnev point-plane, best known:           t2 = 49/20, t3 = 4
  Both are EXACTLY the 'generic' menu already swept.  Pricing them at beta=4 below.""")


# ---------------------------------------------------------------------------
# exponent engine (matches probe_466_dibenedetto_half.py; L in {1,2,3})
# ---------------------------------------------------------------------------
def bilinear(m1, m2, t1, t2, beta):
    """L=2 bilinear finisher (sqrt(p) DFT operator norm), weights c=(1,1), c0=2.
       Returns (theta, E, kappa); theta=1 (vacuous) if E<=beta."""
    E = (2 * m1 - t1) + (2 * m2 - t2)
    e0 = 2 * m1
    e1 = 2 * m2 - 2
    e2 = 2 - 2
    kappa = F(0)
    kappa += e0 if e0 > 0 else 0
    kappa += (e1 * m1) if e1 > 0 else 0
    kappa += (e2 * m1 * m2) if e2 > 0 else 0
    if E <= beta:
        return F(1), E, kappa
    return 1 - (E - beta) / kappa, E, kappa


def moment(k, tk, beta):
    return min((beta - 1 + tk) / (2 * k), F(1))


beta = F(4)
print(f"  --- pricing the multiplicative-energy transfers at beta = {beta} ---")
# direct HBK single-application subgroup bound
thm = moment(2, F(5, 2), beta)
thb, Eb, kb = bilinear(2, 2, F(5, 2), F(5, 2), beta)
print(f"  HBK t2=5/2 : moment k=2 theta={thm}={float(thm):.4f} ; bilinear(2,2) E={Eb} "
      f"(<= beta={beta} -> VACUOUS: theta={thb})   [dies at beta=3, the p^{{1/3}} wall]")
# best unconditional sum-product (generic menu, di Benedetto trilinear) -- reproduced from
# probe_466_dibenedetto_half.py anchor
print(f"  MRSS/generic t2=49/20,t3=4 : di Benedetto trilinear = 2849/2880 = "
      f"{float(F(2849,2880)):.6f}  (= 1 - 31/2880; the SOTA EFFECTIVE unconditional)")
print(f"  ==> C1 VERDICT: the multiplicative energy is UNCONDITIONAL but only feeds t_r via")
print(f"      sum-product; its best unconditional output at beta=4 is 0.98924 = n^{{1-o(1)}}.")
print(f"      NO unconditional power-saving past BGK.  (Direct HBK route is VACUOUS at beta=4.)")


# ---------------------------------------------------------------------------
# (C2) higher EXACT additive energies + incidence: cannot beat 8/9 (supply-surviving),
#      infimum 7/8 (supply dead).  Optimum sits at fold order = beta.
# ---------------------------------------------------------------------------
print()
print(LINE)
print("(C2) EXACT higher additive energies T_4, T_6 (char-0 Wick) + incidence finisher")
print(LINE)


def energies_upto(H, p, R):
    """exact T_2..T_R additive energies of H over F_p."""
    from collections import defaultdict
    J = {1: defaultdict(int)}
    for a in H:
        J[1][a % p] += 1
    for r in range(2, R + 1):
        Jr = defaultdict(int)
        for s, v in J[r - 1].items():
            for c in H:
                Jr[(s + c) % p] += v
        J[r] = Jr
    return {r: sum(v * v for v in J[r].values()) for r in range(2, R + 1)}


# char-0 Wick leading coeff (2r-1)!!
def dfact(r):
    p = 1
    for j in range(1, r + 1):
        p *= (2 * j - 1)
    return p


for n in [8, 16]:
    p = primes_1modn(n)[0]
    H = mun(n, p)
    Ts = energies_upto(H, p, 6)
    print(f"  n={n} p={p}: " + "  ".join(
        f"T_{r}={Ts[r]} (lead (2r-1)!!*n^r={dfact(r)*n**r}, ratio={Ts[r]/(dfact(r)*n**r):.3f})"
        for r in (2, 3, 4)))

print(f"""
  Best finisher per EXACT input t_r = r (good-prime), fold order m, at beta=4:
    bilinear(m,m), t=(r,r)=(m,m):  optimum at m = beta = 4  ->  7/8 = 0.875  (family infimum)
      but t_4 = 4 good-prime supply is DEAD (D_4 generic K-bad, round 8) -> UNREACHABLE
    bilinear(3,3), t=(3,3):  8/9 = 0.8889  (T_3 good-prime, LANDED _BilinearDFTBeat)
    bilinear(6,6): CS mass floor forces t_6 = max(6, 2*6-4) = 8 (NOT 6) -> theta = 17/18 WORSE
  A Rudnev point-plane / point-line finisher is the TRILINEAR PS shape already swept
  (weights (1,1,1/2), c0=4); at beta=4 it is DOMINATED by bilinear for beta < 17/3.
  ==> C2 VERDICT: higher exact energies do NOT beat 8/9 with surviving supply; the
      k=beta optimum 7/8 is the family floor and its supply is dead.  No gain.""")
for m in [3, 4, 5, 6]:
    tm = max(F(m), 2 * m - beta)          # LEGAL (mass-floor) exponent
    th, E, k = bilinear(m, m, tm, tm, beta)
    print(f"    bilinear({m},{m}) legal t={tm}: theta = {th} = {float(th):.6f}")


# ---------------------------------------------------------------------------
# (C3) character second moment: exact, gives ONLY the Parseval floor (no sup upper bound)
# ---------------------------------------------------------------------------
print()
print(LINE)
print("(C3) CHARACTER SECOND MOMENT  sum_{b!=0}|eta_b|^2 = p*n - n^2  (exact Parseval)")
print(LINE)


def second_moment(H, p):
    tot = 0.0
    absq = []
    for b in range(1, p):
        s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in H)
        absq.append(abs(s) ** 2)
        if b > 6 * n:                      # eta_b is coset-invariant; a few cosets suffice
            break
    return absq


for n in [8]:
    for p in primes_1modn(n):
        # exact identity check via full sum over ALL b (n small)
        tot = 0.0
        H = mun(n, p)
        for b in range(1, p):
            s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in H)
            tot += abs(s) ** 2
        print(f"  n={n} p={p}: sum_{{b!=0}}|eta_b|^2 = {tot:.1f}   p*n - n^2 = {p*n - n*n}   "
              f"match={abs(tot-(p*n-n*n))<1e-4}")
print(f"""
  The 2nd moment gives:
    * LOWER bound (Parseval floor):  max_b |eta_b|^2 >= average = (pn-n^2)/(p-1) ~ n,
      i.e. M >= sqrt(n - n^2/p) ~ sqrt(n)  (already in-tree, GaussPeriodParsevalFloor).
    * UPPER bound from the 2nd moment ALONE:  M <= sqrt(sum) = sqrt(pn - n^2) ~ n^{{(beta+1)/2}}
      = n^{{5/2}} at beta=4 -- TRIVIAL (worse than the trivial n).
  Exponent of the pure-2nd-moment sup bound = (beta+1)/2 = {float((beta+1)/2)} >> 1.
  ==> C3 VERDICT: the exact 2nd moment is the Parseval FLOOR, not a sup-norm lever.
      It brackets [sqrt(n), trivial]; no upper improvement.  (Only the 2r-th moment at
      r ~ log p -- the OPEN Wick atom -- controls the sup; that IS the wall.)""")


# ---------------------------------------------------------------------------
# assembled verdict
# ---------------------------------------------------------------------------
print()
print(LINE)
print("VERDICT (LANE W2)")
print(LINE)
print(f"""
  The exact energies of mu_n are EXHAUSTED at:
    * good-prime-conditional : 8/9 = {float(F(8,9)):.6f}  (bilinear (3,3), T_3; LANDED)
    * family infimum         : 7/8 = {float(F(7,8)):.6f}  (bilinear (4,4), T_4; supply DEAD)
    * unconditional          : n^{{1-o(1)}}  (BGK; effective SOTA 0.98924 via sum-product)
  None of the THREE candidate NEW inputs breaks this:
    (C1) multiplicative energy n^3 : unconditional, but only feeds t_r via sum-product;
         best unconditional output 0.98924 = n^{{1-o(1)}}, direct HBK vacuous at beta=4.
    (C2) higher exact additive energies T_4,T_6 : k=beta optimum is 7/8 (supply dead),
         do not beat 8/9 with surviving supply; incidence finisher = swept trilinear.
    (C3) character 2nd moment : the Parseval floor sqrt(n); no sup UPPER control.
  Binding obstruction (all three): the moment identity routes every ADDITIVE sup bound
  through the ADDITIVE energy T_r; the CS mass floor T_k >= n^{{2k}}/p forces the legal
  envelope t_k >= max(k, 2k-beta), whose method-shape infimum is 1 - 1/(2 beta) = 7/8.
  The exact-energy exponent axis is CLOSED at 8/9 good-prime / n^{{1-o(1)}} unconditional.
""")
