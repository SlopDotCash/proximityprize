#!/usr/bin/env python3
"""R25 lane D8: verify the d=8 fold + octic descent algebra.

Claims to verify:
 (1) FOLD: with w^8 = c (w = g^e shadow), R = sum_j w^j S_j, Rbar = sum_j (-1)^j w^j S_j,
     R*Rbar = P(v)^2 - v*Q(v)^2 with v = w^2, P = S0+S2 v+S4 v^2+S6 v^3, Q = S1+S3 v+S5 v^2+S7 v^3.
 (2) BLOCKS: P^2 - v Q^2 = sum_{i<8} c_i v^i with the eight quadratic forms c_i as derived;
     after v^4 -> c fold, blocks e_i = c_i + c*c_{i+4}:
       e0 = a0^2 + c*(2a2a6 + a4^2 - 2a1a7 - 2a3a5)
       e1 = 2a0a2 - a1^2 + c*(2a4a6 - 2a3a7 - a5^2)
       e2 = 2a0a4 + a2^2 - 2a1a3 + c*(a6^2 - 2a5a7)
       e3 = 2a0a6 + 2a2a4 - 2a1a5 - a3^2 - c*a7^2
 (3) TOWER REGROUP: with s^2 = c, P0=a0+a4 s, Q0=a1+a5 s, P1=a2+a6 s, Q1=a3+a7 s:
       e0 + s*e2 == P0^2 + s*(P1^2 - 2 Q0 Q1)      (quartic h0 with c->s)
       e1 + s*e3 == 2 P0 P1 - Q0^2 - s*Q1^2        (quartic h1 with c->s)
 (4) DESCENT over F_q (q = 17, 41, 73; c ranging over non-squares with -c non-square):
     e0=e1=e2=e3=0  ==>  a0=..=a7=0 (exhaustive-ish random + small exhaustive check).
 (5) KUMMER: c = -4 b^4 ==> -c = (2b^2)^2 square, so hc & hnc imply c not in -4K^4.
"""
import itertools, random
import sympy as sp

a = sp.symbols('a0:8'); c, s, v = sp.symbols('c s v')

# (1)+(2): symbolic fold
w = sp.symbols('w')
R  = sum(a[j]*w**j for j in range(8))
Rb = sum((-1)**j*a[j]*w**j for j in range(8))
prod = sp.expand(R*Rb)
P = a[0]+a[2]*v+a[4]*v**2+a[6]*v**3
Q = a[1]+a[3]*v+a[5]*v**2+a[7]*v**3
target = sp.expand((P**2 - v*Q**2).subs(v, w**2))
print("(1) fold identity:", sp.simplify(prod-target)==0)

poly = sp.Poly(sp.expand(P**2 - v*Q**2), v)
cs = [poly.coeff_monomial(v**i) for i in range(8)]
e = [sp.expand(cs[i] + c*cs[i+4]) for i in range(4)]
e_claim = [
 a[0]**2 + c*(2*a[2]*a[6]+a[4]**2-2*a[1]*a[7]-2*a[3]*a[5]),
 2*a[0]*a[2]-a[1]**2 + c*(2*a[4]*a[6]-2*a[3]*a[7]-a[5]**2),
 2*a[0]*a[4]+a[2]**2-2*a[1]*a[3] + c*(a[6]**2-2*a[5]*a[7]),
 2*a[0]*a[6]+2*a[2]*a[4]-2*a[1]*a[5]-a[3]**2 - c*a[7]**2]
print("(2) blocks:", all(sp.expand(e[i]-e_claim[i])==0 for i in range(4)))

# (3) tower regroup, reduce mod s^2 - c
P0,Q0,P1,Q1 = a[0]+a[4]*s, a[1]+a[5]*s, a[2]+a[6]*s, a[3]+a[7]*s
def red(x): return sp.expand(sp.rem(sp.expand(x), s**2-c, s))
lhs0 = red(e_claim[0]+s*e_claim[2]); rhs0 = red(P0**2+s*(P1**2-2*Q0*Q1))
lhs1 = red(e_claim[1]+s*e_claim[3]); rhs1 = red(2*P0*P1-Q0**2-s*Q1**2)
print("(3) regroup h0:", sp.expand(lhs0-rhs0)==0, " h1:", sp.expand(lhs1-rhs1)==0)

# (4) finite-field descent check
def descent_check(q):
    sq = {x*x % q for x in range(q)}
    fails = 0; tested = 0
    for cc in range(1,q):
        if cc in sq or (q-cc) % q in sq: continue
        # random nonzero tuples + all tuples with support size <=2
        eqs = lambda t: (
            (t[0]**2 + cc*(2*t[2]*t[6]+t[4]**2-2*t[1]*t[7]-2*t[3]*t[5])) % q == 0 and
            (2*t[0]*t[2]-t[1]**2 + cc*(2*t[4]*t[6]-2*t[3]*t[7]-t[5]**2)) % q == 0 and
            (2*t[0]*t[4]+t[2]**2-2*t[1]*t[3] + cc*(t[6]**2-2*t[5]*t[7])) % q == 0 and
            (2*t[0]*t[6]+2*t[2]*t[4]-2*t[1]*t[5]-t[3]**2 - cc*t[7]**2) % q == 0)
        for _ in range(4000):
            t = tuple(random.randrange(q) for _ in range(8))
            if any(t):
                tested += 1
                if eqs(t): fails += 1; print("   COUNTEREXAMPLE q=%d c=%d t=%s"%(q,cc,t))
        for i,j in itertools.combinations(range(8),2):
            for x in range(1,q):
                for y in range(q):
                    t = [0]*8; t[i]=x; t[j]=y; t=tuple(t)
                    tested += 1
                    if eqs(t): fails += 1; print("   CE q=%d c=%d t=%s"%(q,cc,t))
    return fails, tested
random.seed(0)
for q in (17,41,73):
    f,t = descent_check(q)
    print("(4) q=%d: descent holds on %d nonzero tuples, %d failures"%(q,t,f))

# sanity: at q=17 with c a nonsquare but -c a SQUARE, descent should FAIL (witness expected)
q=17; sq={x*x%q for x in range(q)}
bad = [cc for cc in range(1,q) if cc not in sq and (q-cc)%q in sq]
found=None
for cc in bad:
    for t in itertools.product(range(q),repeat=4):
        tt=(t[0],t[1],t[2],t[3],0,0,0,0)
        if not any(tt): continue
        if ((tt[0]**2+cc*(2*tt[2]*tt[6]+tt[4]**2-2*tt[1]*tt[7]-2*tt[3]*tt[5]))%q==0 and
            (2*tt[0]*tt[2]-tt[1]**2+cc*(2*tt[4]*tt[6]-2*tt[3]*tt[7]-tt[5]**2))%q==0 and
            (2*tt[0]*tt[4]+tt[2]**2-2*tt[1]*tt[3]+cc*(tt[6]**2-2*tt[5]*tt[7]))%q==0 and
            (2*tt[0]*tt[6]+2*tt[2]*tt[4]-2*tt[1]*tt[5]-tt[3]**2-cc*tt[7]**2)%q==0):
            found=(cc,tt); break
    if found: break
print("(5) necessity of hnc: witness when -c IS a square:", found)
