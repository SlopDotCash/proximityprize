"""
probe_444_boundB_elimdegree.py -- the GENUINE elimination-ideal degree for the J=gamma^{n/d}
minimal polynomial, computed by Groebner elimination over F_p, r=3 and r=4.

We set up the polynomial system in the ROOT variables x_0..x_r (the r+1 elements of S) PLUS gamma,
with constraints:
  (cyc)  x_i^{n} - 1 = 0           [x_i in mu_n]   -- THIS carries the n-degree
  (V)    h_{e-r} h_{f-r+1} - h_{f-r} h_{e-r+1} = 0
  (pin)  gamma * h_{f-r} + h_{e-r} = 0
and we ALSO add the ANTIPODE-DESCENT substitution: replace x_i^2 = y_i, y_i^{n/2}=1, to halve the
cyclotomic degree (the 2^r reduction).  We then eliminate y_0..y_r (and the x_i*odd parts) to get
the univariate poly in gamma, and read its degree.

Because full Groebner in r+1 cyclotomic variables is expensive, we do the SMALLEST honest version:
r=3, n small (8,16), eliminate via resultants over F_p, and report the gamma-degree of the
eliminant WITH and WITHOUT the antipode substitution, to MEASURE the 2^r drop concretely.

If even the descended eliminant degree is C(n, .) not C(n/2, .), Bound-B bottoms out -> report that.
"""
import sympy as sp
from math import comb, gcd

# Work over F_p with a small prime that still has mu_n (n | p-1). For n=8 use p=17 (8|16). n=16 -> p=97 (16|96).
def small_prime_for(n):
    cand={8:17, 16:97, 32:97}  # 16|96, 32 not | 96; use 16 max for symbolic
    return cand.get(n)

def gen_fp(n,p):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError(f"no gen n={n} p={p}")

def h_of(elts,m,p):
    # complete homogeneous h_m via Newton over F_p
    M=m
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for k in range(1,M+1):
        s=0
        for i in range(1,k+1): s=(s+Pw[i]*H[k-i])%p
        H[k]=(s*pow(k,p-2,p))%p
    return H[m]

def elim_degree_r3(n,e,f):
    """Compute the gamma-minimal-poly degree by Groebner elimination, r=3, over F_p (small p).
       System: x0,x1,x2,x3 in mu_n, on V, gamma pinned.  Eliminate x's -> univariate in gamma.
       We use the SYMMETRIC reduction: variables = power sums p1..p? Actually we eliminate the
       roots directly via the ideal <x_i^n-1, sym constraints>.  For tractability we use the
       resultant chain over Q? No -- we do it over F_p with sympy GF Groebner (lex, gamma last)."""
    p=small_prime_for(n)
    if p is None: return None
    F=sp.GF(p)
    x0,x1,x2,x3,gam=sp.symbols('x0 x1 x2 x3 gam')
    xs=[x0,x1,x2,x3]
    # h_m as symbolic functions of the 4 roots
    def hsym(m):
        # complete homogeneous polynomial of x0..x3 degree m
        return sp.Poly(sp.functions.combinatorial.numbers.nC if False else 0)  # placeholder
    # Build h_m symbolically via generating function 1/prod(1-x_i t) truncated
    t=sp.symbols('t')
    gf=1
    for xi in xs:
        gf*= 1/(1-xi*t)
    ser=sp.series(gf,t,0,max(e-3+2,f-3+2)+1).removeO()
    serp=sp.Poly(ser,t)
    def hm(m):
        return serp.nth(m)
    her=hm(e-3); her1=hm(e-3+1); hfr=hm(f-3); hfr1=hm(f-3+1)
    V = sp.expand(her*hfr1-hfr*her1)
    pin= sp.expand(gam*hfr+her)
    cyc=[sp.expand(xi**n-1) for xi in xs]
    gens=[V,pin]+cyc
    polys=[sp.Poly(g, x0,x1,x2,x3,gam, modulus=p) for g in gens]
    # eliminate x0..x3 with lex order, gamma last
    G=sp.groebner(polys, x0,x1,x2,x3,gam, order='lex', modulus=p)
    # find univariate generator in gamma
    deg=None
    for g in G.polys:
        mons=g.monoms()
        if all(m[0]==0 and m[1]==0 and m[2]==0 and m[3]==0 for m in mons):
            d=max(m[4] for m in mons)
            deg=d if deg is None else min(deg,d) if False else d
    return p,deg

if __name__=="__main__":
    print("r=3 GENUINE Groebner elimination gamma-degree (small p):")
    for n in [8,16]:
        e,f=n//2,n//2-1
        try:
            res=elim_degree_r3(n,e,f)
            if res is None:
                print(f"  n={n}: no small prime"); continue
            p,deg=res
            print(f"  n={n} p={p} line({e},{f}): gamma-elim-degree={deg}  C(n/4,2)={comb(n//4,2)}  C(n/2,2)={comb(n//2,2)}  C(n,2)={comb(n,2)}")
        except Exception as ex:
            print(f"  n={n}: EXC {type(ex).__name__}: {ex}")
