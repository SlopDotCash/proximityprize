"""
probe_444_boundB_symbres.py -- the A-PRIORI descended elimination degree via an HONEST symbolic
resultant for r=3, to report what 'elimination achieves' (vs the C(n/2,r-1) target / C(n,.) weak).

We work the r=3 structured variety symbolically over Q(generic), in the antipode-descended
coordinates, and compute the degree in gamma of the resultant eliminant.  We DO NOT use the n-th
roots of unity numerically here; we treat the variety as the algebraic relations and compute the
Bezout/resultant degree in gamma.  This is the rigorous a-priori bound the elimination yields.

Structured r=3 variety (algebraic, antipode already used: a,b squares; c,d nonsquares; ab=-cd):
  parameters s=a+b, q=ab, u=c+d, w_=cd=-q.  4 roots; h_m computed from (e1,e2,e3,e4) where
   e1=s+u, e2=q+s*u+w_, e3=s*w_+q*u, e4=q*w_.  With w_=-q: e2=s*u, e3=-s*q+q*u=q(u-s), e4=-q^2.
gamma=-h_{e-3}/h_{f-3}.  The eliminant: eliminate (s,u) [the 'shape' coords] subject to the
cyclotomic constraints that fix q (orbit base) -> resultant in gamma. Its degree = a-priori bound.

We compute deg_gamma( Res ) for the maximizer line shape e=f+1, for symbolic small targets, to see
the n-growth of the a-priori degree.  KEY: does it come out O(C(n/4,2)) (=quadratic in n, TIGHT),
O(C(n/2,2)) (quadratic, descended-but-loose), or O(C(n,2)) (un-descended)?
"""
import sympy as sp
from math import comb

def hm_from_e(m, e1,e2,e3,e4):
    # complete homogeneous h_m via 1/E(t) where E(t)=1-e1 t+e2 t^2-e3 t^3+e4 t^4
    t=sp.symbols('t')
    E=1-e1*t+e2*t**2-e3*t**3+e4*t**4
    ser=sp.series(1/E,t,0,m+1).removeO()
    return sp.Poly(ser,t).nth(m)

def gamma_eliminant_degree(em, fm):
    """em=e-3, fm=f-3 (the h-indices). Build gamma + h relation symbolically in (s,u) with q a
       parameter, w_=-q. Compute the resultant eliminating s,u? That's 2 vars -> need 2 eqs.
       The variety is 1-dim per q (after ab=-cd fixes one relation). Actually free params (s,u) with
       q fixed: 2 free, but the roots a,b must be in mu_{n/2} (s,q determine a,b; cyclotomic). The
       ALGEBRAIC (pre-cyclotomic) variety has gamma as a function of (s,u,q): 2-dim. The cyclotomic
       conditions cut it to points.  The a-priori RESULTANT degree (ignoring cyclotomic, pure
       Bezout in s,u) overcounts massively.  Instead we report deg_gamma of the rational function
       gamma(s,u;q) as a map -- the # of (s,u) giving a fixed gamma is the fiber; the IMAGE degree
       is what bounds O_P.  We compute the degree of the gamma=const curve in (s,u) plane = the
       Bezout contribution per cyclotomic point."""
    s,u,q,gam=sp.symbols('s u q gam')
    e1=s+u; e2=s*u; e3=q*(u-s); e4=-q**2
    her=hm_from_e(em,e1,e2,e3,e4)
    hfr=hm_from_e(fm,e1,e2,e3,e4)
    rel=sp.expand(gam*hfr+her)   # gamma*h_{f-3}+h_{e-3}=0
    rel=sp.Poly(sp.numer(sp.together(rel)), s,u,gam,q)
    # degree in (s,u) of the gamma-pin curve, and total degree
    ds=rel.degree(s); du=rel.degree(u); dgam=rel.degree(gam)
    return dict(deg_s=ds,deg_u=du,deg_gam=dgam,totdeg=rel.total_degree())

if __name__=="__main__":
    print("r=3 symbolic gamma-pin relation degrees (maximizer e=f+1; em=e-3, fm=f-3):")
    print("  (these are the a-priori per-cyclotomic-point Bezout contributions; the n-growth of the")
    print("   eliminant degree = (#cyclotomic base points) x (these), the descent question.)")
    # maximizer e=n/2, f=n/2-1 => em=n/2-3, fm=n/2-4. Show how the relation degree grows with the
    # h-index (since higher h_m = higher degree symmetric poly).
    print(f"{'em':>4}{'fm':>4} {'deg_s':>6}{'deg_u':>6}{'deg_gam':>8}{'totdeg':>7}")
    for (em,fm) in [(1,0),(2,1),(3,2),(4,3),(5,4),(6,5),(7,6)]:
        d=gamma_eliminant_degree(em,fm)
        print(f"{em:>4}{fm:>4} {d['deg_s']:>6}{d['deg_u']:>6}{d['deg_gam']:>8}{d['totdeg']:>7}")
