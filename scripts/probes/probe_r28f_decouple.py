#!/usr/bin/env python3
"""R28F DECOUPLE lane probe (#466 round 28F).

Attack MixedMainResHalfCS S A B (1/2):  sum A^2 B^2 <= (1/2) sqrt(sumA^4) sqrt(sumB^4)
with A = M'.re = (-n + Main_Y).re on Y-block (coarse) chars,
     B = Res.re on complement (Omega) chars.

Measured target from r27f: ratio ~0.33-0.49, want <= 1/2.

Step-1 questions:
 (Q1) exact ratio  r = <A^2,B^2> / (||A^2|| ||B^2||)   [cos of angle]
 (Q2) "q-uncorrelation" test: is <A^2,B^2> ~ (sumA^2)(sumB^2)/q ?
      define indep value V = (sumA^2)(sumB^2)/q ; measure <A^2,B^2>/V (want ~1)
      and V/(||A^2|| ||B^2||) = the "independent cos" (want <=1/2).
 (Q3) diagonal-half test: is <A^2,B^2> exactly half CS by a reality/parity argument?
Domains: 'off-D' (s0 not in G u {0}) = the rung domain, and 'all' (all s0 in F).
"""
import cmath, math

def run_cell(p, n, m, d, domain='offD', verbose=True):
    def is_gen(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=x*g%p
            if x in seen: return False
            seen.add(x)
        return len(seen)==p-1
    g=next(a for a in range(2,p) if is_gen(a))
    dlog={}; x=1
    for k in range(p-1):
        dlog[x]=k; x=x*g%p
    assert (p-1)%m==0 and (p-1)%n==0
    def chi_pow(t):
        def f(a):
            if a%p==0: return 0j
            return cmath.exp(2j*math.pi*((t*dlog[a%p])%m)/m)
        return f
    G=sorted({pow(g,(p-1)//n*j,p) for j in range(n)})
    q=p; sq=math.sqrt(q)
    mprime=m//math.gcd(m,d)
    fine=list(range(1,m))
    coarse=[d*t%m for t in range(1,mprime)]      # Y block = chiFamily(chi^d)
    Omega=[t for t in fine if t not in coarse]    # complement block
    # regime check: chi^t(-1) = 1 for all t (2m | q-1)  -> realness
    even_regime = ((p-1) % (2*m) == 0)
    T={t:[sum(chi_pow(t)((s0-x)%p) for x in G) for s0 in range(p)] for t in fine}
    def gauss(t):
        c=chi_pow(t)
        return sum(c(a)*cmath.exp(2j*math.pi*a/p) for a in range(1,p))
    gs={t:gauss(t) for t in fine}

    D=set(G)|{0}
    if domain=='offD':
        S=[s for s in range(p) if s not in D]
    else:
        S=list(range(p))

    # M'(s0) = -n + Main_Y(s0),  Main_Y = sum_{t in coarse} g(t) conj T_t(s0)
    # Res(s0) = sum_{t in Omega} g(t) conj T_t(s0)
    Mp=[-n + sum(gs[t]*T[t][s].conjugate() for t in coarse) for s in S]
    Rv=[sum(gs[t]*T[t][s].conjugate() for t in Omega) for s in S]
    maxImM=max(abs(z.imag) for z in Mp)
    maxImR=max(abs(z.imag) for z in Rv)
    A=[z.real for z in Mp]
    B=[z.real for z in Rv]

    sumA2=sum(a*a for a in A); sumB2=sum(b*b for b in B)
    sumA4=sum(a**4 for a in A); sumB4=sum(b**4 for b in B)
    inner=sum(a*a*b*b for a,b in zip(A,B))          # <A^2,B^2> = sum A^2 B^2
    CS=math.sqrt(sumA4)*math.sqrt(sumB4)
    ratio = inner/CS if CS>0 else float('nan')      # Q1 cos
    V = sumA2*sumB2/q                                # independent value
    indep_cos = V/CS if CS>0 else float('nan')      # Q2b
    corr = inner/V if V>0 else float('nan')          # Q2a  (want ~1)
    if verbose:
        print(f"p={p} n={n} m={m} d={d} m'={mprime} |Omega|={len(Omega)} dom={domain} "
              f"even={even_regime} |S|={len(S)}")
        print(f"   maxIm M'={maxImM:.2e} Res={maxImR:.2e}")
        print(f"   Q1 ratio <A2,B2>/CS      = {ratio:.4f}   (target <= 0.5)")
        print(f"   Q2 indep cos V/CS        = {indep_cos:.4f}   (V=(SA2)(SB2)/q)")
        print(f"   Q2 corr  <A2,B2>/V       = {corr:.4f}   (want ~1 => q-uncorrelated)")
        print(f"   sumA2={sumA2:.4g} sumB2={sumB2:.4g} sumA4={sumA4:.4g} sumB4={sumB4:.4g}")
    return dict(ratio=ratio, indep_cos=indep_cos, corr=corr, inner=inner, V=V, CS=CS,
                sumA2=sumA2, sumB2=sumB2, sumA4=sumA4, sumB4=sumB4, mprime=mprime,
                even=even_regime, maxImM=maxImM, maxImR=maxImR)

if __name__=="__main__":
    cells=[(97,8,16,8),(193,8,16,8),(257,8,16,4),(1153,8,16,8),
           (1153,8,16,4),(40961,8,16,8),(40961,8,16,4)]
    for (p,n,m,d) in cells:
        for dom in ('offD','all'):
            run_cell(p,n,m,d,domain=dom)
        print()
