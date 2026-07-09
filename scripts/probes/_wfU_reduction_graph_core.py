"""
LENS [reduction-graph] verification probe (FAST, convolution-based).
Verify the load-bearing IDENTITIES closing reduction-graph cycles among
F2 (Gauss-period house eta_b), F5 (additive energy E_r), F16 (relation count N0),
F18 (autocorrelation r(h)).
"""
import cmath, numpy as np
from sympy import primitive_root

def run(p, a):
    n = 2**a
    assert (p-1) % n == 0
    g0 = primitive_root(p)
    g = pow(g0, (p-1)//n, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*g) % p
    mu = sorted(set(mu)); assert len(mu)==n
    m = (p-1)//n
    w = cmath.exp(2j*cmath.pi/p)
    etas = np.array([sum(w**((b*y)%p) for y in mu) for b in range(p)])

    # indicator of mu in Z/p
    ind = np.zeros(p)
    for y in mu: ind[y]=1.0
    # r-fold sum distribution via FFT convolution (over Z/p cyclic)
    F = np.fft.fft(ind)
    def sumdist(r):
        return np.round(np.real(np.fft.ifft(F**r))).astype(np.int64)  # counts of r-tuples summing to s
    # E_r = sum_s (count_r(s))^2  ; N0(r)=count_r(0)
    out={}
    for r in [1,2,3]:
        cr = sumdist(r)
        E_r = int(np.sum(cr.astype(np.int64)**2))
        lhs = p*E_r
        rhs = float(np.sum(np.abs(etas)**(2*r)))
        out[('plancherel',r)] = (lhs, rhs, abs(lhs-rhs))
    n0out={}
    for r in [2,3,4]:
        cr = sumdist(r)
        N0 = int(cr[0])
        s = complex(np.sum(etas**r))
        n0out[r] = (s.real, p*N0, abs(s.real-p*N0), abs(s.imag))
    # distinct eta_b over b!=0
    vals=set()
    for b in range(1,p):
        vals.add((round(etas[b].real,6),round(etas[b].imag,6)))
    distinct=len(vals)
    # autocorrelation r(0)
    muset=set(mu); r0=sum(1 for y in mu if ((y-0)%p) in muset)
    return dict(p=p,a=a,n=n,m=m,distinct=distinct,r0=r0,plancherel=out,n0=n0out)

if __name__=="__main__":
    for (p,a) in [(17,4),(97,5),(193,6),(257,8),(769,8)]:
        try: R=run(p,a)
        except Exception as e:
            print(f"p={p} a={a}: SKIP {e}"); continue
        print(f"=== p={R['p']} n={R['n']}=2^{R['a']} m={R['m']} ===")
        print(f"  (IV) distinct eta_b(b!=0)={R['distinct']} vs m={R['m']} -> {'OK' if R['distinct']<=R['m'] else 'FAIL'}")
        print(f"  r(0)={R['r0']} vs n={R['n']} -> {'OK' if R['r0']==R['n'] else 'FAIL'}")
        for (t,r),(l,rr,d) in R['plancherel'].items():
            print(f"  (II/I) q*E_{r}={l}  sum|eta|^{2*r}={rr:.2f}  |d|={d:.2e} -> {'OK' if d<1e-3 else 'FAIL'}")
        for r,(sr,pN0,d,im) in R['n0'].items():
            print(f"  (III) Re sum eta^{r}={sr:.2f}  p*N0={pN0}  |d|={d:.2e} im={im:.2e} -> {'OK' if d<1e-2 and im<1e-2 else 'FAIL'}")

# ---- Appendix: dilation-collapse edge E(H)=|H|*T(H) and n | E(H)  (C092/C091) ----
def dilation_edge(p,a):
    import itertools
    from collections import Counter
    n=2**a
    g0=primitive_root(p); g=pow(g0,(p-1)//n,p)
    H=[]; x=1
    for _ in range(n):
        H.append(x); x=(x*g)%p
    H=sorted(set(H)); Hset=set(H)
    # additive energy E(H) = #{(a,b,c,d) in H^4 : a+b=c+d}
    c=Counter()
    for s in H:
        for t in H:
            c[(s+t)%p]+=1
    E=sum(v*v for v in c.values())
    # T(H) = #{(b,c) in H^2 : 1 + b - c in H}
    T=sum(1 for b in H for cc in H if ((1+b-cc)%p) in Hset)
    return E, n*T, (E==n*T), (E % n == 0)

print("\n--- dilation-collapse edge E(H)=|H|*T(H) and n|E(H) (C092) ---")
for (p,a) in [(17,4),(97,5),(193,6),(257,8),(769,8)]:
    try:
        E,nT,eq,dvd=dilation_edge(p,a)
        print(f"  p={p} n={2**a}: E(H)={E}  n*T(H)={nT}  E==n*T -> {'OK' if eq else 'FAIL'}   n|E -> {'OK' if dvd else 'FAIL'}")
    except Exception as e:
        print(f"  p={p}: SKIP {e}")
