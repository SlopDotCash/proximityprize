# Part 5: autocorrelation r(h)=|mu_n cap (mu_n+h)| = Fourier-square of eta (C021/C092),
# and the curve-incidence T(H)=#{(b,c) in H^2: 1+b-c in H} energy chain (C092)
import cmath, math
from collections import Counter

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g

def setup(p,n):
    g=primitive_root(p); return set(pow(g,((p-1)//n)*k,p) for k in range(n))

# autocorr r(h) = #{(x,y) in mu_n^2 : x - y = h}
def autocorr(sub,p):
    r=Counter()
    for x in sub:
        for y in sub:
            r[(x-y)%p]+=1
    return r

# Claim C021: r(h) = (1/p) sum_b |eta_b|^2 exp(-2pi i h b/p)  (Fourier of |eta|^2)
def autocorr_from_periods(sub,p,h):
    etas=[abs(sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub))**2 for b in range(p)]
    s=sum(etas[b]*cmath.exp(-2j*math.pi*h*b/p) for b in range(p))/p
    return s

print("=== C021: r(h)=|mu_n cap(mu_n+h)| =?= (1/p)sum_b|eta_b|^2 e^{-2pi i hb/p} ===")
for p,n in [(73,8),(97,4),(257,8)]:
    sub=setup(p,n); ac=autocorr(sub,p)
    ok=True
    for h in range(p):
        lhs=ac.get(h,0)
        rhs=autocorr_from_periods(sub,p,h)
        if abs(lhs-rhs.real)>1e-6 or abs(rhs.imag)>1e-6: ok=False
    print(f"  p={p:>4} n={n}: all h match = {ok}")

# C092 energy chain: q*E(H) = sum_b |eta_b|^4   [this is E_2, already verified]
# AND   E = |H| * T(H),  T(H) = #{(b,c) in H^2 : 1+b-c in H}   (normalized curve-incidence)
print("\n=== C092: E_2(H) =?= |H| * T(H), T(H)=#{(b,c)in H^2: 1+b-c in H} ===")
for p,n in [(17,4),(17,8),(73,8),(97,4),(257,8),(257,16)]:
    if (p-1)%n: continue
    sub=setup(p,n)
    subl=sorted(sub)
    # E_2 = #{(a,b,c,d) in H^4 : a+b=c+d}
    c=Counter()
    for a in subl:
        for b in subl: c[(a+b)%p]+=1
    E2=sum(v*v for v in c.values())
    # T(H) = #{(b,c): 1+b-c in H}
    T=sum(1 for b in subl for cc in subl if (1+b-cc)%p in sub)
    print(f"  p={p:>4} n={n:>3}: E_2={E2:>6}  |H|*T={n*T:>6}  T={T:>4}  match={E2==n*T}")
