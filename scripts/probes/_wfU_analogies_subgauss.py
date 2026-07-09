# Part 6: Salem-Zygmund sub-Gaussian face + dyadic-tower fold + B=max-of-m extreme value
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

def periods(p,n):
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    etas=[sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub) for b in range(p)]
    return sub,etas

# B = max_{b!=0} |eta_b|.  Claim (C006/C080): B ~ sqrt(n log m), m=(p-1)/n,
#   NOT 2 sqrt(n) [Ramanujan].  Extreme-value of m sub-Gaussians of variance n.
print("=== Extreme-value law: B/sqrt(n) vs B/sqrt(n log m) ===")
print(f"{'p':>6}{'n':>4}{'m':>6} | {'B':>8} {'B/sqrt(n)':>10} {'B/sqrt(n ln m)':>14}")
for p,n in [(257,8),(769,8),(3329,8),(7681,8),(12289,8),(12289,16),(40961,8),(65537,16)]:
    if (p-1)%n: continue
    m=(p-1)//n
    _,etas=periods(p,n)
    B=max(abs(etas[b]) for b in range(1,p))
    bsn=B/math.sqrt(n)
    bsnl=B/math.sqrt(n*math.log(m)) if m>1 else float('nan')
    print(f"{p:>6}{n:>4}{m:>6} | {B:>8.3f} {bsn:>10.4f} {bsnl:>14.4f}")

# Dyadic tower fold (anchor): eta_b(mu_{2n}) = eta_b(mu_n) + eta_{zeta b}(mu_n),
# zeta = generator coset rep mapping mu_n -> the other coset of mu_{2n}.
# Test: |eta_b(mu_{2n})|^2 <= 2(|eta_b(mu_n)|^2+|eta_{zeta b}(mu_n)|^2) parallelogram tower
print("\n=== Dyadic parallelogram tower: M(2n)^2 <= 2 M(n)^2 ? (B^2 sub-doubling) ===")
print(f"{'p':>6}{'n':>4} | {'M(n)^2':>10} {'M(2n)^2':>10} {'ratio':>7} {'<=2?':>5}")
for p in [257,769,3329,12289,40961,65537]:
    for n in [4,8,16]:
        if (p-1)%(2*n): continue
        _,en=periods(p,n); _,e2n=periods(p,2*n)
        Mn2=max(abs(en[b])**2 for b in range(1,p))
        M2n2=max(abs(e2n[b])**2 for b in range(1,p))
        ratio=M2n2/Mn2
        print(f"{p:>6}{n:>4} | {Mn2:>10.3f} {M2n2:>10.3f} {ratio:>7.3f} {str(ratio<=2.0001):>5}")
