# Part 4: r=2 additive energy = Fermat CURVE point count (Hasse-Weil regime)
#         + the V_4 = 3p(n-1) - n^3 closed form (C010) + platykurtosis
import itertools, math
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
    g=primitive_root(p); return sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})

def Er(sub,p,r):
    c=Counter()
    for t in itertools.product(sub,repeat=r): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

# C010 claims V_4 = sum_s eta_s^4 = p*E_2 has closed form 3p(n-1)-n^3 when no anomaly.
# Test that closed form for the CHAR-0 / clean case (n=8 over p with no anomaly e.g. p=73,193,257)
print("=== C010 V_4 closed form: p*E_2 =?= 3p(n-1) - n^3  (clean cases) ===")
print(f"{'p':>5}{'n':>4} | {'p*E_2':>10} {'3p(n-1)-n^3':>13} {'match':>6}")
for p,n in [(257,8),(73,8),(193,8),(97,4),(257,16),(17,8)]:
    if (p-1)%n: continue
    sub=setup(p,n)
    pE2=p*Er(sub,p,n if False else 2)
    closed=3*p*(n-1)-n**3
    print(f"{p:>5}{n:>4} | {pE2:>10d} {closed:>13d} {str(pE2==closed):>6}")

# E_2 itself = 3p(n-1)/p - n^3/p ... actually E_2 = V_4/p. The Sidon-mod-neg char0 value
# is 3n^2-3n. Check: when does E_2 = 3n^2-3n exactly (the curve has NO extra F_p points)?
print("\n=== E_2 vs char-0 Sidon-mod-neg 3n^2-3n (Fermat-curve clean count) ===")
print(f"{'p':>5}{'n':>4} | {'E_2':>6} {'3n^2-3n':>8} {'clean':>6}")
for p in [17,41,73,89,97,113,137,193,233,257]:
    for n in [4,8]:
        if (p-1)%n: continue
        sub=setup(p,n)
        e2=Er(sub,p,2)
        c=3*n*n-3*n
        print(f"{p:>5}{n:>4} | {e2:>6d} {c:>8d} {str(e2==c):>6}")

# Platykurtosis (F13/C075): kurtosis of the eta_b distribution -> approaches 3 from BELOW
# kurtosis = E[|eta|^4]/E[|eta|^2]^2.  For complex: compare to 2 (cplx gauss) ; here real-ish.
print("\n=== Period-distribution kurtosis (excl b=0): E4/E2^2, complex-Gaussian=2 ===")
import cmath
def kurt(p,n):
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    etas=[abs(sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub))**2 for b in range(1,p)]
    m1=sum(etas)/len(etas)         # E|eta|^2
    m2=sum(e*e for e in etas)/len(etas)  # E|eta|^4
    return m2/(m1*m1)
for p,n in [(97,4),(257,8),(769,8),(1153,8),(3329,8)]:
    if (p-1)%n: continue
    print(f"  p={p:>5} n={n:>3}: kurtosis(|eta|^2) = {kurt(p,n):.4f}  (cplx-Gauss ref = 2.0)")
