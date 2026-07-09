# Part 3: correct GLT + anomaly defect = char-0 vs char-p E_r gap (the "Betti error")
import itertools, cmath, math
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
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    return sub

def Er(sub,p,r):
    c=Counter()
    for t in itertools.product(sub,repeat=r): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

def char0_Er(n,r):
    h=n//2
    a=[1/(math.factorial(k)**2) for k in range(r+1)]
    poly=[1.0]+[0.0]*r
    for _ in range(h):
        np_=[0.0]*(r+1)
        for i in range(r+1):
            if poly[i]==0: continue
            for j in range(r+1-i):
                np_[i+j]+=poly[i]*a[j]
        poly=np_
    return poly[r]*math.factorial(2*r)

def gaussian_moment(n,r):
    """Real-Gaussian analogy: sum of n iid points on unit circle (random walk),
       E|S|^{2r} where S = sum of n unit complex numbers with random phase.
       The Wick/sub-Wick value for genuinely random phases is n^r * r! (complex Gaussian).
       For our DETERMINISTIC roots-of-unity sum the relevant comparison is Bessel char0."""
    return (n**r)*math.factorial(r)  # complex-Gaussian 2r-th moment

print("=== The deep-moment analogy quartet (char-0 regime, no anomaly) ===")
print("E_r(char-p) | E_r(char-0 Bessel) | complex-Gaussian n^r r! | (2r-1)!! n^r [Wick]")
print(f"{'p':>5}{'n':>4}{'r':>3} | {'Ep':>10} {'Bessel':>10} {'CplxGauss':>10} {'Wick':>10} {'anomaly':>9}")
for p,n in [(97,4),(257,8),(257,16),(17,4),(17,8),(73,8),(193,8)]:
    if (p-1)%n: continue
    sub=setup(p,n)
    for r in [2,3]:
        ep=Er(sub,p,r)
        b=char0_Er(n,r)
        cg=gaussian_moment(n,r)
        wick=math.prod(2*i-1 for i in range(1,r+1))*(n**r)  # (2r-1)!! n^r
        anomaly=ep-b
        print(f"{p:>5}{n:>4}{r:>3} | {ep:>10d} {b:>10.0f} {cg:>10d} {wick:>10.0f} {anomaly:>9.0f}")

# KEY analogy direction check: is char-0 Bessel ALWAYS a LOWER bound for char-p E_r? (anomaly>=0)
print("\n=== Anomaly sign test (is char-p E_r >= char-0 Bessel always?) ===")
allpos=True
import random
for p in [17,41,73,89,97,113,193,257,337,433]:
    for n in [4,8,16]:
        if (p-1)%n: continue
        sub=setup(p,n)
        for r in [2,3,4]:
            if n**r > 5*10**6: continue
            ep=Er(sub,p,r); b=char0_Er(n,r)
            if ep < b-1e-6:
                print(f"  NEGATIVE anomaly! p={p} n={n} r={r}: Ep={ep} < Bessel={b:.0f}")
                allpos=False
print("  all anomalies >= 0 (char-p E_r >= char-0 Bessel):", allpos)
