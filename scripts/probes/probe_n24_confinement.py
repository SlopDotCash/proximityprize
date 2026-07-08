# N24 probe: are "bad" primes (where the DC-subtracted Wick r=2 rung is closest to failing / worst M)
# confined to high-v2(p-1)?  If bad primes need v2 >> mu, a GENERIC prize prime (v2 == mu) is good.
# We test the r=2 diagonal-subtracted energy ratio and M=max|eta_b| across primes p=1 mod n,
# tracking v2(p-1). n small for feasibility.
import cmath, math
def v2(x):
    v=0
    while x%2==0: x//=2; v+=1
    return v
def primes_1modn(n, lo, hi):
    out=[]
    x = lo + ((1-lo)%n)
    if x<lo: x+=n
    while x<hi:
        if x>2 and all(x%d for d in range(3,int(x**.5)+1,2)) and x%2:
            out.append(x)
        x+=n
    return out
def gen(p):
    for c in range(2,p):
        s=set(); v=1
        for _ in range(p-1):
            v=v*c%p; s.add(v)
        if len(s)==p-1: return c
def probe(n, lo, hi):
    rows=[]
    for p in primes_1modn(n, lo, hi):
        g=gen(p); m=(p-1)//n
        mun=[pow(g,m*i,p) for i in range(n)]
        e=lambda a: cmath.exp(2j*math.pi*a/p)
        # eta_b for b in coset reps (eta constant on mu_n cosets): just compute all b!=0, take max
        M=0.0
        for b in range(1,p):
            s=sum(e(b*x%p) for x in mun)
            a=abs(s)
            if a>M: M=a
        rows.append((p, v2(p-1), M/math.sqrt(n)))  # M/sqrt(n): Ramanujan=2, wall grows
    return rows
n=8
rows=probe(n, 3, 4000)
mu=v2(n)  # =3
print(f"n={n}, mu=v2(n)={mu}; M/sqrt(n) (Ramanujan bound=2). rows sorted by M desc:")
rows.sort(key=lambda r:-r[2])
for p,v,r in rows[:12]:
    print(f"  p={p:5d}  v2(p-1)={v:2d} ({'excess' if v>mu else 'minimal' if v==mu else 'LOW'})  M/sqrtn={r:.3f}")
print("... generic (v2==mu) primes M/sqrtn stats:")
gen_r=[r for p,v,r in rows if v==mu]
exc_r=[r for p,v,r in rows if v>mu]
import statistics as st
if gen_r: print(f"  v2==mu ({len(gen_r)} primes): max M/sqrtn={max(gen_r):.3f} mean={st.mean(gen_r):.3f}")
if exc_r: print(f"  v2> mu ({len(exc_r)} primes): max M/sqrtn={max(exc_r):.3f} mean={st.mean(exc_r):.3f}")
