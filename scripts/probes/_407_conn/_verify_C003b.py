import itertools, math
from math import comb

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs
def primitive_root(q):
    facs=factorize(q-1)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in facs): return g
    raise RuntimeError
def mu_subgroup(q,n):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%q
    return S,h
def esymm(subset,j,q):
    if j==0: return 1%q
    if j>len(subset): return 0
    tot=0
    for c in itertools.combinations(subset,j):
        p=1
        for x in c: p=(p*x)%q
        tot=(tot+p)%q
    return tot%q
def variety_count(mu,a,t,q):
    cnt=0
    for Sb in itertools.combinations(mu,a):
        ok=all(esymm(Sb,j,q)==0 for j in range(1,t))
        if ok: cnt+=1
    return cnt

primes16=[97,113,193,241,257,337,353,401,433,449,577,641,769,929,1153,1409,1601,
          2017,4001,8081,12289,40961,65537]
# attacker's other named counterexamples: (a=6,t=2) char-0=C(8,3)=56 ; (a=5,t=2) char-0=0 (2 not | 5)
for (a,t,base) in [(6,2,comb(8,3)),(5,2,0),(7,2,0)]:
    print(f"\n=== (n=16,a={a},t={t}): char-0/coset-union baseline = {base} ===")
    for q in primes16:
        if (q-1)%16: continue
        mu,h=mu_subgroup(q,16)
        cnt=variety_count(mu,a,t,q)
        flag = "" if cnt==base else "  <-- DEVIATES from char-0"
        print(f"  q={q:6d} (n^{math.log(q)/math.log(16):.2f})  #variety={cnt}{flag}")
