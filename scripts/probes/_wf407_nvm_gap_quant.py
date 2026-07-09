"""
Quantify the exact numeric GAP between what R3/NVM delivers and the prize.
- NVM delivers: det != 0 (a 0/1 nonvanishing predicate) -- WHEN it holds.
- Over mu_n at 2-power index it does NOT even hold: fraction of singular
  distinct-degree minors grows with the 2-adic depth a = log2(n).
- The prize needs B <= C*sqrt(n log m). NVM nonsingularity is logically
  orthogonal to B. We report both: (i) the failure rate of NVM vs 2-adic
  depth, (ii) that B is uninformed by det even where det != 0.
"""
import itertools, math, cmath
def is_prime(x):
    if x<2:return False
    i=2
    while i*i<=x:
        if x%i==0:return False
        i+=1
    return True
def primitive_root(p):
    if p==2:return 1
    f=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:f.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in f):return g
def det(M,p):
    M=[r[:] for r in M];n=len(M);dd=1
    for c in range(n):
        piv=None
        for r in range(c,n):
            if M[r][c]%p:piv=r;break
        if piv is None:return 0
        if piv!=c:M[c],M[piv]=M[piv],M[c];dd=(-dd)%p
        inv=pow(M[c][c],p-2,p);dd=(dd*M[c][c])%p
        for r in range(c+1,n):
            ff=(M[r][c]*inv)%p
            for cc in range(c,n):M[r][cc]=(M[r][cc]-ff*M[c][cc])%p
    return dd%p

print("NVM FAILURE RATE over mu_{2^a} (distinct-degree 3x3 minors singular):")
print(f"{'a':>2} {'n=2^a':>6} {'p':>6} {'singular/total':>18} {'fail-rate':>10}")
for a in range(1,6):
    n=2**a
    p=None
    for q in range(101,40000):
        if is_prime(q) and (q-1)%n==0:p=q;break
    g=primitive_root(p);m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    r=3
    if n<3: 
        print(f"{a:>2} {n:>6} {p:>6}  (n<3, skip r=3)")
        continue
    tot=0;sing=0
    for degs in itertools.combinations(range(n),r):
        for pts in itertools.combinations(H,r):
            M=[[pow(x,d,p) for d in degs] for x in pts]
            tot+=1
            if det(M,p)==0:sing+=1
    print(f"{a:>2} {n:>6} {p:>6}  {sing:>7}/{tot:<9} {sing/tot:>10.4f}")

print()
print("Control prime n (NVM holds, fail-rate 0):")
for n in [3,5,7,11,13]:
    p=None
    for q in range(101,40000):
        if is_prime(q) and (q-1)%n==0:p=q;break
    g=primitive_root(p);m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    r=3; tot=0;sing=0
    for degs in itertools.combinations(range(n),r):
        for pts in itertools.combinations(H,r):
            M=[[pow(x,d,p) for d in degs] for x in pts]
            tot+=1
            if det(M,p)==0:sing+=1
    print(f"   n={n:3d} (prime) p={p}: {sing}/{tot} singular  rate={sing/tot:.4f}")
