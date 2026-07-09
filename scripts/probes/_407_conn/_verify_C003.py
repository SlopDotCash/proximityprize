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
    assert (q-1)%n==0
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%q
    assert len(set(S))==n
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

# (1) verify the named char-p escape witness S={1,8,18,70} in mu_16 over F_97
q=97; n=16
mu,h=mu_subgroup(q,n)
print("mu_16 over F_97:", sorted(mu))
S={1,8,18,70}
print("S subset mu?", S.issubset(set(mu)))
print("sum(S) mod 97 = e_1 =", sum(S)%q)
# closed under negation? negation = mult by -1 = q-x ... but in mu, -1 = element of order 2
neg1 = (q-1)%q  # -1 mod q
print("-1 mod q =", neg1, " in mu?", neg1 in mu)
negS = {(neg1*x)%q for x in S}
print("negS =", sorted(negS), "closed under neg?", negS==S)

# (2) The CRUCIAL adversarial check: is the q-dependence a SMALL-PRIME artifact?
# Test (n=16,a=4,t=2): variety = {|S|=4, e_1=0}. Count over MANY primes q=1 mod 16.
print("\n=== (n=16,a=4,t=2): #variety over many proper-subgroup primes ===")
print("char-0 / coset-union baseline C(8,2) =", comb(8,2))
primes16=[97,113,193,241,257,337,353,401,433,449,577,593,641,673,769,881,929,977,
          1153,1217,1249,1297,1361,1409,1489,1553,1601,1697,1777,2017,
          12289,40961,65537]
for q in primes16:
    if (q-1)%16: continue
    mu,h=mu_subgroup(q,16)
    cnt=0
    for Sb in itertools.combinations(mu,4):
        if esymm(Sb,1,q)==0: cnt+=1
    print(f"  q={q:6d} (q/n^?={math.log(q)/math.log(16):.2f})  #variety={cnt}")
