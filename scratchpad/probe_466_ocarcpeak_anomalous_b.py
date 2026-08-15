"""
Pin the anomalous b at the canonical cell n=32, p=4129, K=5 (census r369 neighborhood).
Question: is the max-achieving coset arithmetically structured relative to mu_n?
If the anomaly is structural, we can state a no-go on generic/union-bound recovery of the max.

We examine:
 - the top-few cosets by S(b), their reps.
 - whether the max coset's arc histogram is "peaked" (one arc holds many H-points) => a
   short-interval / small-difference cluster (the CG object).
 - the *ratio structure*: for the max b, which arc holds the cluster, and is that cluster a
   coset of a SUBGROUP of H (a sub-2-power)? i.e. does b*mu_n concentrate a coset of mu_m, m|n
   into one arc = an arithmetic-progression / GP resonance.
"""
import math

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; m=phi; fac=[]; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

p=4129; n=32; K=5
assert is_prime(p) and (p-1)%n==0
g=primitive_root(p)
gen=pow(g,(p-1)//n,p)
H=[]; x=1
for _ in range(n): H.append(x); x=x*gen%p
Hset=set(H)

def hist(b):
    buckets={}
    for h in H:
        a=(K*((b*h)%p))//p
        buckets.setdefault(a,[]).append((b*h)%p)
    return buckets

def S(b):
    bk=hist(b)
    return sum(len(v)*len(v) for v in bk.values())

# reps one per coset
reps=[]; seen=set()
for b in range(1,p):
    if b in seen: continue
    reps.append(b)
    for h in H: seen.add((b*h)%p)

scored=sorted(((S(b),b) for b in reps), reverse=True)
print("Top 6 cosets by S(b):")
for sval,b in scored[:6]:
    bk=hist(b)
    sizes=sorted((len(v) for v in bk.values()),reverse=True)
    # discrete log of b base g (position in F_p^*)
    dl=None
    y=1
    for e in range(p-1):
        if y==b: dl=e; break
        y=y*g%p
    print(f"  b={b:5d} S={sval:4d} arc_sizes={sizes} dlog(b) mod {n}={dl%n if dl is not None else '?'} dlog={dl}")

print("\nBottom 3 (most uniform):")
for sval,b in scored[-3:]:
    bk=hist(b)
    sizes=sorted((len(v) for v in bk.values()),reverse=True)
    print(f"  b={b:5d} S={sval:4d} arc_sizes={sizes}")

# The max coset: is its peak arc a coset of a subgroup mu_m (m|n)?
smax,bmax=scored[0]
bk=hist(bmax)
peak_arc=max(bk,key=lambda a:len(bk[a]))
peak_pts=set(bk[peak_arc])
# the H-elements landing in peak arc:
peak_h=[h for h in H if (bmax*h)%p in peak_pts]
print(f"\nMax coset b={bmax}, peak arc={peak_arc}, #H in peak arc={len(peak_h)}")
# are these peak_h a coset of a subgroup of H? test: is peak_h/peak_h[0] a subgroup?
h0=peak_h[0]
h0inv=pow(h0,p-2,p)
normed=sorted((h*h0inv)%p for h in peak_h)
# is 'normed' multiplicatively closed subset of H?
nset=set(normed)
closed=all((a*b)%p in nset for a in normed for b in normed) if len(normed)<=64 else None
print(f"peak_h normalized (÷first) is mult-closed subgroup? {closed}  (size {len(normed)})")
print(f"normalized set sample: {normed[:8]}")
# Is it an arithmetic progression in the exponent (=> a sub-2-power coset)?
# map each peak_h to its dlog base gen (index in H)
idx=[]
y=1; pos={}
for e in range(n):
    pos[y]=e; y=y*gen%p
peak_idx=sorted(pos[h] for h in peak_h)
print(f"exponent positions in H of peak points: {peak_idx}")
diffs=[peak_idx[i+1]-peak_idx[i] for i in range(len(peak_idx)-1)]
print(f"consecutive gaps in exponent: {diffs}")
