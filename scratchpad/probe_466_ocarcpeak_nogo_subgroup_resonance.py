"""
NO-GO test: at the saddle, is the peak-arc cluster of the MAX coset EVER a coset of a proper
multiplicative subgroup mu_m < mu_n (m | n, m<n)?  If NEVER, the max-vs-mean wall is not an
algebraic subgroup resonance -- it is purely short-interval/additive (the CG object). This
closes the "sub-2-power resonance reopens the averaging route" hope.

We also record: peak fraction (largest arc / n), and whether the peak set, sorted by additive
lift value, is an INTERVAL/contiguous run (short-interval signature) rather than algebraic.
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
    phi=p-1; mm=phi; fac=[]; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def analyze(p,n,K):
    g=primitive_root(p); gen=pow(g,(p-1)//n,p)
    H=[]; x=1
    for _ in range(n): H.append(x); x=x*gen%p
    def hist(b):
        bk={}
        for h in H:
            a=(K*((b*h)%p))//p
            bk.setdefault(a,[]).append(h)   # store the H-element
        return bk
    def S(b):
        return sum(len(v)*len(v) for v in hist(b).values())
    reps=[]; seen=set()
    for b in range(1,p):
        if b in seen: continue
        reps.append(b)
        for h in H: seen.add((b*h)%p)
    smax=-1; bmax=None
    for b in reps:
        s=S(b)
        if s>smax: smax=s; bmax=b
    bk=hist(bmax)
    peak_arc=max(bk,key=lambda a:len(bk[a]))
    peak_h=bk[peak_arc]                 # H-elements in peak arc
    m=len(peak_h)
    # test: is peak_h a COSET of a proper subgroup of H?
    # a coset c*mu_d has size d|n; and (peak_h) c-normalized is mult-closed of size d.
    is_subgroup_coset=False
    if n % m == 0 and m>1 and m<n:
        c=peak_h[0]; cinv=pow(c,p-2,p)
        norm=set((h*cinv)%p for h in peak_h)
        # closed under mult AND inverse?
        closed=all((a*bb)%p in norm for a in norm for bb in norm)
        # and is it the actual mu_m subgroup? (contains 1)
        is_subgroup_coset = closed and (1 in norm)
    # short-interval signature: sort peak points by additive lift of (bmax*h), check contiguity
    lifts=sorted((bmax*h)%p for h in peak_h)
    span=lifts[-1]-lifts[0]
    # arc width in lift units:
    arcwidth=p/K
    contiguous = span <= arcwidth*1.001   # they're all in one arc by construction
    return dict(p=p,n=n,K=K,bmax=bmax,Smax=smax, peak_size=m, peak_frac=round(m/n,3),
                is_subgroup_coset=is_subgroup_coset,
                peak_span=span, arcwidth=round(arcwidth,1), in_one_arc=contiguous)

results=[]
for n in [8,16,32,64,128]:
    start=max(4*n*n,400)
    p=None
    for cand in range(start,start+80000):
        if is_prime(cand) and (cand-1)%n==0:
            p=cand; break
    if p is None: continue
    K=max(2,round(math.sqrt(2*math.pi*n/math.log(p))))
    results.append(analyze(p,n,K))

print("NO-GO: is the max-coset peak-arc cluster a coset of a PROPER subgroup mu_m<mu_n?\n")
for r in results:
    print(f"n={r['n']:3d} p={r['p']:7d} K={r['K']:2d} bmax={r['bmax']:6d} Smax={r['Smax']:5d} "
          f"peak={r['peak_size']:3d}/{r['n']} (frac={r['peak_frac']}) subgroup_coset={r['is_subgroup_coset']} in_one_arc={r['in_one_arc']}")
print("\nIf subgroup_coset=False across all cells => wall is NOT algebraic subgroup resonance; purely short-interval (CG).")
