#!/usr/bin/env python3
"""
#466 LANE S3 -- floor successor structure.

Recompute exact floor-bad witness patterns at n=16/p=17 and n=32/p=97, print
their algebraic structure (as subsets of Z/n), and test 16->32 lifting maps.

Predicate (floor_scan_exact.c / floor_scan_poly.c semantics):
  Points x_j = g0^j, j in Z/n, g0 of exact order n (p == 1 mod n).
  A subset A of Z/n is REALIZABLE (a floor-bad witness) iff
     rank[M_A] == rank[M_A | b_A],
     M_A rows (for j in A) = [x^0 .. x^{n/2-1} | -x^{n/2}], b = x^{3n/4}.
  Pattern space: 4 rotations c0; minority classes c0,c0+1 mod 4 pick agr_min=m-m/4
  of the m=n/4 elements; majority classes c0+2,c0+3 pick agr_maj=m-m/2. |A|=5n/8.

We use the equivalent poly test: r = x^{3n/4} mod V_A ; realizable iff r_k==0 for
k in [n/2+1, |A|-1].
"""
import sys, itertools
from itertools import combinations

def isprime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True

def generator(p):
    m=p-1
    fac=[]; mm=m; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.append(mm)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac):
            return h
    raise RuntimeError("no generator")

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j,bj in enumerate(b):
            r[i+j]=(r[i+j]+ai*bj)%p
    return r

def vanishing_poly(roots,p):
    # monic prod (x-root), low-to-high coeffs
    V=[1]
    for rt in roots:
        # multiply by (x - rt)
        newV=[0]*(len(V)+1)
        for i,c in enumerate(V):
            newV[i]=(newV[i]-rt*c)%p
            newV[i+1]=(newV[i+1]+c)%p
        V=newV
    return V

def x_pow_mod_V(deg, V, p):
    # return coeffs (len = len(V)-1) of x^deg mod V, V monic len D+1
    D=len(V)-1
    if deg<D:
        r=[0]*D; r[deg]=1; return r
    # start r = x^D mod V = -(V without leading)  (since x^D = V - (V-x^D))
    r=[(-V[k])%p for k in range(D)]  # x^D mod V
    for _ in range(deg-D):
        top=r[D-1]
        nr=[0]*D
        # multiply by x then reduce: x*r = sum r[k] x^{k+1}; x^D -> -(V low)
        for k in range(D-1,0,-1):
            nr[k]=(r[k-1]-top*V[k])%p
        nr[0]=(-top*V[0])%p
        r=nr
    return r

def realizable(A, Xpow, p, half, deg34):
    roots=[Xpow[j] for j in A]
    V=vanishing_poly(roots,p)
    D=len(V)-1  # = |A|
    r=x_pow_mod_V(deg34,V,p)
    for k in range(half+1, D):
        if r[k]!=0: return False
    return True

def setup(p,n):
    g=generator(p)
    g0=pow(g,(p-1)//n,p)
    Xpow=[pow(g0,j,p) for j in range(n)]
    return Xpow

def enumerate_realizable(p,n):
    m=n//4; half=n//2; deg34=3*n//4
    agr_min=m-m//4; agr_maj=m-m//2
    Xpow=setup(p,n)
    cls=[[j for j in range(n) if j%4==c] for c in range(4)]
    cmin=list(combinations(range(m),agr_min))
    cmaj=list(combinations(range(m),agr_maj))
    found=[]
    total=0
    for c0 in range(4):
        mn0,mn1,mj0,mj1=c0,(c0+1)%4,(c0+2)%4,(c0+3)%4
        for a in cmin:
            for b in cmin:
                for d in cmaj:
                    for e in cmaj:
                        A=[cls[mn0][i] for i in a]+[cls[mn1][i] for i in b]+\
                          [cls[mj0][i] for i in d]+[cls[mj1][i] for i in e]
                        total+=1
                        if realizable(A,Xpow,p,half,deg34):
                            found.append(tuple(sorted(A)))
    return found,total

def test_patterns(p,n,patterns):
    """test explicit subsets of Z/n for realizability."""
    m=n//4; half=n//2; deg34=3*n//4
    Xpow=setup(p,n)
    out=[]
    for A in patterns:
        out.append((tuple(sorted(A)), realizable(sorted(A),Xpow,p,half,deg34)))
    return out

def translate(A,t,n):
    return tuple(sorted((j+t)%n for j in A))

def orbit(A,n,step=1):
    seen=set(); cur=A
    for t in range(n):
        seen.add(translate(A,t,n))
    return seen

def analyze(found,n,label):
    print(f"\n===== {label}: n={n}, {len(found)} realizable patterns =====")
    S=set(found)
    # translation orbits under +1 mod n
    orbits=[]
    unassigned=set(S)
    while unassigned:
        a=next(iter(unassigned))
        orb=set()
        for t in range(n):
            orb.add(translate(a,t,n))
        # only keep those actually in S
        orb_in=orb & S
        orbits.append(sorted(orb_in))
        unassigned-=orb_in
    print(f"  # translation(+1) orbits within realizable set: {len(orbits)}")
    orbit_sizes=sorted(len(o) for o in orbits)
    print(f"  orbit sizes: {orbit_sizes}")
    # is the whole set closed under +1 translation?
    closed = all(translate(a,1,n) in S for a in S)
    print(f"  set closed under +1 translation: {closed}")
    closed4 = all(translate(a,4,n) in S for a in S)
    print(f"  set closed under +4 translation: {closed4}")
    # representative pattern structure
    rep=sorted(found[0])
    print(f"  representative A = {rep}")
    print(f"    complement = {sorted(set(range(n))-set(rep))}")
    print(f"    class distribution (mod4): {[sum(1 for j in rep if j%4==c) for c in range(4)]}")
    print(f"    residues mod4 of A: {sorted(j%4 for j in rep)}")
    # gaps
    ext=rep+[rep[0]+n]
    gaps=[ext[i+1]-ext[i] for i in range(len(rep))]
    print(f"    consecutive gaps (cyclic): {gaps}")
    return orbits, S

def energy(A,Xpow,p,half,deg34):
    roots=[Xpow[j] for j in A]
    V=vanishing_poly(roots,p)
    D=len(V)-1
    r=x_pow_mod_V(deg34,V,p)
    return sum(1 for k in range(half+1,D) if r[k]!=0)

def anneal_find(p,n,seed=1,restarts=400,steps=6000):
    """local search restricted to c0=0 to find one realizable pattern."""
    import random
    rng=random.Random(seed)
    m=n//4; half=n//2; deg34=3*n//4
    agr_min=m-m//4; agr_maj=m-m//2
    Xpow=setup(p,n)
    cls=[[j for j in range(n) if j%4==c] for c in range(4)]
    c0=0; mn0,mn1,mj0,mj1=0,1,2,3
    agr=[agr_min,agr_min,agr_maj,agr_maj]
    classes=[mn0,mn1,mj0,mj1]
    def build(sel):
        A=[]
        for ci,c in enumerate(classes):
            for i in sel[ci]:
                A.append(cls[c][i])
        return A
    for _ in range(restarts):
        sel=[rng.sample(range(m),agr[ci]) for ci in range(4)]
        E=energy(build(sel),Xpow,p,half,deg34)
        stagn=0
        for _s in range(steps):
            if E==0:
                return tuple(sorted(build(sel)))
            ci=rng.randrange(4)
            cur=sel[ci]
            missing=[x for x in range(m) if x not in cur]
            if not missing: continue
            pos=rng.randrange(len(cur)); old=cur[pos]
            new=rng.choice(missing)
            cur2=cur[:]; cur2[pos]=new
            sel2=sel[:]; sel2[ci]=cur2
            E2=energy(build(sel2),Xpow,p,half,deg34)
            if E2<=E:
                if E2<E: stagn=0
                else: stagn+=1
                sel=sel2; E=E2
            else:
                stagn+=1
            if stagn>1500: break
        if E==0:
            return tuple(sorted(build(sel)))
    return None

if __name__=="__main__":
    # n=16, p=17
    f16,tot16=enumerate_realizable(17,16)
    print(f"n=16 p=17: {len(f16)} realizable of {tot16}  (expect 160/2304)")
    orb16,S16=analyze(f16,16,"n=16 p=17")

    # sanity: confirm other n=16 primes are good
    for pp in [97,113,193,241,257]:
        fx,_=enumerate_realizable(pp,16)
        print(f"  n=16 p={pp}: {len(fx)} realizable (expect 0)")

    # dump all 160 rep-per-orbit
    print("\n--- all n=16/p=17 realizable patterns (sorted) ---")
    for A in sorted(S16):
        print("  ",A)
