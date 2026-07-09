#!/usr/bin/env python3
"""
probe_444_parity_argument.py  (#444 SEAM A)

TASK 1 focused: the even-vs-odd degree PARITY argument.

The claim:  R(y) := (F-F')^2 - y(G - sigma G')^2  has even-degree leading term from the square
minus odd-degree term from y*(square); a perfect square can't equal y*(square) as a POLYNOMIAL
identity, so R != 0 as a polynomial, hence R has <= deg R <= about k roots, so overlap <= k (ish).

We dissect this with explicit symbolic degrees AND test whether R is actually forced to be the
zero polynomial by a large overlap.

Key correction to test:  the relation on the overlap is  (F-F')(y) = -x (G-G')(y)  at points x in
the common agreement set, which gives the POINTWISE  (F-F')^2 = y (G-G')^2 ONLY at those y (NOT a
poly identity, NO free sigma sign). The question is whether overlap > deg(R) forces R==0.

deg(R): deg F, deg F' < kF = ceil(k/2); deg G, deg G' < kG = floor(k/2).
   deg (F-F')^2 <= 2(kF-1).   deg y(G-G')^2 <= 1 + 2(kG-1).
   R has degree <= max(2(kF-1), 2kG-1).  For k even: kF=kG=k/2 => max(2(k/2-1), 2(k/2)-1)=
      max(k-2, k-1)=k-1.  For k odd: kF=(k+1)/2,kG=(k-1)/2 => max(k-1, k-2)=k-1.
   So deg R <= k-1 in general.  R lives over mu_N (N=n/2 points). If R has > k-1 distinct roots in
   mu_N it must be the zero poly.

   BUT overlap counts points x in mu_n, i.e. fibre roots; the y-values (=x^2) of the overlap are
   <= overlap distinct y's but could be as few as overlap/2 (full fibres) up to overlap (single).
   The number of distinct y at which (F-F')^2 = y(G-G')^2 is what bounds against deg R = k-1.

We TEST: (a) is R ever the zero polynomial for DISTINCT members (would refute parity claim)?
         (b) does (F-F')^2=y(G-G')^2 hold at MORE than k-1 distinct y for a distinct pair? If yes
             => R==0 => parity claim false.  We measure #distinct-y where it holds vs deg R.
         (c) the sigma freedom: does the SAME overlap relation ever need sigma=-1 (it shouldn't;
             the real relation has fixed sign G-G').
"""
import itertools
from sympy import isprime, primitive_root, symbols, Poly, GF

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r

def interp_coeffs(xs,ys,p):
    k=len(xs); c=[0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        inv=pow(den,p-2,p); sc=(ys[i]*inv)%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return tuple(c)

def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r

def list_RS_members(uvals, elts, k, s, p):
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

def split_FG(c, k):
    c = list(c) + [0]*(k-len(c))
    F = tuple(c[i] for i in range(0,k,2))
    G = tuple(c[i] for i in range(1,k,2))
    return F,G

def build_word(exps, elts, p):
    return [sum(pow(x,a,p) for a in exps)%p for x in elts]

def poly_sub(a,b,p):
    L=max(len(a),len(b)); r=[0]*L
    for i in range(L):
        ai=a[i] if i<len(a) else 0; bi=b[i] if i<len(b) else 0
        r[i]=(ai-bi)%p
    return tuple(r)

def poly_sq(a,p): return tuple(poly_mul(a,a,p))
def poly_shift(a,p):  # multiply by y
    return tuple([0]+list(a))
def poly_trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0: a.pop()
    return tuple(a)
def deg(a):
    a=poly_trim(a); return len(a)-1 if any(x!=0 for x in a) else -1

def R_poly(F,Fp,G,Gp,sigma,p):
    dF=poly_sub(F,Fp,p)
    dG=poly_sub(G,tuple((sigma*g)%p for g in Gp),p)
    return poly_trim(poly_sub(poly_sq(dF,p), poly_shift(poly_sq(dG,p),p), p))

def run(n,k,eta,words):
    rho=k/n; s=round((rho+eta)*n); s=max(s,k)
    p=find_window_prime(n,4.0); elts=subgroup(n,p); N=n//2
    kF=(k+1)//2; kG=k//2
    print(f"\n  n={n} k={k} s={s} p={p}  kF(degF<)={kF} kG(degG<)={kG}  N=|mu_N|={N}  "
          f"predicted deg R <= k-1 = {k-1}")
    for wn,exps in words:
        u=build_word(exps,elts,p)
        members=sorted(list_RS_members(u,elts,k,s,p))
        if len(members)<2:
            print(f"    {wn}: |L|={len(members)} (skip)"); continue
        agsets=[frozenset(i for i in range(n) if peval(c,elts[i],p)==u[i]) for c in members]
        Rzero_distinct=0; max_y_hits=0; sigma_needed=set()
        printed=0
        for i in range(len(members)):
            for j in range(i+1,len(members)):
                ci,cj=members[i],members[j]
                F,G=split_FG(ci,k); Fp,Gp=split_FG(cj,k)
                ov=len(agsets[i]&agsets[j])
                # distinct y in the overlap
                ys_overlap=set(pow(elts[t],2,p) for t in (agsets[i]&agsets[j]))
                # check the REAL relation (sigma=+1, fixed sign G-G') pointwise on overlap:
                relA=all((peval(F,pow(elts[t],2,p),p)-peval(Fp,pow(elts[t],2,p),p)
                          + elts[t]*(peval(G,pow(elts[t],2,p),p)-peval(Gp,pow(elts[t],2,p),p)))%p==0
                         for t in (agsets[i]&agsets[j]))
                # #distinct y where (F-Fp)^2 = y(G-Gp)^2 holds (over ALL mu_N, sigma=+1)
                yhits=0
                for x in elts[:N] if False else subgroup(N,p):
                    dF=(peval(F,x,p)-peval(Fp,x,p))%p
                    dG=(peval(G,x,p)-peval(Gp,x,p))%p
                    if (dF*dF - x*dG*dG)%p==0: yhits+=1
                max_y_hits=max(max_y_hits,yhits)
                Rp=R_poly(F,Fp,G,Gp,1,p); Rm=R_poly(F,Fp,G,Gp,-1,p)
                isz_p=(deg(Rp)<0); isz_m=(deg(Rm)<0)
                if isz_p: sigma_needed.add('+1->R==0')
                if isz_m: sigma_needed.add('-1->R==0')
                if (isz_p or isz_m):
                    Rzero_distinct+=1
                if printed<5 and ov>=1:
                    print(f"      pair({i},{j}) ov={ov} ys_in_ov={len(ys_overlap)} relA(real,sigma=+1)={relA} "
                          f"degR+={deg(Rp)} degR-={deg(Rm)} Rzero+={isz_p} Rzero-={isz_m} "
                          f"#y:(dF^2=y dG^2)={yhits}/{N}")
                    printed+=1
        print(f"    {wn}: |L|={len(members)}  distinct pairs with R==0 (some sigma)={Rzero_distinct}  "
              f"max #y-hits over pairs={max_y_hits} (vs deg R bound k-1={k-1})  sigma_modes={sigma_needed}")

if __name__=="__main__":
    print("="*90)
    print("#444 PARITY-ARGUMENT DISSECTION (Task 1): is R=(F-F')^2 - y(G-sigma G')^2 ever 0?")
    print("="*90)
    # use words that produce large lists w/ mixed members per memory note (worst window x^{n/4}+x^e+1)
    cfgs=[
        (16,2,0.125,[("x^4+1",[4,0]),("x^4+x+1",[4,1,0]),("x^4+x^3+1",[4,3,0]),
                     ("x^2+x+1",[2,1,0]),("x^6+x+1",[6,1,0]),("x^5+x^3+1",[5,3,0])]),
        (16,4,0.0625,[("x^4+1",[4,0]),("x^4+x+1",[4,1,0]),("x^6+x^3+1",[6,3,0])]),
        (32,4,0.125,[("x^8+1",[8,0]),("x^8+x+1",[8,1,0]),("x^8+x^3+1",[8,3,0]),
                     ("x^{12}+x^5+1",[12,5,0])]),
    ]
    for (n,k,eta,words) in cfgs:
        run(n,k,eta,words)
