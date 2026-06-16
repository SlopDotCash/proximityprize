#!/usr/bin/env python3
"""
probe_444_capstone_close.py  (#444 SEAM A) -- final closure checks for the capstone claim.

(A) SURJECTIVITY-BY-CONSTRUCTION: for every lacunary T (prod(x-t)=x^a-alpha x+c), the linear
    poly f(x)=alpha*x+(1-c) agrees with u=x^a+1 on ALL of T  (proves backward direction is a
    theorem, not luck). Check across primes & both a=2(defect) and a=4(no-defect).
(B) AGREEMENT-IS-EXACTLY-a: every window-list member of u=x^a+1 (k=2,s=a) agrees on EXACTLY a
    points (so no oversized agreement set / the binding radius is tight, T-size always a).
(C) BINDING-RADIUS sensitivity: if we LOWER s below a, do spurious non-lacunary members appear?
    (The claim is stated AT the binding radius s=gcd(a,n)=a. Confirm s=a is the right threshold:
    at s=a only lacunary members survive; at s=a-1 extra members with |T|=a-1 appear that are NOT
    in the bijection -- i.e. the binding radius is load-bearing.)
(D) LARGE-INDEX a=4 stress: confirm defect still 0 at index-1 and very large-index primes.
"""
import itertools
from sympy import isprime, primitive_root

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
def prod_coeffs(vals,p):
    poly=[1]
    for t in vals: poly=poly_mul(poly,[(-t)%p,1],p)
    return poly
def primes_idx(n,count,idx_min=2,pmin=0):
    out=[]; pp=n+1
    while len(out)<count:
        if pp>pmin and isprime(pp) and (pp-1)%n==0 and (pp-1)//n>=idx_min: out.append(pp)
        pp+=n
    return out
def list_RS_members(uvals,elts,k,s,p):
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

def A_surjectivity(n,a,p):
    elts=subgroup(n,p)
    bad=0; tested=0
    for Tidx in itertools.combinations(range(n),a):
        poly=prod_coeffs([elts[i] for i in Tidx],p)
        if not all(poly[j]==0 for j in range(2,a)): continue  # lacunary only
        tested+=1
        alpha=(-poly[1])%p; c=poly[0]
        f=((1-c)%p, alpha)  # beta=1-c, then f(x)=beta+alpha x
        u=[(pow(x,a,p)+1)%p for x in elts]
        if not all(peval(f,elts[i],p)==u[i] for i in Tidx): bad+=1
    return tested,bad

def B_agreement_exactly_a(n,a,p):
    elts=subgroup(n,p); u=[(pow(x,a,p)+1)%p for x in elts]
    members=list_RS_members(u,elts,2,a,p)
    sizes=set()
    for c in members:
        sizes.add(sum(1 for i in range(n) if peval(c,elts[i],p)==u[i]))
    return len(members), sorted(sizes)

def C_binding(n,a,p):
    elts=subgroup(n,p); u=[(pow(x,a,p)+1)%p for x in elts]
    out={}
    for s in [a, a-1, a-2 if a>=4 else None]:
        if s is None: continue
        m=list_RS_members(u,elts,2,s,p)
        # how many are lacunary-size-a (agree on exactly a) vs smaller
        exact_a=sum(1 for c in m if sum(1 for i in range(n) if peval(c,elts[i],p)==u[i])==a)
        out[s]=(len(m),exact_a)
    return out

if __name__=="__main__":
    print("="*100); print("(A) SURJECTIVITY: every lacunary T -> member f=alpha x+(1-c) agrees on all of T")
    print("="*100)
    for (n,a) in [(8,2),(16,2),(16,4),(12,3)]:
        for p in primes_idx(n,3,idx_min=2,pmin=8):
            t,b=A_surjectivity(n,a,p)
            print(f"  n={n} a={a} p={p}: lacunary tested={t}  construction-failures={b} "
                  f"{'OK' if b==0 else 'FAIL'}")
    print("\n"+"="*100); print("(B) AGREEMENT EXACTLY a for every window member (k=2,s=a)")
    print("="*100)
    for (n,a) in [(16,4),(32,8),(8,2),(16,2),(12,3),(20,4)]:
        p=primes_idx(n,1,idx_min=2,pmin= (60000 if n in(16,32) else 8))[0]
        L,sizes=B_agreement_exactly_a(n,a,p)
        print(f"  n={n} a={a} p={p}: |L|={L} distinct-agreement-sizes among members={sizes} "
              f"{'OK(all=a)' if sizes==[a] else 'NOTE'}")
    print("\n"+"="*100); print("(C) BINDING-RADIUS load-bearing: members at s=a vs s<a")
    print("="*100)
    for (n,a) in [(16,4),(20,4),(12,3)]:
        p=primes_idx(n,1,idx_min=2,pmin=(60000 if n==16 else 8))[0]
        out=C_binding(n,a,p)
        print(f"  n={n} a={a} p={p}: (|members|, #agree-exactly-a) by s: "
              + "  ".join(f"s={s}:{v}" for s,v in out.items()))
    print("\n"+"="*100); print("(D) a=4 defect=0 at index-1 and large-index primes")
    print("="*100)
    for (n,a) in [(16,4),(32,4)]:
        # index-1 primes (p-1 = n exactly => p=n+1 if prime) and large index
        idx1=primes_idx(n,3,idx_min=1,pmin=0)
        large=primes_idx(n,3,idx_min=2,pmin=n**5)  # huge index
        for grp,name in [(idx1,"idx>=1 small"),(large,"huge index ~n^5")]:
            tot=0
            for p in grp:
                elts=subgroup(n,p)
                img={}
                for i,x in enumerate(elts): img.setdefault(pow(x,a,p),[]).append(i)
                cosets=set(tuple(sorted(v)) for v in img.values())
                for Tidx in itertools.combinations(range(n),a):
                    poly=prod_coeffs([elts[i] for i in Tidx],p)
                    if all(poly[j]==0 for j in range(2,a)) and tuple(sorted(Tidx)) not in cosets:
                        tot+=1
            print(f"  n={n} a={a} {name} (primes {grp}): non-coset lacunary total = {tot}")
