#!/usr/bin/env python3
"""
probe_444_worstfamily_n64.py  (#444 SEAM A, G2 decisive question)

THIRD 2-power data point at n=64 for the conjectured worst-word FAMILY.

Setting: explicit 2-power Reed-Solomon. Evaluation domain mu_n = n-th roots of unity in F_p,
n=2^mu, p "prize-shaped" (p ~ n^beta, index m=(p-1)/n >= 2, NOT p=n+1).
Code = deg<k polys, rate rho=k/n. Window list L(u,n,k,s) = # distinct deg<k polys agreeing
with u on >= s points of mu_n. Window interior s=round((rho+eta)*n) with eta=rho (so s=2k),
clamped s>=k, s<=n. BEYOND Johnson.

DECISIVE QUESTION (G2): does worst-case window list L* GROW with n or stay bounded/constant?
Prior verified data at rho=1/16: L*~7 at n=16 and n=32, worst word x^{n/4}+1.

This script computes L for a FAMILY of candidate worst words at rho=1/16 (k=n/16),
window interior s clamped >=k, for n=16(k=1), n=32(k=2), n=64(k=4), over TWO prize primes
each (beta=4.0 and 4.5). For n=64,k=4 the k-subset count C(64,4)=635376 is handled by an
optimized exact enumeration (vectorized agreement check via precomputed Vandermonde powers).
"""
import itertools, sys, time
from math import comb
from sympy import isprime, primitive_root

# ----- reused decoder primitives (from probe_444_worstword_exponent.py) -----
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

# ----- optimized exact window-list enumeration -----
# Precompute, for each domain point i, the row of powers [x_i^0 .. x_i^{k-1}] (Vandermonde).
# For a candidate poly with coeff tuple c, peval(c, x_i) = dot(powrow_i, c) mod p.
# We dedup by coeff tuple, and for each unique tuple count agreements via the matrix.
def list_RS_fast(uvals, elts, k, s, p):
    n=len(elts)
    # Vandermonde rows: pow_rows[i] = [x_i^0, ..., x_i^{k-1}]
    pow_rows=[]
    for x in elts:
        row=[1]*k
        for t in range(1,k):
            row[t]=(row[t-1]*x)%p
        pow_rows.append(row)
    seen=set()
    # iterate over k-subsets, interpolate, dedup, then count agreements with full eval
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        # count agreement over all n points using precomputed power rows (Horner-free dot)
        ag=0
        for i in range(n):
            row=pow_rows[i]; acc=0
            for t in range(k):
                ct=c[t]
                if ct: acc+=row[t]*ct
            if acc%p==uvals[i]: ag+=1
        if ag>=s: seen.add(c)
    return len(seen)

def classify_members(members, n):
    """Describe structure of the list members (coeff tuples, deg<k)."""
    info={'monomial':0,'binomial':0,'even':0,'total':len(members),'degs':{}}
    for c in members:
        # trim trailing zeros for degree
        deg=-1
        nz=[t for t,ct in enumerate(c) if ct!=0]
        if nz:
            deg=nz[-1]
        info['degs'][deg]=info['degs'].get(deg,0)+1
        nzc=len(nz)
        if nzc==1: info['monomial']+=1
        elif nzc==2: info['binomial']+=1
        # even poly: only even-degree terms nonzero
        if all(t%2==0 for t in nz): info['even']+=1
    return info

def list_RS_members(uvals, elts, k, s, p):
    """Same as list_RS_fast but returns the set of member coeff tuples."""
    n=len(elts)
    pow_rows=[]
    for x in elts:
        row=[1]*k
        for t in range(1,k):
            row[t]=(row[t-1]*x)%p
        pow_rows.append(row)
    seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=0
        for i in range(n):
            row=pow_rows[i]; acc=0
            for t in range(k):
                ct=c[t]
                if ct: acc+=row[t]*ct
            if acc%p==uvals[i]: ag+=1
        if ag>=s: seen.add(c)
    return seen

def make_word(spec, elts, p, n):
    """spec is a function name; returns word values u over mu_n."""
    out=[]
    for x in elts:
        out.append(spec(x,p,n))
    return out

# Candidate worst-word family. Each is u(x) over mu_n. Use x^{-1}=x^{n-1} since x^n=1.
def w_xq4_plus1(x,p,n):   return (pow(x,n//4,p)+1)%p          # x^{n/4}+1   (conjectured worst)
def w_xq4_plus_xinv(x,p,n): return (pow(x,n//4,p)+pow(x,n-1,p))%p  # x^{n/4}+x^{-1}
def w_xq8_plus1(x,p,n):   return (pow(x,n//8,p)+1)%p          # x^{n/8}+1
def w_xq4(x,p,n):         return pow(x,n//4,p)                # x^{n/4} (monomial)

def consecutive(a):
    def f(x,p,n): return (pow(x,a,p)+pow(x,a-1,p))%p          # x^a + x^{a-1}
    return f

def run(n,k,eta,betas=(4.0,4.5)):
    rho=k/n
    rows=[]
    for beta in betas:
        p=find_window_prime(n,beta)
        elts=subgroup(n,p)
        m=(p-1)//n
        s=round((rho+eta)*n); s=max(s,k); s=min(s,n)
        words=[
            ("x^(n/4)+1",     w_xq4_plus1),
            ("x^(n/4)+x^-1",  w_xq4_plus_xinv),
            ("x^(n/8)+1",     w_xq8_plus1),
            ("x^(n/4)",       w_xq4),
        ]
        # consecutive all-ones words x^a+x^{a-1} for a few a (only valid for n>=8)
        cons_as=[n//4, n//4+1, n//8, n//2-1] if n>=8 else []
        for a in cons_as:
            if 1<=a<n and a!=n//2 and (a-1)!=n//2:
                words.append((f"x^{a}+x^{a-1}", consecutive(a)))
        for name,spec in words:
            t0=time.time()
            u=make_word(spec, elts, p, n)
            members=list_RS_members(u, elts, k, s, p)
            L=len(members)
            info=classify_members(members, n)
            dt=time.time()-t0
            rows.append((n,k,rho,s,beta,p,m,name,L,info,dt))
            print(f"  n={n:3d} k={k} rho={rho:.4f} s={s} beta={beta} p={p} m={m} "
                  f"word={name:16s} L={L:4d}  mono={info['monomial']} bino={info['binomial']} "
                  f"even={info['even']} degs={info['degs']}  ({dt:.1f}s)", flush=True)
    return rows

if __name__=="__main__":
    print("### #444 G2: worst-word FAMILY window-list across n=16,32,64 at rho=1/16 ###")
    print("### s = round((rho+eta)*n), eta=rho, clamped >=k ###\n")
    allrows=[]
    configs=[(16,1,1/16),(32,2,1/16),(64,4,1/16)]
    for (n,k,eta) in configs:
        print(f"--- n={n}, k={k} (rho=1/16), eta={eta:.4f} ---", flush=True)
        allrows += run(n,k,eta)
        print()
    # Focused tabulation for the conjectured worst word x^{n/4}+1
    print("\n### FOCUS TABLE: L(x^(n/4)+1) vs n ###")
    print("  n    k    s   beta   p              m       L   structure")
    for r in allrows:
        n,k,rho,s,beta,p,m,name,L,info,dt=r
        if name=="x^(n/4)+1":
            struct=f"mono={info['monomial']} bino={info['binomial']} even={info['even']}"
            print(f"  {n:<4} {k:<4} {s:<3} {beta:<6} {p:<14} {m:<7} {L:<3} {struct}")
    print("\n### FOCUS TABLE: max L over the family vs n ###")
    print("  n    beta   maxL  achieving-word(s)")
    for (n,k,eta) in configs:
        for beta in (4.0,4.5):
            sub=[r for r in allrows if r[0]==n and r[4]==beta]
            if not sub: continue
            mx=max(r[8] for r in sub)
            winners=[r[7] for r in sub if r[8]==mx]
            print(f"  {n:<4} {beta:<6} {mx:<5} {winners}")
