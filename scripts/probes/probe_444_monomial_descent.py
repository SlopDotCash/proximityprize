#!/usr/bin/env python3
"""
probe_444_monomial_descent.py  (#444, SEAM A: even/odd non-symmetric descent)

Tests the NEW descent recursion for the window list size on 2-power mu_n.

Claim chain (the new math):
  (1) DESCENT IDENTITY: for n=2N, f(x)=F(x^2)+xG(x^2), u(x)=u_e(x^2)+x u_o(x^2),
      P=F-u_e, Q=G-u_o, then agreement |S| = 2*#commonroots(P,Q in mu_N)
      + #{y in mu_N : Q(y)!=0 and P(y)^2 = y Q(y)^2}.  (the single-fiber term is deg O(k))
  (2) MONOMIAL CONSTANCY: the list of a MONOMIAL word w=y^j on mu_N, code RS[k'], at window
      radius, is CONSTANT in N (does not grow). Monomials descend to monomials -> closes.
  (3) CONSEQUENCE: consecutive-word list <= product of two monomial lists -> constant.

If (2) holds with constant lists, this is a proof PATH for the explicit-2-power RS
window list-decoding bound (a "related quantity" to the prize). Verify, do not assume.

Exact arithmetic, proper subgroups mu_N != p-1, multiple primes, window-interior radius.
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

def find_window_prime(N, beta=4.0, idx_min=2):
    target = int(N ** beta)
    base = target - (target % N) + 1
    p = base
    while True:
        if p > N and isprime(p) and (p - 1) % N == 0 and (p - 1) // N >= idx_min:
            return p
        p += N

def subgroup(N, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // N, p)
    elts, x = [], 1
    for _ in range(N):
        elts.append(x); x = (x * zeta) % p
    assert len(set(elts)) == N
    return elts

def poly_coeffs(xs, ys, p):
    k = len(xs); coeffs = [0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        inv=pow(den,p-2,p); scale=(ys[i]*inv)%p
        for t in range(len(num)): coeffs[t]=(coeffs[t]+scale*num[t])%p
    return tuple(coeffs)

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r

def peval(coeffs,x,p):
    r=0
    for c in reversed(coeffs): r=(r*x+c)%p
    return r

def full_list(uvals, elts, k, s, p):
    """all deg<k polys agreeing with u on >= s points; return list of (coeffs, agreement_size)."""
    N=len(elts); idxs=list(range(N)); seen={}
    for T in itertools.combinations(idxs,k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=poly_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in idxs if peval(c,elts[i],p)==uvals[i])
        seen[c]=ag
    return [(c,a) for c,a in seen.items() if a>=s]

def monomial_list(N, j, kp, eta, beta=4.0, primes=2):
    """worst over primes: list size of word y^j on mu_N, code deg<kp, agreement s=ceil((? )N)."""
    results=[]
    ps=[]
    p=find_window_prime(N,beta); ps.append(p)
    p2=find_window_prime(N,beta+0.5)
    if p2!=p and primes>1: ps.append(p2)
    for p in ps:
        elts=subgroup(N,p)
        uv=[pow(x,j,p) for x in elts]
        # window radius: rho'=kp/N, s = round((rho'+eta)*N), clamp
        rho=kp/N; s=round((rho+eta)*N)
        s=max(s,kp); s=min(s,N)
        if comb(N,kp)>3_000_000:
            results.append((p,None)); continue
        lst=full_list(uv,elts,kp,s,p)
        results.append((p,len(lst),s))
    return results

def run_monomial_constancy(eta=0.25):
    print(f"\n### MONOMIAL-WORD LIST CONSTANCY (eta={eta}) ###")
    print("  word y^j on mu_N, code deg<kp; checking if list is CONSTANT in N")
    for kp in [2,3,4]:
        print(f"  -- kp={kp} (rho'~{kp}/N) --")
        for N in [8,16,32,64]:
            if kp>=N: continue
            # pick a 'far' monomial exponent j (>= kp so not a codeword), e.g. j=N-1, j=N//2+1
            for j in sorted(set([kp, N//2+1, N-1, N-kp])):
                if j<=0 or j>=N: continue
                res=monomial_list(N,j,kp,eta)
                vals=[r[1] for r in res if len(r)>1 and r[1] is not None]
                if not vals:
                    print(f"    N={N:3d} j={j:3d}: SKIP(too big)"); continue
                s=res[0][2] if len(res[0])>2 else '?'
                print(f"    N={N:3d} j={j:3d} kp={kp} s={s}: list sizes over primes = {vals}")

def verify_descent_identity():
    """numerically verify the agreement decomposition formula for random f,u."""
    print("\n### DESCENT IDENTITY CHECK ###")
    N=16; n=2*N
    p=find_window_prime(n,4.0)
    eltsn=subgroup(n,p)
    # squaring map to mu_N
    sq={x:(x*x)%p for x in eltsn}
    eltsN=sorted(set(sq.values()))
    import random
    random.seed(1)
    ok=0; tot=0
    for trial in range(200):
        k=6
        # random codeword f on mu_n, random word u (consecutive a)
        coeffs=[random.randrange(p) for _ in range(k)]
        a=random.randrange(2,n)
        uv={x:(pow(x,a,p)+pow(x,a-1,p))%p for x in eltsn}
        # direct agreement
        S=[x for x in eltsn if peval(coeffs,x,p)==uv[x]]
        direct=len(S)
        # decomposition: split f into even/odd in x: F(y),G(y); u into u_e,u_o
        # f(x)=sum coeffs[i] x^i; even part F(y)=sum_{i even} coeffs[i] y^{i/2}, odd part coeff of x: G(y)=sum_{i odd} coeffs[i] y^{(i-1)/2}
        # u: a-> if a even u_e=y^{a/2},u_o=y^{a/2-1}; a odd u_e=y^{(a-1)/2},u_o=y^{(a-1)/2}
        def F(y):
            r=0
            for i in range(0,k,2): r=(r+coeffs[i]*pow(y,i//2,p))%p
            return r
        def G(y):
            r=0
            for i in range(1,k,2): r=(r+coeffs[i]*pow(y,(i-1)//2,p))%p
            return r
        if a%2==0: ue=lambda y:pow(y,a//2,p); uo=lambda y:pow(y,a//2-1,p)
        else: ue=lambda y:pow(y,(a-1)//2,p); uo=lambda y:pow(y,(a-1)//2,p)
        cnt2=0; cnt1=0
        for y in eltsN:
            P=(F(y)-ue(y))%p; Q=(G(y)-uo(y))%p
            if P==0 and Q==0: cnt2+=1
            elif Q!=0 and (P*P-y*Q*Q)%p==0: cnt1+=1
        decomp=2*cnt2+cnt1
        tot+=1
        if decomp==direct: ok+=1
        elif trial<5:
            print(f"    MISMATCH a={a} direct={direct} decomp={decomp} (2*{cnt2}+{cnt1})")
    print(f"    descent identity holds {ok}/{tot} random trials")

if __name__=="__main__":
    verify_descent_identity()
    run_monomial_constancy(eta=0.25)
    run_monomial_constancy(eta=0.125)
