"""
sweep_A33_realizability_v3.py  —  Actionable A33 (407-T05), FAST exact search.

Same question/object as v2 (max realizable RAGGED |S| vs sqrt(n*k), coset-unions separated),
but a MUCH faster exact search exploiting the structure:

  Realizability of a candidate set T = "exists deg-<k poly c and scalar gamma with
  c(x)=x^a+gamma x^b on T" is DOWNWARD-CLOSED in T (a subset of a realizable set is realizable),
  and the system has |T| equations in k+1 unknowns (c_0..c_{k-1}, gamma).  So:
    - any T with |T| <= k+1 is AUTOMATICALLY realizable (>= equations? no: <=k+1 unknowns, so
      a (k+1)-subset is generically realizable; exactly realizable when the (k+1)x(k+1) system
      is consistent -- it always is unless degenerate).  We DO NOT assume; we test.
    - the binding regime is |T| >= k+2: each extra point adds one equation; realizable iff the
      x^a-vector lies in span(V_k columns, x^b column) over T.

  FAST max-realizable search: realizability(T) iff rank([V_k(T) | x^b(T)]) == rank([... | x^a(T)]).
  We want the largest T.  Equivalent: the largest T on which the linear functional defined by
  "x^a is a combination of {1,x,...,x^{k-1}, x^b}" holds.  This is exactly: T avoids the
  "syndrome" -- the largest agreement set of the received word w_gamma(x)=x^a+gamma x^b with the
  (k+1)-dim space U_gamma = span{1,...,x^{k-1}} (deg-<k) under one free gamma.

  We compute the max agreement DIRECTLY:
    For each gamma in F_q:  received r_gamma(x) = x^a + gamma x^b  (a word in F_q^{mu_n}).
    Decode against RS[k] (deg-<k): the max agreement set = mu_n minus the min #errors, i.e.
    n - dist(r_gamma, C).  The agreement set itself = {x: c*(x)=r_gamma(x)} for the closest c*.
    But there can be MANY codewords; we want the MAX agreement = n - d_min.
  Then realizable max over gamma = max_gamma (n - dist(r_gamma, RS[k])).
  We compute dist via: for each k-subset basis we'd get a codeword -- too many.  Instead we use
  the EXACT agreement-set enumeration but pruned by the rank test, top-down, with the
  downward-closure giving aggressive pruning (a la max-clique on the "realizable" hypergraph).

  To keep it exact AND fast we use: enumerate gamma; for each gamma, the agreement positions of
  the BEST codeword = the largest set of evaluation points consistent with ONE deg-<k poly.
  Since C is RS (MDS), any k positions determine a codeword; agreement = positions where that
  codeword matches r_gamma.  So max-agreement(gamma) = max over k-subsets K of mu_n of
  |{x: c_K(x)=r_gamma(x)}| where c_K interpolates r_gamma on K.  That's C(n,k) per gamma --
  feasible for n<=16 (C(16,4)=1820, C(16,8)=12870) x q gammas.  For n=32 we SAMPLE gamma and
  use k-subset sampling + a greedy refinement, reporting a LOWER bound on the true max
  (conservative for "does it beat sqrt(nk)": if even the lower bound already < sqrt(nk) is not
  meaningful; we report the MAX FOUND, an under-estimate, so "beats" verdict at n=32 is only
  suggestive -- n=8,16 are exact and decisive).

Run:  python sweep_A33_realizability_v3.py
"""

import itertools, math, random

def inv_mod(a, q): return pow(a % q, q - 2, q)

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def prim_root(q):
    phi = q-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,phi//pf,q)!=1 for pf in fac): return g
    raise RuntimeError

def mu_n(n,q):
    assert (q-1)%n==0
    z = pow(prim_root(q),(q-1)//n,q)
    return [pow(z,j,q) for j in range(n)]

def divisors(n): return [d for d in range(1,n+1) if n%d==0]

def is_coset_union(Sexp,n):
    Sset=set(x%n for x in Sexp)
    if len(Sset)<=1: return False
    for d in divisors(n):
        if d==1 or d==n: continue
        g=n//d; H=[(i*g)%n for i in range(d)]
        if all(((s+h)%n in Sset) for s in Sset for h in H): return True
    return False

def interp_codeword(K, mu_elts, rvals, k, q):
    """interpolate deg-<k poly through points (mu_elts[j], rvals[j]) for j in K (|K|=k).
       Return coeff list (len k) or None if Vandermonde singular (distinct x => never singular)."""
    # solve V c = y, V[i][t]=x_i^t
    rows=[]; ys=[]
    for j in K:
        x=mu_elts[j]; rows.append([pow(x,t,q) for t in range(k)]); ys.append(rvals[j]%q)
    # gaussian elimination on augmented
    A=[rows[i][:]+[ys[i]] for i in range(k)]
    for c in range(k):
        piv=None
        for i in range(c,k):
            if A[i][c]%q!=0: piv=i;break
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]
        ip=inv_mod(A[c][c],q); A[c]=[(v*ip)%q for v in A[c]]
        for i in range(k):
            if i!=c and A[i][c]%q!=0:
                f=A[i][c]; A[i]=[(A[i][t]-f*A[c][t])%q for t in range(k+1)]
    return [A[i][k]%q for i in range(k)]

def eval_poly(coef, x, q):
    r=0
    for t in range(len(coef)-1,-1,-1):
        r=(r*x+coef[t])%q
    return r

def max_agreement_for_gamma(n,k,a,b,gamma,mu_elts,q,ksub_sample=None):
    """max |{x: c(x)=x^a+gamma x^b}| over deg-<k c, via k-subset interpolation (MDS)."""
    rvals=[(pow(mu_elts[j],a,q)+gamma*pow(mu_elts[j],b,q))%q for j in range(n)]
    best=0; best_S=None
    Ks = itertools.combinations(range(n),k) if ksub_sample is None else None
    if ksub_sample is not None:
        # sample k-subsets
        seen=set()
        Klist=[]
        for _ in range(ksub_sample):
            K=tuple(sorted(random.sample(range(n),k)))
            if K in seen: continue
            seen.add(K); Klist.append(K)
        Ks=Klist
    for K in Ks:
        coef=interp_codeword(K,mu_elts,rvals,k,q)
        if coef is None: continue
        S=[j for j in range(n) if eval_poly(coef,mu_elts[j],q)==rvals[j]]
        if len(S)>best:
            best=len(S); best_S=S
    return best,best_S

def maxes_by_class(n,k,a,b,q,gamma_sample=None,ksub_sample=None):
    mu_elts=mu_n(n,q)
    best_r=0; best_c=0; wit_r=None
    gammas = range(q) if gamma_sample is None else random.sample(range(q),min(gamma_sample,q))
    for gamma in gammas:
        m,S=max_agreement_for_gamma(n,k,a,b,gamma,mu_elts,q,ksub_sample=ksub_sample)
        if S is None: continue
        if is_coset_union(S,n):
            best_c=max(best_c,m)
        else:
            if m>best_r: best_r=m; wit_r=S
    return best_r,best_c,wit_r

def primes_1_mod_n(n,count,start):
    out=[]; cand=((start-1)//n)*n+1
    while cand<=start: cand+=n
    while len(out)<count:
        if cand>1 and is_prime(cand): out.append(cand)
        cand+=n
    return out

def genuine_dir(n,k,d):
    for bb in range(k,n):
        aa=bb+d
        if aa<n and math.gcd(aa-bb,n)==d: return aa,bb
    return None,None

def run(n,rhos,q_list,mu,gamma_sample=None,ksub_sample=None,exact_tag=""):
    print("="*96); print(f"n={n}=2^{mu}  {exact_tag}"); print("="*96)
    for rho in rhos:
        k=int(round(rho*n))
        if k<1: continue
        target=math.sqrt(n*k)
        print(f"\n  rho={rho} k={k} sqrt(n*k)={target:.3f}")
        ds=sorted(set(math.gcd(abs(aa-bb),n) for aa in range(k,n) for bb in range(k,n) if aa!=bb))
        print(f"    {'d':>4} {'s':>4} {'(a,b)':>9} {'q':>9} | {'MAXragged':>9} {'sqrt(nk)':>9} {'beats?':>7} {'orbit-inc':>10} {'MAXcoset':>9}")
        for d in ds:
            if d==n: continue
            s=n//d; a,b=genuine_dir(n,k,d)
            if a is None: continue
            t1=n/(2.0*d); oinc=t1+math.sqrt(t1*t1+n*(d-1)*(k-1)/d)
            q=q_list[0]
            if (q-1)%n!=0: continue
            mr,mc,_=maxes_by_class(n,k,a,b,q,gamma_sample=gamma_sample,ksub_sample=ksub_sample)
            beats="YES" if mr<target-1e-9 else ("tie" if abs(mr-target)<1e-9 else "no")
            print(f"    {d:>4} {s:>4} {('('+str(a)+','+str(b)+')'):>9} {q:>9} | {mr:>9} {target:>9.3f} {beats:>7} {oinc:>10.2f} {mc:>9}")

def chartest(n,rho,mu,q_list,gamma_sample=None,ksub_sample=None):
    k=int(round(rho*n)); target=math.sqrt(n*k)
    ds=sorted(set(math.gcd(abs(aa-bb),n) for aa in range(k,n) for bb in range(k,n) if aa!=bb
                  if math.gcd(abs(aa-bb),n) not in (1,n)))
    if not ds: return
    td=min(ds,key=lambda dd:abs(dd-max(2,int(round(n**0.5)))))
    a,b=genuine_dir(n,k,td)
    if a is None: return
    print(f"\n  [char-test n={n} rho={rho} k={k}] Kambire-worst d={td} s={n//td} (a,b)=({a},{b}) sqrt(nk)={target:.3f}")
    vals=[]
    for q in q_list:
        if (q-1)%n!=0: continue
        mr,mc,_=maxes_by_class(n,k,a,b,q,gamma_sample=gamma_sample,ksub_sample=ksub_sample)
        vals.append(mr)
        print(f"      q={q:>9} MAXragged={mr} MAXcoset={mc} beats={'YES' if mr<target-1e-9 else 'no'}")
    print(f"      -> ragged char-{'INDEP' if len(set(vals))==1 else 'DEP'} (values {sorted(set(vals))})")

if __name__=="__main__":
    print("\n### A33 v3 (fast exact n<=16, sampled n=32): realizable RAGGED max vs sqrt(n*k)\n")
    q8=primes_1_mod_n(8,6,17)
    run(8,[0.5,0.25],q8,3,exact_tag="(EXACT: all gamma, all k-subsets)")
    chartest(8,0.25,3,q8)

    q16=primes_1_mod_n(16,6,97)
    run(16,[0.5,0.25,0.125],q16,4,exact_tag="(EXACT: all gamma, all k-subsets)")
    chartest(16,0.25,4,q16)
    chartest(16,0.5,4,q16)

    q32=primes_1_mod_n(32,4,193)
    # n=32: sample gamma + sample k-subsets -> LOWER bound on true max (under-estimate)
    run(32,[0.25],q32,5,gamma_sample=400,ksub_sample=3000,exact_tag="(SAMPLED: lower bound on max)")
    chartest(32,0.25,5,q32,gamma_sample=400,ksub_sample=3000)
    print("\n### DONE.")
