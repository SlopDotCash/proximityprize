#!/usr/bin/env python3
"""
probe_444_branching_mechanism.py  (#444 SEAM A, list-decoding side)

Tests the BRANCHING=1 hypothesis for the even/odd dyadic descent of explicit
2-power Reed-Solomon list-decoding.

Setup. mu_n = n-th roots of unity in F_p, n=2^mu, p prize-shaped (p~n^4,
index (p-1)/n >= 2). Code = deg<k polys. Squaring map pi: mu_n -> mu_N
(N=n/2), x |-> y=x^2, fibre {x,-x}.

Even/odd split: any deg<k poly f(x) = F(x^2) + x*G(x^2) with
  deg F < ceil(k/2),  deg G < floor(k/2).
Received word u(x) = u_e(x^2) + x*u_o(x^2) where
  u_e(y) = (u(x)+u(-x))/2,  u_o(y) = (u(x)-u(-x))/(2x).

Descent identity (proven axiom-clean in Lean):
  agreement(f,u on mu_n) = 2A + B  where
    A = #{y in mu_N : F(y)=u_e(y) AND G(y)=u_o(y)}    (BOTH fibre roots agree)
    B = #{y in mu_N : (F-u_e)(y)^2 = y*(G-u_o)(y)^2 AND (G-u_o)(y) != 0}
        (exactly ONE fibre root agrees; the NON-SYMMETRIC single-fibre term)

Classification of a list member f with split (F,G):
  EVEN  : G == 0  (descends cleanly to level mu-1, an RS word in F over mu_N)
  MIXED : G != 0  (carried by the single-fibre B term)

Hypotheses under test:
  H1  branching=1: #EVEN members == |L(u_e, N, ceil(k/2))|, the level-(mu-1) list.
  H2  #MIXED is O(1) (bounded correction, independent of n).
  H3  for MIXED members, B <= deg of the descent poly (F-y^c)^2 - y*G^2 for
      a word x^a = x^{2c} (even a); B exceeds budget only for mid-exponent words.
"""
import itertools
from math import comb
from sympy import isprime, primitive_root

# ----- reused decoder primitives (verbatim from probe_444_worstword_exponent.py) -----
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
    """Return the FULL set of distinct deg<k coeff-tuples agreeing with u on >= s pts."""
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

def list_RS(uvals, elts, k, s, p):
    return len(list_RS_members(uvals, elts, k, s, p))

# ----- even/odd split machinery -----
def split_FG(c, k):
    """Given coeff tuple c (length k, deg<k poly f(x)=sum c_i x^i), return (F,G)
    where f(x)=F(x^2)+x*G(x^2). F = even-index coeffs, G = odd-index coeffs."""
    c = list(c) + [0]*(k-len(c))
    F = tuple(c[i] for i in range(0,k,2))   # coeffs of y^0,y^1,... in F(y)
    G = tuple(c[i] for i in range(1,k,2))
    return F,G

def is_even_member(c, k):
    F,G = split_FG(c,k)
    return all(g==0 for g in G)

def build_word(exps, elts, p):
    """word u(x)=sum_{a in exps} x^a (weight = len(exps))."""
    return [sum(pow(x,a,p) for a in exps)%p for x in elts]

def squaring_fibres(elts, p):
    """Return (mu_N elements list yN, and for each y the fibre indices into elts)."""
    n=len(elts); N=n//2
    yvals = [pow(x,2,p) for x in elts]
    # mu_N = distinct squares, in canonical order = first N elements squared (since
    # elts[i]^2 = elts[2i mod n]); we build a list of distinct y and their fibre.
    fib = {}
    for i,x in enumerate(elts):
        y=yvals[i]
        fib.setdefault(y,[]).append(i)
    yN = list(fib.keys())
    return yN, fib

def even_odd_decompose(uvals, elts, p):
    """Return (u_e: dict y->val, u_o: dict y->val) over mu_N."""
    n=len(elts)
    half_inv = pow(2,p-2,p)
    u_e={}; u_o={}
    yN, fib = squaring_fibres(elts,p)
    for y in yN:
        idxs = fib[y]
        # fibre {x,-x}: identify them. -x is the element with index (i+n//2) mod n.
        i = idxs[0]
        j = (i + n//2) % n
        x = elts[i]
        ux = uvals[i]; uminus = uvals[j]
        u_e[y] = ((ux+uminus)*half_inv)%p
        # u_o(y) = (u(x)-u(-x))/(2x)
        invx = pow(x,p-2,p)
        u_o[y] = ((ux-uminus)*half_inv%p)*invx%p
    return u_e, u_o

def measure_B(F, G, u_e, u_o, p):
    """B = #{y in mu_N : (F-u_e)(y)^2 = y*(G-u_o)(y)^2 AND (G-u_o)(y)!=0}."""
    B=0
    for y in u_e:
        dF = (peval(F,y,p) - u_e[y])%p
        dG = (peval(G,y,p) - u_o[y])%p
        if dG==0: continue
        if (dF*dF)%p == (y*dG*dG)%p:
            B+=1
    return B

def measure_A(F, G, u_e, u_o, p):
    A=0
    for y in u_e:
        if peval(F,y,p)==u_e[y] and peval(G,y,p)==u_o[y]:
            A+=1
    return A

# ----- main analysis -----
def analyze(word_name, exps, n, k, s_override=None, eta=None, primes=2):
    """Full ground-truth analysis for one word at level n (computes level mu-1 list too)."""
    N=n//2
    kF = (k+1)//2   # ceil(k/2)  -> deg F < kF
    rho = k/n
    if s_override is not None:
        s = s_override
    else:
        s = round((rho+eta)*n); s=max(s,k)
    ps=[find_window_prime(n,4.0), find_window_prime(n,4.5)]
    ps=list(dict.fromkeys(ps))[:primes]
    rows=[]
    for p in ps:
        elts=subgroup(n,p)
        u=build_word(exps,elts,p)
        members = list_RS_members(u,elts,k,s,p)
        u_e,u_o = even_odd_decompose(u,elts,p)
        # level mu-1 descended list: L(u_e, mu_N, ceil(k/2)) at agreement threshold.
        # The descent identity: an EVEN member f=F(x^2) agrees with u on 2A points
        # (B=0 since G=0 => dG=-u_o; the B term needs dG!=0 & dF^2=y dG^2, but for
        # EVEN members the agreement is 2*#{F=u_e} ONLY when u_o=0 on those y... ).
        # The clean descended threshold for the EVEN sublist is sF = ceil(s/2):
        # f even agrees on >= s pts  <=>  2*#{F(y)=u_e(y), and the fibre contributes 2}
        # Actually agreement(F(x^2),u) = #{x: F(x^2)=u(x)} = sum over y of [F(y)=u(x)]
        # counted per fibre root. We instead derive sF empirically below, but the
        # natural prediction is L(u_e,N,kF) at threshold ceil(s/2).
        elts_N = [pow(x,2,p) for x in elts][:N]
        # canonical mu_N order: use distinct squares preserving subgroup(N,?) — build directly
        eltsN = subgroup(N,p) if (p-1)%N==0 else None
        u_e_vec=None
        if eltsN is not None:
            u_e_vec=[u_e[y] for y in eltsN]
        sF = (s+1)//2  # ceil(s/2)
        L_descended = None
        if u_e_vec is not None:
            L_descended = list_RS(u_e_vec, eltsN, kF, sF, p)
        # classify members
        nEven=0; nMixed=0; maxB=0; Bvals=[]; identity_ok=True; details=[]
        for c in members:
            F,G = split_FG(c,k)
            A = measure_A(F,G,u_e,u_o,p)
            B = measure_B(F,G,u_e,u_o,p)
            true_ag = sum(1 for i in range(len(elts)) if peval(c,elts[i],p)==u[i])
            if 2*A+B != true_ag:
                identity_ok=False
            if all(g==0 for g in G):
                nEven+=1
            else:
                nMixed+=1
                Bvals.append(B); maxB=max(maxB,B)
            details.append((c,A,B,true_ag,all(g==0 for g in G)))
        rows.append(dict(word=word_name,n=n,k=k,s=s,p=p,Ltot=len(members),
                         nEven=nEven,nMixed=nMixed,Ldesc=L_descended,sF=sF,
                         maxB=maxB,Bvals=sorted(Bvals,reverse=True)[:6],
                         identity_ok=identity_ok,details=details))
    return rows

def fmt_rows(rows):
    out=[]
    for r in rows:
        out.append(f"  {r['word']:<14} n={r['n']:<3} k={r['k']:<2} s={r['s']:<3} "
                   f"p={r['p']:<9} |L|={r['Ltot']:<4} #EVEN={r['nEven']:<4} "
                   f"#MIXED={r['nMixed']:<4} L(u_e,N,ceil(k/2))@sF={r['sF']}={r['Ldesc']!s:<5} "
                   f"maxB={r['maxB']:<3} topB={r['Bvals']} id2A+B={'OK' if r['identity_ok'] else 'FAIL'}")
        if not r['identity_ok'] or r['Bvals'] and r['maxB']==0:
            for (c,A,B,ag,ev) in r['details']:
                out.append(f"        member c={c} A={A} B={B} 2A+B={2*A+B} true_ag={ag} {'EVEN' if ev else 'MIXED'}")
    return "\n".join(out)

def scan_all_words_for_B(n, k, eta, weight=2, beta=4.0):
    """Brute over ALL weight-`weight` words x^{a1}+...; for each, find list members
    with B>0 (genuinely single-fibre-carried), report the max B observed and which word/
    member achieves it, and flag any word whose #EVEN members exceeds the descended list
    L(u_e,N,ceil(k/2)) (a branching>1 event)."""
    p=find_window_prime(n,beta); elts=subgroup(n,p); N=n//2
    kF=(k+1)//2; rho=k/n; s=round((rho+eta)*n); s=max(s,k); sF=(s+1)//2
    eltsN=subgroup(N,p) if (p-1)%N==0 else None
    maxB_global=0; maxB_word=None; branchgt1=[]; anyBpos=[]
    exps_pool=range(0,n)
    for combo in itertools.combinations(exps_pool,weight):
        if any(a==n//2 for a in combo): continue
        u=build_word(list(combo),elts,p)
        members=list_RS_members(u,elts,k,s,p)
        if not members: continue
        u_e,u_o=even_odd_decompose(u,elts,p)
        nEven=0; localmaxB=0; bpos=False
        for c in members:
            F,G=split_FG(c,k)
            if all(g==0 for g in G):
                nEven+=1
            else:
                B=measure_B(F,G,u_e,u_o,p)
                if B>0: bpos=True
                localmaxB=max(localmaxB,B)
        if localmaxB>maxB_global:
            maxB_global=localmaxB; maxB_word=combo
        if bpos: anyBpos.append((combo,localmaxB,len(members)))
        # descended even-list comparison
        if eltsN is not None:
            u_e_vec=[u_e[y] for y in eltsN]
            Ldesc=list_RS(u_e_vec,eltsN,kF,sF,p)
            if nEven>Ldesc:
                branchgt1.append((combo,nEven,Ldesc))
    return dict(n=n,k=k,s=s,p=p,maxB=maxB_global,maxB_word=maxB_word,
                nWordsBpos=len(anyBpos),Bpos_sample=anyBpos[:8],
                branchgt1=branchgt1)

if __name__=="__main__":
    print("="*100)
    print("#444 BRANCHING MECHANISM: even/odd descent classification of window list members")
    print("="*100)

    # window interior s = round((rho+eta)*n) per task; here both word and code share rho,
    # interior s ~ round((rho+rho)*n) = round(2*rho*n) = round(2k) for eta=rho.
    configs = []
    for (n, ks, etas) in [
        (16, [2,4], [0.125, 0.0625]),   # rho=1/8 (k=2), rho=1/16-ish; we sweep k & eta below
        (32, [4],   [0.125, 0.0625]),
    ]:
        pass

    # Explicit config list following the task: n in {16,32}, rho=1/8 (k=2 at n=16, k=4 at n=32),
    # also rho=1/16 (k=1 at n=16, k=2 at n=32). window interior s=round((rho+rho)*n)=round(2k).
    test_set = [
        # (n, k, eta) with eta=rho so s=round(2*rho*n)=2k (the "window interior s=round((rho+rho)n)")
        (16, 2, 0.125),    # rho=1/8, s=4
        (16, 1, 0.0625),   # rho=1/16, s=2
        (32, 4, 0.125),    # rho=1/8, s=8
        (32, 2, 0.0625),   # rho=1/16, s=4
    ]

    for (n,k,eta) in test_set:
        N=n//2
        words = [
            (f"x^{n//4}+1",        [n//4, 0]),         # worst word
            (f"x^{n//4}",          [n//4]),            # pure monomial mid-exponent
            (f"x^{n//4}+x+1",      [n//4, 1, 0]),      # weight-3
            (f"1+x^2",             [0, 2]),            # small even-exponent pair
        ]
        print(f"\n----- n={n}, k={k} (rho={k/n:.4f}), eta={eta}, s=round((rho+rho)*n)="
              f"{round((k/n+k/n)*n)} -----")
        for wname,exps in words:
            rows = analyze(wname, exps, n, k, eta=eta)
            print(fmt_rows(rows))

    print("\n" + "="*100)
    print("FULL SCAN over ALL weight-2 words: hunt for genuine B>0 members + branching>1 events")
    print("="*100)
    for (n,k,eta) in test_set:
        r=scan_all_words_for_B(n,k,eta,weight=2)
        print(f"\n  n={n} k={k} s={r['s']} p={r['p']}:")
        print(f"    max B over ALL weight-2 words = {r['maxB']}  (achieved by exps {r['maxB_word']})")
        print(f"    # weight-2 words with ANY B>0 member = {r['nWordsBpos']}")
        if r['Bpos_sample']:
            print(f"    sample (exps, localMaxB, |L|): {r['Bpos_sample']}")
        print(f"    branching>1 events (#EVEN > L(u_e,N,ceil(k/2))): {r['branchgt1'] if r['branchgt1'] else 'NONE'}")
