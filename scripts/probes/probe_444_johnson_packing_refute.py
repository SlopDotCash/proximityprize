#!/usr/bin/env python3
"""
probe_444_johnson_packing_refute.py  (#444 SEAM A)

ADVERSARIAL VERIFICATION of the claim:
 "Two distinct window-list members (F,G),(F',G') for an EVEN word, on their common
  agreement set, satisfy (F-F')^2 = y(G - sigma G')^2 with sigma in {+1,-1}; perfect
  square cannot equal y*(square) by even/odd degree parity, so overlap > k forces
  F=F', G=+-G'.  Hence distinct mixed members pairwise overlap in <= 2k points; the
  packing route reduces to JOHNSON (tau > sqrt(rho)+rho/2)."

Tasks:
 (1) Re-derive (F-F')^2 = y(G-sigma G')^2 from per-fibre agreement; test parity argument.
 (2) Re-derive double-counting threshold tau > sqrt(rho)+rho/2; check it excludes tau<sqrt(rho).
 (3) NUMERICALLY measure actual pairwise overlap of distinct list members for an even word.
"""
import itertools
from math import comb, sqrt
from sympy import isprime, primitive_root

# ---- decoder primitives (verbatim from probe_444_branching_mechanism.py) ----
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

# ====================================================================
# TASK 3 (do it first; it grounds 1 & 2): ACTUAL pairwise overlaps
# ====================================================================
def actual_overlaps(word_name, exps, n, k, eta, primes=2):
    """For an EVEN word, list all members, compute pairwise overlap (# of mu_n points where
    both members agree with each other... no: where both AGREE WITH u). Report overlaps and
    compare to 2k."""
    rho=k/n; s=round((rho+eta)*n); s=max(s,k)
    ps=[find_window_prime(n,4.0), find_window_prime(n,4.5)]
    ps=list(dict.fromkeys(ps))[:primes]
    out=[]
    for p in ps:
        elts=subgroup(n,p)
        u=build_word(exps,elts,p)
        members=sorted(list_RS_members(u,elts,k,s,p))
        # agreement set of each member with u
        agsets=[]
        for c in members:
            ags=frozenset(i for i in range(n) if peval(c,elts[i],p)==u[i])
            agsets.append((c,ags))
        # classify even/mixed
        cls=[]
        for c,ags in agsets:
            F,G=split_FG(c,k)
            cls.append('EVEN' if all(g==0 for g in G) else 'MIXED')
        # pairwise overlaps = |ags_i ∩ ags_j| (points where BOTH agree with u; on these f_i=f_j=u)
        pair=[]
        worst_overlap=0
        for i in range(len(members)):
            for j in range(i+1,len(members)):
                ov=len(agsets[i][1] & agsets[j][1])
                pair.append((i,j,ov,cls[i],cls[j]))
                worst_overlap=max(worst_overlap,ov)
        out.append(dict(word=word_name,n=n,k=k,s=s,p=p,L=len(members),
                        twok=2*k, worst_overlap=worst_overlap,
                        nEven=cls.count('EVEN'),nMixed=cls.count('MIXED'),
                        members=members, cls=cls, pair=pair,
                        agsets=[a for _,a in agsets], u=u, elts=elts))
    return out

# ====================================================================
# TASK 1: test the polynomial identity (F-F')^2 = y(G-sigma G')^2 on common agreement set
# ====================================================================
def test_identity(row):
    """On the COMMON agreement set of two members, where x AND -x both lie (full fibre),
    and where only ONE of {x,-x} lies (single fibre), check what relation holds between
    (F-F') and (G-G'). The claim asserts (F-F')^2 = y(G-sigma G')^2 as a POLYNOMIAL identity
    forced by overlap > k."""
    p=row['p']; elts=row['elts']; n=len(elts); k=row['k']; N=n//2
    members=row['members']; cls=row['cls']; agsets=row['agsets']
    findings=[]
    for i in range(len(members)):
        for j in range(i+1,len(members)):
            ci,cj=members[i],members[j]
            Fi,Gi=split_FG(ci,k); Fj,Gj=split_FG(cj,k)
            common = agsets[i] & agsets[j]   # indices where both agree with u (=> f_i=f_j there)
            ov=len(common)
            # On common set: f_i(x)=f_j(x), i.e. (Fi-Fj)(y) + x(Gi-Gj)(y)=0  at those x.
            # The CLAIM's identity is a DIFFERENT object. Test BOTH things:
            #  (a) does (Fi-Fj)(x^2) = -x*(Gi-Gj)(x^2) hold on the common set? (the REAL relation)
            #  (b) does (Fi-Fj)^2 = y(Gi - sigma Gj)^2 hold as a poly id for some sigma, when ov>k?
            # (a):
            relA=all((peval(Fi,pow(x,2,p),p)-peval(Fj,pow(x,2,p),p)
                      + x*(peval(Gi,pow(x,2,p),p)-peval(Gj,pow(x,2,p),p)))%p==0
                     for x in [elts[t] for t in common])
            # (b) polynomial identity test for sigma=+1 and sigma=-1, as polys in y over many y:
            def poly_id_holds(sigma):
                # build (Fi-Fj)^2 - y*(Gi-sigma Gj)^2 and check it is the zero poly by evaluating
                # at N+ k +5 random-ish distinct y values (the elements of mu_N suffice plus more)
                ys=[pow(elts[t],2,p) for t in range(n)]
                ys=list(dict.fromkeys(ys))
                # extend with extra evaluation points (just use 0..some) to exceed degree
                extra=list(range(2, 2+2*k+10))
                allys=ys+extra
                for y in allys:
                    dF=(peval(Fi,y,p)-peval(Fj,y,p))%p
                    dG=(peval(Gi,y,p)-sigma*peval(Gj,y,p))%p
                    if (dF*dF - y*dG*dG)%p !=0:
                        return False
                return True
            idp=poly_id_holds(1); idm=poly_id_holds(-1)
            findings.append(dict(i=i,j=j,ov=ov,clsi=cls[i],clsj=cls[j],
                                 relA_on_common=relA, polyid_sigma_p1=idp, polyid_sigma_m1=idm,
                                 equalFG=(Fi==Fj and (Gi==Gj or Gi==tuple((-g)%p for g in Gj)))))
    return findings

# ====================================================================
# TASK 2: the double-counting threshold
# ====================================================================
def packing_threshold():
    """Johnson-style 2nd moment packing:  L sets each of size >= a = s = tau*n inside ground
    set of size n=|mu_n|... but the claim packs in mu_N (size N=n/2) with pairwise <= w=2k.
    Standard bound:  if L sets of size >= a, pairwise intersection <= w, in ground n:
      sum_{i<j}|Ai∩Aj| <= C(L,2) w ; also by inclusion (Fisher/2nd moment):
      sum_i|Ai| <= n + (something). The 'tau > sqrt(rho)+rho/2' figure: derive and check.

    Concretely the Johnson 2nd-moment / Plotkin packing: agreement a=tau*n, overlap w<=2k=2*rho*n.
    A family with pairwise overlap <= w and each size a fits with
        L <= (n - w) / (a - w)   [Fisher-type, when a>w]
    bounded (constant) only when a-w bounded below ~ a, i.e. a >> w, i.e. tau*n >> 2 rho n.
    But the relevant 'Johnson radius' statement: list stays poly/constant when
        a > sqrt(w * n)  (the Johnson/Singleton pairwise packing), i.e. tau*n > sqrt(2k*n)
        => tau > sqrt(2 rho / n)... that's n-dependent, vanishes. Hmm.
    The claim's threshold tau> sqrt(rho)+rho/2 must come from a SPECIFIC counting; reproduce it
    and TEST whether window tau<sqrt(rho) is excluded for rho in {1/8,1/16}."""
    res=[]
    for rho in [1/8, 1/16]:
        sqrt_rho=sqrt(rho)
        thr=sqrt_rho + rho/2
        # window interior: s=round((rho+eta)n), eta=rho => tau=2*rho  (since s/n = rho+eta=2rho)
        tau_window=2*rho
        # Johnson radius tau_J = 1 - sqrt(rho)?? but here tau is AGREEMENT fraction not distance.
        # Per task: "window interior s=round((rho+eta)n), eta=rho beyond Johnson radius 1-sqrt(rho)"
        # AGREEMENT fraction tau = s/n = rho+eta = 2*rho.
        res.append(dict(rho=rho, sqrt_rho=sqrt_rho, claim_thr=thr,
                        tau_window_agree=tau_window,
                        window_below_sqrt_rho=(tau_window < sqrt_rho),
                        window_above_claim_thr=(tau_window > thr)))
    return res

if __name__=="__main__":
    print("="*90)
    print("TASK 2: double-counting threshold tau > sqrt(rho)+rho/2 vs window")
    print("="*90)
    for r in packing_threshold():
        print(f"  rho={r['rho']:.5f}: sqrt(rho)={r['sqrt_rho']:.4f}  claim_thr(sqrt+rho/2)={r['claim_thr']:.4f}")
        print(f"     window agreement tau = s/n = 2*rho = {r['tau_window_agree']:.4f}")
        print(f"     window tau < sqrt(rho)?  {r['window_below_sqrt_rho']}   (window IS inside Johnson interior)")
        print(f"     window tau > claim_thr?  {r['window_above_claim_thr']}   (does claim's packing apply?)")

    print("\n"+"="*90)
    print("TASK 3 + 1: actual overlaps and identity test, EVEN words")
    print("="*90)
    # EVEN words: word built from EVEN exponents only => u_o = 0 => u is 'even'.
    # e.g. x^{n/4}+1 has exponents {n/4, 0} both even when n/4 even (n=16 => n/4=4 even; n=32 => 8 even).
    # Also test x^{n/4}+x^{n/8}+1 style even words. We pick words whose exponents are all even.
    configs = [
        ("x^4+1",          [4,0],   16, 2, 0.125),
        ("x^4+x^2+1",      [4,2,0], 16, 2, 0.125),
        ("x^8+1",          [8,0],   32, 4, 0.125),
        ("x^8+x^2+1",      [8,2,0], 32, 4, 0.125),
        ("x^4+1(rho1/16)", [4,0],   16, 1, 0.0625),
        ("x^8+1(rho1/16)", [8,0],   32, 2, 0.0625),
    ]
    for (wn,exps,n,k,eta) in configs:
        rows=actual_overlaps(wn,exps,n,k,eta)
        for row in rows:
            print(f"\n  {wn:<16} n={row['n']} k={row['k']} s={row['s']} p={row['p']}  "
                  f"|L|={row['L']} (EVEN={row['nEven']} MIXED={row['nMixed']})  2k={row['twok']}")
            print(f"     WORST pairwise overlap (both agree with u) = {row['worst_overlap']}   "
                  f"<= 2k={row['twok']} ? {row['worst_overlap']<=row['twok']}")
            # show overlaps that VIOLATE <=2k, with the member classes
            viol=[(i,j,ov,ci,cj) for (i,j,ov,ci,cj) in row['pair'] if ov>row['twok']]
            if viol:
                print(f"     VIOLATIONS of overlap<=2k: {len(viol)} pairs; sample:")
                for (i,j,ov,ci,cj) in viol[:8]:
                    print(f"        members {i}({ci}) & {j}({cj}): overlap={ov} > 2k={row['twok']}")
            # identity test
            idf=test_identity(row)
            # summarize: among pairs with overlap>k, does the claimed poly identity hold?
            big=[f for f in idf if f['ov']>k]
            holds=[f for f in big if f['polyid_sigma_p1'] or f['polyid_sigma_m1']]
            distinct_big=[f for f in big if not f['equalFG']]
            print(f"     pairs with overlap>k: {len(big)};  of those, claimed poly-id holds: {len(holds)};"
                  f"  DISTINCT (not F=F',G=+-G') pairs with overlap>k: {len(distinct_big)}")
            for f in distinct_big[:6]:
                print(f"        DISTINCT pair i={f['i']}({f['clsi']}) j={f['j']}({f['clsj']}) "
                      f"overlap={f['ov']} polyid+={f['polyid_sigma_p1']} polyid-={f['polyid_sigma_m1']} "
                      f"realRelA(f_i=f_j on common)={f['relA_on_common']}")
