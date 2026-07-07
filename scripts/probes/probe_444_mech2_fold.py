"""
probe_444_mech2_fold.py -- Mechanism-2, take 2.  The candidate-(b) 'codeword roots' was empty
(P_gamma is nonzero on all mu_n); the RIGHT object is the DIFFERENCE D_gamma=W_gamma-P_gamma whose
zero set is the bad subset S itself.  Here we attack via the SAME-PARITY ANTIPODAL FOLD, which the
CONTEXT flags as the mechanism, and via a direct DISCRETE-LOG analysis of J.

KEY STRUCTURE to test:
  (F1) DISCRETE-LOG OF J.  J=gamma^{n/d} is always a square in F_p (verified).  Compute its order
       and, crucially, whether J lies in mu_n or a small structured subgroup.  If J in mu_{n/2}
       (squares of mu_n) then J ITSELF is a single square-class -> would give O_P<=n/2, too weak;
       we need J pinned by an (r-1)-TUPLE.  Measure: the multiplicative SPAN of {J} -- do all J's
       lie in one cyclic subgroup of small order?  what order?

  (F2) ANTIPODAL FOLD (same parity).  For e==f mod 2, W_gamma(-x)=(-1)^e W_gamma(x).  So on the
       n/2 antipodal pairs {x,-x}, W_gamma is determined by its values on mu_{n/2} (one per pair).
       The bad subset S, projected to antipodal pairs (i mod n/2), and which pairs are hit.  The
       'codeword' P_gamma also (anti)symmetric => lives on a deg-related poly in y=x^2 on mu_{n/2}.
       Re-derive the badness as a SMALLER problem on mu_{n/2} in the variable y=x^2.

  (F3) y=x^2 SUBSTITUTION.  Same parity e=2e', f=2f' (or both odd e=2e'+1,f=2f'+1 -> factor x).
       Then W_gamma = (x^{2})^{e'}+gamma(x^2)^{f'} = U_gamma(y), y=x^2 ranges over mu_{n/2}.
       The agreement of W_gamma with deg<r poly on mu_n PULLS BACK to agreement of U_gamma with a
       related code on mu_{n/2}.  This is the (r-1)-on-squares structure!  Test: does the badness
       of S reduce to a badness of the SQUARED multiset {x^2 : x in S} as a multiset in mu_{n/2}?
       If gamma^{n/d}=J depends ONLY on the multiset {x_i^2} -> O_P <= #such multisets.

We measure:  does J depend ONLY on the squared multiset of S?  (the cleanest possible Phi).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921, 3221225473]

def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError("no gen")

def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def collect_bad(n,r,e,f,p):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list); g2S=defaultdict(list)
    Mmax=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return w,{},{},d,nd
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        J2S[J].append(Sidx); g2S[g].append(Sidx)
    return w,J2S,g2S,d,nd

def order_of(a,p,maxdiv):
    """order of a in F_p* restricted: return order if it divides maxdiv else -1."""
    o=1; cur=a%p
    while cur!=1 and o<=maxdiv:
        cur=cur*a%p; o+=1
    return o if cur==1 else -1

def analyze(n,r,e,f,p):
    w,J2S,g2S,d,nd=collect_bad(n,r,e,f,p)
    OP=len(J2S)
    print(f"r={r} n={n} (x^{e},x^{f}) parity({e%2},{f%2}) d={d} nd={nd}: "
          f"O_P={OP} C(n/2,r-1)={comb(n//2,r-1)} C(n/4,2)={comb(n//4,2)}")
    if OP==0: return
    # (F1) orders of J: are they all in mu_n? mu_{n/2}? a bigger cyclic group?
    Jvals=list(J2S)
    orders=Counter()
    for J in Jvals:
        o=order_of(J,p,2*n*n)  # search up to 2n^2
        orders[o]+=1
    inmu = sum(1 for J in Jvals if pow(J,n,p)==1)
    inmuhalf = sum(1 for J in Jvals if pow(J,n//2,p)==1)
    print(f"    (F1) J in mu_n: {inmu}/{OP}; in mu_(n/2): {inmuhalf}/{OP}; "
          f"order-dist (capped 2n^2)={dict(sorted((k,v) for k,v in orders.items()))}")

    # (F3) does J depend ONLY on the squared MULTISET {x_i^2}?  square-class multiset = Counter(i mod n/2)
    sq2J=defaultdict(set)
    for J,Ss in J2S.items():
        for S in Ss:
            key=frozenset(Counter(i%(n//2) for i in S).items())  # multiset of square-classes
            sq2J[key].add(J)
    collide=sum(1 for v in sq2J.values() if len(v)>1)
    print(f"    (F3) #distinct squared-multisets among bad S = {len(sq2J)}; "
          f"squared-multiset -> J well-defined (each maps to 1 J)? "
          f"{'YES' if collide==0 else f'NO ({collide} multisets hit >1 J)'}")
    # and reverse: J -> set of squared-multisets (fiber). is it the SET-supports that matter?
    J2sq=defaultdict(set)
    for key,Js in sq2J.items():
        for J in Js: J2sq[J].add(key)
    # SUPPORT (set, not multiset) of square-classes per S: does J fix the support SET?
    J2supp=defaultdict(set)
    for J,Ss in J2S.items():
        for S in Ss:
            J2supp[J].add(frozenset(i%(n//2) for i in S))
    suppconst=all(len(v)==1 for v in J2supp.values())
    suppsizes=Counter(len(next(iter(v))) for v in J2supp.values() if len(v)==1)
    print(f"    (F3') square-SUPPORT-set constant per J? {suppconst}; "
          f"support-size-dist={dict(sorted(suppsizes.items()))} (want r-1={r-1})")

if __name__=="__main__":
    p=PRIMES[0]
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
           5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    print(f"# Mechanism-2 fold/disclog, prime p={p}\n")
    for (r,n) in todo:
        e,f=LINES[r](n)
        analyze(n,r,e,f,p)
        print()
