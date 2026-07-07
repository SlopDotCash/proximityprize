"""
probe_444_boundA_r3whycount.py -- WHY is #distinct I3=e1^4/e4 equal to C(n/4,2) at r=3?

bad S={a,b sq}U{c,d nsq}, ab=-cd. Let P:=ab (a square, since a,b squares). cd=-P.
e1=a+b+c+d, e4=abcd=ab*cd= P*(-P)=-P^2.  So e4=-P^2 is determined by P alone.
e1^4/e4 = (a+b+c+d)^4 / (-P^2).
Under dilation S->gS: e1->g e1, e4->g^4 e4, so I3 invariant. Good.

Let's parametrize. squares a,b in mu_{n/2}=<w^2>; ab=P. nonsquares c,d with cd=-P.
The free data: choice of unordered {a,b} with ab=P among squares, and {c,d} with cd=-P among
nonsquares. For each P (a square), how many {a,b}? a in squares, b=P/a in squares automatically
(P square => P/a square). Need a != b i.e. a^2 != P. So ~ (n/2)/2 = n/4 unordered pairs per P
(minus the sqrt). Similarly {c,d}: c nonsquare, d=-P/c; -P/c: -P is nonsquare? -1 is a square iff
n/2 even iff mu has -1 as square... -1=w^{n/2}; is n/2 even? n=2^mu so n/2=2^{mu-1} even for mu>=2.
So -1 is an (n/2)-th power... is -1 a square in mu_n? square = even index; n/2 even => -1=w^{n/2}
has even index => -1 IS a square. So -P=(-1)*P is square*square=square?? but cd=-P and c,d
nonsquare => cd=square. Yes consistent: nonsquare*nonsquare=square=-P. Good, -P is a square.

So both P and -P are squares. {a,b}: a,b squares, ab=P. {c,d}: c,d NONsquares, cd=-P=(square).
Count of unordered {a,b} squares with product P: a ranges over squares, b=P/a square => n/2 choices
ordered, /2 unordered, minus a=b case => (n/2)/2 = n/4 pairs (if P is a square but not a 4th power
issue...). Similarly {c,d} nonsquares with cd=-P: c nonsquare, d=-P/c; d nonsquare iff -P/c
nonsquare iff (since -P square) c nonsquare => d nonsquare. ok n/2 nonsquares, ordered n/2, /2 =>
n/4 pairs.

So per square-value P there are ~ (n/4)*(n/4) bad S. Total bad ~ (n/2)*(n/4)^2?? But we measured
#badS=96 at n=16 => 96/(n/4)^2 = 96/16=6 = #distinct P? Let's just COUNT and find what gives
C(n/4,2). The invariant I3=e1^4/e4. e4=-P^2 fixed by P. So I3 = -e1^4/P^2; distinct I3 <-> distinct
(e1^4/P^2) = distinct (e1/P^{1/2})^4-ish. e1=a+b+c+d. With ab=P, cd=-P.

We just compute, per bad S: P, e1, I3, and see the map (P, e1) -> I3 and count.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H
def inv(a,p): return pow(a,p-2,p)

def collect(n,p):
    r=3; e,f=n//2,n//2-1; a0=4; w=gen(n,p); nd=n
    M=max(e-r+1,f-r+1); rows=[]
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        sq=[pow(w,i,p) for i in Sidx if i%2==0]; ns=[pow(w,i,p) for i in Sidx if i%2==1]
        a,b=sq; c,dd=ns
        P=a*b%p
        e1=sum(xs)%p; e4=1
        for z in xs: e4=e4*z%p
        I3=pow(e1,4,p)*inv(e4,p)%p
        rows.append((J,P,e1,I3,Sidx))
    return rows,w

if __name__=="__main__":
    p=PRIMES[0]
    for n in [16,32]:
        rows,w=collect(n,p)
        OP=len(set(r[0] for r in rows))
        Ps=set(r[1] for r in rows)
        print(f"### n={n}: O_P={OP} C(n/4,2)={comb(n//4,2)} #distinctP={len(Ps)} (=n/2? {len(Ps)==n//2})")
        # For each P, how many distinct I3?
        P2I3=defaultdict(set)
        for J,P,e1,I3,S in rows: P2I3[P].add(I3)
        perP=Counter(len(s) for s in P2I3.values())
        print(f"   #distinct I3 per P: {dict(perP)}  (sum check: sum={sum(len(s) for s in P2I3.values())})")
        # but I3 can coincide across different P. total distinct I3:
        allI3=set(r[3] for r in rows)
        print(f"   total #distinct I3 = {len(allI3)} (==O_P? {len(allI3)==OP})")
        # Is P determined by I3? i.e. does e4=-P^2 mean I3 sees P^2 => P up to sign?
        I32P=defaultdict(set)
        for J,P,e1,I3,S in rows: I32P[I3].add(P)
        print(f"   #P per I3: {dict(Counter(len(s) for s in I32P.values()))}")
        # the e1 values: per P, e1 ranges over a set of size?
        P2e1=defaultdict(set)
        for J,P,e1,I3,S in rows: P2e1[P].add(e1)
        print(f"   #distinct e1 per P: {dict(Counter(len(s) for s in P2e1.values()))}")
