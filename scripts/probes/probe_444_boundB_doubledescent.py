"""
probe_444_boundB_doubledescent.py -- decode why O_P = C(n/4, 2) at r=3 (a DOUBLE descent), and
test whether the general pattern is O_P <= C(n/2, r-1) via the SAME double-square mechanism.

r=3 FINDING (probe_444_boundB_r3symbolic): O_P = C(n/4,2), #square-pairs = C(n/2,2). So the
square-support is too coarse by ratio 4.  O_P = C(n/4,2) suggests J is determined by a 2-subset of
mu_{n/4} = the squares-of-squares (4th powers).

We test the precise descent hypotheses for r=3:
  (H4) J is a function of the unordered pair {a^2, b^2} (the squares of the square pair, living in
       mu_{n/4})  -- would give C(n/4,2) if a^2,b^2 distinct and the map is injective.
  Equivalently J depends on (a*b, a^2+b^2) or on the pair {a^2,b^2}.

And for general r we test the analogue: J factors through power sums of the "doubled" coordinates,
i.e. through an (r-1)-subset after TWO antipodal foldings -- but the C(n/2,r-1) shape (single n/2,
not n/4) says the general bound is LOOSER than the r=3 reality.  We check both:
  (G) O_P vs C(n/2,r-1) (the conjecture)  and  vs C(n/4,r-1) (the r=3-tight shape) for r>=4.
"""
from math import comb, gcd
from itertools import combinations
from collections import defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def r3_test_H4(n,e,f,p=P):
    """For r=3: build J and test whether J is a function of the pair {a^2,b^2} (mu_{n/4})."""
    w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    sq=[pow(w,2*i,p) for i in range(n//2)]
    nsq=[pow(w,2*i+1,p) for i in range(n//2)]
    M=max(e-3+1,f-3+1)
    key_to_J=defaultdict(set)   # key = sorted {a^2 index, b^2 index} on mu_{n/4} (=4i mod n -> i mod n/4)
    J_to_keys=defaultdict(set)
    for (ia,ib) in combinations(range(n//2),2):
        a,b=sq[ia],sq[ib]; target=(-(a*b))%p
        for (ic,idd) in combinations(range(n//2),2):
            c,d=nsq[ic],nsq[idd]
            if (c*d)%p!=target: continue
            S=[a,b,c,d]; H=hpow(S,M,p)
            if (H[e-3]*H[f-3+1]-H[f-3]*H[e-3+1])%p: continue
            if H[f-3]==0: continue
            g=(-H[e-3]*pow(H[f-3],p-2,p))%p
            if not g: continue
            J=pow(g,nd,p)
            # square-of-square indices: a=w^{2ia} -> a^2=w^{4ia} -> on mu_{n/4} index = (2ia) mod (n/2)?
            # mu_{n/4} elements are w^{4k}; a^2=w^{4ia}; index in mu_{n/4} = ia mod (n/4)
            k=tuple(sorted((ia % (n//4), ib % (n//4))))
            key_to_J[k].add(J); J_to_keys[J].add(k)
    # H4 holds if each key maps to exactly one J AND each J to one key (bijection-ish)
    keys_multi=sum(1 for v in key_to_J.values() if len(v)>1)
    J_multi=sum(1 for v in J_to_keys.values() if len(v)>1)
    return len(J_to_keys), len(key_to_J), keys_multi, J_multi

if __name__=="__main__":
    print("r=3: test H4 (J <- {a^2,b^2} in mu_{n/4}):")
    print(f"{'n':>4} {'O_P':>5} {'#keys(n/4 pairs)':>16} {'keys->1J?':>10} {'J->1key?':>10} {'C(n/4,2)':>9}")
    for n in [16,32,64]:
        e,f=n//2,n//2-1
        OP,nkeys,km,jm=r3_test_H4(n,e,f)
        print(f"{n:>4} {OP:>5} {nkeys:>16} {('yes' if km==0 else 'NO('+str(km)+')'):>10} "
              f"{('yes' if jm==0 else 'NO('+str(jm)+')'):>10} {comb(n//4,2):>9}")
