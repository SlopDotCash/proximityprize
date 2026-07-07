"""
probe_444_boundA_r3closed.py -- closed-form r=3 invariant and the C(n/4,2) count, fully explained.

bad S={a,b sq}U{c,d nsq}, ab=P (square), cd=-P. e4=abcd=-P^2.
Define the scale-invariant W := e1^2 / P = (a+b+c+d)^2 / (ab).  (scale wt: e1^2 ~ g^2, P~g^2 => W deg0.)
Then I3 = e1^4/e4 = e1^4/(-P^2) = -(e1^2/P)^2 = -W^2.  So J = bijective image of W^2 (= -I3).
So O_P = #distinct W (up to the W<->? identification giving W^2). Actually J<->I3<->W^2.
#distinct J = #distinct W^2.

Now compute W = (a+b+c+d)^2/(ab). Use ab=P, cd=-P. Let s1=a+b, s2=c+d. e1=s1+s2.
a,b roots of t^2-s1 t+P=0; c,d roots of t^2-s2 t-P=0 (since cd=-P).
W=(s1+s2)^2/P.
The discrete data: a,b squares with product P -> s1=a+b ranges over {a+P/a : a square}; this is a set
of size ~ n/4 (a and P/a give same s1). Similarly s2=c+P? wait cd=-P so d=-P/c, s2=c+d=c-P/c,
c nonsquare -> s2 ranges over ~n/4 values.
So W=(s1+s2)^2/P with s1 in A (|A|~n/4), s2 in B (|B|~n/4). #distinct W^2 = ?

We test the cleaner normalization: dilate so P=1 (possible? P=ab is a square=w^{even}; we can dilate
by g with g^2 = 1/P to set P=1, g in mu_n exists since P is a square => P=h^2, take g=1/h, then
gS has product (ga)(gb)=g^2 P=1). After P=1: a,b squares ab=1 => b=1/a=a^{-1}; s1=a+a^{-1}.
c,d nonsquares cd=-1 => d=-1/c; s2=c-1/c. W=(s1+s2)^2.
a in squares=mu_{n/2}: s1=a+a^{-1} -- as a ranges over mu_{n/2}, a+a^{-1} takes n/4 values (a,a^{-1}
give same). c in nonsquares: s2=c-c^{-1}; c,-c^{-1}?? c and ? give same s2: s2=c-1/c; c'->? c-1/c=
c'-1/c' => (c-c')(1+1/(cc'))=0 => c'=c or cc'=-1 i.e. c'=-1/c=d. So s2 same for c and d=-1/c =>
n/4 values. So W=(s1+s2)^2, s1 in S1 (n/4 vals), s2 in S2 (n/4 vals). #distinct W=#distinct(s1+s2)^2.

C(n/4,2) = (n/4)(n/4-1)/2. Hmm (s1+s2) ranges over a sumset of two size-n/4 sets => up to (n/4)^2.
But #distinct W=C(n/4,2). Let's just COMPUTE s1,s2 sets and #distinct (s1+s2)^2 and confirm
=C(n/4,2), then understand the collision giving C(n/4,2) instead of (n/4)^2.
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
def inv(a,p): return pow(a,p-2,p)

def direct_count(n,p):
    """With P=1 normalization: a in squares (mu_{n/2}), s1=a+1/a; c nonsquare, s2=c-1/c.
       W=(s1+s2)^2.  Count distinct W and distinct s1, s2."""
    w=gen(n,p)
    squares=[pow(w,2*i,p) for i in range(n//2)]
    nonsq=[pow(w,2*i+1,p) for i in range(n//2)]
    S1=set((a+inv(a,p))%p for a in squares)
    S2=set((c-inv(c,p))%p for c in nonsq)   # cd=-1 => d=-1/c, s2=c+d=c-1/c
    Ws=set((( (s1+s2)%p )**2)%p for s1 in S1 for s2 in S2)
    # also W without square (the s1+s2 sumset)
    SUM=set((s1+s2)%p for s1 in S1 for s2 in S2)
    return len(S1),len(S2),len(SUM),len(Ws)

if __name__=="__main__":
    p=PRIMES[0]
    print("P=1 normalized direct count (s1=a+1/a squares, s2=c-1/c nonsquares, W=(s1+s2)^2):")
    for n in [16,32,64,128,256]:
        nS1,nS2,nSUM,nW=direct_count(n,p)
        print(f"  n={n}: |S1|={nS1} (n/4={n//4}) |S2|={nS2}  |s1+s2 sumset|={nSUM}  |W=(s1+s2)^2|={nW}  C(n/4,2)={comb(n//4,2)}  match={nW==comb(n//4,2)}")
