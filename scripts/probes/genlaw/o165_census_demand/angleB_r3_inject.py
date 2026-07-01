# r=3 INJECTION (corrected): bad 4-subset = {a,b}(squares) U {c,d}(nonsquares) with a*b = -(c*d).
# squares = mu_{n/2} (the squares in mu_n), nonsquares = w * mu_{n/2}.
# Write a=w^{2i}, b=w^{2j}; c=w^{2k+1}, d=w^{2l+1}. Condition a b = -c d = w^{n/2} c d:
#   2i+2j = (n/2) + 2k+2l+2  mod n.  Divide by 2:  i+j = n/4 + k+l+1  mod n/2.  (n=2^mu, n/4 integer)
# gamma is pinned (fiber 1). The INJECTION TARGET = signed 3-subsets of mu_{n/2} = 2^3 C(n/2,3).
#
# Build the injection Phi: gamma -> signed 3-subset of mu_{n/2}.
# From the bad subset, define the descent to the half via squaring:
#   sq(a)=a^2, sq(b)=b^2 in mu_{n/2} (these are squares-of-squares = elements of mu_{n/4}).
#   sq(c)=c^2, sq(d)=d^2 in mu_{n/2} (squares of nonsquares = also in mu_{n/2} but other structure).
# That's 4 squares -> still 4 objects, target wants 3. Need the relation to collapse one DOF.
#
# Better: the natural injection for this 2-squares/2-nonsquares + product relation is into
# (unordered pair {a,b} of squares) x (sign data). #bad = #distinct gamma. Let's first just
# CONFIRM the closed count, find #distinct gamma exactly, and the cleanest injective encoding.

from math import comb, gcd
from itertools import combinations
from collections import Counter
p = 2013265921
def inv(x): return pow(x,p-2,p)
def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
    raise RuntimeError

def r3_closed(n):
    dom=mu_n(n)
    sqidx=[i for i in range(n) if i%2==0]   # a=w^{2i}, even exponent = square (w order n)
    nsidx=[i for i in range(n) if i%2==1]
    # verify squares: w^{even} has (w^even)^{n/2}=w^{even*n/2}=w^{multiple of n}=1 yes.
    gammas=set(); detail=[]
    for (ia,ib) in combinations(sqidx,2):
        a,b=dom[ia],dom[ib]; ab=(a*b)%p
        for (ic,idd) in combinations(nsidx,2):
            c,d=dom[ic],dom[idd]
            if (c*d)%p != (-ab)%p: continue
            # pin gamma. g(z)=sigma(z)(1+gamma/z) on deg<=1. sq: 1+gamma/z; ns: -(1+gamma/z).
            # sq pair => gamma=-beta ab ; ns pair => -gamma(1/c-1/d)=beta(c-d):
            #   -gamma(d-c)/cd = beta(c-d) => gamma = -beta cd. combined: ab=cd?? but we have ab=-cd.
            # Recompute ns pair carefully: value V(z) = -(1+gamma/z). V(c)-V(d)= -gamma(1/c-1/d)
            #   = -gamma (d-c)/(cd) = gamma(c-d)/(cd). Set = beta(c-d): gamma/(cd)=beta => gamma=beta cd.
            # sq pair: value 1+gamma/z. diff = gamma(1/a-1/b)=gamma(b-a)/ab = -gamma(a-b)/ab=beta(a-b)
            #   => gamma=-beta ab. So -beta ab = beta cd => ab=-cd. CONSISTENT with our condition!
            # gamma = -beta ab = beta cd. determine beta from cross eq (sq a vs ns c):
            #   1+gamma/a = alpha+beta a ;  -(1+gamma/c)=alpha+beta c. subtract:
            #   1+gamma/a +1+gamma/c = beta(a-c) => 2 + gamma(1/a+1/c) = beta(a-c).
            #   gamma=-beta ab => 2 - beta ab(1/a+1/c)=beta(a-c) => 2 - beta(b + ab/c)=beta(a-c)
            #   => 2 = beta(a-c + b + ab/c) => beta = 2/(a+b-c+ab/c).
            den=(a+b-c+(ab*inv(c)))%p
            if den%p==0: continue
            beta=(2*inv(den))%p; gamma=(-beta*ab)%p
            if gamma==0: continue
            # verify on d
            alpha=(1+gamma*inv(a)-beta*a)%p
            if (-(1+gamma*inv(d)))%p != (alpha+beta*d)%p: continue
            gammas.add(gamma); detail.append((ia,ib,ic,idd,gamma))
    return gammas,detail,dom

if __name__=="__main__":
    for n in [16,32]:
        gammas,detail,dom=r3_closed(n)
        K=(1<<3)*comb(n//2,3)
        print(f"n={n}: closed #distinct nonzero gamma={len(gammas)} (expect {comb(n//4,2)*n}={comb(n//4,2)*n}) | K={K} | #tuples={len(detail)}")
        # fiber of construction: how many (a,b,c,d) per gamma
        gc=Counter(g for *_,g in detail)
        print(f"   tuple->gamma fiber dist: {dict(sorted(Counter(gc.values()).items()))}")
        # INJECTION attempt: gamma -> the pair {a,b} of squares (as 2-subset of mu_{n/2}) PLUS
        # the value ab (=product). Is (sorted {a,b}) determined by gamma? i.e. is the map
        # gamma -> {a,b} well-defined (constant over construction fiber)?
        g2ab=Counter()
        gmap={}
        welldef=True
        for (ia,ib,ic,idd,g) in detail:
            key=tuple(sorted((ia//2, ib//2)))  # square pair as elements of mu_{n/2} (index/2)
            if g in gmap and gmap[g]!=key: welldef=False
            gmap.setdefault(g,key)
        print(f"   gamma -> square-pair {{a,b}} well-defined? {welldef}; #distinct square-pairs={len(set(gmap.values()))}")
