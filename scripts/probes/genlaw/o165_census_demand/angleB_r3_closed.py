# r=3 CLOSED FORM derivation & the injection.
# Bad 4-subset S has 2 squares {a,b} (sigma=+1, a,b in mu_{n/2}) and 2 non-squares {c,d}
# (sigma=-1).  g(z)=sigma(z)(1+gamma/z). On squares g= 1+gamma/z; on non-squares g= -(1+gamma/z).
# Require {(z, g(z))} (4 pts) collinear-deg<=1: i.e. the 4 points lie on a line Y=alpha+beta X.
#  For square z: 1+gamma/z = alpha+beta z
#  For nonsq  z: -(1+gamma/z) = alpha+beta z
# 4 equations, unknowns alpha,beta,gamma (3). 4 eqns 3 unknowns => 1 condition on S = V.
# Subtract within squares (a,b):  gamma(1/a-1/b) = beta(a-b)  => gamma = -beta a b. (from
#  (1+gamma/a)-(1+gamma/b)= beta(a-b) => gamma(b-a)/(ab)=beta(a-b) => gamma= -beta ab).
# Within nonsq (c,d): -(gamma)(1/c-1/d)=beta(c-d) => -gamma(d-c)/(cd)=beta(c-d) => gamma=-beta cd ... wait sign:
#   -(1+gamma/c) - ( -(1+gamma/d)) = beta(c-d) => -gamma/c + gamma/d = beta(c-d)
#     => gamma(d-c)/(cd) = beta(c-d) => gamma = -beta cd.
# So gamma = -beta ab = -beta cd  => (if beta!=0) ab = cd.  THE CONDITION V at r=3:
#     a*b = c*d   (product of the 2 squares = product of the 2 non-squares).   [exact]
# Then need consistency with alpha (the cross sq-vs-nonsq eqn) to pin everything & beta!=0.
# gamma = -beta ab.  beta determined by remaining eqn. Let's compute gamma in closed form and
# COUNT: #bad = #distinct gamma. ab=cd with a,b squares (in mu_{n/2}), c,d nonsquares.
#
# squares = mu_{n/2} (n/2 of them); nonsquares = w*mu_{n/2} (the other coset), also n/2.
# Choose {a,b} subset squares, {c,d} subset nonsquares with ab=cd.
# Let a=w^{2i}, b=w^{2j} (squares), c=w^{2k+1}, d=w^{2l+1} (nonsquares), w=gen of mu_n.
# ab=cd: 2i+2j = 2k+2l+2 mod n => i+j = k+l+1 mod n/2.
# Count pairs etc. Let's just MEASURE the resulting gamma and verify #bad, then exhibit injection.

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

def r3_via_closed(n):
    """Build bad gammas directly from a*b=c*d structure and pin gamma; cross-check count."""
    dom=mu_n(n)
    sqidx=[i for i in range(n) if pow(dom[i],n//2,p)==1]      # squares
    nsidx=[i for i in range(n) if pow(dom[i],n//2,p)!=1]      # nonsquares
    sq=set(sqidx)
    gammas=set()
    detail=[]
    for (ia,ib) in combinations(sqidx,2):
        a,b=dom[ia],dom[ib]
        ab=(a*b)%p
        for (ic,idd) in combinations(nsidx,2):
            c,d=dom[ic],dom[idd]
            if (c*d)%p!=ab: continue
            # pin gamma: solve full system. unknowns alpha,beta,gamma.
            # eqs: sq:  1+gamma/a = alpha+beta a ; 1+gamma/b=alpha+beta b
            #      nsq: -(1+gamma/c)=alpha+beta c ; -(1+gamma/d)=alpha+beta d
            # We have gamma=-beta*ab. Use sq pair to get beta, alpha; then check nsq consistency.
            # From sq two eqs: (1+gamma/a)-(1+gamma/b)=beta(a-b) auto gives gamma=-beta ab (already).
            # Use one sq eq + one nsq eq to solve alpha,beta with gamma=-beta ab substituted.
            # sq a: 1 + gamma/a = alpha+beta a -> 1 - beta b = alpha + beta a  (gamma/a=-beta ab/a=-beta b)
            #   => alpha = 1 - beta(a+b)
            # nsq c: -(1+gamma/c) = alpha+beta c -> -(1 - beta ab/c) = alpha+beta c
            #   gamma/c = -beta ab/c. -(1)+beta ab/c = alpha+beta c
            #   => alpha = -1 + beta ab/c - beta c = -1 + beta(ab/c - c)
            # set equal: 1 - beta(a+b) = -1 + beta(ab/c - c)
            #   => 2 = beta[(a+b) + ab/c - c]
            denom=((a+b) + (ab*inv(c))%p - c)%p
            if denom%p==0: continue
            beta=(2*inv(denom))%p
            gamma=(-beta*ab)%p
            if gamma==0: continue
            # verify on d too
            alpha=(1-beta*(a+b))%p
            okd = (-(1+gamma*inv(d)))%p == (alpha+beta*d)%p
            if not okd: continue
            gammas.add(gamma)
            detail.append((ia,ib,ic,idd,gamma))
    return gammas,detail,dom,sqidx,nsidx

if __name__=="__main__":
    for n in [16,32]:
        gammas,detail,dom,sqidx,nsidx=r3_via_closed(n)
        print(f"n={n}: closed-form #distinct nonzero gamma = {len(gammas)} (expect {comb(n//4,2)*n})")
        # how many (a,b,c,d) tuples map to a gamma (fiber of the construction)?
        gc=Counter(g for *_,g in detail)
        print(f"   #(a,b,c,d) tuples = {len(detail)}; construction-fiber dist: {dict(sorted(Counter(gc.values()).items()))}")
        # ab=cd count: number of {a,b}sq,{c,d}nsq with equal product
        # injection candidate: gamma -> ? Let's see if gamma <-> (ab, and the pair-of-pairs) bijective.
