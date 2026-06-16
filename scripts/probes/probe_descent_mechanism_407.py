#!/usr/bin/env python3
r"""
probe_descent_mechanism_407.py  (#407)

WHY THE DESCENT BREAKS -- the decisive structural probe.

The assigned idea: split a relation sum eps_i g^{x_i} = 0 (mod q) by parity x_i = 2u_i+b_i.
  EVEN block  A = sum_{b_i=0} eps_i g^{2u_i}   in <g^2> = mu_{n/2}
  ODD block   g*B,  B = sum_{b_i=1} eps_i g^{2u_i}   in mu_{n/2}
So the relation is  A + g*B == 0 (mod q).
In CHAR 0 (the Q(zeta_n) tower being a deg-2 ext of Q(zeta_{n/2}), basis {1,g}):
  A + g*B = 0 in C  <=>  A = 0 AND B = 0  separately  (clean descent to two mu_{n/2} relations).
In CHAR p:  only A == -g*B (mod q) jointly.

CLASSIFICATION of a defect (A + gB == 0 mod q, not 0 in C):
  TYPE-pure : A == 0 in C and B == 0 in C  but combined nonzero in C -- impossible (then it's 0 in C).
              So a DEFECT must have A != 0 in C OR B != 0 in C.
  TYPE-split-leak : A != 0 in C and B != 0 in C, but A == -gB mod q.  This is the CROSS-PARITY
              leak the descent cannot see (it needs the full tower, not the sublevel).
  TYPE-single : exactly one of A,B is nonzero in C.  Then A == -gB mod q with (say) B==0 in C,
              B != 0 mod q?  If B==0 in C then B's coeff vector reduces to 0, so B==0 in Z[zeta]
              hence ==0 mod q, forcing A==0 mod q -- a mu_{n/2} defect for A.  These DO descend.

We measure, for each actual defect tuple at small (n,r,q):  what fraction are TYPE-split-leak
(cross-parity, undescendable) vs descendable.  If the BULK are split-leaks, the tower descent
provably cannot bound the defect count from the sub-level -- which is what the earlier probe
saw (D_r(n)>0 while D_r(n/2)=0).
"""
import itertools
from collections import Counter
import sympy

def E_r_complex_reduced(n):
    """return function mapping an r-tuple's reduced vector; and whether a multiset of (exp) sums to 0 in C."""
    half=n//2
    def redvec(exps):
        v=[0]*half
        for (sign,a) in exps:
            if a<half: v[a]+=sign
            else: v[a-half]-=sign
        return tuple(v)
    return redvec, half

def subgroup_exps(p,n):
    """return (h, list of (exponent j -> value g^{(p-1)/n * j} mod p)) i.e. mu_n = {w_j}."""
    g=int(sympy.primitive_root(p)); h=pow(g,(p-1)//n,p)
    vals=[]; x=1
    for j in range(n): vals.append(x); x=x*h%p
    return vals   # vals[j] = (n-th root)^j, j=0..n-1   (g here = h, order n)

def classify_defects(p, n, r):
    """enumerate all (x,y) in [n]^r x [n]^r with sum_q equal; among those, count char-0 vs defect,
    and among defects classify by parity-split leak.  alpha = sum w_{x_i} - sum w_{y_i}.
    represent alpha as signed exponent list [(+1,x_i)] + [(-1,y_i)]; even/odd split by parity."""
    redvec, half = E_r_complex_reduced(n)
    vals = subgroup_exps(p,n)
    # group r-tuples by mod-q sum
    bym=Counter()
    tuples_by_sum={}
    for x in itertools.product(range(n), repeat=r):
        s=sum(vals[a] for a in x)%p
        tuples_by_sum.setdefault(s,[]).append(x)
    n_char0=0; n_defect=0; n_leak=0; n_descend=0
    for s,lst in tuples_by_sum.items():
        for x in lst:
            for y in lst:
                # alpha = sum w_x - sum w_y ; char-0 zero iff redvec equal
                exps = [(+1,a) for a in x] + [(-1,b) for b in y]
                rv = redvec(exps)
                isc0 = all(c==0 for c in rv)
                if isc0:
                    n_char0+=1
                else:
                    n_defect+=1
                    # split by parity
                    evenA = [(sgn,a) for (sgn,a) in exps if a%2==0]
                    oddB  = [(sgn,a) for (sgn,a) in exps if a%2==1]
                    # A as element of mu_{n/2}=<g^2>: exponent a -> a//2 in [n/2]; reduce in Q(zeta_{n/2})
                    def redhalf(lst2):
                        # zeta_{n/2}, dim (n/2)/2 = n/4 ; basis reduction zeta^{j+n/4} = -zeta^j (n/2-th roots)
                        quarter = half//2 if half>=2 else 1
                        if half==1:
                            # mu_{n/2}=mu_1={1}; A is just integer sum of signs
                            return (sum(sgn for sgn,_ in lst2),)
                        v=[0]*quarter
                        for sgn,a in lst2:
                            j=(a//2)% half   # exponent in mu_{n/2}
                            if j<quarter: v[j]+=sgn
                            else: v[j-quarter]-=sgn
                        return tuple(v)
                    A0 = all(c==0 for c in redhalf(evenA))
                    B0 = all(c==0 for c in redhalf(oddB))
                    if (not A0) and (not B0):
                        n_leak+=1        # cross-parity leak: needs full tower
                    else:
                        n_descend+=1     # one block vanishes in C => descends to a sub-level relation
    return n_char0, n_defect, n_leak, n_descend

print("=== WHY THE DESCENT BREAKS: parity-split classification of defects (#407) ===\n")
print("A defect alpha=sumW_x - sumW_y (==0 mod q, !=0 in C) splits A+gB.")
print("  LEAK   = both even-block A and odd-block B nonzero in C (cross-parity; UNDESCENDABLE)")
print("  DESC   = one block vanishes in C (reduces to a mu_{n/2} relation; descendable)\n")
print(f"{'n':>4} {'r':>2} {'p':>8} | {'char0':>8} {'defects':>8} {'LEAK':>8} {'DESC':>6} {'leak%':>7}")
cases = [(16,3,257),(16,3,7457),(32,3,1153),(16,4,257),(16,4,2417),(16,4,7457),(8,4,113),(8,4,233)]
for (n,r,p) in cases:
    if n**r>200000:  # enumerate n^r tuples; group; double loop within sum-class -- keep small
        continue
    if (p-1)%n!=0 or not sympy.isprime(p):
        # find nearest valid
        continue
    c0,d,lk,ds = classify_defects(p,n,r)
    pct = 100.0*lk/d if d>0 else 0.0
    print(f"{n:>4} {r:>2} {p:>8} | {c0:>8} {d:>8} {lk:>8} {ds:>6} {pct:>6.1f}%")
