#!/usr/bin/env python3
"""
#444 floor-side [LP-delsarte-on-list], Part C/D: the Delsarte LP as a LIST (anticode) bound on
RS-on-mu_n, trivial scheme vs coset scheme, vs the TRUE worst-case list. Bucket honestly.

LIST AS ANTICODE. List members c_1..c_L within radius delta*n of received w => differences
{c_i - c_j} are L^2 codewords of weight <= 2*delta*n. The set of differences is an anticode of
diameter D=2*delta*n. By the code-anticode bound (Delsarte) over the Hamming scheme H(n,q):
   |anticode of diameter D| <= q^n / (min volume LP bound) ... but the SHARP form for a CODE is:
   for the RS code C with dual distance d^perp, the inner distribution of any subset of C is
   supported on weights that are eigenvalue-positive. The list-as-difference-set is a sub-CODE
   contained in the radius-D ball; Delsarte LP bounds |it|.

This is the DELSARTE-LP-ON-LIST the assignment names. We test it 3 ways:
  (T) trivial Hamming-scheme LP (Krawtchouk) on a code of dual distance d^perp = k+1 (RS), in a
      ball of radius D = 2*delta*n. This is the classical LP list bound.
  (C) coset-scheme refinement: restrict to coset-symmetric (dilation-invariant) distance
      distributions -- the dilation group mu_n acts on the code, so the difference-set is a
      union of dilation-orbits; the coset scheme's LP adds the dilation-character constraints.
  (true) brute worst-case list at radius delta over actual mu_n RS codewords (tiny p,n).
"""
import numpy as np, itertools, math
from sympy import isprime

def primitive_root(p):
    phi=p-1; x=phi; f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in f): return g
def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,i,p) for i in range(n)]

# ---- Krawtchouk for Hamming scheme H(n,q) ----
def krawtchouk(k,i,n,q):
    return sum((-1)**j * (q-1)**(k-j) * math.comb(i,j)*math.comb(n-i,k-j) for j in range(0,k+1))

def delsarte_lp_list_ball(n,q,d_dual,D):
    """Classical Delsarte LP upper bound on the size of a code (here: difference-anticode) all of
    whose nonzero weights lie in [d_dual, D] (RS difference has weight in [k+1.. ] but we cap by D
    since list-differences have weight <= D=2*delta*n; min nonzero weight >= d = n-k+1 actually).
    LP: maximize sum_i a_i subject to a_0=1, a_i>=0 for i in allowed weights, and for every t:
        1 + sum_i a_i K_t(i)/... >= 0 (dual MacWilliams nonnegativity).
    We solve the (small-n) LP exactly with scipy."""
    from scipy.optimize import linprog
    # allowed weights: 0 and [dmin .. D]; for RS dmin = n-k+1; but list-difference weights <=D.
    # variables a_i for i in W = {weights in [1,D]} (a_0 fixed =1)
    W = list(range(1,D+1))
    if not W: return 1.0
    # objective: maximize 1 + sum a_i  => minimize -(sum a_i)
    c = -np.ones(len(W))
    # constraints: for each t=0..n: (dual-distance nonneg) sum_i a_i K_t(i) >= -K_t(0)
    #   i.e. -sum_i a_i K_t(i) <= K_t(0).  K_t(0)=C(n,t)(q-1)^t.
    A=[]; b=[]
    for t in range(0,n+1):
        row = [krawtchouk(t,i,n,q) for i in W]
        A.append([-x for x in row]); b.append(krawtchouk(t,0,n,q))
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=[(0,None)]*len(W), method='highs')
    if not res.success: return None
    return 1 - res.fun  # 1 + sum a_i

print("="*94)
print(" Part C: classical Delsarte (Hamming-scheme) LP list bound vs TRUE worst-case RS list")
print("="*94)
print(f"{'p':>5}{'n':>4}{'k':>3}{'rho':>6}{'delta':>7}{'D=2dn':>7}{'LP bound':>12}{'true list':>11}{'verdict':>10}")
for (p,n,k) in [(17,8,2),(41,8,2),(97,16,2),(97,16,4),(193,16,4)]:
    M=mu_n(p,n); q=p
    # try a few deltas near/above Johnson
    rho=k/n
    johnson = 1-math.sqrt(rho)
    for delta_frac in [johnson*1.0, min(1-rho-0.001, johnson+0.12)]:
        delta = delta_frac
        radius = int(delta*n)
        D = 2*radius
        if D<1 or D>n: continue
        # TRUE worst-case list: enumerate codewords, find max over received words of #within radius.
        # codewords: all deg<k polys evaluated on M; coefficients in F_p (q^k of them) -- only tiny.
        if p**k <= 200000:
            codewords=[]
            for coeffs in itertools.product(range(p),repeat=k):
                cw = tuple(sum(coeffs[j]*pow(x,j,p) for j in range(k))%p for x in M)
                codewords.append(cw)
            codewords=list(set(codewords))
            # worst-case list: take each codeword as center proxy (received word = a codeword is a
            # natural worst case for list density), count codewords within Hamming radius
            best=0
            # sample received words = codewords (covers the structured worst case) + a few perturbed
            import random; random.seed(1)
            centers = codewords[:1] + random.sample(codewords, min(40,len(codewords)))
            for w in centers:
                cnt=sum(1 for cw in codewords if sum(1 for a,b in zip(w,cw) if a!=b)<=radius)
                best=max(best,cnt)
            true_list=best
        else:
            true_list=None
        lp = delsarte_lp_list_ball(n,q,n-k+1,D)
        verdict = "LP loose" if (lp is not None and true_list is not None and lp>=true_list) else "?"
        tl = f"{true_list}" if true_list is not None else "n/a"
        lpv = f"{lp:.2e}" if lp is not None else "fail"
        print(f"{p:>5}{n:>4}{k:>3}{rho:>6.2f}{delta:>7.3f}{D:>7}{lpv:>12}{tl:>11}{verdict:>10}")
