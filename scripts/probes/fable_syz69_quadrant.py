# Fable referee 2026-07-11: G56 reports the A5/A6 sign sweep over 68 primes
# p==1 mod 32, n=32, found ZERO (A5<0, A6>0) cells. Question: is
#   H_impl:   A5 < 0  =>  A6 < 0   (a usable one-directional structural law)
# TRUE as a field-uniform partial theorem, or is the empty quadrant just a
# small/biased sample (H_null)? A one-directional implication would be a real
# partial gate (it would let a prover certify A6>=0 by ruling out A5<0), so it
# must be tested hard before G56's "no monotone rule" verdict is accepted as
# fully closing the route. Extend the sweep + widen to multiple dyadic n.
import math
import numpy as np

def factor(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out
def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise ValueError(p)
def subgroup(p,n):
    z=pow(primitive_root(p),(p-1)//n,p)
    G=[];x=1
    for _ in range(n):G.append(x);x=x*z%p
    assert x==1 and len(set(G))==n
    return G
def subset_hists(G,p,R):
    dp=np.zeros((R+1,p),dtype=np.int64);dp[0,0]=1;used=0
    for x in G:
        used+=1
        for k in range(min(R,used),0,-1):
            dp[k]+=np.roll(dp[k-1],x)
    return dp
def circ_corr(a,b):
    c=np.rint(np.fft.ifft(np.fft.fft(a)*np.conj(np.fft.fft(b))).real).astype(np.int64)
    assert c.min()>=0
    assert int(c.sum())==int(a.sum())*int(b.sum())
    return c
def A_r(p,n,r):
    G=subgroup(p,n);dp=subset_hists(G,p,r)
    GS=set(G)
    W=np.zeros(p,dtype=np.int64)
    for y in G:
        for z in G:W[(2*y-z)%p]+=1
    R=circ_corr(dp[r],dp[r-1])
    totalR=math.comb(n,r)*math.comb(n,r-1)
    C12=sum(int(W[t])*int(R[t]) for t in range(p))
    return p*C12-n*n*totalR

def sweep(n, r_pair, pmax, label):
    r5,r6=r_pair
    cnt={"--":0,"+-":0,"++":0,"-+":0}
    viol=[]
    checked=0
    p=n+1
    while p<=pmax:
        # p == 1 mod n and prime
        if p%n==1:
            isp=all(p%d for d in range(2,int(p**0.5)+1))
            if isp:
                try:
                    a5=A_r(p,n,r5);a6=A_r(p,n,r6)
                except Exception:
                    p+=1;continue
                s5='-' if a5<0 else '+'
                s6='-' if a6<0 else '+'
                cnt[s5+s6]+=1
                checked+=1
                if s5=='-' and s6=='+':
                    viol.append((p,a5,a6))
        p+=1
    print(f"[{label}] n={n} r={r_pair} primes_checked={checked} pmax={pmax}")
    print(f"    (A5<0,A6<0)={cnt['--']}  (A5>0,A6<0)={cnt['+-']}  (A5>0,A6>0)={cnt['++']}  (A5<0,A6>0)={cnt['-+']}")
    if viol:
        print(f"    *** H_impl VIOLATED: A5<0 & A6>0 witnesses: {viol[:5]}")
    else:
        print(f"    H_impl (A5<0 => A6<0) HOLDS on this sample; also flag reverse-quadrant count (A5>0,A6<0)={cnt['+-']}")
    return cnt,viol

# n=32 extended well past G56's 19937 cap
sweep(32,(5,6),40000,"n32-extended")
# a DIFFERENT dyadic n to test field-uniformity of the implication
sweep(16,(5,6),8000,"n16")
sweep(64,(5,6),30000,"n64")
