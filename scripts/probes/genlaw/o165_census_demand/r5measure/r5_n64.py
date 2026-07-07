#!/usr/bin/env python3
"""
r5_n64.py — numpy-vectorized variety count for n=64 r=5 (#S_on_V, #bad, gamma0 fiber).
Processes the C(64,6)=74,974,368 6-subsets in batches; for each S computes the 4 needed
h_m via the incremental recurrence, vectorized over the batch. Self-checks r=3 n=16 and
r=5 n=16/32 against the known integers BEFORE running n=64.

h_m needed indices for line (e,f)=(n/2+1,n-1), r=5: {e-r, e-r+1, f-r, f-r+1} = {n/2-4, n/2-3, n-6, n-5}.
We compute h_0..h_M, M=n-5, via the per-root recurrence prev=h[m]+z*prev, vectorized over batch.
Modulus p=2013265921 (< 2^31), products fit in int64 (2^62), safe.
"""
import numpy as np
from math import comb, gcd
from itertools import combinations, islice
import sys
p = 2013265921
def mu_n(n, prime):
    e=(prime-1)//n
    for c in range(2,400):
        h=pow(c,e,prime)
        if pow(h,n,prime)==1 and pow(h,n//2,prime)!=1: return [pow(h,i,prime) for i in range(n)]

def batch_count(n, e, f, r, batch=200000, verbose_every=20):
    a0=r+1; dom=np.array(mu_n(n,p), dtype=np.int64)
    M=max(e-r, e-r+1, f-r, f-r+1, 0)
    ie0, ie1, if0, if1 = e-r, e-r+1, f-r, f-r+1
    # distinct gamma via a python set; gamma0 fiber count; S_on_V
    from collections import Counter
    gammas=Counter(); S_on_V=0; gamma0_fiber=0
    it=combinations(range(n), a0)
    total=comb(n,a0); done=0; bno=0
    while True:
        chunk=list(islice(it, batch))
        if not chunk: break
        idx=np.array(chunk, dtype=np.int64)         # (B, a0)
        Z=dom[idx]                                    # (B, a0) roots of each subset
        B=Z.shape[0]
        # compute h[0..M] vectorized: H shape (B, M+1)
        H=np.zeros((B, M+1), dtype=np.int64); H[:,0]=1
        for col in range(a0):
            z=Z[:,col]                                # (B,)
            new=np.zeros_like(H); prev=np.zeros(B, dtype=np.int64)
            for m in range(M+1):
                prev=(H[:,m] + z*prev) % p
                new[:,m]=prev
            H=new
        her=H[:,ie0]; her1=H[:,ie1]; hfr=H[:,if0]; hfr1=H[:,if1]
        onV=((her*hfr1 - hfr*her1) % p)==0
        pin=onV & (hfr!=0)
        # gamma = -her/hfr mod p for pinned rows
        rows=np.nonzero(pin)[0]
        S_on_V += int(rows.size)
        if rows.size:
            herp=her[rows]; hfrp=hfr[rows]
            # modular inverse via pow in python (vectorized not available); batch using pow on ndarray? loop
            inv=np.array([pow(int(x), p-2, p) for x in hfrp], dtype=np.int64)
            gam=((-herp*inv) % p)
            for g in gam.tolist():
                gammas[g]+=1
                if g==0: gamma0_fiber+=1
        done+=B; bno+=1
        if bno % verbose_every == 0:
            sys.stderr.write(f"  ... {done}/{total} ({100*done/total:.1f}%) S_on_V={S_on_V}\n"); sys.stderr.flush()
    distinct_nonzero=len([g for g in gammas if g!=0])
    nbad=distinct_nonzero + (1 if 0 in gammas else 0)
    d=gcd(e-f,n); orbit=n//d
    fib=sorted(gammas.values())
    from collections import Counter as C2
    fibdist=dict(sorted(C2(fib).items()))
    K=(1<<r)*comb(n//2,r)
    return dict(n=n,e=e,f=f,r=r,K=K,S_on_V=S_on_V,nbad=nbad,distinct_nonzero=distinct_nonzero,
                gamma0=(0 in gammas),gamma0_fiber=gamma0_fiber,d=d,orbit=orbit,
                OP=(distinct_nonzero//orbit if distinct_nonzero%orbit==0 else None),
                fibmin=min(fib),fibmax=max(fib),fibdist=fibdist)

def selfcheck():
    c3=batch_count(16,8,7,3); assert c3['nbad']==97, c3['nbad']
    c5a=batch_count(16,9,15,5); assert c5a['nbad']==89 and c5a['S_on_V']==456, (c5a['nbad'],c5a['S_on_V'])
    print(f"[selfcheck] r3 n16 #bad={c3['nbad']}(==97); r5 n16 #bad={c5a['nbad']}(==89) S_on_V={c5a['S_on_V']}(==456) OK", flush=True)

if __name__=="__main__":
    selfcheck()
    ns=[int(x) for x in sys.argv[1:]] if len(sys.argv)>1 else [32]
    for n in ns:
        res=batch_count(n, n//2+1, n-1, 5)
        print(f"\n=== r=5 n={n} line(x^{res['e']},x^{res['f']}) [numpy] ===", flush=True)
        for kk in ['K','S_on_V','nbad','distinct_nonzero','gamma0','gamma0_fiber','d','orbit','OP','fibmin','fibmax']:
            print(f"  {kk} = {res[kk]}", flush=True)
        print(f"  #S_on_V<=K ? {res['S_on_V']<=res['K']}  K/#S_on_V={res['K']/max(res['S_on_V'],1):.3f}", flush=True)
        print(f"  #S_on_V/#bad={res['S_on_V']/max(res['nbad'],1):.3f}  #bad<=#S_on_V ? {res['nbad']<=res['S_on_V']}", flush=True)
        print(f"  fiber dist (truncated to 12) = {dict(list(res['fibdist'].items())[:12])}", flush=True)
