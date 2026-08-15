#!/usr/bin/env python3
"""SYZ28 part 3: (a) analyze the single classification mismatch; (b) mca-filtered lift test."""
import itertools, random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached, A_C_basis,
    deficiency, sum_excess)
from probe_syz28_verify_classification import forced_defect, build_interp_mats

# ---------- (a) the mismatch cover ----------
MM=[[0, 2, 3, 5, 6, 7, 8, 9, 13, 15, 16, 18, 19, 21, 22, 23],
    [0, 1, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 18, 19, 20, 21],
    [3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 16, 17, 18, 20, 21, 22]]
n=24;k=12
S=[set(c) for c in MM]
print("(a) mismatch cover analysis  n=24 k=12  ceil(2n/3)=16  band interior sizes={17}")
print("   sizes:",[len(c) for c in MM],"(ALL = 16 = boundary size, delta=1/3 edge, NOT strict interior)")
print("   pairwise overlaps:",sorted(len(S[a]&S[b]) for a,b in itertools.combinations(range(3),2)),
      "  triple:",len(S[0]&S[1]&S[2]))
print("   pair unions:",sorted(len(S[a]|S[b]) for a,b in itertools.combinations(range(3),2)))
ds=[deficiency(list(range(n)),k,p,MM)[0] for p in (101,1009,65537,1000003,2147483647)]
print("   d over primes {101,1009,65537,1e6+3,2^31-1}:",ds,
      " -> ", "FIELD-INDEPENDENT (genuine deeper shape)" if all(x>0 for x in ds) else "FIELD ACCIDENT")
print("   forced pair-union defect:",forced_defect(n,k,MM))

# is it on the boundary only?  strict-interior-only resweep for n=24 (all cores size 17)
print("\n   strict-interior-only resweep (all cores size 17, n=24): does classification hold exactly?")
random.seed(11); alpha=list(range(24)); mism=0; tested=0
for _ in range(120000):
    cores=[];seen=set();ok=True
    for _c in range(3):
        C=tuple(sorted(random.sample(range(24),17)))
        if C in seen: ok=False;break
        seen.add(C);cores.append(list(C))
    if not ok: continue
    if len(set().union(*[set(c) for c in cores]))<24: continue
    tested+=1
    d=deficiency(alpha,12,65537,cores)[0]
    if d!=forced_defect(24,12,cores):
        mism+=1
        print("      STRICT-INTERIOR MISMATCH:",cores,"d=",d,"forced=",forced_defect(24,12,cores))
print(f"      tested={tested}  mismatches={mism}")

# ---------- (b) mca-filtered lift test on the n=16 witness ----------
print("\n(b) mca-filtered word-level lift test, n=16 witness, p=17, s=11")
W=[[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 15],
   [1, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15],
   [0, 1, 3, 4, 5, 9, 10, 11, 12, 14, 15]]
n16,k16,s16,p=16,8,11,17
alpha=list(range(n16))
mats=build_interp_mats(n16,k16,s16,p)

def agreement_sets(w):
    """all maximal agreement indicator sets (>= s16) of w with deg<k polys."""
    outs=set()
    for T,M in mats:
        vals=[w[t] for t in T]
        agr=[]
        for j in range(n16):
            v=sum(a*b for a,b in zip(M[j],vals))
            if v%p==w[j]%p: agr.append(j)
        if len(agr)>=s16: outs.add(tuple(agr))
    return outs

def is_close(w): return len(agreement_sets(w))>0

def mca_holds(u0,u1):
    """exists S, |S|>=s16, and polys f,g with u0|S=f|S and u1|S=g|S."""
    A0=agreement_sets(u0); A1=agreement_sets(u1)
    for a in A0:
        for b in A1:
            if len(set(a)&set(b))>=s16: return True
    return False

Db=dual_basis_cached(alpha,k16,p)
AC=[A_C_basis(Db,C,n16,p) for C in W]
random.seed(3)
maxbad=0; best=None
for trial in range(60):
    zs=random.sample(range(1,p),3)
    rows=[]
    for i in range(3):
        for v in AC[i]:
            rows.append([v[j]%p for j in range(n16)]+[(zs[i]*v[j])%p for j in range(n16)])
    r,null=rref_rank_nullbasis(rows,2*n16,p)
    if not null: continue
    u=[0]*(2*n16)
    for b in null:
        c=random.randrange(p)
        for j in range(2*n16): u[j]=(u[j]+c*b[j])%p
    u0,u1=u[:n16],u[n16:]
    if all(x==0 for x in u1): continue
    if mca_holds(u0,u1): continue   # correlated agreement => not an mca-bad stack
    bad=[z for z in range(p) if is_close([(u0[j]+z*u1[j])%p for j in range(n16)])]
    if is_close(u1): bad.append('inf')
    if len(bad)>maxbad: maxbad=len(bad); best=(zs,bad,u0,u1)
print(f"   max mca-bad scalars over non-correlated pencil stacks: {maxbad}")
if best: print(f"   achieved at z_i={best[0]}  bad={best[1]}")
print(f"   yield cap sum(n-s_i)=15;  SYZ22 budget n-1=15;  falsification needs > n=16")
print("   VERDICT:", "UNDER-BUDGET, strip safe at D=3" if maxbad<=15 else
      ("AT BUDGET EDGE" if maxbad<=16 else "OVER BUDGET - INVESTIGATE"))
