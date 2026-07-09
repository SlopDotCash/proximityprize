#!/usr/bin/env python3
"""
probe_444_n64_m16_j8_fast.py  (#444 CRACK-HUNT stage 1, FAST)

TARGET: n=64, m0=16, j=8. DEFECT = non-(mu_16-coset) size-16 subset T of mu_64 with
e_1..e_8 = 0 mod p. C(64,16) ~ 5e14 infeasible -> structured + MITM search, HONEST coverage.

Power-sum form: e_1..e_8 = 0  <=>  p_1..p_8 = 0 mod p (Newton; p>16 so invertible).
pvec(T) = (sum_{i in T} zeta^{k i})_{k=1..8} in (F_p)^8.  Want pvec(T)=0, |T|=16, T != mu16-coset.

Coverage tiers (each EXACT within its family, across ALL primes):
  T1  the 4 mu_16-cosets  (baseline: clean binomials, e_1..e_15=0).
  T2  unions of 2 mu_8-coset blocks  (C(8,2)=28).
  T3  unions of 4 mu_4-coset blocks  (C(16,4)=1820).
  T4  unions of 8 mu_2-coset blocks  (C(32,8)=10.5M)  -- via MITM (16+16 block split).
  T5  GENERAL roots MITM: T = A(idx 0..31) cup B(idx 32..63), |A|+|B|=16, balanced band,
      EXACT over the chosen |A| band. (This is the real "any non-coset" net.)
"""
import itertools, sys, math
from sympy import isprime, primitive_root

N=64; M0=16; J=8

def primes_mod(n, count, idx_min=2, pmin=64):
    out=[]; pp=pmin - (pmin % n) + 1
    while pp<=pmin or pp<n+1: pp+=n
    while len(out)<count:
        if isprime(pp) and (pp-1)%n==0 and (pp-1)//n>=idx_min: out.append(pp)
        pp+=n
    return out

def prize_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e

def elem_sym_idx(idxs, elts, p, upto):
    e=[1]+[0]*upto
    for i in idxs:
        r=elts[i]
        for t in range(min(len(e)-1,upto),0,-1): e[t]=(e[t]+e[t-1]*r)%p
    return e[1:upto+1]

def is_mu16_coset(idxs):
    s=set(idxs)
    if len(s)!=16: return False
    for i0 in range(4):
        if set((i0+4*j)%N for j in range(16))==s: return True
    return False

def mu_d_blocks(d):
    step=N//d
    return [tuple((i0+step*j)%N for j in range(d)) for i0 in range(step)]

def build_powtab(elts,p):
    # powtab[k][i] = zeta^{(k+1) i}, k=0..J-1
    return [[pow(elts[i],k,p) for i in range(N)] for k in range(1,J+1)]

def pvec(idxs, powtab, p):
    v=[0]*J
    for i in idxs:
        for k in range(J): v[k]=(v[k]+powtab[k][i])%p
    return tuple(v)

def verify_defect(idxs, elts, p):
    """final exact check: |T|=16, e_1..e_8=0, not mu16-coset."""
    if len(set(idxs))!=16: return False
    if is_mu16_coset(idxs): return False
    es=elem_sym_idx(idxs, elts, p, J)
    return all(z==0 for z in es)

# ---- Tier 1 ----
def tier1(p, elts):
    cs=[frozenset((i0+4*j)%N for j in range(16)) for i0 in range(4)]
    ok=all(all(z==0 for z in elem_sym_idx(c,elts,p,15)) for c in cs)
    return len(cs), ok

# ---- Tier 2,3 (small exact) ----
def tier23(p, elts, powtab):
    found=[]
    b8=mu_d_blocks(8)
    for combo in itertools.combinations(range(8),2):
        idxs=set()
        for c in combo: idxs|=set(b8[c])
        if pvec(idxs,powtab,p)==(0,)*J and verify_defect(idxs,elts,p):
            found.append(('2xmu8',tuple(sorted(idxs))))
    b4=mu_d_blocks(4)
    for combo in itertools.combinations(range(16),4):
        idxs=set()
        for c in combo: idxs|=set(b4[c])
        if len(idxs)!=16: continue
        if pvec(idxs,powtab,p)==(0,)*J and verify_defect(idxs,elts,p):
            found.append(('4xmu4',tuple(sorted(idxs))))
    return found

# ---- Tier 4: 8 of 32 mu_2-blocks via MITM ----
def tier4(p, elts, powtab, report=3):
    b2=mu_d_blocks(2)  # 32 blocks, each {i0, i0+32}
    blkpv=[pvec(set(b),powtab,p) for b in b2]
    L=list(range(16)); H=list(range(16,32))
    # choose 8 blocks total split as (a from L, 8-a from H). Hash H-combos by pvec.
    found=[]
    for a in range(0,9):
        bcnt=8-a
        if bcnt<0 or bcnt>16 or a>16: continue
        table={}
        for Hc in itertools.combinations(H,bcnt):
            v=[0]*J
            for blk in Hc:
                pv=blkpv[blk]
                for k in range(J): v[k]=(v[k]+pv[k])%p
            nv=tuple((-x)%p for x in v)
            table.setdefault(nv,Hc)
        for Lc in itertools.combinations(L,a):
            v=[0]*J
            for blk in Lc:
                pv=blkpv[blk]
                for k in range(J): v[k]=(v[k]+pv[k])%p
            v=tuple(v)
            if v in table:
                blocks=list(Lc)+list(table[v])
                idxs=set()
                for blk in blocks: idxs|=set(b2[blk])
                if verify_defect(idxs,elts,p):
                    found.append(('8xmu2',tuple(sorted(idxs))))
                    if len(found)>=report: return found
    return found

# ---- Tier 5: general roots MITM, LOW0..31 / HIGH32..63 ----
def tier5(p, elts, powtab, a_lo, a_hi, report=3, cap=15_000_000):
    LOW=list(range(0,32)); HIGH=list(range(32,64))
    found=[]
    for a in range(a_lo,a_hi+1):
        b=16-a
        if b<0 or b>32: continue
        nA=math.comb(32,a); nB=math.comb(32,b)
        hashHigh = nB<=nA
        small_n = min(nA,nB)
        if small_n>cap: continue
        table={}
        if hashHigh:
            for Bc in itertools.combinations(HIGH,b):
                v=pvec(Bc,powtab,p); nv=tuple((-x)%p for x in v)
                table.setdefault(nv,Bc)
            for Ac in itertools.combinations(LOW,a):
                v=pvec(Ac,powtab,p)
                if v in table:
                    idxs=set(Ac)|set(table[v])
                    if verify_defect(idxs,elts,p):
                        found.append(('mitm_a%d'%a,tuple(sorted(idxs))))
                        if len(found)>=report: return found
        else:
            for Ac in itertools.combinations(LOW,a):
                v=pvec(Ac,powtab,p); nv=tuple((-x)%p for x in v)
                table.setdefault(nv,Ac)
            for Bc in itertools.combinations(HIGH,b):
                v=pvec(Bc,powtab,p)
                if v in table:
                    idxs=set(table[v])|set(Bc)
                    if verify_defect(idxs,elts,p):
                        found.append(('mitm_a%d'%a,tuple(sorted(idxs))))
                        if len(found)>=report: return found
    return found

if __name__=="__main__":
    tiers = sys.argv[1] if len(sys.argv)>1 else "1234"
    small=primes_mod(N,12,idx_min=2,pmin=64)
    prize=list(dict.fromkeys([prize_prime(N,4.0),prize_prime(N,4.25),prize_prime(N,4.5)]))
    allp=small+prize
    print(f"### n={N} m0={M0} j={J} FAST DEFECT HUNT  tiers={tiers} ###",flush=True)
    print(f"### small primes ({len(small)}): {small}",flush=True)
    print(f"### prize primes: {prize}  log2={[round(math.log2(x),1) for x in prize]}",flush=True)

    any_defect=False
    for p in allp:
        elts=subgroup(N,p); powtab=build_powtab(elts,p)
        msgs=[]
        if '1' in tiers:
            n,ok=tier1(p,elts); msgs.append(f"T1 cosets={n} clean={ok}")
        if '2' in tiers:
            f=tier23(p,elts,powtab)
            msgs.append(f"T2/3 defects={len(f)}")
            if f: any_defect=True; msgs.append(f"  !!{f[0]}")
        if '4' in tiers:
            f=tier4(p,elts,powtab)
            msgs.append(f"T4 defects={len(f)}")
            if f: any_defect=True; msgs.append(f"  !!{f[0]}")
        print(f"  p={p} (m={(p-1)//N}): " + " | ".join(msgs), flush=True)
    if '5' in tiers:
        print("\n--- TIER 5: general MITM (LOW/HIGH split) band a in [7,9] ---",flush=True)
        for p in allp[:6]:
            elts=subgroup(N,p); powtab=build_powtab(elts,p)
            f=tier5(p,elts,powtab,7,9,report=3)
            if f: any_defect=True; print(f"  p={p}: MITM DEFECT {f[0]}",flush=True)
            else: print(f"  p={p}: no MITM defect (band 7..9)",flush=True)
    print(f"\n### ANY DEFECT FOUND: {any_defect} ###",flush=True)
