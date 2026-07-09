#!/usr/bin/env python3
"""
probe_444_n64_m16_j8_defect.py  (#444 SEAM A, CRACK-HUNT stage 1)

TARGET CONFIG (exactly as specified): n=64, m0=16, j=8.
A DEFECT = a NON-COSET lacunary subset T subset mu_64, |T|=16, with
   e_1(T) = ... = e_8(T) = 0  mod p,
that is NOT a coset of mu_16 (the 4 cosets: index sets closed under +4).

C(64,16) ~ 4.9e14 -> NO full enumeration. We use the ALGEBRAIC view + structural search.

STRATEGY A (coset baseline + structure):
  The 4 mu_16-cosets are index sets {i, i+4, ..., i+60}, i=0..3. Their product polynomial is
  x^16 - c (a clean binomial), so e_1..e_15 all vanish (even more than 8). These are the
  guaranteed char-0 / char-p solutions. Confirm count.

STRATEGY B (block-union meet-in-the-middle over mu_8 sub-blocks):
  A defect that is "structured" would be a union of smaller coset-blocks arranged off-pattern.
  We enumerate unions of mu_8-cosets-pieces / sub-blocks that hit |T|=16 and test e_1..e_8.
  (This is the natural place a *combinatorial* non-coset solution would live.)

STRATEGY C (Newton / power-sum guided randomized + greedy divisor walk):
  Build f = monic deg-16 divisor of x^64-1 with top-8 coeffs zero by:
   - choosing roots to kill power sums p_1..p_8 (Newton <=> e_1..e_8) greedily/branch-and-bound.
   - We do a depth-limited DFS over which of the 64 roots to include, pruning by partial
     symmetric-function feasibility. Exact for the parts we can reach; HONEST about coverage.

We sweep MANY primes p = 1 mod 64 (small-index m=(p-1)/64 >= 2 AND prize-shaped p ~ 64^4).
Report the FIRST/SMALLEST non-coset lacunary subset (defect) or "NO defect" with coverage.
"""
import itertools, sys, random
from math import comb
from sympy import isprime, primitive_root

N = 64
M0 = 16
J = 8

def primes_mod(n, count, idx_min=2, pmin=0):
    out=[]; pp=pmin - (pmin % n) + 1
    if pp <= pmin: pp += n
    if pp < n+1: pp = n+1
    while len(out) < count:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= idx_min:
            out.append(pp)
        pp += n
    return out

def find_prize_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e   # e[i] = zeta^i, index i = discrete log

def elem_sym_from_idx(idxs, elts, p, upto):
    """elementary symmetric e_1..e_upto of {elts[i]} mod p."""
    e=[1]+[0]*upto
    for i in idxs:
        r=elts[i]
        for t in range(min(len(e)-1,upto),0,-1): e[t]=(e[t]+e[t-1]*r)%p
    return e[1:upto+1]

def is_mu16_coset(idxs):
    """T (as index set) is a mu_16 coset iff it = {i0 + 4*j mod 64 : j=0..15} for some i0 in 0..3."""
    s=set(idxs)
    if len(s)!=16: return False
    for i0 in range(4):
        if set((i0+4*j)%N for j in range(16))==s: return True
    return False

def coset_index_sets():
    return [frozenset((i0+4*j)%N for j in range(16)) for i0 in range(4)]

# ---------- STRATEGY A: confirm the 4 cosets ----------
def confirm_cosets(p, elts):
    cs=coset_index_sets()
    ok=True
    for c in cs:
        es=elem_sym_from_idx(c, elts, p, 15)
        if any(v!=0 for v in es):  # binomial x^16 - const: ALL e_1..e_15 vanish
            ok=False
    return len(cs), ok

# ---------- STRATEGY B: union of mu_8-coset sub-blocks ----------
# mu_8 cosets (size 8) are index sets closed under +8: {i0+8j: j=0..7}, i0=0..7 (8 blocks).
# A union of TWO distinct mu_8-cosets has size 16. Test all C(8,2)=28 such unions.
# Also: more general "structured" size-16 sets = arbitrary unions of size-4 (mu_4-coset, +16)
# blocks: there are 16 such blocks, choose 4 -> C(16,4)=1820 unions of size 16. Test all.
def mu_d_coset_blocks(d):
    """index sets of mu_d cosets: closed under +N/d. There are N/d of them, each size d."""
    step=N//d
    return [frozenset((i0+step*j)%N for j in range(d)) for i0 in range(step)]

def strategy_B(p, elts, report):
    """structured unions: 2x(mu_8 block size8), 4x(mu_4 block size4), 8x(mu_2 block size2),
       16x(mu_1 = singletons, that's everything -> skip). Test e_1..e_8 for each union."""
    found=[]
    # 2 unions of mu_8-cosets (size 8 each)
    blocks8=mu_d_coset_blocks(8)   # 8 blocks
    for combo in itertools.combinations(range(8),2):
        idxs=set()
        for b in combo: idxs|=blocks8[b]
        es=elem_sym_from_idx(idxs, elts, p, J)
        if all(v==0 for v in es) and not is_mu16_coset(idxs):
            found.append(('2xmu8', tuple(sorted(idxs))))
    # 4 unions of mu_4-cosets (size 4 each), 16 blocks choose 4
    blocks4=mu_d_coset_blocks(4)   # 16 blocks
    for combo in itertools.combinations(range(16),4):
        idxs=set()
        for b in combo: idxs|=blocks4[b]
        if len(idxs)!=16: continue
        es=elem_sym_from_idx(idxs, elts, p, J)
        if all(v==0 for v in es) and not is_mu16_coset(idxs):
            found.append(('4xmu4', tuple(sorted(idxs))))
            if len(found)>=report: return found
    # 8 unions of mu_2-cosets (size 2: {i0,i0+32}), 32 blocks choose 8
    blocks2=mu_d_coset_blocks(2)   # 32 blocks
    cnt=0
    for combo in itertools.combinations(range(32),8):
        idxs=set()
        for b in combo: idxs|=blocks2[b]
        if len(idxs)!=16: continue
        es=elem_sym_from_idx(idxs, elts, p, J)
        if all(v==0 for v in es) and not is_mu16_coset(idxs):
            found.append(('8xmu2', tuple(sorted(idxs))))
            if len(found)>=report: return found
        cnt+=1
    return found

# ---------- STRATEGY C: branch-and-bound DFS over root inclusion killing power sums ----------
# Use power sums p_k = sum_{i in T} zeta^{k i}. e_1..e_8=0  <=>  p_1..p_8 = 0 (Newton, char p
# large > 16 so invertible). We DFS choosing indices in increasing order, maintaining partial
# power sums; prune when remaining capacity can't reach |T|=16. Full pruning on the symmetric
# side is weak, so we instead use a MEET-IN-THE-MIDDLE on power-sum vectors:
#   split mu_64 into LOW indices 0..31 and HIGH indices 32..63.
#   For each subset A of LOW with |A|=a and each subset Bset of HIGH with |B|=16-a,
#   we need pvec(A) + pvec(B) = 0  in (F_p)^8. Hash all pvec(B) (negated) and look up pvec(A).
# Even C(32,8) ~ 10.5M is large but feasible to hash for a few primes; we cap |A| range to make
# it tractable and HONEST. We focus a in a band around 8 (balanced) for richest coverage.
def pvec_of_idx_set(idxs, powtab, p):
    """power sums p_1..p_8 of {zeta^i : i in idxs}, using precomputed powtab[k][i]=zeta^{k*i}."""
    v=[0]*J
    for i in idxs:
        for k in range(J):
            v[k]=(v[k]+powtab[k][i])%p
    return tuple(v)

def build_powtab(elts,p):
    # powtab[k][i] = elts[i]^(k+1) = zeta^{(k+1) i}
    powtab=[]
    for k in range(1,J+1):
        powtab.append([pow(elts[i],k,p) for i in range(N)])
    return powtab

def strategy_C_mitm(p, elts, a_lo=6, a_hi=10, report=4, cap_half=20_000_000):
    """meet in the middle: T = A (subset of indices 0..31) cup B (subset 32..63), |A|=a,|B|=16-a.
       want pvec(A) = -pvec(B). For each a in [a_lo,a_hi], hash HIGH side, scan LOW side.
       Returns list of defect index-sets found (non-coset). HONEST: only covers the
       LOW=0..31 / HIGH=32..63 split and the |A| band [a_lo,a_hi]."""
    powtab=build_powtab(elts,p)
    LOW=list(range(0,32)); HIGH=list(range(32,64))
    found=[]
    for a in range(a_lo, a_hi+1):
        b=16-a
        if b<0 or b>32: continue
        nA=comb(32,a); nB=comb(32,b)
        # choose to hash the smaller side
        if nB>cap_half and nA>cap_half:
            continue
        # hash HIGH side (negated pvec) -> map from pvec to a sample B (store a few)
        # to bound memory, if nB huge, swap so we hash the smaller
        hashHIGH = (nB <= nA)
        table={}
        if hashHIGH:
            if nB>cap_half: continue
            for Bc in itertools.combinations(HIGH,b):
                v=pvec_of_idx_set(Bc,powtab,p)
                nv=tuple((-x)%p for x in v)
                table.setdefault(nv,Bc)   # store one representative B per pvec
            for Ac in itertools.combinations(LOW,a):
                v=pvec_of_idx_set(Ac,powtab,p)
                if v in table:
                    idxs=set(Ac)|set(table[v])
                    if len(idxs)==16 and not is_mu16_coset(idxs):
                        # double-check elem_sym truly 0 (Newton edge cases)
                        es=elem_sym_from_idx(idxs, elts, p, J)
                        if all(z==0 for z in es):
                            found.append(('mitmLH_a%d'%a, tuple(sorted(idxs))))
                            if len(found)>=report: return found
        else:
            if nA>cap_half: continue
            for Ac in itertools.combinations(LOW,a):
                v=pvec_of_idx_set(Ac,powtab,p)
                nv=tuple((-x)%p for x in v)
                table.setdefault(nv,Ac)
            for Bc in itertools.combinations(HIGH,b):
                v=pvec_of_idx_set(Bc,powtab,p)
                if v in table:
                    idxs=set(table[v])|set(Bc)
                    if len(idxs)==16 and not is_mu16_coset(idxs):
                        es=elem_sym_from_idx(idxs, elts, p, J)
                        if all(z==0 for z in es):
                            found.append(('mitmLH_a%d'%a, tuple(sorted(idxs))))
                            if len(found)>=report: return found
    return found

if __name__=="__main__":
    mode = sys.argv[1] if len(sys.argv)>1 else "AB"
    # prime sets
    small = primes_mod(N, 12, idx_min=2, pmin=64)        # small-index m>=2
    prize = [find_prize_prime(N,4.0), find_prize_prime(N,4.25), find_prize_prime(N,4.5)]
    prize = list(dict.fromkeys(prize))
    allp = small + prize
    print(f"### n={N} m0={M0} j={J} DEFECT HUNT ###", flush=True)
    print(f"### small-index primes: {small}", flush=True)
    print(f"### prize-shaped primes: {prize}  (log2 ~ {[round(__import__('math').log2(x),1) for x in prize]})", flush=True)

    if mode in ("A","AB","ALL"):
        print("\n--- STRATEGY A: confirm the 4 mu_16 cosets are clean lacunary (e_1..e_15=0) ---", flush=True)
        for p in allp[:6]:
            ncos, ok = confirm_cosets(p, subgroup(N,p))
            print(f"   p={p}: #mu16-cosets={ncos}  all binomial(e_1..e_15=0)? {ok}", flush=True)

    if mode in ("B","AB","ALL"):
        print("\n--- STRATEGY B: structured block-union defects (2xmu8, 4xmu4, partial 8xmu2) ---", flush=True)
        total_def=0
        for p in allp:
            f=strategy_B(p, subgroup(N,p), report=4)
            if f:
                total_def+=len(f)
                print(f"   p={p}: STRUCTURED DEFECTS={len(f)} e.g. {f[0]}", flush=True)
            else:
                print(f"   p={p}: no structured (block-union) defect", flush=True)
        if total_def==0:
            print("   => STRATEGY B: NO structured block-union defect at any prime tested.", flush=True)

    if mode in ("C","ALL"):
        print("\n--- STRATEGY C: meet-in-the-middle power-sum search (LOW0..31/HIGH32..63 split) ---", flush=True)
        total_def=0
        for p in allp[:6]:
            f=strategy_C_mitm(p, subgroup(N,p), a_lo=7, a_hi=9, report=4)
            if f:
                total_def+=len(f)
                print(f"   p={p}: MITM DEFECTS={len(f)} e.g. {f[0]}", flush=True)
            else:
                print(f"   p={p}: no MITM defect in |A| band [7,9]", flush=True)
        if total_def==0:
            print("   => STRATEGY C: NO non-coset defect in the searched band.", flush=True)
