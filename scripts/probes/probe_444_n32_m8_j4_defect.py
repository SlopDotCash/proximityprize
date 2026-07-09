#!/usr/bin/env python3
"""
probe_444_n32_m8_j4_defect.py  (#444 SEAM A, CRACK-HUNT stage 1)

TARGET CONFIG (exactly as specified): n=32, m0=8, j=4.
A DEFECT = a NON-COSET lacunary subset T subset mu_32, |T|=8, with
   e_1(T) = ... = e_4(T) = 0  mod p,
that is NOT a coset of mu_8 (the 4 cosets of mu_8 = index sets closed under +4: {i0+4*j: j=0..7}).

C(32,8) = 10,518,300.  Full per-prime enumeration is feasible but slow over many primes.
We use a MEET-IN-THE-MIDDLE on power sums which is EXACT and EXHAUSTIVE over ALL size-8 subsets:

  Newton's identities: over F_p with p > 8, e_1..e_4 = 0  <=>  p_1..p_4 = 0  (power sums),
  where p_k(T) = sum_{i in T} zeta^{k*i}.  (Invertible since 1,2,3,4 < p.)

  Split indices of mu_32 into LOW = {0..15}, HIGH = {16..31}.  Every size-8 subset T splits
  uniquely as A = T cap LOW (|A|=a) and B = T cap HIGH (|B|=8-a).  We need
       pvec(A) + pvec(B) = 0  in (F_p)^4.
  For each a in 0..8: hash all pvec(B) over B subset HIGH of size 8-a (negated), then scan
  all A subset LOW of size a and look up.  This enumerates EVERY size-8 subset exactly once
  (collisions on the 4-dim power-sum vector are the lacunary subsets).  Sum of C(16,a)*C(16,8-a)
  over a = C(32,8) by Vandermonde, so coverage is COMPLETE / EXHAUSTIVE.

A collision is a lacunary subset.  We then test is_mu8_coset; non-coset => DEFECT.
We ALSO record, for each defect, the char-0 sum |beta_T| (Lam-Leung: =0 over C means a
"hidden coset"/antipodal type; !=0 means genuine non-coset) and antipodality.

Sweeps MANY primes p = 1 mod 32 (small-index m=(p-1)/32 >= 2 AND prize-shaped p ~ 32^4).
Reports the FIRST/SMALLEST non-coset lacunary subset (defect) or "NO defect" with coverage.
"""
import itertools, sys, math, cmath
from math import comb
from sympy import isprime, primitive_root

N = 32
M0 = 8
J = 4

def primes_mod(n, count, idx_min=2, pmin=0):
    """primes p > pmin with (p-1)%n==0 and index (p-1)//n >= idx_min."""
    out=[]; pp = pmin - (pmin % n) + 1
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
    e=[1]+[0]*upto
    for i in idxs:
        r=elts[i]
        for t in range(min(len(e)-1,upto),0,-1): e[t]=(e[t]+e[t-1]*r)%p
    return e[1:upto+1]

def is_mu8_coset(idxs):
    """T (index set) is a mu_8 coset iff = {i0 + 4*j mod 32 : j=0..7} for some i0 in 0..3."""
    s=set(idxs)
    if len(s)!=M0: return False
    for i0 in range(4):
        if set((i0+4*j)%N for j in range(M0))==s: return True
    return False

def coset_index_sets():
    return [frozenset((i0+4*j)%N for j in range(M0)) for i0 in range(4)]

def beta_char0_abs(idxs):
    z=2j*math.pi/N
    return abs(sum(cmath.exp(z*i) for i in idxs))

def is_antipodal(idxs):
    s=set(idxs)
    return all(((i+N//2)%N) in s for i in s)

# is T a coset of ANY sub-subgroup mu_d (d | 32), i.e. structured (union/coset)?
def coset_of_subgroup_d(idxs, d):
    """is T exactly a coset of mu_d (size d)?  Only meaningful when |idxs|==d."""
    if len(idxs)!=d: return False
    step=N//d; s=set(idxs)
    for i0 in range(step):
        if set((i0+step*j)%N for j in range(d))==s: return True
    return False

def build_powtab(elts,p):
    """powtab[k][i] = elts[i]^(k+1) = zeta^{(k+1)*i}, k=0..J-1 -> power sums p_1..p_J."""
    return [[pow(elts[i],k,p) for i in range(N)] for k in range(1,J+1)]

def pvec(idxs, powtab, p):
    v=[0]*J
    for i in idxs:
        for k in range(J): v[k]=(v[k]+powtab[k][i])%p
    return tuple(v)

def mitm_search(p, elts, max_report=None, collect_all=False):
    """EXHAUSTIVE meet-in-the-middle over ALL size-8 subsets.
       Returns (n_lacunary, defects) where defects = list of (sorted_idx, beta_abs, antip)."""
    powtab=build_powtab(elts,p)
    LOW=list(range(0,16)); HIGH=list(range(16,32))
    n_lac=0; defects=[]
    cosets=set(coset_index_sets())
    for a in range(0,9):
        b=8-a
        # hash the smaller side
        if comb(16,b) <= comb(16,a):
            # hash HIGH (size b), scan LOW (size a)
            table={}
            for Bc in itertools.combinations(HIGH,b):
                v=pvec(Bc,powtab,p)
                nv=tuple((-x)%p for x in v)
                table.setdefault(nv,[]).append(Bc)
            for Ac in itertools.combinations(LOW,a):
                v=pvec(Ac,powtab,p)
                if v in table:
                    for Bc in table[v]:
                        idxs=set(Ac)|set(Bc)
                        n_lac+=1
                        fs=frozenset(idxs)
                        if fs not in cosets and not is_mu8_coset(idxs):
                            Tidx=tuple(sorted(idxs))
                            defects.append((Tidx, beta_char0_abs(Tidx), is_antipodal(Tidx)))
                            if (max_report is not None) and (len(defects)>=max_report) and not collect_all:
                                return n_lac, defects
        else:
            # hash LOW (size a), scan HIGH (size b)
            table={}
            for Ac in itertools.combinations(LOW,a):
                v=pvec(Ac,powtab,p)
                nv=tuple((-x)%p for x in v)
                table.setdefault(nv,[]).append(Ac)
            for Bc in itertools.combinations(HIGH,b):
                v=pvec(Bc,powtab,p)
                if v in table:
                    for Ac in table[v]:
                        idxs=set(Ac)|set(Bc)
                        n_lac+=1
                        fs=frozenset(idxs)
                        if fs not in cosets and not is_mu8_coset(idxs):
                            Tidx=tuple(sorted(idxs))
                            defects.append((Tidx, beta_char0_abs(Tidx), is_antipodal(Tidx)))
                            if (max_report is not None) and (len(defects)>=max_report) and not collect_all:
                                return n_lac, defects
    return n_lac, defects

def verify_lacunary(Tidx, elts, p):
    """Double-check e_1..e_4 = 0 mod p directly (Newton edge-case guard)."""
    es=elem_sym_from_idx(Tidx, elts, p, J)
    return all(v==0 for v in es), es

if __name__=="__main__":
    mode = sys.argv[1] if len(sys.argv)>1 else "small"
    print(f"### n={N} m0={M0} j={J} DEFECT HUNT (meet-in-the-middle, EXHAUSTIVE over all C(32,8)=10.5M subsets) ###", flush=True)

    # confirm the 4 mu_8 cosets are clean lacunary at a sample prime (sanity)
    psanity = primes_mod(N, 1, idx_min=2, pmin=N)[0]
    es_elts = subgroup(N, psanity)
    print(f"[sanity] p={psanity}: 4 mu_8-cosets e_1..e_4:", flush=True)
    for c in coset_index_sets():
        es = elem_sym_from_idx(c, es_elts, psanity, J)
        print(f"    coset {tuple(sorted(c))[:4]}... e_1..e_4={es}", flush=True)

    if mode == "small":
        primes = primes_mod(N, 30, idx_min=2, pmin=N)
        label = "SMALL-INDEX primes (m>=2)"
    elif mode == "prize":
        primes = [find_prize_prime(N, b) for b in (4.0, 4.1, 4.25, 4.4, 4.5, 4.75)]
        primes = list(dict.fromkeys(primes))
        label = "PRIZE-SHAPED primes (p ~ 32^4)"
    elif mode == "wide":
        primes = primes_mod(N, 80, idx_min=2, pmin=N)
        label = "WIDE small-index sweep (80 primes)"
    elif mode == "scales":
        # sweep primes near a geometric ladder of scales 2^k, k = 14..52, incl the
        # predicted onset ~ (2j)^{n/2} = 8^16 ~ 2^48.  ~5 primes per scale.
        primes=[]
        for k in range(14, 53, 2):
            primes += primes_mod(N, 4, idx_min=2, pmin=2**k)
        primes = sorted(dict.fromkeys(primes))
        label = "GEOMETRIC SCALE LADDER 2^14..2^52 (incl onset 2^48)"
    elif mode == "onset":
        # dense sweep right around the predicted onset 2^48 and well beyond, to 2^52
        primes = primes_mod(N, 200, idx_min=2, pmin=2**47)
        label = "DENSE sweep around/above predicted onset 2^48 (200 primes)"
    else:
        primes = primes_mod(N, int(mode), idx_min=2, pmin=N)
        label = f"{mode} small-index primes"

    print(f"\n### {label}: {len(primes)} primes ###", flush=True)
    first_defect=None
    n_primes_clean=0
    for p in primes:
        elts=subgroup(N,p)
        n_lac, defects = mitm_search(p, elts, max_report=6)
        idx=(p-1)//N
        if defects:
            # verify the first defect's lacunarity directly
            ok, es = verify_lacunary(defects[0][0], elts, p)
            tag = "VERIFIED" if ok else f"NEWTON-FALSE(es={es})"
            print(f"   p={p:>9} idx={idx:>4} log2={math.log2(p):5.1f}: #lacunary={n_lac:>4} "
                  f"DEFECTS>=1 (showing {len(defects)}) [{tag}]", flush=True)
            for Tidx, babs, antip in defects[:6]:
                print(f"       T idx={list(Tidx)}  |beta_char0|={babs:.4f}  antipodal={antip}", flush=True)
            if first_defect is None and ok:
                first_defect=(p, defects[0])
        else:
            n_primes_clean+=1
            print(f"   p={p:>9} idx={idx:>4} log2={math.log2(p):5.1f}: #lacunary={n_lac:>4} "
                  f"NO non-coset defect", flush=True)

    print("\n" + "="*90, flush=True)
    if first_defect is not None:
        p, (Tidx, babs, antip) = first_defect
        print(f"FIRST/SMALLEST DEFECT: p={p}  T(idx)={list(Tidx)}  |beta_char0|={babs:.4f}  antipodal={antip}", flush=True)
    else:
        print(f"NO non-coset defect found at any of the {len(primes)} primes tested "
              f"({n_primes_clean} clean). EXHAUSTIVE over all C(32,8) subsets per prime.", flush=True)
