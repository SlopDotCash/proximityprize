"""
probe_444_OP1_persistence.py  (#444 -- DECISIVE: does O_P=1 persist past n=16? char-0 vs char-p)

Apples-to-apples: the binding J=1 descent (single condition e_2=0, the 'trinomial' case).
 - n=16 binding  <->  4-subsets of mu_8  with e_2=0,  gamma=-e_1.   (PROVEN char-0, O_P=1)
 - n=32 binding  <->  8-subsets of mu_16 with e_2=0,  gamma=-e_1.   (this probe)
 - n=64 binding  <->  16-subsets of mu_32 with e_2=0.               (if feasible)

For each level we compute BOTH:
 (A) the CHAR-0 condition e_2=0  ==  pairwise-sum cyclotomic balance M_r = M_{r+N/2}
     (since zeta_N^{N/2} = -1 and {1,zeta,...,zeta^{phi(N)-1}} is a Q-basis); p-INDEPENDENT.
 (B) the CHAR-p condition e_2 == 0 mod p, at several primes p == 1 mod N.

Then O_P = #dilation(shift-by-1)-orbits of the NONZERO-e_1 subsets, computed in char-0.

DECIDES:
 * is O_P=1 a char-0 fact at each n, or does it fail in char-0 already?
 * does char-p add a defect (count_p > count_0) -> the additive-energy wall, and from which n?
This settles whether a clean 'p-independent proxy face with O_P=1' exists for n>=32.
"""
import itertools
from collections import Counter

def char0_e2_zero(J, N):
    """M_r = M_{r+N/2} over pairwise sums mod N (cyclotomic vanishing of e_2)."""
    h = N // 2
    M = [0]*N
    for i, j in itertools.combinations(J, 2):
        M[(i+j) % N] += 1
    return all(M[r] == M[(r+h) % N] for r in range(h))

def char0_e1_zero(J, N):
    """e_1 = 0 in char 0: J closed under x -> x + N/2 (antipodal pairs cancel)."""
    h = N // 2
    Js = set(J)
    return all(((j+h) % N) in Js for j in J)

def mu_zeta(p, N):
    def order(x):
        o, cur = 1, x
        while cur != 1: cur = cur*x % p; o += 1
        return o
    g = 2
    while order(g) != p-1: g += 1
    return pow(g, (p-1)//N, p)

def charp_e2_zero(J, zeta, p, N):
    e2 = 0
    for i, j in itertools.combinations(J, 2):
        e2 = (e2 + pow(zeta, (i+j) % N, p)) % p
    return e2 % p == 0

def OP_char0(N, size):
    """O_P over char-0 e_2=0 subsets: #shift-orbits of the nonzero-e_1 ones."""
    subs = [J for J in itertools.combinations(range(N), size) if char0_e2_zero(J, N)]
    nz = [J for J in subs if not char0_e1_zero(J, N)]
    z  = [J for J in subs if char0_e1_zero(J, N)]
    # shift-orbit count of nz under J -> J+1 (mod N), comparing the SUM value not the set
    # (different sets can share e_1; O_P counts distinct gamma=-e_1 orbits). Represent e_1 by
    # its char-0 coordinate vector in basis 1..zeta^{phi-1}, with zeta^{N/2}=-1.
    phi = N//2
    def e1vec(J):
        m=[0]*N
        for j in J: m[j%N]+=1
        return tuple(m[r]-m[r+phi] for r in range(phi))
    def mulzeta(v):
        # multiply by zeta: shift coords up, with zeta^{phi} = -1 (since zeta^{N/2}=-1, phi=N/2)
        return tuple([-v[phi-1]] + list(v[:phi-1]))
    vecs = set(e1vec(J) for J in nz)
    rem=set(vecs); orbs=0
    while rem:
        v=next(iter(rem)); o=set(); cur=v
        for _ in range(N):
            o.add(cur); cur=mulzeta(cur)
        orbs+=1; rem-=o
    return len(subs), len(z), len(nz), len(vecs), orbs

def charp_counts(N, size, primes):
    out={}
    for p in primes:
        z=mu_zeta(p,N)
        cnt=sum(1 for J in itertools.combinations(range(N),size) if charp_e2_zero(J,z,p,N))
        out[p]=cnt
    return out

print("=== O_P=1 persistence: the J=1 (e_2=0) binding descent across n ===\n")

for (n, N, size, primes) in [
        (16, 8, 4,  [17,41,73,97,65537]),
        (32, 16, 8, [97,193,257,65537]),
    ]:
    tot,z,nz,vecs,orbs = OP_char0(N, size)
    print(f"n={n}  (mu_{N}, {size}-subsets, e_2=0):")
    print(f"  CHAR-0: total e_2=0 subsets={tot}  (e_1=0:{z}, e_1!=0:{nz})  distinct e_1 vecs={vecs}  O_P(char0)={orbs}")
    cp = charp_counts(N, size, primes)
    print(f"  CHAR-p e_2=0 counts: {cp}")
    print(f"  defect (char-p - char-0) per prime: { {p: cp[p]-tot for p in cp} }")
    print(f"  => O_P=1 in char-0? {'YES' if orbs==1 else 'NO (O_P='+str(orbs)+')'};"
          f"  char-p defect present? {'YES' if any(cp[p]!=tot for p in cp) else 'NO'}\n")
