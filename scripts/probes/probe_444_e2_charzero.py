"""
probe_444_e2_charzero.py  (#444 -- is the O_P=1 e_2=0 condition CHAR-0 / provable?)

The binding O_P=1 at n=16 reduces to: 4-subsets J of mu_8 (exponent set in Z/8) with e_2=0,
counted by gamma=-e_1, form ONE dilation orbit (J -> J+1).

KEY question: is 'e_2=0' the CHAR-0 cyclotomic condition, hence p-INDEPENDENT and PROVABLE?
On mu_8: zeta^4=-1, so {1,zeta,zeta^2,zeta^3} is a Q-basis and zeta^{r+4}=-zeta^r.  A sum
Sum_r m_r zeta^r = 0 over Q(zeta_8)  <=>  m_r = m_{r+4} for r=0,1,2,3 (cyclotomic vanishing).

e_2(J) = Sum_{i<j in J} zeta^{(i+j) mod 8}.  Let M_r = #{pairs i<j in J : i+j ≡ r mod 8}.
CHAR-0 condition:  M_r = M_{r+4} for r=0,1,2,3.

Tests:
 (1) compare char-0 (M_r=M_{r+4}) vs char-p (e_2≡0 mod p) e_2=0 subsets, at several primes.
     If they AGREE for all p, the condition is char-0 => p-independent => provable.
 (2) for the char-0 e_2=0 subsets, compute the dilation-orbit count O_P of gamma=-e_1
     (also via the cyclotomic structure of e_1), confirm O_P=1.
 (3) likewise e_1=Sum zeta^j ; char-0 distinct values.  Show single shift-orbit.
"""
import itertools
from collections import Counter

def char0_e2_zero(J):
    """M_r = M_{r+4} for r=0..3 over pairwise sums mod 8."""
    M=[0]*8
    for i,j in itertools.combinations(J,2):
        M[(i+j)%8]+=1
    return all(M[r]==M[r+4] for r in range(4))

def charp_e2_zero(J, zeta, p):
    e2=0
    for i,j in itertools.combinations(J,2):
        e2=(e2+pow(zeta,(i+j)%8,p))%p
    return e2%p==0

def e1_char0_vec(J):
    """e_1 = Sum zeta^j as integer vector (m_0-m_4, m_1-m_5, m_2-m_6, m_3-m_7) in basis 1,z,z^2,z^3."""
    m=[0]*8
    for j in J: m[j%8]+=1
    return tuple(m[r]-m[r+4] for r in range(4))

# primes p ≡ 1 mod 8 with mu_8
def mu8_zeta(p):
    def order(x):
        o,cur=1,x
        while cur!=1: cur=cur*x%p; o+=1
        return o
    g=2
    while order(g)!=p-1: g+=1
    return pow(g,(p-1)//8,p)

primes=[17,41,73,97,65537]
print("=== (1) char-0 vs char-p e_2=0 on 4-subsets of mu_8 ===")
char0_sets=[J for J in itertools.combinations(range(8),4) if char0_e2_zero(J)]
print(f"char-0 e_2=0 4-subsets: {len(char0_sets)}")
for p in primes:
    z=mu8_zeta(p)
    charp_sets=[J for J in itertools.combinations(range(8),4) if charp_e2_zero(J,z,p)]
    agree = set(char0_sets)==set(charp_sets)
    print(f"  p={p:6d}: char-p e_2=0 count={len(charp_sets)}  AGREES with char-0: {agree}")

print("\n=== (2) dilation-orbit count O_P of gamma=-e_1 over char-0 e_2=0 subsets ===")
# dilation J->J+1 (mod 8). Orbit of gamma=-e_1 corresponds to shift-orbit of J that may change e_1.
# Represent e_1 by its char-0 vector; gamma=-e_1; dilation multiplies gamma by zeta => shifts vector.
# Count distinct e_1 char-0 vectors up to the shift action (zeta-multiplication = exponent shift).
def shift_vec(J,t): return e1_char0_vec([ (j+t)%8 for j in J])
# distinct e_1 vectors:
e1vecs=set(e1_char0_vec(J) for J in char0_sets)
print(f"  distinct char-0 e_1 vectors among e_2=0 subsets: {len(e1vecs)}")
# orbit under zeta-multiplication: zeta*(sum) shifts exponents; on the vector (a0,a1,a2,a3) with
# basis 1,z,z^2,z^3 and z^4=-1, multiply by z: (a0,a1,a2,a3)-> (-a3,a0,a1,a2).
def mul_zeta(v): a0,a1,a2,a3=v; return (-a3,a0,a1,a2)
rem=set(e1vecs); orbs=0
while rem:
    v=next(iter(rem)); o=set(); cur=v
    for _ in range(8):
        o.add(cur); cur=mul_zeta(cur)
    orbs+=1; rem-=o
print(f"  O_P (zeta-orbits of e_1 over char-0 e_2=0 subsets) = {orbs}")

print("\n=== (3) explicit char-0 e_2=0 subsets (exponent sets) ===")
for J in char0_sets:
    M=[0]*8
    for i,j in itertools.combinations(J,2): M[(i+j)%8]+=1
    print(f"  J={J}  pairwise-sum mult M={M}  e1vec={e1_char0_vec(J)}")
