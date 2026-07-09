#!/usr/bin/env python3
"""
C008 verification: confirm the prize-form prime factor of Res(e2Fold, Phi_{2^m}) is a
GENUINE bad alpha at a proper-subgroup prize prime (mu_n a proper subgroup of F_q*).

We take a witness A at n=32 with a large odd prime factor q | Res, q = 1 mod n, q >> n,
and check DIRECTLY in F_q:
  - q is prime, q = 1 mod n  => mu_n is a PROPER subgroup of F_q* (since q-1 > n);
  - there exists a primitive 2^m-th root g in F_q;
  - e2(A, g) = sum_{i<j in A} g^{i+j} = 0 in F_q   (the bad-alpha collision).
This is the EXACT condition the Lean pair_sum_collision_dvd_resultant /
qualifying_implies_char0_vanishing pin: p | Res  <=>  e2 collision mod p.

If this holds, then the "finite divisor set" of C008 CONTAINS prize-sized
proper-subgroup primes => the per-instance criterion does NOT escape BGK; deciding
"p | Res" for a prize prime q ~ n^beta IS deciding the thin-subgroup collision = BGK.
"""
from sympy import factorint, isprime, primitive_root, nextprime
from itertools import combinations

def e2_mod(A, g, q):
    Al = sorted(A)
    s = 0
    L = len(Al)
    for a in range(L):
        for b in range(a+1, L):
            s = (s + pow(g, (Al[a]+Al[b]) % (q-1), q)) % q
    return s

def char0_vanishes(m, A):
    """e2Fold = 0 over Z[zeta]? compute folded coeffs, check all zero."""
    n = 2**m; h = 2**(m-1); coeff=[0]*h
    Al=sorted(A)
    for a in range(len(Al)):
        for b in range(a+1,len(Al)):
            e=(Al[a]+Al[b])%n
            if e<h: coeff[e]+=1
            else: coeff[e-h]-=1
    return all(c==0 for c in coeff)

def find_g(q, n):
    """A primitive 2^m-th root of unity in F_q: g = pr^((q-1)/n) for primitive root pr."""
    pr = primitive_root(q)
    g = pow(pr, (q-1)//n, q)
    # verify order exactly n
    assert pow(g, n, q) == 1
    assert pow(g, n//2, q) != 1
    return g

# Witness from the sweep: n=32, A of size 12 with prize-form factor 139292647009.
m = 5; n = 2**m
A = {1, 5, 6, 7, 8, 10, 19, 20, 23, 27, 28, 31}

from sympy import symbols, Poly, resultant
X = symbols('X')
def res_val(m, A):
    n=2**m; h=2**(m-1); coeff=[0]*h; Al=sorted(A)
    for a in range(len(Al)):
        for b in range(a+1,len(Al)):
            e=(Al[a]+Al[b])%n
            if e<h: coeff[e]+=1
            else: coeff[e-h]-=1
    p_ef=Poly(list(reversed(coeff)),X,domain='ZZ')
    cyc=[0]*(h+1); cyc[0]=1; cyc[-1]=1
    p_cy=Poly(cyc,X,domain='ZZ')
    return int(resultant(p_ef.as_expr(),p_cy.as_expr(),X))

R = res_val(m,A)
print(f"n={n}, |A|={len(A)}, A={sorted(A)}")
print(f"char-0 e2Fold vanishes? {char0_vanishes(m,A)}  (must be False for a real surplus)")
print(f"Res(e2Fold,Phi_{n}) = {R}")
fac = factorint(abs(R))
print(f"factorization = {dict(fac)}")
# pick the largest ODD prime factor that is = 1 mod n
prize_q = [p for p in fac if p%2==1 and p%n==1 and p>n]
print(f"prize-form prime factors (q=1 mod {n}, q>n): {prize_q}")

for q in sorted(prize_q):
    assert isprime(q)
    proper = (q-1) > n and (q-1) % n == 0
    g = find_g(q, n)
    val = e2_mod(A, g, q)
    print(f"\n  q = {q}  (= {float(q):.3e}, log2={__import__('math').log2(q):.1f})")
    print(f"    q prime: True; q-1 = {q-1} = {n} * {(q-1)//n}")
    print(f"    mu_{n} PROPER subgroup of F_q*? {proper}  (index = {(q-1)//n})")
    print(f"    prize-regime beta = log_n(q) = {__import__('math').log(q,n):.2f}  "
          f"(prize wants beta ~ 4-5)")
    print(f"    primitive 2^{m}-th root g = {g}")
    print(f"    e2(A,g) mod q = {val}   ==> BAD ALPHA EXISTS: {val==0}")

print("\n" + "="*70)
print("VERDICT SIGNAL:")
print("  If 'BAD ALPHA EXISTS: True' at a PROPER-subgroup prime q with beta~4-7,")
print("  then C008's finite divisor set contains prize-sized thin-subgroup")
print("  collisions => the per-instance criterion does NOT escape BGK.")
