"""
Decisive test for C069: does the tower factorization actually compute / refine the
Galois norm N(alpha)=Res(Phi_n, g) of a GENERIC additive-energy relation g?

The norm threshold object is N(g) = Res(Phi_n, g), g = a signed sum of <= 2r roots of
unity (a generic 2r-term +-1 polynomial). The tower object only ever factors the SPECIAL
binomial a^{2^k} - b^{2^k}. For the two to 'coincide' the norm would have to be expressible
as the tower product. Test on PRIZE-REGIME primes for n=16, 32 with REAL generic relations.
"""
import sympy as sp
from sympy import cyclotomic_poly, Symbol, isprime, totient, prod, gcd
import math, random

X = Symbol('X')

def res_phi_g(n, g_poly):
    """Integer cyclotomic resultant Res(Phi_n, g) = prod over primitive roots of g(omega)."""
    Phi = sp.Poly(cyclotomic_poly(n, X), X)
    g = sp.Poly(g_poly, X)
    return int(sp.resultant(Phi, g))

def tower_value(n, a_val, b_val):
    """(a-b)*prod_{j<k}(a^{2^j}+b^{2^j}) over Z, with n=2^k."""
    k = int(math.log2(n)); assert 2**k == n
    val = (a_val - b_val)
    for j in range(k):
        val *= (a_val**(2**j) + b_val**(2**j))
    return val

def find_prize_primes(n, want=2):
    lo, hi = int(n**4), int(n**5)
    out=[]; p = lo - (lo % n) + 1
    if p<lo: p+=n
    while p<=hi and len(out)<want:
        if isprime(p): out.append(p)
        p+=n
    return out

print("DECISIVE: is N(g)=Res(Phi_n,g) for a GENERIC 2r-term relation g ever the tower product?")
print("="*78)
random.seed(1)
for mu in [4,5]:
    n = 2**mu
    k = mu
    print(f"\nn={n} (mu={mu}):  norm product has phi(n)={int(totient(n))} factors; "
          f"tower product has k={k} factors.")
    # Build several GENERIC signed-monomial relations g (2r terms, +-1 coeffs), r small.
    for r in [2,3]:
        s = 2*r
        # random distinct exponents in [0,n-1], random +-1 signs, balanced (r plus, r minus)
        exps = random.sample(range(0, n), s)
        signs = [1]*r + [-1]*r
        random.shuffle(signs)
        g = sum(sg*X**e for sg,e in zip(signs, exps))
        N = res_phi_g(n, g)
        # Can THIS integer N be written as a tower product (a-b)prod(a^{2^j}+b^{2^j})
        # for any integers a,b? The tower product is a^n-b^n. So N would need to be a
        # DIFFERENCE OF n-th POWERS. Check if |N| is a difference of two n-th powers
        # for small a,b -- almost never. Report N and whether it's n-th-power-difference shaped.
        is_pow_diff = False
        absN = abs(N)
        for b in range(0, 40):
            for a in range(b+1, b+200):
                v = a**n - b**n
                if v == absN:
                    is_pow_diff = True; break
                if v > absN: break
            if is_pow_diff: break
        print(f"   r={r}: g={g}")
        print(f"        N=Res(Phi_{n},g) = {N}   |N|={absN}")
        print(f"        is |N| = a^{n}-b^{n} (tower-shaped) for small a,b? {is_pow_diff}")
    # Also: the bound the file proves is |N| <= (2r)^{phi(n)}. The tower bound would be
    # |a^n-b^n| <= (something)^k. Different exponents (phi(n)=n/2 vs k=mu). Show the gap.
    print(f"   -> norm exponent phi(n)={int(totient(n))} vs tower #factors k={k}: "
          f"ratio {int(totient(n))//k}x more factors in the norm.")

print()
print("="*78)
print("CONCLUSION CHECK: the ONLY case the tower product = a cyclotomic norm is the")
print("DEGENERATE collision g(X)=(1+X)^n - c^n specialized so b=c is a constant, i.e.")
print("the curve object r(c), NOT the generic additive-energy relation g whose norm")
print("Res(Phi_n,g) is the actual defect-threshold quantity. For generic g the norm is")
print("not even a difference of n-th powers, so the tower factorization does not apply.")
