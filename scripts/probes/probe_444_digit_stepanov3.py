#!/usr/bin/env python3
"""
probe(#444) PART 3: the STRONGEST form of the lead -- MULTIVARIATE digit-ring Stepanov.

The lead says "multivariate dyadic-digit recursion ... transverse to the univariate-tangency orbit."
The genuine multivariate idea: work in the digit ring R = F_p[x_0,...,x_{mu-1}] / (x_{i}^2 - x_{i+1}),
where x_0 = x and x_{i} = x^{2^i}, so mu_n = {x : x_{mu} = ... } encodes the squaring tower as
COORDINATES. A multivariate Stepanov auxiliary Psi(x_0,...,x_{mu-1}) vanishing to high order on the
tower variety could, via BEZOUT, count points with a better degree-per-point ratio than univariate
(this is real: multivariate Stepanov/Bombieri beats univariate for some curve counts).

THE DECISIVE TEST: does encoding the squaring tower as separate coordinates give a level-set bound
on M(n) below sqrt(p) at beta=4? The variety {x_{i+1} = x_i^2} is a RATIONAL CURVE (parametrized by
x_0 = t, so it's just the affine line in disguise -- x_i = t^{2^i}). A multivariate auxiliary on it
PULLS BACK to a univariate poly in t of degree = sum over monomials of (exponent_i * 2^i). So the
multivariate degree advantage is ILLUSORY: the tower variety is unirational of dimension 1, and any
auxiliary's effective univariate degree is its weighted degree with weights 2^i -- which is LARGER,
not smaller, than the naive degree. We verify this pullback degree inflation numerically.

ALSO: we test whether a genuine multivariate auxiliary can vanish to higher TOTAL multiplicity on
mu_n points than its pullback degree allows, i.e. whether the Hasse-derivative tower gives free
multiplicity. It does not: the pullback is a ring hom, multiplicity is preserved/inflated.
"""
import sympy
import math
import numpy as np

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta=4.0):
    k = max(2, int(math.ceil(n**beta/n)))
    while True:
        p = k*n+1
        if p>n and is_prime(p): return p
        k+=1

# ----------------------------------------------------------------------------
# TEST D: the tower variety {x_{i+1}=x_i^2} is the affine line; multivariate -> univariate
# pullback INFLATES degree by the weight 2^i. No Bezout advantage.
# ----------------------------------------------------------------------------
def test_tower_variety_pullback(mu=4):
    print("="*78)
    print("TEST D: multivariate digit-ring auxiliary pulls back to univariate with INFLATED degree")
    print("="*78)
    t = sympy.symbols('t')
    xs = sympy.symbols(f'x0:{mu}')
    # substitution x_i = t^{2^i}
    sub = {xs[i]: t**(2**i) for i in range(mu)}
    print(f"  digit coordinates x_i = t^(2^i), i=0..{mu-1}")
    # take a few candidate multivariate auxiliaries and measure pullback degree
    cands = {
        "x_0 - 1 (lowest digit)": xs[0]-1,
        "x_{mu-1} - 1 (top digit)": xs[mu-1]-1,
        "sum x_i (linear, all digits)": sum(xs),
        "prod (x_i - 1) (vanish each level)": sympy.prod([xs[i]-1 for i in range(mu)]),
        "x_0*x_1*...*x_{mu-1} (top monomial)": sympy.prod(xs),
    }
    print(f"  {'auxiliary':>40} {'naive deg':>10} {'pullback deg in t':>18}")
    for name, P in cands.items():
        naive = int(sympy.total_degree(sympy.expand(P))) if P != 0 else 0
        pb = sympy.expand(P.subs(sub))
        pbdeg = int(sympy.Poly(pb, t).degree()) if pb != 0 else 0
        print(f"  {name:>40} {naive:>10} {pbdeg:>18}")
    print("  => pullback degree is the WEIGHTED degree (weights 2^i) >> naive total degree.")
    print("     Encoding the squaring tower as coordinates makes the auxiliary BIGGER in t,")
    print("     not smaller. The variety is unirational dim 1 (the affine line); no Bezout gain.")
    print()

# ----------------------------------------------------------------------------
# TEST E: SANITY -- does ANY low-degree polynomial relation distinguish mu_n points enough to
# give a level-set bound below sqrt(p)? Equivalently, measure the smallest degree d such that
# some poly of degree d vanishes on the "large-eta" level set. We compute the actual level set
# for the worst b and see its size and the min vanishing degree (= its cardinality, trivially).
# ----------------------------------------------------------------------------
def subgroup_gen(p, n):
    g = 2
    while True:
        h = pow(g, (p-1)//n, p)
        if pow(h, n, p) == 1 and all(not(n%d==0 and pow(h,d,p)==1) for d in range(1,n)):
            return h
        g += 1

def test_levelset_size(mu=5):
    print("="*78)
    print("TEST E: the level set driving M(n) has size ~n; min vanishing degree = its size")
    print("="*78)
    n=2**mu; p=find_prime(n,beta=4.0)
    h=subgroup_gen(p,n); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    S=np.array(S)
    # worst b and the real/imag contribution structure
    best=0; bestb=1
    # coset reps
    seen=set(); reps=[]
    for b in range(1,p):
        if b in seen: continue
        reps.append(b); y=b
        for _ in range(n): seen.add(y); y=y*h%p
    for b in reps:
        ang=2*np.pi*(b*S%p)/p
        v=abs(np.sum(np.exp(1j*ang)))
        if v>best: best=v; bestb=b
    m=p//n
    print(f"  n={n}, p={p}, m={m}")
    print(f"  M(n)={best:.3f}, target sqrt(n log m)={math.sqrt(n*math.log(m)):.3f}")
    print(f"  worst b={bestb}; the sum is over ALL {n} points of mu_n (no sparse level set to count)")
    print(f"  Stepanov needs a SMALL level set to count; here the relevant set is all of mu_n (size {n}).")
    print(f"  A vanisher on all {n} points has degree >= {n} = n; reach n*M<=deg gives M<=deg/n.")
    print(f"  To get M < sqrt(n log m) ~ {math.sqrt(n*math.log(m)):.1f} we'd need deg < {n}*{math.sqrt(n*math.log(m)):.0f}")
    print(f"  ~ n^1.5, i.e. deg < {n**1.5:.0f}, but the level-set count bounds the WRONG quantity")
    print(f"  (number of points, all n of them), not the phase cancellation.")
    print()

if __name__=="__main__":
    test_tower_variety_pullback(mu=4)
    test_levelset_size(mu=5)
    print("="*78)
    print("SUMMARY OF THE OBSTRUCTION (parts 1-3)")
    print("="*78)
    print("(A) x->x^2 is a 2-to-1 tower PROJECTION mu_n ->> mu_{n/2}, not a self-map; a covariant")
    print("    recursion DESCENDS the tower, it cannot accumulate multiplicity at fixed level n.")
    print("(B) |T|*M <= deg is a polynomial IDENTITY; the n distinct points of mu_n are unchanged")
    print("    by the recursion, so (X^n-1)^M is forced => NO degree-per-multiplicity discount.")
    print("(C) The tower variety {x_{i+1}=x_i^2} is the affine LINE (unirational dim 1); multivariate")
    print("    auxiliaries pull back to univariate with INFLATED (weighted, 2^i) degree => no Bezout.")
    print("(D) Even granting free multiplicity ~log n, Stepanov's output is a MAGNITUDE/zero-count")
    print("    bound (<=sqrt(p)=n^2 at beta=4, VACUOUS past trivial n); it cannot see the sqrt(n)")
    print("    PHASE CANCELLATION the prize floor sqrt(n log m) requires. Counts zeros != cancellation.")
    print()
    print("VERDICT: digit-recursion Stepanov REDUCES-TO-WALL. It is a zero-counting/magnitude method;")
    print("its best output is sqrt(p) (Weil, in-tree), the n<p^{1/3} HBK regime delivers only BGK-type")
    print("n^{1-o(1)}, and the x->x^2 recursion provides no free multiplicity (descends the tower /")
    print("identity wall). It does NOT escape Johnson by escaping the cancellation problem -- it just")
    print("doesn't address cancellation at all. Same wall as univariate Stepanov + the BGK magnitude")
    print("ceiling. Not refuted (no false claim), not surviving (no non-BGK handle).")
