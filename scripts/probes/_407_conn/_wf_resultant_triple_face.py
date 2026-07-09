#!/usr/bin/env python3
"""
C013 probe: ONE resultant R = Res(Phi_n, g) = N(alpha) as the "Rosetta stone".

Claim to attack: the SAME integer R has three arithmetic readings that ARE the
faces F5/F13 (char-0 energy collision = R==0), F12 (char-p anomaly = p|R but R!=0),
F11 (ideal-SVP short vector, magnitude |R| crossing p = onset of shortness).

We verify EXACTLY (integer arithmetic) at PRIZE-REGIME proper-subgroup primes:
  - dyadic n = 2^mu, n | p-1, p prime, p ~ n^beta (beta in [4,5]), n << sqrt(q),
    proper subgroup mu_n < F_p^*  (NOT the full group; the #400 trap).
For each: enumerate signed g = sum of <=2r unit-monomials, compute
  R = Res(Phi_n, g) over Z (= prod over primitive n-th roots of g(omega) = N(alpha)),
and check:
  (face A / F5) R==0  <=>  g vanishes at a primitive complex n-th root <=> char-0 collision
  (face B / F12) p | R and R != 0  <=>  g has a primitive n-th root of ZMod p as root (mod-p collision)
  (face C / F11) when p|R, R!=0: alpha=g(zeta_n) in Z[zeta_n], 𝔭|alpha is a short vector;
     compare |R|=|N(alpha)| vs (2r)^{phi(n)} (the box) and the Minkowski/SVP scale.

Then the LOAD-BEARING test: is "magnitude |R| crossing p = onset of ideal-SVP shortness"
a NEW reduction, or does it just say p <= (2r)^{phi(n)} = the already-known VACUOUS
clean-range threshold (phi(n)=n/2, p^{1/phi(n)}->1 in prize regime)?
"""
import sympy
from sympy import primerange, isprime, totient, resultant, Poly, symbols, cyclotomic_poly, gcd
import itertools, math

X = symbols('X')

def prize_primes(n, beta_lo=4.0, beta_hi=5.5, count=3):
    """Primes p == 1 mod n with p ~ n^beta, n << sqrt(p) (proper subgroup, large prime)."""
    lo = int(n**beta_lo)
    hi = int(n**beta_hi)
    out = []
    # search p == 1 mod n
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi and len(out) < count:
        if isprime(p):
            # proper-subgroup guard: n is a PROPER divisor of p-1 and n << sqrt(p)
            if (p-1) % n == 0 and n*n < p and n < p-1:
                out.append(p)
        p += n
    return out

def primitive_root_modp(p):
    return int(sympy.primitive_root(p))

def primitive_nth_root_modp(p, n):
    """A primitive n-th root of unity in Z/p (exists since n | p-1)."""
    g = primitive_root_modp(p)
    return pow(g, (p-1)//n, p)

def Res_Phi_g_int(n, gpoly):
    """Integer resultant Res(Phi_n, g) over Z; equals N(alpha), alpha=g(zeta_n)."""
    Phi = Poly(cyclotomic_poly(n, X), X)
    g = Poly(gpoly, X)
    return int(resultant(Phi.as_expr(), g.as_expr(), X))

def make_signed_g(exps, signs):
    """g = sum signs[i] * X^exps[i]."""
    e = 0
    for ex, s in zip(exps, signs):
        e += s * X**ex
    return e

def reduce_exps_mod_n(g_expr, n):
    """Reduce X exponents mod n (since on n-th roots X^n=1). Returns Poly mod (X^n-1)-equiv."""
    return g_expr  # resultant with Phi_n already enforces this; keep raw.

def char0_collision(n, gpoly):
    """R==0 <=> g vanishes at a primitive complex n-th root."""
    return Res_Phi_g_int(n, gpoly) == 0

def modp_collision(p, n, gpoly):
    """g has a primitive n-th root zeta of Z/p as a root mod p."""
    zeta = primitive_nth_root_modp(p, n)
    g = Poly(gpoly, X)
    val = g.eval(zeta) % p
    return val == 0, zeta

print("="*78)
print("C013 Rosetta-stone probe: R = Res(Phi_n, g) = N(alpha), three faces co-occur?")
print("="*78)

results = []
for mu in (3,4,5,6):        # n = 8,16,32,64
    n = 2**mu
    phin = int(totient(n))   # = n/2 for n=2^mu
    ps = prize_primes(n)
    print(f"\n### n = 2^{mu} = {n}, phi(n) = {phin}, prize primes (p~n^[4,5.5], n^2<p): {ps}")
    if not ps:
        print("   (no prize prime found in window)")
        continue
    for p in ps:
        zeta = primitive_nth_root_modp(p, n)
        # enumerate signed g: pick 2r distinct exponents in [0,n), signs +-1, look for mod-p collisions
        # to keep it exact & fast, search small r=2 (4 terms) and r=3 (6 terms) lightly
        found = 0
        examples = []
        box_2r = {}  # 2r -> (2r)^phin
        for r in (2,3):
            twoR = 2*r
            box = twoR**phin
            box_2r[twoR] = box
            # canonical balanced obstruction: x1+..+xr - y1-..-yr = 0 mod p
            # search a handful of exponent multisets
            tried = 0
            for combo in itertools.combinations(range(1, n), twoR-1):
                exps = (0,) + combo  # include exponent 0
                # balanced signs: first r are +, last r are -
                signs = [1]*r + [-1]*r
                gpoly = make_signed_g(exps, signs)
                R = Res_Phi_g_int(n, gpoly)
                c0 = (R == 0)
                # mod p
                gP = Poly(gpoly, X)
                vp = int(gP.eval(zeta) % p)
                cp = (vp == 0)
                if cp and not c0:
                    # F12 anomaly + F11 short vector: p | R, R != 0
                    assert R % p == 0, (R, p)
                    found += 1
                    if len(examples) < 3:
                        examples.append((exps, R, abs(R), box))
                tried += 1
                if tried >= 4000: break
            # report
        print(f"  p={p:>10}  zeta(prim {n}-th)={zeta}")
        print(f"     box (2r)^phi(n): " + ", ".join(f"2r={k}:{v}" for k,v in box_2r.items()))
        print(f"     p^(1/phi(n)) (clean-range ceiling on 2r) = {p**(1.0/phin):.4f}  "
              f"(VACUOUS if < smallest 2r=4)")
        print(f"     #anomaly collisions found (p|R, R!=0): {found}")
        for (exps,R,absR,box) in examples:
            ratio = absR/p
            print(f"       g exps={exps}: R={R}, |R|/p={ratio:.3f}, |R|<=box? {absR<=box}")
        results.append((n,p,phin,found, p**(1.0/phin)))

print("\n" + "="*78)
print("LOAD-BEARING VERDICT TEST: does the magnitude reading give a NEW bound,")
print("or is 'crossing p' identical to the VACUOUS clean-range p <= (2r)^{phi(n)}?")
print("="*78)
for (n,p,phin,found,ceil2r) in results:
    print(f"n={n} p={p}: clean-range allows 2r < p^(1/phi(n)) = {ceil2r:.4f}; "
          f"smallest meaningful 2r=4 => threshold {'VACUOUS' if ceil2r<4 else 'active'}; "
          f"anomalies present: {found>0}")
