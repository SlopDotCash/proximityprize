"""
probe_444_unifyA_depth_and_normsupport.py  (#444 Unify-A, part 2)

Part-1 found NESTING not equality:  at n=16,
   SUPPLY(Spur_2>0) = {17,97,113,193,257,337}  is a SUBSET of
   DEMAND(e2=0 RISE,any w) = {17,97,113,193,241,257,337,353,433,593}.

Hypothesis: BOTH defects are the SAME underlying object = "a short signed sum of 2^mu-th roots
vanishes mod p but not in Z[zeta]" = p | N(alpha) for some sparse alpha in Z[zeta_n].  They differ
only in WHICH alpha's appear (which short relations the object reaches), governed by DEPTH:
  - SUPPLY Spur_r: alpha = (z_1+...+z_r) - (z'_1+...+z'_r), a +-1 combination of <= 2r roots.
  - DEMAND e2=0 on size-w S: alpha = e_2(S) = sum_{i<j} z_i z_j, a sum of C(w,2) roots (all +1).

This probe: (A) characterize each defect's bad-prime set as a UNION of norm-divisor sets
  {p : p | N(alpha)} over the relevant sparse alpha, and test set-equality of the supports;
  (B) DEPTH match: does SUPPLY Spur_r bad set == DEMAND e2=0 bad set when the # of roots in the
  relation is matched (2r roots for supply vs the carrier alpha for demand)?
  (C) the cleanest test: is EVERY supply-bad prime a divisor of some sparse 2^mu-root +-1 relation
  norm, and vice versa -> SAME generating object (consolidation).
"""
import itertools
from collections import Counter
import sympy

def primes_1_mod_n(n, lo, hi):
    return [p for p in range(max(lo, n+1), hi) if p % n == 1 and sympy.isprime(p)]

def subgroup(n, p):
    g = int(sympy.primitive_root(p)); h = pow(g, (p-1)//n, p)
    H = []; x = 1
    for _ in range(n):
        H.append(x); x = x*h % p
    return H

def char0_vec(coeffs_by_exp, n):
    """reduce a Z-combination of zeta^e (dict exp->coeff) to Q-vector over 1..zeta^{n/2-1}."""
    half = n // 2
    v = [0]*half
    for e, c in coeffs_by_exp.items():
        e %= n
        if e < half: v[e] += c
        else:        v[e-half] -= c
    return tuple(v)

def dfac(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

# ---------- SUPPLY ----------
def E_r_char0_brute(n, r):
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        cnt[char0_vec(Counter(x), n)] += 1
    return sum(c*c for c in cnt.values())

def E_r_modp(n, p, r, H):
    cnt = Counter()
    for x in itertools.product(H, repeat=r):
        cnt[sum(x) % p] += 1
    return sum(c*c for c in cnt.values())

def supply_bad(n, r, primes):
    Ec = E_r_char0_brute(n, r)
    bad = set()
    for p in primes:
        H = subgroup(n, p)
        if E_r_modp(n, p, r, H) - Ec > 0:
            bad.add(p)
    return bad, Ec

# ---------- DEMAND (e2=0 RISE carriers) ----------
def e2_char0_zero(S, n):
    half = n // 2
    v = [0]*half
    for i, j in itertools.combinations(S, 2):
        a = (i+j) % n
        if a < half: v[a] += 1
        else:        v[a-half] -= 1
    return all(c == 0 for c in v)

def e2_modp(S, p, H):
    s = 0
    for i, j in itertools.combinations(S, 2):
        s = (s + H[i]*H[j]) % p
    return s % p

def demand_bad(n, w, primes):
    """primes p with a RISE carrier: e2(S)!=0 char-0 but =0 mod p for some size-w S."""
    bad = set()
    Scand = [S for S in itertools.combinations(range(n), w) if not e2_char0_zero(S, n)]
    for p in primes:
        H = subgroup(n, p)
        for S in Scand:
            if e2_modp(S, p, H) == 0:
                bad.add(p); break
    return bad

# ---------- NORM-SUPPORT generator: sparse +-1 root relations ----------
def norm_of_alpha(coeffs_by_exp, n):
    """N(alpha) = Res(Phi_n, alpha) = prod over primitive n-th roots of alpha(zeta).
       Use the integer resultant of the min-poly-free product via cyclotomic field norm.
       alpha = sum c_e X^e mod (X^n-1); norm over Q(zeta_n) = prod_{j in (Z/n)^*} alpha(zeta^j)."""
    # Build alpha(X) as a sympy poly, take resultant with cyclotomic Phi_n.
    X = sympy.symbols('X')
    poly = sum(c * X**(e % n) for e, c in coeffs_by_exp.items())
    Phi = sympy.cyclotomic_poly(n, X)
    res = sympy.resultant(sympy.Poly(poly, X), sympy.Poly(Phi, X))
    return abs(int(res))

def short_relation_norm_primes(n, max_terms, primes):
    """
    Generate the bad-prime support from ALL sparse +-1 relations of 2^mu-th roots with <= max_terms
    nonzero +-1 coefficients, alpha = sum_{e in subset} (+-1) zeta^e, alpha != 0 in Z[zeta].
    Return {p in primes : p | N(alpha) for some such alpha}.
    This is the GENERATING OBJECT both defects are conjectured to reduce to.
    """
    primeset = set(primes)
    bad = set()
    rels = []
    half = n // 2
    # +1-only sums of up to max_terms distinct roots (the e2-style carriers are +1 sums);
    # also include the +-1 signed sums (the supply alpha = sum z_i - sum z'_j).
    for t in range(2, max_terms+1):
        for exps in itertools.combinations(range(n), t):
            # all sign patterns, dedup by leading +; skip char-0-zero alpha
            for signs in itertools.product((1, -1), repeat=t):
                if signs[0] != 1:
                    continue
                cby = {e: s for e, s in zip(exps, signs)}
                if all(c == 0 for c in char0_vec(cby, n)):
                    continue  # char-0 zero alpha = not a defect carrier
                rels.append(cby)
    # dedup norms by computing once per alpha
    for cby in rels:
        N = norm_of_alpha(cby, n)
        for p in primes:
            if p in bad:
                continue
            if N % p == 0:
                bad.add(p)
        if bad == primeset:
            break
    return bad

def main():
    print("="*78)
    print("Unify-A part 2: are SUPPLY Spur_r and DEMAND e2=0 the SAME norm-divisor support?")
    print("="*78)

    for n in (8, 16):
        primes = primes_1_mod_n(n, 0, 700)[:12]
        print(f"\n########## n={n}   primes(<=700, =1 mod n): {primes}")

        # SUPPLY at r=2 (4 roots) and r=3 (6 roots)
        sb2, Ec2 = supply_bad(n, 2, primes)
        sb3, Ec3 = supply_bad(n, 3, primes) if n**3 <= 300000 else (set(), None)
        print(f"  SUPPLY Spur_2>0 (alpha = +-1 sum of <=4 roots): {sorted(sb2)}")
        print(f"  SUPPLY Spur_3>0 (alpha = +-1 sum of <=6 roots): {sorted(sb3)}")

        # DEMAND e2=0 at w=4 (carrier e2 = sum of 6 products) and w=6
        db4 = demand_bad(n, 4, primes)
        db6 = demand_bad(n, 6, primes) if n >= 6 else set()
        print(f"  DEMAND e2=0 RISE w=4: {sorted(db4)}")
        print(f"  DEMAND e2=0 RISE w=6: {sorted(db6)}")

        # NORM-SUPPORT generating object: sparse +-1 root relations up to k terms
        for k in (4, 6):
            ns = short_relation_norm_primes(n, k, primes)
            print(f"  GEN norm-support (<= {k}-term +-1 root relations p|N(alpha)): {sorted(ns)}")

    print("\n" + "="*78)
    print("INTERPRETATION: if SUPPLY Spur_r, DEMAND e2=0, and GEN norm-support all share the same")
    print("bad-prime support (as a function of depth/#terms), the two defects are ONE object")
    print("(short +-1 2^mu-root relations vanishing mod p) = consolidation. Differences in the SET")
    print("of primes = different REACH (which alpha appear), not a different object.")
    print("="*78)

if __name__ == "__main__":
    main()
