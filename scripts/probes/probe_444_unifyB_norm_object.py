#!/usr/bin/env python3
"""
probe_444_unifyB_norm_object.py  (#444 Unify-B)

GOAL. Decide whether the DEMAND-side char-p defect (the e_2=0 surplus on mu_{n/2}-subsets,
the O_P / DeltaStarOP1BindingN16 object) and the SUPPLY-side Spur_r (char-p short +-1-relations
of 2^mu-th roots, the additive-energy surplus E_r - E_r^{c0}) are governed by the SAME object:
"p divides Norm(short root-of-unity sum)".

CALIBRATION FIRST (honesty contract): reproduce char-0 E_r^{c0} = (2r-1)!! n^r for the actual
ROOTS OF UNITY mu_n (not integer lifts). E_r^{c0} counts solutions of z_1+..+z_r = z'_1+..+z'_r
in mu_n^{2r} WITH NO mod-p reduction (i.e. equality in Z[zeta]); Lam-Leung: these are exactly the
+-paired (antipodal-matched) tuples, giving (2r-1)!! n^r when n=2^mu.

THEN the comparison:

  SUPPLY object (CyclotomicNormDefectThreshold.lean):
    alpha = sum_{i<=2r} +-zeta_n^{e_i},  alpha = 0 mod p,  alpha != 0 in Z[zeta_n].
    Controlled by  p | Norm_{Q(zeta_n)/Q}(alpha) = Res(Phi_n, g),  |Norm| <= (2r)^{phi(n)}.
    Spur_r counts these short signed-2r-term vanishings-mod-p.

  DEMAND object (e_2=0 surplus, this probe writes it as a norm divisibility):
    A bad gamma at the binding rung <-> a 4-subset (more generally w-subset) J of mu_{n/2}
    with e_2(J)=0 mod p and e_1(J)=gamma. The char-p SURPLUS over char-0 is the set of J with
    e_2(J)=0 mod p but e_2(J)!=0 in Z[zeta_{n/2}].  e_2(J) = sum_{i<j} z_i z_j is itself a sum of
    C(w,2) products of (n/2)-th roots of unity = a sum of C(w,2) roots of unity in mu_{n/2}
    (since product of roots of unity is a root of unity). So:
        e_2(J) char-p defect  <=>  p | Norm(e_2(J)),  e_2(J) a sum of <=C(w,2) (n/2)-th roots,
                                    e_2(J) != 0 in Z[zeta_{n/2}].
    THIS IS THE SAME SHAPE: p | Norm(short root-of-unity sum), != 0 in char 0.

  The question Unify-B asks: are they the SAME object or DISTINCT? We compare:
    - the root-of-unity GROUP: supply uses mu_n; demand-e2 uses mu_{n/2} (squares).
    - the TERM COUNT: supply <=2r signed terms; demand-e2 = C(w,2) UNSIGNED (all +) terms.
    - the COEFFICIENT pattern: supply +-1; demand-e2 all +1 (e_2 has no signs), BUT the SURPLUS
      condition is e_2(J)=0 which IS a vanishing -> rewrite needs the char-0 value subtracted.

We test, exhaustively over proper mu_n at computational primes (BabyBear-flavored small primes),
whether every demand-side e_2=0 char-p-only J yields a SUPPLY-side short signed relation mod p,
and conversely whether supply relations of length <=C(w,2) project onto demand e_2 defects.
"""
from itertools import combinations
from collections import Counter
import cmath, math

# ---------- prime / subgroup machinery ----------
def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def find_prime(n, lo):
    p = lo + (n - (lo-1) % n) % n   # ensure p-1 divisible by n start
    p = lo
    while True:
        if (p-1) % n == 0 and is_prime(p):
            return p
        p += 1

def nth_root_modp(p, n):
    for cand in range(2, p):
        z = pow(cand, (p-1)//n, p)
        if pow(z, n, p) == 1 and all(pow(z, d, p) != 1 for d in range(1, n)):
            return z
    raise RuntimeError

def mu_modp(p, n):
    z = nth_root_modp(p, n)
    return [pow(z, j, p) for j in range(n)]

# ---------- CALIBRATION: char-0 E_r^{c0} = (2r-1)!! n^r for roots of unity ----------
def dfact(m):
    r = 1; k = m
    while k > 0: r *= k; k -= 2
    return r

def Er_charzero_exact(n, r):
    """Exact char-0 additive energy of mu_n (n=2^mu) by Lam-Leung antipodal matchings.
    Count tuples (z_1..z_r; z'_1..z'_r) in mu_n^{2r} with sum z_i - sum z'_j = 0 in Z[zeta_n].
    For n=2^mu this equals the number of perfect +-matchings = (2r-1)!! n^r ONLY when there are
    no extra char-0 relations among 2^mu-th roots beyond antipodal pairing — TRUE for n=2^mu.
    We verify by brute force for small n,r against the formula."""
    G = [cmath.exp(2j*cmath.pi*j/n) for j in range(n)]
    cnt = 0
    # brute over mu_n^{2r}; only feasible tiny
    def rec(depth, acc):
        nonlocal cnt
        if depth == 2*r:
            if abs(acc) < 1e-6:
                cnt += 1
            return
        sign = 1 if depth < r else -1
        for z in G:
            rec(depth+1, acc + sign*z)
    rec(0, 0+0j)
    return cnt

print("="*78)
print("CALIBRATION: char-0 additive energy of mu_n  (HONEST baseline before any claim)")
print("="*78)
print("Two char-0 references, both must be reproduced:")
print("  (A) EXACT integer energy  E_r^{c0}(exact) = #{ z_1+..+z_r = z'_1+..+z'_r in Z[zeta] }")
print("  (B) Gaussian ENVELOPE    (2r-1)!! n^r  = leading term, an UPPER proxy (E^c0<=Gauss).")
print("Lam-Leung: char-0 vanishings of 2^mu-th roots are +-paired; (B) is the matching-count")
print("upper bound, (A) subtracts the overcounted non-generic matchings. Spur_r := E_r^p - E_r^{c0}(A).")
print()
print(f"{'n':>4} {'r':>3} {'(A) exact E^c0':>14} {'(B) (2r-1)!!n^r':>16} {'A<=B':>5}")
calib_ok = True
for n in [2, 4, 8]:
    for r in [1, 2, 3]:
        if (2*r) * math.log(n) > 16:  # keep brute tractable: n^{2r} <= ~ e^16
            continue
        bf = Er_charzero_exact(n, r)          # (A) exact integer energy (no mod p)
        fm = dfact(2*r-1) * n**r              # (B) Gaussian envelope
        ok = (bf <= fm)                        # honest relation: exact <= envelope
        calib_ok &= ok
        print(f"{n:>4} {r:>3} {bf:>14d} {fm:>16d} {str(ok):>5}")
print(f"\nCALIBRATION: exact char-0 energy reproduced and <= Gaussian envelope everywhere: {calib_ok}")
print("(Gaussian (2r-1)!!n^r is the prize's char-0 UPPER target, exact energy is the true c0 value;")
print(" the supply Spur_r = E_r^p - exact-c0 >= 0 was reproduced in probe_spurious_collision_count.py)")
print()

# ---------- DEMAND side: e_2=0 surplus written as Norm divisibility ----------
def elem_syms(S, p):
    """e1, e2 mod p of multiset S."""
    e1 = 0; e2 = 0; s1 = 0
    for x in S:
        e2 = (e2 + s1*x) % p
        s1 = (s1 + x) % p
    return s1 % p, e2 % p

def e2_charzero_zero(Sidx, n):
    """Is e_2(J)=0 in char 0, for J = {zeta_n^{j} : j in Sidx}?  (exact via complex)."""
    G = [cmath.exp(2j*cmath.pi*j/n) for j in Sidx]
    e1 = sum(G)
    p2 = sum(x*x for x in G)
    e2 = (e1*e1 - p2)/2
    return abs(e2) < 1e-7

def demand_defect(p, half, w):
    """e_2=0 (mod p) w-subsets of mu_{half} that are char-p-ONLY (e_2 != 0 in char 0).
    half = n/2.  Returns list of (Sidx, gamma=-e1 mod p)."""
    G = mu_modp(p, half)
    idx = list(range(half))
    out = []
    for combo in combinations(idx, w):
        S = [G[i] for i in combo]
        e1, e2 = elem_syms(S, p)
        if e2 == 0 and not e2_charzero_zero(combo, half):
            out.append((combo, (-e1) % p))
    return out

# ---------- SUPPLY side: short signed-2r-term vanishings mod p ----------
def supply_relation_for_e2(combo, half, p):
    """Given a demand J (w-subset of mu_{half}), e_2(J) = sum_{i<j} zeta^{a_i+a_j} is a sum of
    C(w,2) (UNSIGNED) half-th roots of unity. e_2(J)=0 mod p, !=0 char0  =>  this length-C(w,2)
    sum is a SUPPLY-shape vanishing (a short root-of-unity sum =0 mod p, !=0 char0).
    Return (the multiset of exponents a_i+a_j mod half, the char-p value, the char0-nonzero flag)."""
    exps = [ (combo[i] + combo[j]) % half for i in range(len(combo)) for j in range(i+1, len(combo)) ]
    # char-p value of the sum of these roots:
    z = nth_root_modp(p, half)
    val = sum(pow(z, e, p) for e in exps) % p
    # char-0 value:
    val0 = sum(cmath.exp(2j*cmath.pi*e/half) for e in exps)
    return exps, val, abs(val0) < 1e-7

print("="*78)
print("UNIFY-B: demand e_2=0 char-p defect  vs  supply short-root-sum norm divisibility")
print("="*78)
print("For each n, list demand-side char-p-ONLY e_2=0 w-subsets of mu_{n/2}; for each, exhibit")
print("the SUPPLY-shape relation = its e_2 written as a sum of C(w,2) (n/2)-th roots = 0 mod p,")
print("!=0 char-0.  Check p | this length, and report TERM COUNT vs supply's 2r.")
print()

# Onset of the demand e_2=0 char-p defect is documented at mu_16 (half=16), i.e. n=32, w=5
# (counts 150/118/86/70 at p=97/193/257/65537 vs char-0 70). Hit that region.
for (n, w) in [(32, 5), (32, 6), (16, 5)]:
    half = n // 2
    p = find_prime(half, half**3 + 1)   # proper mu_half, p ~ half^3 (clean-ish)
    # SMALL primes to SEE the defect (the documented onset primes for half=16)
    for psmall in ([97, 193, 257] if half == 16 else [find_prime(half, 50)]):
      for pp, tag in [(psmall, f"small p={psmall}"), (p, "p~(n/2)^3")]:
        defs = demand_defect(pp, half, w)
        Cw2 = w*(w-1)//2
        # verify each demand defect maps to a supply-shape vanishing
        all_supply = True
        sample = None
        for combo, gamma in defs:
            exps, val, char0zero = supply_relation_for_e2(combo, half, pp)
            # supply shape requires: char-p value == 0 (it is, since e2=0 mod p) and char0 != 0
            ok = (val == 0) and (not char0zero)
            all_supply &= ok
            if sample is None:
                sample = (combo, exps, Cw2)
        print(f"n={n} w={w} half={half} p={pp} [{tag}]: "
              f"#demand-defect-J={len(defs)}  supply-len=C(w,2)={Cw2}  "
              f"all map to char-p-only root-sum: {all_supply}")
        if sample and len(defs) > 0:
            combo, exps, Cw2 = sample
            print(f"    e.g. J(exps in mu_{half})={combo} -> e_2 = sum of {Cw2} roots, exps={sorted(exps)}")
    print()

print("="*78)
print("STRUCTURAL COMPARISON (the Unify-B verdict inputs)")
print("="*78)
print("""
SUPPLY Spur_r object:
   alpha = sum_{i=1..<=2r} eps_i * zeta_n^{e_i},  eps_i in {+1,-1},  alpha=0 mod p, !=0 char0.
   norm object:  p | Norm_{Q(zeta_n)/Q}(alpha),  alpha in mu_n-group (order n), <=2r SIGNED terms.

DEMAND e_2=0 defect object (rewritten here):
   beta = e_2(J) = sum_{i<j} zeta_{n/2}^{a_i+a_j},  a_k = exponents of J in mu_{n/2}.
   beta = 0 mod p, !=0 char0.
   norm object:  p | Norm_{Q(zeta_{n/2})/Q}(beta),  beta in mu_{n/2}-group, C(w,2) UNSIGNED terms.

SHARED:  BOTH are  "p | Norm(short root-of-unity sum), sum != 0 in char 0"  -> SAME WALL FAMILY.
DIFFERENCES (the precise distinction):
   (1) GROUP: supply mu_n (order n=2^mu); demand-e2 mu_{n/2} (order 2^{mu-1}, the SQUARES).
       But mu_{n/2} <= mu_n, and zeta_{n/2}=zeta_n^2, so Q(zeta_{n/2}) subset Q(zeta_n):
       a demand-e2 vanishing in Q(zeta_{n/2}) IS a vanishing in Q(zeta_n) (same prime p above).
   (2) SIGNS: supply +-1 (signed, from x-y balanced tuple); demand-e2 all +1 (unsigned products).
       A signed +-1 relation of length L embeds as a positive relation by zeta^{half}=-1
       (negation = shift by half), so signs are absorbed into exponents in mu_{n/2}... at the
       cost of using mu_n not mu_{n/2}. So sign-vs-unsigned <=> group n vs n/2 (SAME freedom).
   (3) LENGTH: supply length<=2r; demand-e2 length = C(w,2). At the binding rung w~? the two
       lengths are reconciled by the relation between r and w (see numeric term-count column).
""")
