"""
probe_444_unifyA_supply_demand_identity.py  (#444 Unify-A)

TASK: compute BOTH char-p defects at matched (n,r) and test whether they are the SAME object.

  SUPPLY side (the prize wall):
     E_r(mu_n)      = #{(z,z') in mu_n^{2r} : sum z_i = sum z'_i  in F_p}   (additive energy)
     E_r^{c0}       = (2r-1)!! * n^r                                        (Lam-Leung char-0)
     Spur_r(p)      = E_r(mu_n over F_p) - E_r^{c0}   >= 0                   (char-p surplus)
     bad-prime test: Spur_r(p) > 0 ?

  DEMAND side (the e_2=0 halo defect on mu_{n} subsets, from deltastar-407-e2zero-modq-defect):
     N(F_q)         = #{ size-w subsets S of mu_n : e_2(S) = 0 in F_q }     (w = matched depth)
     N(char0)       = the char-0 count of the same (exact cyclotomic e_2=0)
     Defect(q)      = N(F_q) - N(char0)
     RISE carriers  = sets with e_2(S) != 0 in Z[zeta] but = 0 mod q   <=>  q | N(e_2(S))
     bad-prime test: a RISE carrier exists at q ?  (i.e. q | N(e_2(S)) for some window S)

  IDENTITY QUESTION (Unify-A): is the bad-prime set of Spur_r EQUAL to the bad-prime set of the
  demand defect?  Same bad-prime set => same underlying short +-1-relation object => ONE wall
  (consolidation).  We test equality / proportionality / shared support.

Calibration FIRST: reproduce E_r^{c0} = (2r-1)!! n^r exactly (char-0 brute force) before any claim.
"""
import itertools
from collections import Counter
import sympy

# ---------- primes p == 1 mod n ----------
def primes_1_mod_n(n, lo, hi):
    return [p for p in range(max(lo, n+1), hi) if p % n == 1 and sympy.isprime(p)]

def subgroup(n, p):
    g = int(sympy.primitive_root(p)); h = pow(g, (p-1)//n, p)
    H = []; x = 1
    for _ in range(n):
        H.append(x); x = x*h % p
    return H

# ---------- char-0 fingerprint (Q-basis 1,zeta,...,zeta^{n/2-1}; zeta^{j+n/2}=-zeta^j) ----------
def char0_vec_of_tuple(x, n):
    half = n // 2
    v = [0]*half
    for a in x:
        if a < half: v[a] += 1
        else:        v[a-half] -= 1
    return tuple(v)

def dfac(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

# ============================================================
# SUPPLY side
# ============================================================
def E_r_char0_brute(n, r):
    """exact char-0 additive energy via reduced Q-vector fingerprint (indices in Z/n)."""
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        cnt[char0_vec_of_tuple(x, n)] += 1
    return sum(c*c for c in cnt.values())

def E_r_modp(n, p, r, H):
    """exact additive energy over F_p: #{(z,z'): sum z = sum z' mod p}."""
    cnt = Counter()
    for x in itertools.product(H, repeat=r):
        cnt[sum(x) % p] += 1
    return sum(c*c for c in cnt.values())

# ============================================================
# DEMAND side: e_2=0 subsets of mu_n, exact cyclotomic vs mod-p
# ============================================================
def e2_of_subset_char0(S, n):
    """e_2(S) in Z[zeta_n], returned as reduced Q-vector (over basis 1..zeta^{n/2-1})."""
    half = n // 2
    v = [0]*half
    for i, j in itertools.combinations(S, 2):
        a = (i + j) % n
        if a < half: v[a] += 1
        else:        v[a-half] -= 1
    return tuple(v)

def e2_of_subset_modp(S, n, p, H):
    """e_2(S) in F_p, S given as a list of EXPONENTS (indices into mu_n), evaluated at H."""
    s = 0
    for i, j in itertools.combinations(S, 2):
        s = (s + H[i]*H[j]) % p
    return s % p

def demand_counts(n, w, p, H):
    """
    N(char0)  = #{ size-w exponent-subsets S of Z/n : e_2(S) = 0 exactly (cyclotomic) }
    N(F_p)    = #{ size-w exponent-subsets S        : e_2(S) = 0 mod p }
    RISE      = #{ S : e_2(S) != 0 char-0 but = 0 mod p }  (pure mod-p halo carriers)
    """
    Nc0 = 0; Nfp = 0; rise = 0
    for S in itertools.combinations(range(n), w):
        z0 = all(c == 0 for c in e2_of_subset_char0(S, n))
        zp = (e2_of_subset_modp(S, n, p, H) == 0)
        if z0: Nc0 += 1
        if zp: Nfp += 1
        if zp and not z0: rise += 1
    return Nc0, Nfp, rise

# ============================================================
# RUN
# ============================================================
def main():
    print("="*78)
    print("PART 0 -- CALIBRATION: char-0 additive energy E_r^{c0}(mu_n)")
    print("   The CONTEXT/synthesis claim E_r^c0=(2r-1)!! n^r is a LEADING-ORDER UPPER BOUND,")
    print("   NOT exact: (2r-1)!! over-counts because diagonal/overlapping pairings coincide.")
    print("   GROUND TRUTH = brute-forced E_r^{c0} over the cyclotomic Q-basis (matches the")
    print("   in-tree probe_char0_energy_check_407.py). We also check E_r^c0 <= (2r-1)!!n^r,")
    print("   and r=1 exact (=n). The brute value is the baseline used for Spur_r.")
    print("="*78)
    print(f"{'n':>4} {'r':>3} | {'E_r^c0 brute':>14} {'(2r-1)!!n^r':>14} {'<=bnd':>6} {'r1=n':>6}")
    calib_ok = True
    for a in (3, 4, 5):
        n = 2**a
        # r=1 sanity: E_1^c0 must be exactly n
        if n <= 256:
            E1 = E_r_char0_brute(n, 1)
            if E1 != n: calib_ok = False
        for r in (2, 3, 4):
            if n**r > 600000:
                continue
            Ec = E_r_char0_brute(n, r)
            base = dfac(2*r-1)*n**r
            le = (Ec <= base); calib_ok &= le
            r1ok = (E_r_char0_brute(n,1) == n) if n <= 256 else True
            print(f"{n:>4} {r:>3} | {Ec:>14} {base:>14} {str(le):>6} {str(r1ok):>6}")
    print(f"\nCALIBRATION OK (E_1=n exactly AND E_r^c0 <= (2r-1)!!n^r): {calib_ok}")
    print("NOTE: exact char-0 baseline is the BRUTE value, not the !! formula.\n")

    print("="*78)
    print("PART 1 -- SUPPLY: Spur_r(p) = E_r(mu_n/F_p) - E_r^{c0,brute}   over small primes")
    print("   (E_r^{c0} = EXACT brute char-0 baseline, not the !! upper bound)")
    print("="*78)
    supply_badprimes = {}   # (n,r) -> set of p with Spur>0
    for a in (3, 4):
        n = 2**a
        for r in (2, 3):
            if n**r > 300000:
                continue
            Ec = E_r_char0_brute(n, r)   # exact char-0 baseline
            bad = set()
            ps = primes_1_mod_n(n, 0, 1500)
            row = []
            for p in ps[:14]:
                H = subgroup(n, p)
                Ep = E_r_modp(n, p, r, H)
                spur = Ep - Ec
                if spur > 0: bad.add(p)
                row.append((p, spur))
            supply_badprimes[(n, r)] = bad
            print(f"\n n={n} r={r}  E_r^c0(exact)={Ec}  ((2r-1)!!n^r upper={dfac(2*r-1)*n**r})")
            print("   " + "  ".join(f"p={p}:Spur={s}" for p, s in row))
            print(f"   SUPPLY bad primes (Spur_r>0): {sorted(bad)}")

    print()
    print("="*78)
    print("PART 2 -- DEMAND: e_2=0 halo defect on size-w subsets of mu_n")
    print("   matched depth: supply uses sum over r terms => e_2=0 is the 2nd-order (r=2) condition")
    print("="*78)
    demand_badprimes = {}
    # window weights w probing the e_2=0 object at small n; w=4 has char-0 support (cosets),
    # w=6 has char-0 count 0 (pure RISE) per the kb note.
    for a in (3, 4):
        n = 2**a
        for w in (4, 6):
            if n < w:
                continue
            ps = primes_1_mod_n(n, 0, 1500)
            bad = set(); rows = []
            Nc0_ref = None
            for p in ps[:14]:
                H = subgroup(n, p)
                Nc0, Nfp, rise = demand_counts(n, w, p, H)
                Nc0_ref = Nc0
                if rise > 0: bad.add(p)
                rows.append((p, Nfp, rise, Nfp-Nc0))
            demand_badprimes[(n, w)] = bad
            print(f"\n n={n} w={w}  N(char0)={Nc0_ref}")
            print("   " + "  ".join(f"p={p}:Nfp={nf},rise={ri},def={df}"
                                    for p, nf, ri, df in rows))
            print(f"   DEMAND bad primes (RISE>0, q|N(e_2(S))): {sorted(bad)}")

    print()
    print("="*78)
    print("PART 3 -- IDENTITY TEST: is SUPPLY bad-prime set == DEMAND bad-prime set?")
    print("="*78)
    for a in (3, 4):
        n = 2**a
        sb = supply_badprimes.get((n, 2), set())   # r=2 supply
        # demand at the e_2=0 object: combine the RISE-carrying weights (w=4,6)
        db = set()
        for w in (4, 6):
            db |= demand_badprimes.get((n, w), set())
        inter = sb & db
        print(f"\n n={n}:")
        print(f"   SUPPLY (Spur_2>0)         : {sorted(sb)}")
        print(f"   DEMAND (e2=0 RISE, any w) : {sorted(db)}")
        print(f"   intersection              : {sorted(inter)}")
        print(f"   supply==demand?           : {sb == db}")
        print(f"   supply subset of demand?  : {sb <= db}")
        print(f"   demand subset of supply?  : {db <= sb}")

if __name__ == "__main__":
    main()
