"""
CORE (opus, 2026-07-11): pin the EXACT rigidity that forces d=0 in the strip interior,
distinguishing concrete RS covers from SYZ25's abstract d>0 counterexample.

CLAIM (candidate theorem): For a cover C_1..C_D of [n] by s-sets with s>=k, generation holds
(d=0) IF the "OVERLAP-CONNECTIVITY" condition holds: there is an ordering C_1..C_D such that
each C_i (i>=2) meets the union of the previous cores in >= k points (SYZ26
incremental_overlap). BUT in the strip interior pairwise overlaps < k, so this is NOT met
pairwise. The RESCUE: C_i meets the PREFIX UNION (not a single predecessor) in >= k points,
because the prefix union is large.

Check: does 'C_i ∩ (C_1∪...∪C_{i-1})' >= k hold for interior covers? prefix union after 2
cores has size <= 2s but the third core of size s meets it... Let me measure the MIN over
adversarial covers of  min_i |C_i ∩ prefixUnion_{i-1}|  and compare to k.

If that incremental-prefix-overlap >= k ALWAYS holds for over-budget interior covers, then
SYZ26's incremental_of_large_cores (which needs pairwise>=k) is the WRONG lemma, but a
PREFIX-incremental version (C_i ∩ prefix >= k) is the right one and it PROVES generation.
That prefix-incremental lemma is the missing lemma 2, and it's a CLEAN combinatorial fact.

SELF-SUBSTANTIATION (per codex review 2026-07-11): for every cover that admits NO
incremental-prefix ordering, this probe ALSO computes the exact RS-dual generation deficiency
d (nullspace of the overlap-agreement system) at four sampled primes, so the finite-sample
observation 'generation resolves (d=0 on some, d=1 at every sampled prime on the near-dup
sibling) even where the prefix criterion fails' is computed by the script itself.
SCOPE: agreement of d at four selected primes is evidence, not a proof of field-independence;
a symbolic argument (e.g. integer minors / characteristic hypotheses) is required before the
d-values are used as field-independent facts. For D > 7 the ordering search is a heuristic and
its failures are reported as UNKNOWN, never as "no ordering exists".
"""
import random


def _matnullity(M, p, cols):
    """Nullity of the ``len(M) x cols`` matrix ``M`` over F_p.

    ``cols`` (the number of unknowns) is passed explicitly so that an empty
    system (no equations, e.g. pairwise-disjoint cores) correctly has nullity
    ``cols`` rather than 0.
    """
    if not M:
        return cols
    M = [r[:] for r in M]
    rows = len(M)
    assert all(len(r) == cols for r in M)
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(cols)]
        r += 1
        if r == rows:
            break
    return cols - r


def rs_dual_deficiency(cores, k, p):
    """Exact generation deficiency d = nullity(overlap-agreement system) - k over F_p.
    d>0 means the union of RS-dual restrictions is d short of the full (n-k)-dim dual
    (generation fails); d=0 means it generates."""
    D = len(cores)
    ncols = D * k
    rows = []
    cs = [set(c) for c in cores]
    for i in range(D):
        for j in range(i + 1, D):
            for x in cs[i] & cs[j]:
                row = [0] * ncols
                for d in range(k):
                    xd = pow(x, d, p)
                    row[i * k + d] = (row[i * k + d] + xd) % p
                    row[j * k + d] = (row[j * k + d] - xd) % p
                rows.append(row)
    return _matnullity(rows, p, ncols) - k

def prefix_overlaps(cores):
    D=len(cores)
    pref=set()
    mins=[]
    for i in range(D):
        if i==0:
            pref=set(cores[0]); mins.append(None); continue
        ov=len(set(cores[i])&pref)
        mins.append(ov)
        pref|=set(cores[i])
    return mins

def can_order_incremental_prefix(cores,k):
    """Is there an ordering s.t. each core (after 1st) meets prefix-union in >= k?

    Returns a three-valued answer:
      * ``(True, order)``  -- a valid ordering was found (certificate);
      * ``(False, None)``  -- NO valid ordering exists (only returned by the complete
        permutation search, used for D <= 7);
      * ``(None, None)``   -- UNKNOWN: for D > 7 only a greedy heuristic is run (from every
        starting core); its failure does NOT prove that no ordering exists. Example:
        A={1,2,3}, B={1,4,5}, C={2,4,5}, cores [A,B,C,B,B,B,B,B], k=2: greedy from core 0
        fails, yet the order [1,2,0,3,...,7] is valid.
    """
    D=len(cores)
    from itertools import permutations
    if D<=7:
        for perm in permutations(range(D)):
            ordered=[cores[i] for i in perm]
            ms=prefix_overlaps(ordered)
            if all((m is None) or m>=k for m in ms):
                return True,perm
        return False,None
    # greedy heuristic for larger D (incomplete): try every starting core.
    for start in range(D):
        used=[start]; pref=set(cores[start])
        order=[start]
        stuck=False
        while len(used)<D:
            best=None
            for j in range(D):
                if j in used: continue
                ov=len(set(cores[j])&pref)
                if best is None or ov>best[0]: best=(ov,j)
            if best[0]<k:
                stuck=True
                break
            order.append(best[1]); used.append(best[1]); pref|=set(cores[best[1]])
        if not stuck:
            return True,tuple(order)
    # heuristic failure is not a proof of non-existence
    return None,None

def build_covers(n,s,D,rng,tries=800):
    points=list(range(1,n+1))
    out=[]
    for _ in range(tries):
        cores=[set(rng.sample(points,s)) for _ in range(D)]
        if set().union(*cores)!=set(points): continue
        if sum(len(c)-(n//2) for c in cores) < (n-(n//2)): continue
        out.append([sorted(c) for c in cores])
        if len(out)>=60: break
    return out

def main():
    rng=random.Random(11072026)
    print("=== PREFIX-incremental overlap criterion: does every over-budget interior cover admit")
    print("    an ordering where each core meets the prefix-union in >= k points? ===")
    print("    If YES universally, that's the clean lemma-2 proof (prefix version of SYZ26).\n")
    allok=True
    worst_examples=[]
    for n in [12,16,20,24,28,32]:
        k=n//2
        for s in range(2*n//3+1,(3*n)//4):
            for D in [3,4,5]:
                covers=build_covers(n,s,D,rng)
                if not covers: continue
                fails=0; checked=0; unknown=0
                minmargin=None
                for cores in covers:
                    checked+=1
                    ok,order=can_order_incremental_prefix(cores,k)
                    if ok is None:
                        unknown+=1
                        continue
                    if not ok:
                        fails+=1
                        worst_examples.append((n,k,s,D,cores))
                    else:
                        ms=[m for m in prefix_overlaps([cores[i] for i in order]) if m is not None]
                        mg=min(ms)-k
                        if minmargin is None or mg<minmargin: minmargin=mg
                flag="  *** SOME COVERS HAVE NO INCREMENTAL-PREFIX ORDERING ***" if fails else ""
                if fails: allok=False
                print(f"n={n:2d} k={k:2d} s={s:2d} D={D} checked={checked} fails={fails} unknown={unknown} minPrefixMargin(overlap-k)={minmargin}{flag}")
    print()
    print("incremental-prefix criterion holds on every sampled cover (finite sample, not universal):", allok)
    if worst_examples:
        print()
        print("=== SELF-SUBSTANTIATION: RS-dual deficiency d on covers with NO prefix ordering ===")
        print("    (d recomputed at the four sampled primes p in {101,1009,65537,10^6+3}; agreement at")
        print("     these primes is finite evidence only, NOT a proof of field-independence)")
        primes = [101, 1009, 65537, 1000003]
        any_gen = False
        any_fieldindep_defect = False
        for (n, k, s, D, cores) in worst_examples[:6]:
            ds = [rs_dual_deficiency(cores, k, p) for p in primes]
            field_indep = len(set(ds)) == 1  # agreement at the sampled primes only
            d0 = ds[0]
            if d0 == 0:
                any_gen = True
            if field_indep and d0 > 0:
                any_fieldindep_defect = True
            print(f"n={n:2d} k={k:2d} s={s:2d} D={D} d(p={primes})={ds} same_d_at_sampled_primes={field_indep} prefix_ordering=None cores={cores}")
        print()
        print("generation (d=0) occurs on a prefix-failing cover:", any_gen)
        print("d>0 at all sampled primes (near-dup-pair defect) occurs on a prefix-failing cover:", any_fieldindep_defect)
        print("=> on these sampled covers the SYZ26 prefix-overlap criterion does not decide generation:")
        print("   d is resolved by RS-dual arithmetic, not by the covering/prefix combinatorics.")

if __name__=="__main__":
    main()
