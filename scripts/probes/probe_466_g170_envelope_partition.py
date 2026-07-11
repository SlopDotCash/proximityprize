"""Test whether the SYZ28 pair-union envelope defect formula is the COMPLETE characterization
of generation deficiency for GENERAL D (D>=3,4,5,6), not just D=3.

SYZ28 (D=3):  d = max(0, (n+k) - min_pairing (|Ci ∪ Cj| + |Cl|))     [Cl the third core]

General-D envelope hypothesis: the joint syndrome span sits inside the sup of any partition
of the cores into groups, each group replaced by its union-envelope A_{∪group} of rank
(|∪group| - k)_+ .  So an upper bound on rank is, for ANY partition P of {1..D}:
   rank(⨆ A_Ci) <= sum_{G in P} max(0, |∪_{i in G} C_i| - k)
and deficiency d >= (n-k) - min over partitions P of that sum.

CLAIM to test:  d == max(0, (n-k) - min_{partitions P} sum_G (|∪G| - k)_+ )   EXACTLY?
i.e. the true deficiency equals the best (smallest) envelope bound over ALL set-partitions.
If exact, this is a clean, field-independent, general-D structural theorem generalizing SYZ28.
"""
import random
from itertools import combinations


def matnullity(M, p):
    if not M:
        return 0
    M = [r[:] for r in M]
    rows = len(M)
    cols = len(M[0])
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


def deficiency_exact(points, cores, k, p):
    """true d = nullity(overlap agreement system) - k."""
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
    return matnullity(rows, p) - k


def all_partitions(collection):
    collection = list(collection)
    if len(collection) == 1:
        yield [collection]
        return
    first = collection[0]
    for smaller in all_partitions(collection[1:]):
        for i, subset in enumerate(smaller):
            yield smaller[:i] + [[first] + subset] + smaller[i + 1:]
        yield [[first]] + smaller


def envelope_bound(cores, k, n):
    """min over partitions of sum_G max(0,|union G|-k); deficiency lower bound = (n-k) - that."""
    cs = [set(c) for c in cores]
    D = len(cores)
    best = None
    for P in all_partitions(range(D)):
        tot = 0
        for G in P:
            u = set()
            for i in G:
                u |= cs[i]
            tot += max(0, len(u) - k)
        if best is None or tot < best:
            best = tot
    return max(0, (n - k) - best)


def exhaustive_cell(n, k, s, D, p):
    """EXHAUSTIVE enumeration of ALL over-budget covering D-tuples of s-subsets of [n]
    (up to the natural ordering), comparing exact d to the envelope-partition formula.
    Feasible only for the smallest cell; substantiates 'exact' beyond random sampling."""
    from itertools import combinations
    pts = list(range(1, n + 1))
    all_cores = [set(c) for c in combinations(pts, s)]
    checked = 0
    mism = 0
    # enumerate unordered D-multisets of distinct cores (combinations of the core list)
    for combo in combinations(range(len(all_cores)), D):
        cs = [all_cores[i] for i in combo]
        u = set()
        for c in cs:
            u |= c
        if u != set(pts):
            continue
        if sum(len(c) - k for c in cs) < (n - k):
            continue
        cores = [sorted(c) for c in cs]
        d_true = deficiency_exact(pts, cores, k, p)
        d_form = envelope_bound(cores, k, n)
        checked += 1
        if d_true != d_form:
            mism += 1
            if mism <= 5:
                print(f"  EXHAUSTIVE MISMATCH cores={cores} d_true={d_true} d_form={d_form}")
    return checked, mism


def main():
    rng = random.Random(20260711)
    print("=== d (exact RS-dual) vs envelope-partition formula (general D) ===")
    print("    seeded-random reproducible sample; results are deterministic under the fixed seed.\n")
    mismatches = 0
    checked = 0
    for n in [12, 16, 20, 24]:
        k = n // 2
        for s in range(2 * n // 3 + 1, (3 * n) // 4):
            for D in [3, 4, 5]:
                if D * (s - k) < (n - k):
                    continue
                pts = list(range(1, n + 1))
                for _ in range(400):
                    cores = [set(rng.sample(pts, s)) for _ in range(D)]
                    if set().union(*cores) != set(pts):
                        continue
                    cores = [sorted(c) for c in cores]
                    d_true = deficiency_exact(pts, cores, k, 65537)
                    d_form = envelope_bound(cores, k, n)
                    checked += 1
                    if d_true != d_form:
                        mismatches += 1
                        if mismatches <= 8:
                            print(f"MISMATCH n={n} k={k} s={s} D={D} d_true={d_true} d_formula={d_form}")
                            print("  cores:", cores)
    print(f"seeded random sample: checked={checked} mismatches={mismatches}")
    if mismatches == 0:
        print("  -> d == envelope-partition bound on the entire seeded sample (D in {3,4,5}).")
    else:
        print("  -> formula is only a BOUND, not exact.")

    # EXHAUSTIVE confirmation at a small interior cell (codex-requested substantiation).
    # n=12,k=6: interior s in (8,9) -> s=9 (delta=1/4 boundary excluded, s=9 gives delta=0.25);
    # use the fully-enumerable near-interior cell n=12,k=6,s=10 (C(12,10)=66 cores, ~46k triples).
    print("\n=== EXHAUSTIVE enumeration at n=12,k=6,s=10,D=3 (ALL over-budget covers) ===")
    ec, em = exhaustive_cell(12, 6, 10, 3, 65537)
    print(f"exhaustive: checked={ec} mismatches={em}")
    if em == 0 and mismatches == 0:
        print("EXACT (exhaustive at the small cell + reproducible sample elsewhere):")
        print("  d == envelope-partition bound. General-D structural theorem candidate; upper-bound half formalized in G170.")
    else:
        print("characterization is NOT exact as stated.")


if __name__ == "__main__":
    main()
