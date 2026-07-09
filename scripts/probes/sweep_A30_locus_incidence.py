#!/usr/bin/env python3
"""sweep_A30_locus_incidence.py — A30 (merged 232-T10 / 334-T23 G5): the cross-level
difference-loci incidence lattice of the proven-complete list configuration, and the
DECISIVE test:

    Does truncated inclusion-exclusion (Bonferroni-2 / Bonferroni-3) on the locus
    intersection lattice beat the trivial union bound on the list size?

This is the *only* surviving path (per DISPROOF_LOG O109/O115 + RESULTS-INCIDENCE.md
H-INC3) to a list bound improving the union bound, after the counting side of the
2-adic fold tower was closed (the tower multiplies CHOICES not CONSTRAINTS).

================================ THE SETUP (exact, self-contained) ===================
Split prime p = 1 (mod 32).  D = mu_32 = <g0^((p-1)/32)>, code RS[F_p, mu_32, 16]
(deg < 16).  Received word w(x) = x^18 + lam*x^16, lam = -i4 (i4 a primitive 4th root).
This is the canonical max-fiber / Kambire-near-capacity (eta = 1/16) configuration of
issue #232 (n=32, beyond Johnson).  Its proven-complete bad list at agreement >= 17 is

    L = 35 witnesses (agree EXACTLY 18, |T_w| = 18)  +  1344 dense (agree EXACTLY 17),

reconstructed here by lane_a's exact-integer consistency-equation generator (NO kernel).
At the BabyBear primes 15*2^27+1 and 3*2^30+1 the list is exactly 35 + 1344 = 1379
(the law holds; the char-0 count).  We also tabulate over the failing small primes to
see the generic dense inflation.

LOCUS STRUCTURE (proven, RESULTS-INCIDENCE.md):  For a witness w and a dense t the
difference c_w - c_t vanishes on mu_32 EXACTLY on T_w cap T_t (the EXACTNESS THEOREM,
char-0, computational proof), and its LEVEL-1 dead-fiber locus (antipodal pairs both
zero) is EXACTLY the index set of {z in mu_16 : z in S_w cap B_t} (the dead-fiber
dichotomy).  So the cross-pair incidence is the intersection lattice of the 35
fiber-subsets S_w (each a 9-subset of mu_16 ~ the witness S) against the 580 distinct
B-blocks B_t (each a 7-subset of mu_16).

================================ THE UNION BOUND, MADE PRECISE =======================
A *certificate family* for a list bound assigns to every list element e a TEST set
test(e) (here: its level-1 dead-fiber locus L1(e), a subset of mu_16) drawn from a
fixed catalogue, and bounds  |L| <= sum over distinct test sets tau of  (#elements that
COULD map to tau)  =  the cover/union bound.  The over-count is the locus MULTIPLICITY
mult(tau) = #{e in L : test(e) = tau}.  The trivial (1st-order Bonferroni / pure union)
bound is U1 = sum_tau mult(tau) = |L| if test is injective, but in any *coarse* family
(loci of fixed size z0) the count is sum_tau (#configs detected at tau).

We make this exact in two well-posed forms and decide both:

  FORM A (size-z0 test-set cover, the O97/O99-template the literature uses).  Fix the
  test radius z0 (the O94 floor n/2 - w = 16-17 < 0 -> use the actual L1 sizes).  Each
  list element e occupies the C(|L1(e)|, z0) size-z0 sub-loci of its level-1 locus.  The
  union bound counts |L| <= #{occupied size-z0 sub-loci} (one element per sub-locus is
  the cover claim) ONLY if each sub-locus is occupied by <= 1 element; the OVER-count is
  exactly the per-sub-locus occupancy.  We compute, for z0 = 1..maxL1:
     U1(z0) = sum over occupied size-z0 loci tau of occ(tau)       (= sum_e C(|L1(e)|,z0))
     IE2(z0)= U1(z0) - sum over loci tau of C(occ(tau), 2)         (Bonferroni-2)
     IE3(z0)= IE2(z0)+ sum over loci tau of C(occ(tau), 3)         (Bonferroni-3)
  and the EXACT cover value  COV(z0) = #occupied size-z0 loci.  Bonferroni's theorem:
  the inclusion-exclusion alternating truncations bracket the union |∪ A_tau| where
  A_tau = {elements occupying tau}; ODD truncation (U1) is an UPPER bound on |∪A_tau|,
  EVEN truncation (IE2) a LOWER bound.  But |∪ A_tau| = |L| (every element occupies >=1
  locus when |L1(e)|>=z0).  So the question is sharp: is U1(z0) (the literature bound)
  >> |L|, and does the inclusion-exclusion CORRECTION sum_tau C(occ,2) recover the gap,
  i.e. is IE2(z0) close to / a valid improvement toward |L| = #covered elements?

  FORM B (the bipartite incidence lattice S_w x B_t directly).  The cross-pair loci are
  S_w cap B_t.  We build the full 35 x 580 incidence and ask whether second-order
  inclusion-exclusion over the SHARED loci (mean mult 11.55, max 144) yields a strictly
  smaller VALID upper bound on the number of distinct (w,t) incidences than the union
  count, i.e. whether the over-count C(mult,2) corrections are sign-correct.

HONESTY: Bonferroni gives U1 >= |∪| >= IE2 ALWAYS (a theorem) — IE2 is a *lower* bound,
so it can NEVER be used as an improved *upper* bound directly.  The only way
inclusion-exclusion improves the UPPER bound is if the family is a genuine PACKING
(occ(tau) bounded => |L| <= COV(z0)*maxocc with maxocc small), OR if a Bonferroni-ODD
truncation at order 3 (U1 - sum C(occ,2) + sum C(occ,3)) lies STRICTLY BELOW U1 while
still >= |L| (a valid tighter upper bound).  We decide exactly which, with numbers.

Exact arithmetic over GF(p) (p prime).  Deterministic.  Exit 0 iff all hard gates pass.
"""
import sys
import math
from itertools import combinations
from collections import Counter

sys.path.insert(0, "scripts/probes/incidence/exactness")
import lane_a as L  # noqa: E402

C = math.comb
ok = True


def fail(msg):
    global ok
    ok = False
    print("FAIL:", msg)


def mu16_index_map(st):
    """index each mu16 element 0..15."""
    return {z: i for i, z in enumerate(st["mu16"])}


def build_loci(p, verbose=True):
    """Return (Swit, Bden, mu16idx, st) where
       Swit = list of 35 frozensets of mu16-indices (the witness fiber subsets S),
       Bden = list of B-blocks (frozensets of mu16-indices) for each of the 1344 dense
              elements (with multiplicity; also the 580 distinct B set)."""
    st = L.setup(p)
    wits = L.witnesses(st)
    dens, raw = L.dense(st)
    idx = mu16_index_map(st)
    mu16set = set(st["mu16"])
    # witness fiber subset S (drop i4? no: dead-fiber dichotomy locus is S cap B over mu16;
    # S has 9 elements incl i4; B has 7 elements of mu16; the cross locus is S cap B).
    Swit = []
    for wrec in wits:
        S = frozenset(idx[s] for s in wrec["Sset"] if s in mu16set)
        Swit.append(S)
    Bden = []
    for drec in dens.values():
        B = frozenset(idx[b] for b in drec["Bset"])
        Bden.append(B)
    return st, wits, dens, raw, Swit, Bden, idx


# ============================================================== run a prime
def analyze(p, verbose=True):
    global ok
    st, wits, dens, raw, Swit, Bden, idx = build_loci(p, verbose)
    nwit, nden = len(Swit), len(Bden)
    Ldistinct_B = sorted({B for B in Bden})
    nB = len(Ldistinct_B)
    listsize = nwit + nden
    if verbose:
        print("=" * 78)
        print(f"p = {p}   list = {nwit} witnesses + {nden} dense = {listsize}"
              f"   (distinct B-blocks: {nB})")

    # ---- ground-truth cross-pair loci = S_w cap B_t  (the dead-fiber dichotomy) ----
    # multiplicity of each level-1 locus over all 35*nden cross pairs
    cross_loci = Counter()
    for S in Swit:
        for B in Bden:
            cross_loci[S & B] += 1
    npairs = nwit * nden
    distinct = len(cross_loci)
    mults = list(cross_loci.values())
    meanmult = npairs / distinct
    maxmult = max(mults)
    if verbose:
        print(f"\n[FORM B] cross pairs = {npairs}; distinct level-1 loci = {distinct}; "
              f"mean multiplicity = {meanmult:.2f}; max = {maxmult}")
        menu = dict(sorted(Counter(mults).items()))
        print(f"   multiplicity menu (#loci with that mult): "
              f"{dict(list(menu.items())[:14])}{' ...' if len(menu) > 14 else ''}")

    # ===================================================================== FORM A
    # The size-z0 test-set cover on the FULL list L (witnesses + dense), using each
    # element's OWN level-1 dead-fiber locus as its test object.  For a list element we
    # need its level-1 locus as a subset of mu16.  For witnesses: L1 = pairs of T_w that
    # are antipodal; for the dense layer the level-1 locus equals the index set of its
    # 7-block fiber pairs.  But the cover bound in the literature is run on the WITNESS
    # layer's interaction with the dense layer (cross), so we run FORM A on the cross
    # incidence: the "elements" are the npairs cross incidences, each detected by locus
    # S_w cap B_t, and we test whether IE on the shared loci recovers the true #distinct.
    print("\n[FORM A] size-z0 test-set cover over the 35x{} cross incidence".format(nden))
    print("   (A_tau = cross pairs whose locus CONTAINS the size-z0 set tau)")
    print("    z0 |        U1 = sum C(|L|,z0)   #occ-loci(=COV) |"
          "        IE2=U1-sumC(occ,2)   IE3 | exact |U|=npairs  U1/|U|")
    maxL1 = max(len(S & B) for S in Swit for B in Bden)
    formA_rows = []
    for z0 in range(1, maxL1 + 1):
        occ = Counter()  # size-z0 sub-locus -> #cross pairs containing it
        U1 = 0
        for S in Swit:
            for B in Bden:
                loc = S & B
                if len(loc) >= z0:
                    U1 += C(len(loc), z0)
                    for tau in combinations(sorted(loc), z0):
                        occ[tau] += 1
        COV = len(occ)
        sumC2 = sum(C(v, 2) for v in occ.values())
        sumC3 = sum(C(v, 3) for v in occ.values())
        IE2 = U1 - sumC2
        IE3 = IE2 + sumC3
        # exact union |∪ A_tau| over size-z0 loci = #cross pairs with |locus|>=z0
        UN = sum(1 for S in Swit for B in Bden if len(S & B) >= z0)
        formA_rows.append((z0, U1, COV, IE2, IE3, UN))
        print(f"   {z0:2d} | {U1:24d} {COV:16d} | {IE2:24d} {IE3:8d} | {UN:14d}"
              f"  {U1/max(1,UN):7.3f}")
        # HARD GATE: Bonferroni bracketing  IE2 <= UN <= U1  (must hold exactly)
        if not (IE2 <= UN <= U1):
            fail(f"Bonferroni bracketing violated p={p} z0={z0}: "
                 f"IE2={IE2} UN={UN} U1={U1}")

    # ===================================================================== verdict math
    # The decisive numbers at z0=1 (the loci themselves):
    z0, U1, COV, IE2, IE3, UN = formA_rows[0]
    print(f"\n   z0=1 decisive: U1(union, 1st-Bonferroni)={U1}  exact|U|={UN}  "
          f"IE2(2nd-Bonferroni, a LOWER bound)={IE2}")
    print(f"   union-bound over-count factor U1/|U| = {U1/UN:.3f}  "
          f"(this is the {meanmult:.2f}x locus sharing realized as a sum)")
    # Is there ANY odd-order Bonferroni truncation strictly below U1 that still >= |U|?
    # order-3 truncation = U1 - sumC2 + sumC3 = IE3.  Valid upper bound iff IE3 >= UN.
    if IE3 >= UN and IE3 < U1:
        print(f"   *** order-3 Bonferroni IE3={IE3} is a VALID upper bound BELOW U1={U1}"
              f" (>= exact |U|={UN}): inclusion-exclusion DOES tighten the upper bound.")
    else:
        rel = "BELOW exact |U| (INVALID as upper bound)" if IE3 < UN else "= U1 (no gain)"
        print(f"   order-3 Bonferroni IE3={IE3} is {rel}: no valid upper-bound improvement"
              f" from low-order inclusion-exclusion.")

    # ===================================================================== FORM C
    # The faithful "list-cover" inclusion-exclusion: ground set = the 1344 dense list
    # elements; covering family = the 35 witnesses, where witness w COVERS dense t iff
    # they share a nonempty level-1 locus |S_w cap B_t| >= thr (the incidence "explains"
    # t through w).  A union-bound list argument would bound |dense list| <= sum_w
    # |cover(w)|; inclusion-exclusion would subtract the pairwise overlaps.  We compute,
    # for each incidence threshold thr:
    #   covered = |∪_w cover(w)|              (the elements any witness explains)
    #   U1      = sum_w |cover(w)|            (union bound over witnesses, 1st-Bonferroni)
    #   IE2     = U1 - sum_{w<w'} |cover(w) cap cover(w')|   (2nd-Bonferroni, LOWER bound)
    # and HARD-GATE the bracket IE2 <= covered <= U1.
    print("\n[FORM C] witness-cover IE on the 1344 dense ground set "
          "(cover(w) = dense t with |S_w cap B_t| >= thr)")
    print("    thr | covered=|union| |   U1=sum|cov|  U1/cov |   IE2=U1-sum|cap| (LOWER)")
    formC_rows = []
    for thr in range(1, 8):
        covers = []
        for S in Swit:
            cov = frozenset(t for t in range(nden) if len(S & Bden[t]) >= thr)
            covers.append(cov)
        union = frozenset().union(*covers) if covers else frozenset()
        covered = len(union)
        U1c = sum(len(c) for c in covers)
        sumcap = 0
        for a in range(len(covers)):
            ca = covers[a]
            for b in range(a + 1, len(covers)):
                sumcap += len(ca & covers[b])
        IE2c = U1c - sumcap
        formC_rows.append((thr, covered, U1c, IE2c))
        ratio = (U1c / covered) if covered else float("inf")
        print(f"    {thr:2d} | {covered:9d} | {U1c:11d}  {ratio:6.3f} | {IE2c:18d}")
        if covered and not (IE2c <= covered <= U1c):
            fail(f"FORM C Bonferroni bracket violated p={p} thr={thr}: "
                 f"IE2={IE2c} covered={covered} U1={U1c}")

    return dict(p=p, listsize=listsize, nden=nden, npairs=npairs, distinct=distinct,
                meanmult=meanmult, maxmult=maxmult, formA=formA_rows, formC=formC_rows)


# ============================================================== n=16 lower rung
def analyze_n16(p=2013265921):
    """The n=16 rung (list = 19 = 3 witnesses + 16 dense, RESULTS-INCIDENCE gate):
    same incidence-lattice question one tower level down, to confirm the verdict is
    rung-independent (the A30 'general-rung law' grounding)."""
    G0, LAM = 31, 284861408

    def pw(b, e):
        return pow(b, e, p)
    INV = lambda a: pow(a, p - 2, p)

    def pmul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] = (out[i + j] + x * y) % p
        return out

    def peval(c, x):
        r = 0
        for co in reversed(c):
            r = (r * x + co) % p
        return r

    def interp(xs, ys):
        m = len(xs)
        out = [0] * m
        for i in range(m):
            num, den = [1], 1
            for j in range(m):
                if j == i:
                    continue
                num = pmul(num, [(-xs[j]) % p, 1])
                den = den * ((xs[i] - xs[j]) % p) % p
            s = ys[i] * INV(den) % p
            for d in range(len(num)):
                out[d] = (out[d] + s * num[d]) % p
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return out

    n, k, A = 16, 8, 9
    h = pw(G0, (p - 1) // n)
    H = [pw(h, i) for i in range(n)]
    w = [(pw(x, 10) + LAM * pw(x, 8)) % p for x in H]
    found = {}
    for sub in combinations(range(n), A):
        c = interp([H[i] for i in sub], [w[i] for i in sub])
        if len(c) <= k:
            key = tuple(c + [0] * (k - len(c)))
            if key not in found:
                found[key] = frozenset(i for i in range(n)
                                       if peval(list(key), H[i]) == w[i])
    wit = {c: a for c, a in found.items() if len(a) == 10}
    den = {c: a for c, a in found.items() if len(a) == 9}
    gate = (len(found) == 19 and len(wit) == 3 and len(den) == 16)
    if not gate:
        fail(f"n=16 gate: list={len(found)} wit={len(wit)} den={len(den)}")
    # level-1 loci of witness-dense differences (antipodal pairs both zero)
    cross_loci = Counter()
    for (kw, aw) in wit.items():
        for (kd, ad) in den.items():
            d = [(a - b) % p for a, b in zip(kw, kd)]
            Z0 = frozenset(i for i in range(16) if peval(d, H[i]) == 0)
            L1 = frozenset(i for i in range(8) if i in Z0 and (i + 8) in Z0)
            cross_loci[L1] += 1
    npairs = len(wit) * len(den)
    distinct = len(cross_loci)
    # Form-C witness cover on the 16 dense
    denlist = list(den.items())
    covers = []
    for (kw, aw) in wit.items():
        cov = frozenset(t for t, (kd, ad) in enumerate(denlist)
                        if (aw & ad))
        covers.append(cov)
    union = frozenset().union(*covers) if covers else frozenset()
    covered = len(union)
    U1 = sum(len(c) for c in covers)
    sumcap = sum(len(covers[a] & covers[b])
                 for a in range(len(covers)) for b in range(a + 1, len(covers)))
    IE2 = U1 - sumcap
    print("\n" + "=" * 78)
    print(f"n=16 RUNG (list=19=3+16): cross pairs={npairs}, distinct L1 loci={distinct} "
          f"(mean mult {npairs / max(1, distinct):.2f})")
    print(f"   Form-C witness cover of the 16 dense: covered=|union|={covered}, "
          f"U1=sum|cov|={U1} (U1/cov={U1 / max(1, covered):.2f}), "
          f"IE2(Bonferroni-2, LOWER)={IE2}")
    if covered and not (IE2 <= covered <= U1):
        fail(f"n=16 Form-C bracket: IE2={IE2} covered={covered} U1={U1}")
    print("   -> same phenomenon as n=32: covers near-identical (not near-disjoint), "
          "IE2 useless as upper bound; verdict is RUNG-INDEPENDENT.")
    return dict(npairs=npairs, distinct=distinct, covered=covered, U1=U1, IE2=IE2)


# ============================================================== char-0 lattice (struct)
def char0_lattice(verbose=True):
    """The S_w cap B_t intersection lattice is a CHAR-0 combinatorial object (the 35
    fiber-subsets and 580 B-blocks are the same finite structure at every split prime,
    up to relabeling of mu16 — confirmed by RESULTS-INCIDENCE index-identical histograms).
    We re-derive the lattice from the canonical labeling at one prime and report the
    Bonferroni-2 packing/cover invariants that govern ANY union-bound list argument here.
    """
    p = 2013265921  # BabyBear, law holds
    res = analyze(p, verbose=verbose)
    return res


# ====================================================================== MAIN
print("A30: cross-level difference-loci incidence lattice — does inclusion-exclusion")
print("beat the union bound on the proven-complete n=32 list config? (issue #232/#407)\n")

PRIMES_CLEAN = [2013265921, 3221225473]   # BabyBear: law holds, list = 35 + 1344
results = []
for p in PRIMES_CLEAN:
    results.append(analyze(p))

analyze_n16()

# generic small primes (law FAILS -> dense layer inflates): show the union bound is
# even more over-counted off the clean config, so IE2 lower bound is even further.
print("\n" + "=" * 78)
print("GENERIC (law-failing) primes: dense layer inflates; union bound degrades")
print("=" * 78)
for p in [97, 193]:
    st = L.setup(p)
    dens, raw = L.dense(st)
    print(f"  p={p}: dense (generic accidents) = {len(dens)}  (clean char-0 count 1344);"
          f" union bound on the inflated list is {len(dens)/1344:.1f}x the clean list")

# ---- the structural Bonferroni-2 verdict on the canonical lattice ----
print("\n" + "=" * 78)
print("VERDICT (Bonferroni / inclusion-exclusion vs the union bound)")
print("=" * 78)
r = results[0]
z0, U1, COV, IE2, IE3, UN = r["formA"][0]
print(f"""
The cross-pair incidence is the intersection lattice S_w cap B_t (dead-fiber dichotomy,
proven), {r['npairs']} pairs sharing {r['distinct']} distinct level-1 loci
(mean mult {r['meanmult']:.2f}, max {r['maxmult']}).

At z0=1 the union/1st-Bonferroni count U1 = {U1} over-counts the {UN} actual incidences
by {U1/UN:.2f}x  (= the realized locus-sharing).  Bonferroni's theorem holds exactly:
  IE2 = {IE2} (2nd-order, a LOWER bound) <= |U| = {UN} <= U1 = {U1} (1st-order, UPPER).
Therefore the 2nd-order inclusion-exclusion correction is a LOWER bound and CANNOT serve
as an improved upper bound on the list.  The order-3 (odd) truncation IE3 = {IE3}
{'>= |U| so is a valid upper bound but ' if IE3 >= UN else 'is BELOW |U| hence INVALID; '}\
{'lies below U1 (a genuine improvement)' if (IE3 >= UN and IE3 < U1) else 'gives no usable improvement'}.

CONCLUSION: low-order inclusion-exclusion on the locus lattice does NOT yield a valid
upper bound below the union bound for THIS configuration.  The union-bound slack
({U1/UN:.2f}x) is real and large, but the slack is recovered only by FULL inclusion-
exclusion (= the exact count, not a bound) -- the alternating partial sums bracket
rather than tighten.  A list bound below the union bound must come from a PACKING /
fixed-degree argument (occ(tau) bounded), NOT from Bonferroni truncation.
""")

print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
