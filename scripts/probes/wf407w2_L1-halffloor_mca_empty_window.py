#!/usr/bin/env python3
"""
wf407w2 / L1-halffloor — EXACT enumeration of the largest delta-window on which the
MCA bad event (ABF26 Def 4.3, exactly the in-tree `mcaEvent`) is EMPTY for ALL stacks
and ALL gamma, hence epsMCA(C, delta) = 0 <= eps*.

Thread claim under test (C1 follow-up): "delta* >= (1-rho)/2 is an UNCONDITIONAL
lower-window floor: every radius delta <= (1-rho)/2 is mca-good."

CAVEAT discovered in the in-tree analysis (Errors.lean L819-850, DISPROOF_LOG L3696):
- the UNCONDITIONAL Lean upper window via the O74 interleaved collapse only reaches
  delta < d/(4n) ~ (1-rho)/4 (the radius DOUBLES because C^{=2} must be unique-
  decodable at 2*delta).
- and mcaEvent can co-occur with jointProximity even under UDR (2*delta*n < d_min).

So we settle EXACTLY: for small RS / linear codes, what is the largest delta with
epsMCA(C,delta)=0? Does it equal (1-rho)/2, (1-rho)/4, or something else?

mcaEvent C delta u0 u1 gamma :=
  exists S, |S| >= (1-delta)*n  AND
    (exists w in C, forall i in S, w i = u0 i + gamma * u1 i)   [line agrees with a codeword on S]
    AND  NOT pairJointAgreesOn C S u0 u1                         [no codeword PAIR agrees with (u0,u1) on S]

The OPTIMAL witness S for "exists codeword w agreeing with the line on S" is the agreement
set of the line with its closest codeword: S = {i : w*(i) = (u0+gamma u1)(i)} for the best w.
For "NOT pairJointAgreesOn on S" we must check every codeword pair (v0,v1) does NOT agree
with (u0,u1) on all of S. We enumerate S = agreement set of line with each codeword w
(monotone: larger S is harder to satisfy the NOT clause but the size clause prefers larger S;
mcaEvent is existential over S, so it fires iff SOME valid S works -> we check, for each w,
the MAXIMAL agreement set A_w = {i: w i = line i}; any S subset A_w with |S|>=(1-delta)n is a
candidate; pairJointAgreesOn is MONOTONE-down in S, so NOT-pairJointAgrees is monotone-UP:
easier on larger S. So the best S = A_w itself if |A_w| >= (1-delta)n. mcaEvent fires iff
exists w in C with |A_w| >= (1-delta)n AND NOT pairJointAgreesOn C A_w u0 u1.)

Actually pairJointAgreesOn C S u0 u1 is ANTITONE in S (larger S -> harder to agree on all of S
-> LESS likely true) so NOT-pairJointAgrees is MONOTONE in S (larger S -> more likely the NOT).
And the size clause |S|>=(1-delta)n also prefers large S. So taking S = A_w (the full agreement
set of line with w) is OPTIMAL for firing mcaEvent for that w. We then also must allow shrinking
S only if pairJointAgrees on A_w but not on a sub-S; but shrinking S makes pairJointAgrees MORE
likely (antitone), so a sub-S can only ever make NOT-pairJointAgrees FALSE more often, never
help. => S = A_w is the unique best candidate per w. mcaEvent <=> exists w: |A_w|>=(1-delta)n
and not pairJointAgrees on A_w.   [verified below by also brute-forcing all subsets at small n]
"""
import itertools, sys
from fractions import Fraction

def rs_code(p, n, k, xs):
    """Reed-Solomon: evaluations of all deg<k polys at points xs (n distinct pts in F_p)."""
    code = []
    for coeffs in itertools.product(range(p), repeat=k):
        cw = tuple(sum(coeffs[j]*pow(x, j, p) for j in range(k)) % p for x in xs)
        code.append(cw)
    return code

def agree_set(a, b, n):
    return frozenset(i for i in range(n) if a[i] == b[i])

def line(u0, u1, gamma, p, n):
    return tuple((u0[i] + gamma*u1[i]) % p for i in range(n))

def pair_joint_agrees_on(code, S, u0, u1):
    """exists v0,v1 in code, forall i in S, v0 i = u0 i and v1 i = u1 i."""
    # split: v0 must agree with u0 on S, v1 must agree with u1 on S (independent)
    has_v0 = any(all(v0[i] == u0[i] for i in S) for v0 in code)
    if not has_v0:
        return False
    has_v1 = any(all(v1[i] == u1[i] for i in S) for v1 in code)
    return has_v1

def mca_event_fires(code, n, u0, u1, gamma, p, t):
    """t = ceil((1-delta)*n) integer floor on |S|. mcaEvent fires for some valid S.
       Uses S = A_w optimal argument; also we double-check correctness against brute subsets
       in the small verifier below."""
    ln = line(u0, u1, gamma, p, n)
    for w in code:
        A = agree_set(w, ln, n)
        if len(A) >= t:
            if not pair_joint_agrees_on(code, A, u0, u1):
                return True
    return False

def mca_event_fires_brute(code, n, u0, u1, gamma, p, t):
    """Brute force over ALL subsets S of size >= t (verifier, small n only)."""
    ln = line(u0, u1, gamma, p, n)
    idx = list(range(n))
    for size in range(t, n+1):
        for S in itertools.combinations(idx, size):
            Sset = frozenset(S)
            # clause: exists w in code agreeing with line on S
            if not any(all(w[i] == ln[i] for i in S) for w in code):
                continue
            if not pair_joint_agrees_on(code, Sset, u0, u1):
                return True
    return False

def min_distance(code, n):
    d = n
    for a, b in itertools.combinations(code, 2):
        dd = sum(1 for i in range(n) if a[i] != b[i])
        d = min(d, dd)
    return d

def analyze(p, n, k, xs, verify=False, sample_stacks=None):
    code = rs_code(p, n, k, xs)
    d = min_distance(code, n)
    rho = Fraction(k, n)
    # candidate floors
    half = (1 - rho) / 2     # (1-rho)/2
    quarter = (1 - rho) / 4  # (1-rho)/4
    # We sweep delta over the rationals j/n for j=0..n (t = ceil((1-delta)n) = n-j when delta=j/n).
    # epsMCA(C,delta)=0  <=>  for ALL stacks (u0,u1), for ALL gamma, mcaEvent does NOT fire.
    stacks = [(u0, u1) for u0 in code_or_all(p, n, full=True)
                       for u1 in code_or_all(p, n, full=True)]
    # full stack space is p^(2n) -- too big. Restrict to a meaningful but exhaustive-enough set:
    # the worst case stacks are arbitrary words u0,u1 in F_p^n. We enumerate ALL when feasible,
    # else sample. We'll enumerate all for tiny (p,n).
    total_stacks = p**(2*n)
    if sample_stacks is None and total_stacks <= 200000:
        gen = ((u0, u1) for u0 in itertools.product(range(p), repeat=n)
                        for u1 in itertools.product(range(p), repeat=n))
        mode = f"EXHAUSTIVE ({total_stacks} stacks)"
    else:
        import random
        random.seed(12345)
        S = sample_stacks or 30000
        def rg():
            for _ in range(S):
                yield (tuple(random.randrange(p) for _ in range(n)),
                       tuple(random.randrange(p) for _ in range(n)))
        gen = rg()
        mode = f"SAMPLED ({sample_stacks or 30000} stacks of {total_stacks})"

    # For each delta = j/n, record whether epsMCA = 0 (no fire anywhere).
    # We compute: for each stack, the smallest |S|-threshold t at which a fire occurs;
    # equivalently the largest t (=> smallest delta) at which mcaEvent still fires.
    # mcaEvent fires for t  iff exists gamma,w with |A_w(gamma)| >= t and not pairJoint on A_w.
    # The "firing radius" of a stack = max over (gamma,w) of |A_w| s.t. not pairJoint(A_w).
    # If firing radius = r*, then fires for all t <= r*. delta = (n-t)/n, so smaller t = larger delta.
    # epsMCA(delta)=0 iff t > r* for all stacks, i.e. (n - delta*n) > max_stack r*, i.e.
    #   t = ceil((1-delta)n) > r*  <=>  delta < (n - r*)/n  ... we want largest delta with eps=0.
    # We track the GLOBAL max firing-S-size r_global over all stacks/gamma/w.
    r_global = -1
    worst_witness = None
    gammas = list(range(p))
    checked = 0
    for (u0, u1) in gen:
        checked += 1
        for gamma in gammas:
            ln = line(u0, u1, gamma, p, n)
            for w in code:
                A = agree_set(w, ln, n)
                if len(A) <= r_global:
                    continue
                if not pair_joint_agrees_on(code, A, u0, u1):
                    if len(A) > r_global:
                        r_global = len(A)
                        worst_witness = (u0, u1, gamma, w, len(A))
    # epsMCA(delta)=0 requires t=ceil((1-delta)n) > r_global, i.e. (1-delta)n > r_global (ceil),
    # the largest INTEGER t that fails is r_global, so the largest mca-EMPTY t is r_global+1,
    # i.e. ceil((1-delta)n) >= r_global+1. The corresponding largest delta (rational j/n grid):
    #   t = n - j (delta = j/n) => fires up to t = r_global. Empty for t >= r_global+1, i.e.
    #   n - j >= r_global + 1  => j <= n - r_global - 1. largest good j = n - r_global - 1.
    j_good = n - r_global - 1
    delta_empty_max = Fraction(j_good, n) if j_good >= 0 else Fraction(-1, 1)
    # The continuous threshold: mcaEvent first fires (over this stack set) at the smallest delta
    # with ceil((1-delta)n) <= r_global, i.e. (1-delta)n <= r_global is NOT quite (ceil). Use grid.

    result = {
        'p': p, 'n': n, 'k': k, 'd': d, 'rho': rho,
        'half': half, 'quarter': quarter,
        'mode': mode, 'checked': checked,
        'r_global': r_global, 'worst_witness': worst_witness,
        'delta_empty_max': delta_empty_max,
        'quarter_minus_oneover4n': quarter,  # (n-e)/(4n) form below
    }
    # verifier: confirm S=A_w optimal == brute force on a few random stacks
    if verify:
        import random
        random.seed(7)
        mism = 0
        for _ in range(40):
            u0 = tuple(random.randrange(p) for _ in range(n))
            u1 = tuple(random.randrange(p) for _ in range(n))
            for gamma in gammas:
                for t in range(0, n+1):
                    a = mca_event_fires(code, n, u0, u1, gamma, p, t)
                    b = mca_event_fires_brute(code, n, u0, u1, gamma, p, t)
                    if a != b:
                        mism += 1
        result['verifier_mismatches'] = mism
    return result

def code_or_all(p, n, full=True):
    # placeholder; not used (we enumerate inline). kept for signature.
    return []

def fmt(fr):
    return f"{float(fr):.4f} (={fr})"

if __name__ == "__main__":
    print("="*92)
    print("wf407w2 / L1-halffloor : EXACT largest mca-EMPTY delta-window vs (1-rho)/2 and (1-rho)/4")
    print("="*92)
    # tiny exhaustive RS instances
    configs = [
        # (p, n, k, xs, verify)
        (5, 4, 2, [0,1,2,3], True),    # rho=1/2, d=3
        (5, 4, 1, [0,1,2,3], True),    # rho=1/4, d=4
        (7, 4, 2, [0,1,2,3], True),    # rho=1/2, d=3
        (7, 4, 1, [0,1,2,3], True),    # rho=1/4, d=4
        (7, 5, 2, [0,1,2,3,4], False), # rho=2/5, d=4  (p^10 too big -> sampled)
        (5, 6, 2, [0,1,2,3,4],False),  # n=6 over F5 needs 6 distinct pts -> only 5; skip handled
    ]
    for cfg in configs:
        p, n, k, xs, verify = cfg
        if len(set(xs)) < n or any(x >= p for x in xs):
            print(f"\n[skip] p={p} n={n}: need {n} distinct points in F_{p}")
            continue
        sample = None if p**(2*n) <= 200000 else 8000
        r = analyze(p, n, k, xs, verify=verify, sample_stacks=sample)
        print(f"\n--- RS[F{p}, n={n}, k={k}]   rho={r['rho']}  d_min={r['d']}  ({r['mode']}) ---")
        print(f"    candidate floors:  (1-rho)/2 = {fmt(r['half'])}    (1-rho)/4 = {fmt(r['quarter'])}")
        print(f"    largest mca-EMPTY delta (eps_mca=0):  {fmt(r['delta_empty_max'])}   "
              f"[r_global={r['r_global']}]")
        ww = r['worst_witness']
        if ww:
            print(f"    first-firing witness: gamma={ww[2]}, |A_w|={ww[4]} "
                  f"(=> fires at delta=(n-|A_w|)/n={Fraction(n-ww[4],n)})")
        # comparisons
        de = r['delta_empty_max']
        print(f"    EMPTY-window vs (1-rho)/2 : {fmt(de)} {'>=' if de>=r['half'] else '<'} {fmt(r['half'])}"
              f"   => half-floor {'HOLDS' if de>=r['half'] else 'FAILS'} (mca empty up to it)")
        print(f"    EMPTY-window vs (1-rho)/4 : {fmt(de)} {'>=' if de>=r['quarter'] else '<'} {fmt(r['quarter'])}"
              f"   => quarter-floor {'HOLDS' if de>=r['quarter'] else 'FAILS'}")
        if 'verifier_mismatches' in r:
            print(f"    [S=A_w optimality verifier vs brute subsets: {r['verifier_mismatches']} mismatches]")
    print("\n" + "="*92)
    print("INTERPRETATION:")
    print(" - 'largest mca-EMPTY delta' is the EXACT unconditional floor where epsMCA(C,delta)=0.")
    print(" - If it equals (1-rho)/2 -> the half-floor is the true empty-window floor.")
    print(" - If it equals (1-rho)/4 -> the half-floor OVERSHOOTS; only the quarter-floor is empty.")
    print("="*92)
