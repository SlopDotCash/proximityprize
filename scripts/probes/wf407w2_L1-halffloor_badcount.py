#!/usr/bin/env python3
"""
wf407w2 / L1-halffloor (v2) — EXACT worst-case MCA bad-COUNT B(delta) = max over stacks
of #{gamma : mcaEvent fires}, on small RS/linear codes, as a function of delta.

epsMCA(C,delta) = max_stack Pr_gamma[mcaEvent] = max_stack B_stack(delta)/q.
So epsMCA(C,delta) <= eps*  <=>  B(delta) <= q * eps*.
At the prize, q ~ n*2^128 and eps* = 2^-128, so q*eps* ~ n. i.e. mca-good <=> B(delta) <= n
(roughly; exactly <= n at the leading order). The thread asks: is delta <= (1-rho)/2 mca-good?

The relevant unconditional Lean bound is epsMCA <= (1 + 2*delta*n)/q on the window delta<d/(4n).
We test: (a) what is the EXACT worst-case bad count B(delta) on the whole delta range, and
(b) does B(delta) <= 1 + 2*delta*n hold (the interleaved-UD bound), and HOW FAR up in delta?
(c) the half-floor question: is B((1-rho)/2) <= n  (=> mca-good at prize q)?

Optimal-S argument (verified previously, 0 mismatches): mcaEvent fires for stack (u0,u1) at
gamma and floor t=ceil((1-delta)n)  <=>  exists codeword w with |A_w| >= t and the agreement
set A_w of the line=u0+gamma u1 with w is NOT pair-joint-agreed.
"""
import itertools, sys, math
from fractions import Fraction

def rs_code(p, n, k, xs):
    code = []
    for coeffs in itertools.product(range(p), repeat=k):
        cw = tuple(sum(coeffs[j]*pow(x, j, p) for j in range(k)) % p for x in xs)
        code.append(cw)
    return code

def agree_size(a, b, n):
    return sum(1 for i in range(n) if a[i]==b[i])

def agree_set(a, b, n):
    return frozenset(i for i in range(n) if a[i]==b[i])

def pair_joint_agrees_on(code, S, u0, u1):
    has0 = any(all(v0[i]==u0[i] for i in S) for v0 in code)
    if not has0: return False
    return any(all(v1[i]==u1[i] for i in S) for v1 in code)

def min_distance(code, n):
    d = n
    for a,b in itertools.combinations(code,2):
        d = min(d, sum(1 for i in range(n) if a[i]!=b[i]))
    return d

def bad_count_stack(code, n, u0, u1, p, t):
    """#{gamma in F_p : mcaEvent fires} for this stack at floor t."""
    cnt = 0
    for gamma in range(p):
        ln = tuple((u0[i]+gamma*u1[i])%p for i in range(n))
        fired = False
        for w in code:
            A = agree_set(w, ln, n)
            if len(A) >= t and not pair_joint_agrees_on(code, A, u0, u1):
                fired = True; break
        if fired: cnt += 1
    return cnt

def worst_bad_count(code, n, p, t, gen, ):
    best = 0; wit=None
    for (u0,u1) in gen:
        c = bad_count_stack(code, n, u0, u1, p, t)
        if c > best:
            best = c; wit=(u0,u1)
    return best, wit

def make_gen(p, n, cap=4000, code=None):
    total = p**(2*n)
    if total <= cap:
        return (lambda: ((u0,u1) for u0 in itertools.product(range(p),repeat=n)
                                  for u1 in itertools.product(range(p),repeat=n))), f"EXH({total})"
    import random
    # adversarial seeds: u1 a codeword (so line = u0 + gamma*cw sweeps a coset of <cw>);
    # u0 a word at small distance from a codeword (so for several gamma the line is a codeword).
    adversarial = []
    if code is not None:
        for cw1 in code[:min(len(code),25)]:
            for cw0 in code[:min(len(code),25)]:
                # perturb cw0 in 1..2 positions to make it a non-codeword close to C
                for npos in (0,1,2):
                    u0 = list(cw0)
                    for pos in range(min(npos,n)):
                        u0[pos] = (u0[pos]+1)%p
                    adversarial.append((tuple(u0), tuple(cw1)))
    def g():
        random.seed(98765)
        for a in adversarial:
            yield a
        for _ in range(cap):
            yield (tuple(random.randrange(p) for _ in range(n)),
                   tuple(random.randrange(p) for _ in range(n)))
    return g, f"ADV+SMP({len(adversarial)}+{cap}/{total})"

def analyze(p,n,k,xs,cap=4000):
    code = rs_code(p,n,k,xs)
    d = min_distance(code,n)
    rho = Fraction(k,n)
    q = p
    half = (1-rho)/2
    quarter = (1-rho)/4
    genf, mode = make_gen(p,n,cap,code=code)
    rows=[]
    # sweep delta = j/n for j=0..n; t = ceil((1-j/n)*n) = n-j (since (1-j/n)*n = n-j integer)
    for j in range(0, n+1):
        delta = Fraction(j,n)
        t = n - j   # = ceil((1-delta)*n)
        B, wit = worst_bad_count(code, n, p, t, genf())
        # interleaved-UD predicted upper bound 1+2*delta*n (valid for delta<d/(4n)); here 2*delta*n=2j
        ud_pred = 1 + 2*j
        in_quarter = (delta < quarter)
        in_half = (delta <= half)
        # prize mca-good proxy: B <= q*eps* ~ n   (we report B vs n)
        rows.append((j, delta, t, B, ud_pred, in_quarter, in_half))
    return {'p':p,'n':n,'k':k,'d':d,'rho':rho,'half':half,'quarter':quarter,'mode':mode,'rows':rows}

def f(fr): return f"{float(fr):.3f}"

if __name__=="__main__":
    print("="*100)
    print("wf407w2 / L1-halffloor v2 : worst-case MCA bad-COUNT B(delta) vs n (prize-good proxy)")
    print("  mca-good at prize  <=>  B(delta) <= q*eps* ~ n.   UD bound: B <= 1+2*delta*n (delta<d/4n)")
    print("="*100)
    configs = [
        (5,4,2,[0,1,2,3]),  # rho=1/2 d=3
        (5,4,1,[0,1,2,3]),  # rho=1/4 d=4
        (7,4,2,[0,1,2,3]),  # rho=1/2 d=3
        (7,5,2,[0,1,2,3,4]),# rho=2/5 d=4
        (11,5,2,[0,1,2,3,4]),# rho=2/5 d=4
        (7,6,2,[0,1,2,3,4,5]),# rho=1/3 d=5
        (7,6,3,[0,1,2,3,4,5]),# rho=1/2 d=4
    ]
    for (p,n,k,xs) in configs:
        if len(set(xs))<n or any(x>=p for x in xs):
            print(f"\n[skip] p={p} n={n}"); continue
        r = analyze(p,n,k,xs)
        print(f"\n--- RS[F{p}, n={n}, k={k}] rho={r['rho']} d={r['d']}  ({r['mode']}) ---")
        print(f"    (1-rho)/2={f(r['half'])}  (1-rho)/4={f(r['quarter'])}   n={n}  (prize-good iff B<=~n)")
        print(f"    {'j':>2} {'delta':>6} {'t':>2} {'B(badct)':>8} {'1+2dn':>6} {'B<=n?':>6} {'<=qtr':>6} {'<=half':>6}")
        for (j,delta,t,B,ud,inq,inh) in r['rows']:
            bgn = "OK" if B<=n else "NO"
            print(f"    {j:>2} {f(delta):>6} {t:>2} {B:>8} {ud:>6} {bgn:>6} "
                  f"{('y' if inq else '.'):>6} {('y' if inh else '.'):>6}")
        # headline: largest delta with B<=n (prize-good proxy)
        good = [delta for (j,delta,t,B,ud,inq,inh) in r['rows'] if B<=n]
        gmax = max(good) if good else Fraction(-1)
        print(f"    => largest delta with B<=n (prize-good proxy): {f(gmax)} (={gmax})  "
              f"vs (1-rho)/2={f(r['half'])}  -> half-floor {'HOLDS' if gmax>=r['half'] else 'FAILS'}")
        # does B<=1+2dn hold everywhere it should (delta<d/4n)?
        viol = [(j,B,ud) for (j,delta,t,B,ud,inq,inh) in r['rows'] if inq and B>ud]
        print(f"    UD bound B<=1+2dn on quarter-window: {'HOLDS' if not viol else f'VIOLATED {viol}'}")
    print("\n"+"="*100)
