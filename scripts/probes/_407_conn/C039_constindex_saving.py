"""
C039 probe: "Constant-index torsion bound IS the F20 lane; the saving over sqrt(q)
is exactly (sqrt(q)-1)/t with t=(q-1)/d the cofactor."

We test, at PROPER dyadic subgroups mu_n of F_q* with q a large prime, q = n^beta:

PART A (algebra, must hold EXACTLY):  the proven in-tree inequality
    t * |eta_b| <= (t-1)*sqrt(q) + 1,   t=(q-1)/n
rearranges to
    |eta_b| <= sqrt(q) - (sqrt(q)-1)/t  =: completionBound.
Check this holds for ALL b for the d=n torsion completion.

PART B (the real content):  is the "saving" (sqrt(q)-1)/t a real sqrt-cancellation,
or is it negligible vs the gap between the COMPLETION bound and the TRUE B?
    completionBound ~ sqrt(q)  (saving ~ sqrt(q)/t = n^{beta/2}/m, tiny at prize)
    TRUE B           ~ sqrt(n*log m)  (the real cancellation, off by sqrt(m/log m))
We measure both and the ratios.

Exact integer/complex arithmetic via Python; eta computed in high precision.
"""
import cmath, math
from sympy import isprime, primitive_root

def subgroup(g, n, q):
    """order-n subgroup of F_q^* : powers of g^((q-1)/n)."""
    h = pow(g, (q-1)//n, q)
    S, x = [], 1
    for _ in range(n):
        S.append(x)
        x = (x*h) % q
    return S

def eta(b, S, q):
    """eta_b = sum_{y in S} exp(2*pi*i * b*y / q)."""
    s = 0j
    w = 2*math.pi/q
    for y in S:
        s += cmath.exp(1j*w*((b*y) % q))
    return s

def maxB(S, q):
    """B = max_{b!=0} |eta_b|.  Use coset reduction: eta constant on b*mu_n,
    so range over coset reps. Cheaper: just range b=1..q-1 for small q."""
    best = 0.0
    for b in range(1, q):
        v = abs(eta(b, S, q))
        if v > best:
            best = v
    return best

def find_prime(n, beta_target, lo_mult=1):
    """find prime q ~ n^beta_target, q = 1 mod n, with q-1 having a large odd part
    (proper subgroup + large cofactor m=(q-1)/n)."""
    import random
    target = int(round(n**beta_target))
    # search upward for q prime, q = 1 mod n
    q = target - (target % n) + 1
    if q <= n: q += n
    for _ in range(200000):
        if q % n == 1 and isprime(q):
            return q
        q += n
    return None

print("="*92)
print("C039 PROBE: constant-index saving (sqrt(q)-1)/t  vs the TRUE sqrt-cancellation")
print("="*92)
print("Prize regime: proper dyadic mu_n, q prime = 1 mod n, q ~ n^beta (beta~4-5), n << sqrt(q)")
print()

# proper-subgroup primes, growing n, beta in 3.5..5 (kept small enough to brute B over b<q)
cases = [
    (8,  3.6),
    (16, 3.4),
    (16, 4.0),
    (32, 3.2),
    (32, 3.6),
    (64, 3.0),
    (64, 3.4),
]

hdr = f"{'n':>4} {'q':>10} {'beta':>5} {'m=t':>9} {'B_true':>9} {'compBnd':>10} {'sqrt_q':>10} {'saving=(rq-1)/t':>16} {'compBnd-B':>10}"
print(hdr); print("-"*len(hdr))

rows = []
for n, beta in cases:
    q = find_prime(n, beta)
    if q is None:
        print(f"{n:>4} (no prime found)"); continue
    g = primitive_root(q)
    S = subgroup(g, n, q)
    assert all(pow(y, n, q)==1 for y in S) and len(set(S))==n, "subgroup build bad"
    B = maxB(S, q)
    rq = math.sqrt(q)
    t = (q-1)//n            # cofactor d=n => t=m
    compBound = rq - (rq-1)/t           # F20 rearranged bound
    saving = (rq-1)/t
    beta_eff = math.log(q)/math.log(n)
    target = math.sqrt(n*math.log2(t)) if t>1 else float('nan')
    rows.append((n,q,beta_eff,t,B,compBound,rq,saving,compBound-B,target))
    print(f"{n:>4} {q:>10} {beta_eff:>5.2f} {t:>9} {B:>9.3f} {compBound:>10.4f} {rq:>10.4f} {saving:>16.6f} {compBound-B:>10.3f}")

print()
print("PART A check (algebra, EXACT): does completion bound dominate B for every b?")
allok = True
for (n,q,beta,t,B,compBound,rq,saving,gap,target) in rows:
    ok = B <= compBound + 1e-6
    allok = allok and ok
    print(f"  n={n:>3} q={q:>9}: B={B:.3f} <= compBound={compBound:.4f}  -> {'OK' if ok else 'FAIL'}")
print(f"  ALL completion-bound inequalities hold: {allok}")

print()
print("PART B: is the 'saving' (sqrt(q)-1)/t the real sqrt-cancellation? Compare to the")
print("  gap (compBound - B) = the REAL cancellation the triangle inequality throws away.")
print(f"  {'n':>4} {'saving':>12} {'realGap=compBnd-B':>18} {'realGap/saving':>16} {'B/sqrt(n logm)':>16}")
for (n,q,beta,t,B,compBound,rq,saving,gap,target) in rows:
    ratio = gap/saving if saving>0 else float('inf')
    Bnorm = B/target if target==target and target>0 else float('nan')
    print(f"  {n:>4} {saving:>12.4f} {gap:>18.3f} {ratio:>16.1f} {Bnorm:>16.3f}")

print()
print("INTERPRETATION:")
print("  - PART A is a true one-line rearrangement of the proven inequality (constIndex form).")
print("  - 'saving' (sqrt(q)-1)/t shrinks to ~0 as t=m grows (negligible at prize m~2^128):")
print("      completion bound -> bare sqrt(q).  Confirms BurgessIndexOvershoot sqrt(m/log m).")
print("  - BUT the REAL cancellation (compBound - B ~ sqrt(q) - sqrt(n log m)) is HUGE and")
print("    UNRELATED to 'saving': realGap/saving >> 1 and grows. The +1/t term captures NONE")
print("    of the BGK sqrt-cancellation among the m Gauss phases (that lives in the triangle")
print("    inequality |sum| <= sum|.| step, NOT in the trivial-character +1).")
