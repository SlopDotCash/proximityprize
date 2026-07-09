#!/usr/bin/env python3
"""
wf407-w2 / D1-fibre PART 2: pin the SCALING of the deep-interior fibre count and
localize the char-p inflation.

Findings from probe 1:
 * char-0 worst-case fibre N_fib(n,a,t) = C(n/tau, a/tau), tau=2^ceil(log2 t)  (EXACT, 0 mism).
 * char-p inflation appears ONLY at t=2 (e1=0, the additive-energy E_2 defect) and VANISHES
   for all t>=3 in the thin regime.  The deep-interior count (t>=t0~n/log n) is tau~t,
   n/tau~log n, so a small-ambient binomial.

This probe settles:
 (1) Is t=2 EVER in the prize window?  t0 = ceil(H(rho)*n/mu).  t0 vs 2.
 (2) Scaling of the t=2 char-p inflation (the E_2 defect) in n -- is it linear or super-linear?
 (3) The EXACT deep-interior (t>=t0) char-0 worst-case scaling: closed-form max over the window.
 (4) char-p at deeper t (t=4,8) for n=32 thin -- confirm NO inflation at depth.
"""
import itertools, math
from math import comb, log2, ceil
from fractions import Fraction

def H2(rho):
    if rho <= 0 or rho >= 1: return 0.0
    return -rho*log2(rho) - (1-rho)*log2(1-rho)

def coset_union_form(n, a, t):
    if t <= 1: return comb(n, a)
    tau = 1 << ceil(log2(t))
    if a % tau or n % tau: return 0
    return comb(n // tau, a // tau)

# ---------------------------------------------------------------------------
print("="*78)
print("(1) Is t=2 (the only inflating depth) EVER in the prize window?  t0=ceil(H*n/mu)")
print("    Window-interior requires t >= t0.  If t0 > 2 ALWAYS at scale, t=2 is OUT-of-window.")
print("="*78)
print(f"  {'rho':>6} {'n':>6} {'mu':>3} {'t0':>5} {'t0>2?':>6}")
for rho in [Fraction(1,2), Fraction(1,4), Fraction(1,8), Fraction(1,16)]:
    for mu in [3,4,5,6,8,10,16,20,30,40]:
        n = 1 << mu
        t0 = max(2, ceil(H2(float(rho)) * n / mu))
        print(f"  {str(rho):>6} {n:>6} {mu:>3} {t0:>5} {'YES' if t0>2 else 'no(t0=2)':>6}")
    print()

# ---------------------------------------------------------------------------
print("="*78)
print("(3) EXACT deep-interior char-0 worst-case scaling (closed form), n up to 2^20.")
print("    worst over t>=t0, a in [t, n], a-t = k (window direction a=k+t).  Also UNRESTRICTED a.")
print("    The orchard pin uses a=k+t; the adversary's best uses any a>=t.")
print("="*78)
for rho in [Fraction(1,2), Fraction(1,4), Fraction(1,8)]:
    k_frac = rho
    print(f"\n--- rho={rho} ---")
    print(f"  {'n':>8} {'mu':>3} {'t0':>6} {'worst(a=k+t)':>13} {'worst(any a)':>13} {'wany/n':>8} {'wany/n^2':>9}")
    for mu in range(3, 21):
        n = 1 << mu
        k = int(rho*n)
        t0 = max(2, ceil(H2(float(rho)) * n / mu))
        # window direction: a = k+t
        w_pin = 0
        for t in range(t0, n-k+1):
            a = k+t
            if a <= n:
                w_pin = max(w_pin, coset_union_form(n, a, t))
        # unrestricted a (only need to test resonant tau | a; n/tau small so few choices)
        w_any = 0
        for t in range(t0, n+1):
            tau = 1 << ceil(log2(t))
            if n % tau: continue
            M = n // tau
            # maximize C(M, j) over j=a/tau with a>=t i.e. j>=t/tau (=1 since tau>=t) and a<=n
            jmax = M
            # the max binomial C(M,*) is at j=M//2; but constraint a>=t means j>=ceil(t/tau)=1
            best_j = M//2
            w_any = max(w_any, comb(M, best_j))
        print(f"  {n:>8} {mu:>3} {t0:>6} {w_pin:>13} {w_any:>13} "
              f"{w_any/n:>8.4f} {w_any/n**2:>9.5f}")

# ---------------------------------------------------------------------------
print("\n" + "="*78)
print("(3b) The deep-interior UNRESTRICTED worst case closed form: at t just below 2*t0,")
print("     tau can be as small as the least 2-power >= t0.  Worst C(n/tau, (n/tau)/2).")
print("     Track n/tau (the ambient) -- if it stays O(log n), the count is quasi-poly in log n,")
print("     i.e. n^{o(1)} -- SUB-linear, not super-linear.")
print("="*78)
for rho in [Fraction(1,2), Fraction(1,4)]:
    print(f"\n--- rho={rho} ---")
    print(f"  {'n':>10} {'mu':>3} {'t0':>7} {'min tau>=t0':>11} {'ambient n/tau':>13} {'C(amb,amb/2)':>14} {'log2(count)/mu':>14}")
    for mu in range(4, 31):
        n = 1 << mu
        t0 = max(2, ceil(H2(float(rho)) * n / mu))
        tau = 1 << ceil(log2(t0))    # smallest 2-power >= t0 gives largest ambient
        amb = n // tau
        cnt = comb(amb, amb//2)
        l2 = log2(cnt) if cnt>1 else 0.0
        print(f"  {n:>10} {mu:>3} {t0:>7} {tau:>11} {amb:>13} {cnt:>14} {l2/mu:>14.4f}")

# ---------------------------------------------------------------------------
print("\n" + "="*78)
print("(4) char-p at DEEPER t for n=32 thin prime: confirm NO inflation at depth.")
print("="*78)
def subgroup_modp(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n//2, p) != 1 and pow(x, n, p) == 1:
            return [pow(x, k, p) for k in range(n)]
    return None
def find_thin_prime(n, mmin):
    p = n*mmin + 1
    while True:
        if p>2 and all(p % d for d in range(2, int(p**0.5)+1)) and (p-1)%n==0:
            return p
        p += n
import cmath
def Nfib_char0(n, a, t, tol=1e-7):
    z = [cmath.exp(2j*math.pi*kk/n) for kk in range(n)]
    cnt=0
    for S in itertools.combinations(z, a):
        if all(abs(sum(x**j for x in S))<tol for j in range(1,t)): cnt+=1
    return cnt
def Nfib_modp(p, H, a, t):
    cnt=0
    for S in itertools.combinations(H, a):
        if all(sum(pow(x,j,p) for x in S)%p==0 for j in range(1,t)): cnt+=1
    return cnt

n=32; p=find_thin_prime(n,30); H=subgroup_modp(p,n)
print(f"  n={n}, thin prime p={p} (m={(p-1)//n}).  Selected (a,t): focus t in {{2,3,4,5,8}} (deep).")
print(f"  {'a':>3} {'t':>3} {'char0':>8} {'modp':>8} {'defect':>8}")
# only enumerate a few representative (a,t) -- full enum at n=32 is C(32,16)=6e8, too big for large a.
# pick small a (fast) at increasing t to see depth behavior, plus the t=2 inflation point.
for (a,t) in [(4,2),(4,3),(4,4),(6,2),(8,2),(8,3),(8,4),(8,5),(8,8),(10,2),(12,3),(12,4)]:
    c0 = Nfib_char0(n,a,t)
    cp = Nfib_modp(p,H,a,t)
    d=cp-c0
    flag = "" if d==0 else f"  <== INFLATION {d:+d} (depth t={t})"
    print(f"  {a:>3} {t:>3} {c0:>8} {cp:>8} {d:>+8}{flag}")

print("\nDONE.")
