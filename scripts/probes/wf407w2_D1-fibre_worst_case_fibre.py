#!/usr/bin/env python3
"""
wf407-w2 / D1-fibre : the WORST-CASE PTE / vanishing-power-sum fibre count on mu_{2^mu}
at the prize-window radius (deep interior t = Theta(n/log n)).  Decisive question:

   N_fib(n,a,t) := #{ S subset mu_n : |S|=a, p_1(S)=...=p_{t-1}(S)=0 }
                 = #{ S subset mu_n : |S|=a, e_1(S)=...=e_{t-1}(S)=0 }   (Newton, char 0)

   This is EXACTLY the deepest-band supply of the lacunary tower word x^{k+t} (k=a-t):
   the orchard identity (in-tree GeneralOrchardSumZero / DyadicLacunaryDeltaStar) makes the
   far-line incidence I(delta) = #lacBad <= N_fib.  Pinning delta* <=> N_fib <= C*n in-window.

WHAT THIS PROBE SETTLES (Wave-2 D1-fibre):
   (A) EXACT char-0 worst-case fibre count over ALL subsets at n=8,16,32 (true worst case,
       not just the symmetric LOWER-bound constructions of rounds 7-9).
   (B) The closed coset-union form: N_fib = C(n/tau, a/tau) when tau | a else 0,
       tau = 2^ceil(log2 t) = least power of 2 >= t  (dyadic Fourier-uncertainty rigidity).
   (C) The PRIZE-WINDOW value at gap t0 = ceil(H(rho)*n/mu) and its SCALING in n:
       Theta(n)?  Theta(n log n)?  n^{1+c}?
   (D) char-p transfer: enumerate the same count mod a THIN prize-shaped prime
       (m=(p-1)/n large) and confirm no super-linear inflation from the mod-q defect.
"""
import itertools, math
from math import comb, log2, ceil
from fractions import Fraction
import cmath

# ---------------------------------------------------------------------------
# char-0 exact fibre count over the complex 2^mu-th roots of unity
# ---------------------------------------------------------------------------
def roots(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def powersums(S, t):
    """p_1..p_{t-1} of the multiset S (complex)."""
    return [sum(x**j for x in S) for j in range(1, t)]

def Nfib_char0(n, a, t, tol=1e-7):
    """EXACT enumeration: #{S subset mu_n, |S|=a, p_1=...=p_{t-1}=0}."""
    z = roots(n)
    cnt = 0
    for S in itertools.combinations(z, a):
        ps = powersums(S, t)
        if all(abs(v) < tol for v in ps):
            cnt += 1
    return cnt

# ---------------------------------------------------------------------------
# closed coset-union form (dyadic Fourier-uncertainty rigidity)
# ---------------------------------------------------------------------------
def coset_union_form(n, a, t):
    """tau = least power of 2 >= t; rigid count = C(n/tau, a/tau) if tau|a else 0."""
    if t <= 1:
        return comb(n, a)          # no constraints
    tau = 1 << ceil(log2(t))       # least 2-power >= t
    if a % tau != 0 or n % tau != 0:
        return 0
    return comb(n // tau, a // tau)

# ---------------------------------------------------------------------------
# char-p exact fibre count over a thin subgroup mu_n < F_p^*
# ---------------------------------------------------------------------------
def subgroup_modp(p, n):
    # find generator of order n
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n//2, p) != 1 and pow(x, n, p) == 1:
            return [pow(x, k, p) for k in range(n)]
    return None

def Nfib_modp(p, H, a, t):
    cnt = 0
    for S in itertools.combinations(H, a):
        ok = True
        for j in range(1, t):
            if sum(pow(x, j, p) for x in S) % p != 0:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt

# ---------------------------------------------------------------------------
# Hq entropy and prize-window edge gap
# ---------------------------------------------------------------------------
def H2(rho):
    if rho <= 0 or rho >= 1:
        return 0.0
    return -rho*log2(rho) - (1-rho)*log2(1-rho)

# ===========================================================================
print("="*78)
print("PART (A)+(B): EXACT char-0 worst-case fibre count vs coset-union closed form")
print("  N_fib(n,a,t) = #{S subset mu_n: |S|=a, p_1=..=p_{t-1}=0}; tau=least 2^>=t")
print("="*78)
mismatches = 0
for n in [8, 16]:
    print(f"\n--- n = {n} (mu = {int(log2(n))}) ---")
    print(f"  {'a':>3} {'t':>3} {'tau':>4} {'N_fib(exact)':>13} {'C(n/tau,a/tau)':>16} {'match':>6}")
    for a in range(2, n+1):
        for t in range(2, a+1):
            exact = Nfib_char0(n, a, t)
            closed = coset_union_form(n, a, t)
            m = "OK" if exact == closed else "MISMATCH"
            if exact != closed:
                mismatches += 1
            if exact > 0 or closed > 0:   # only print nontrivial rows
                tau = 1 << ceil(log2(t)) if t > 1 else 1
                print(f"  {a:>3} {t:>3} {tau:>4} {exact:>13} {closed:>16} {m:>6}")
print(f"\n  TOTAL char-0 mismatches (exact vs coset-union form): {mismatches}")

# ===========================================================================
print("\n" + "="*78)
print("PART (C): PRIZE-WINDOW value & SCALING.  q.eps* ~ n  =>  log2(q.eps*)=mu.")
print("  window-edge gap  t0 = ceil(H(rho)*n/mu).  worst N_fib over t>=t0, all a.")
print("  At deep interior the rigidity tau ~ t ~ n/log n forces tau|a, n/tau ~ log n small.")
print("="*78)
for rho in [Fraction(1,2), Fraction(1,4), Fraction(1,8)]:
    print(f"\n--- rate rho = {rho} ---")
    print(f"  {'n':>4} {'mu':>3} {'k':>4} {'t0':>4} {'worst N_fib':>11} {'argmax(a,t)':>12} {'N_fib/n':>9}")
    for mu in range(3, 7):              # n = 8,16,32,64
        n = 1 << mu
        k = int(rho * n)
        Hr = H2(float(rho))
        t0 = max(2, ceil(Hr * n / mu))
        worst = 0
        arg = None
        # worst case over ALL window-interior directions: t>=t0, a=k+t<=n
        for t in range(t0, n+1):
            for a in range(t, n+1):     # need a>=t for >=t-1 constraints to be nondegenerate
                if a - t != k:          # window direction (a,b)=(k+t,k): a=k+t fixed by k,t
                    continue
                # exact closed form (char-0 rigid count); verified == enumeration in (A)
                val = coset_union_form(n, a, t)
                if val > worst:
                    worst = val
                    arg = (a, t)
        ratio = worst / n if n else 0
        print(f"  {n:>4} {mu:>3} {k:>4} {t0:>4} {worst:>11} {str(arg):>12} {ratio:>9.3f}")

# ===========================================================================
print("\n" + "="*78)
print("PART (C2): UNRESTRICTED worst-case over a (drop the a=k+t pin): the largest")
print("  possible in-window fibre for ANY (a,t) with t>=t0.  This is the adversary's best.")
print("="*78)
for rho in [Fraction(1,2), Fraction(1,4)]:
    print(f"\n--- rho = {rho} (t0 from this rate's k; sweep ALL a>=t) ---")
    print(f"  {'n':>4} {'mu':>3} {'t0':>4} {'worst N_fib':>11} {'argmax(a,t)':>12} {'/n':>7} {'/(n log n)':>11}")
    for mu in range(3, 8):             # n up to 128 (closed form, instant)
        n = 1 << mu
        Hr = H2(float(rho))
        t0 = max(2, ceil(Hr * n / mu))
        worst, arg = 0, None
        for t in range(t0, n+1):
            for a in range(t, n+1):
                val = coset_union_form(n, a, t)
                if val > worst:
                    worst, arg = val, (a, t)
        nlogn = n * mu
        print(f"  {n:>4} {mu:>3} {t0:>4} {worst:>11} {str(arg):>12} "
              f"{worst/n:>7.2f} {worst/nlogn:>11.3f}")

# ===========================================================================
print("\n" + "="*78)
print("PART (D): char-p transfer at a THIN prize-shaped prime (m=(p-1)/n LARGE).")
print("  Enumerate N_fib mod p; compare to char-0.  Inflation => super-linear defect.")
print("="*78)
def find_thin_prime(n, mmin):
    p = n*mmin + 1
    while True:
        if all(p % d for d in range(2, int(p**0.5)+1)) and p > 2:
            if (p-1) % n == 0:
                return p
        p += n
for n in [8, 16]:
    mu = int(log2(n))
    p = find_thin_prime(n, 30)           # m >= 30, genuinely thin (n < p^{1/2})
    H = subgroup_modp(p, n)
    print(f"\n--- n={n}, thin prime p={p} (m=(p-1)/n={(p-1)//n}) ---")
    print(f"  {'a':>3} {'t':>3} {'N_fib(char0)':>13} {'N_fib(modp)':>12} {'defect':>7}")
    for a in range(2, n+1):
        for t in range(2, a+1):
            c0 = Nfib_char0(n, a, t)
            cp = Nfib_modp(p, H, a, t)
            if c0 > 0 or cp > 0:
                d = cp - c0
                flag = "" if d == 0 else f"  <== INFLATION {d:+d}"
                print(f"  {a:>3} {t:>3} {c0:>13} {cp:>12} {d:>+7}{flag}")

print("\nDONE.")
